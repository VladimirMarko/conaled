import { createHash } from 'node:crypto';
import { Worker } from 'node:worker_threads';
import { readFile } from 'node:fs/promises';

function slots(shape) {
  if (shape === 'unit') return 0;
  if (shape === 'bit' || shape === 'i32') return 1;
  if (shape?.product?.length === 2) return shape.product.reduce((n, s) => n + slots(s), 0);
  if (shape?.sum?.length === 2) return 1 + shape.sum.reduce((n, s) => n + slots(s), 0);
  throw new Error('Invalid ABI shape');
}

function rawWords(values) {
  if (!Array.isArray(values)) return false;
  for (const value of values) {
    if (!Number.isInteger(value) || value < 0 || value > 0xffffffff) return false;
  }
  return true;
}

function admitted(shape, values) {
  if (!rawWords(values) || values.length !== slots(shape)) return false;
  if (shape === 'unit' || shape === 'i32') return true;
  if (shape === 'bit') return values[0] <= 1;
  if (shape.product) {
    const [a, b] = shape.product, n = slots(a);
    return admitted(a, values.slice(0, n)) && admitted(b, values.slice(n));
  }
  const [a, b] = shape.sum, n = slots(a), tag = values[0];
  const left = values.slice(1, 1 + n), right = values.slice(1 + n);
  return tag === 0 ? admitted(a, left) && right.every(x => x === 0) :
    tag === 1 && left.every(x => x === 0) && admitted(b, right);
}

// This reader admits only the closed selected syntax. Engine validation remains separate.
function selectedSignature(bytes) {
  let offset = 8;
  const refuse = (kind, message) => { throw Object.assign(new Error(message), { kind }); };
  const byte = () => {
    if (offset >= bytes.length) refuse('validation_refused', 'Truncated module');
    return bytes[offset++];
  };
  const u32 = () => {
    let n = 0;
    for (let i = 0; i < 5; i++) {
      const b = byte();
      if (i === 4 && b > 15) refuse('validation_refused', 'Invalid u32 immediate');
      n += (b & 127) * 2 ** (7 * i);
      if (b < 128) return n;
    }
    refuse('validation_refused', 'Invalid u32 immediate');
  };
  const require = (ok, message, kind = 'unsupported') => { if (!ok) refuse(kind, message); };
  let parameters, results;
  for (const id of [1, 3, 7, 10]) {
    require(byte() === id, 'Expected only type, function, export and code sections');
    const length = u32(), end = offset + length;
    require(end <= bytes.length, 'Section length exceeds module', 'validation_refused');
    require(u32() === 1, 'Expected one entry per section');
    if (id === 1) {
      require(byte() === 0x60, 'Expected function type');
      const types = () => {
        const count = u32();
        require(count <= 1000, 'Runtime signature limit', 'resource_refused');
        for (let i = 0; i < count; i++) require(byte() === 0x7f, 'Expected i32 type');
        return count;
      };
      parameters = types(); results = types();
    } else if (id === 3) require(u32() === 0, 'Expected function type index zero', 'binding_refused');
    else if (id === 7) {
      require(u32() === 3 && byte() === 0x72 && byte() === 0x75 && byte() === 0x6e &&
        byte() === 0 && u32() === 0, 'Expected run export bound to function zero', 'binding_refused');
    } else {
      const size = u32(), bodyEnd = offset + size;
      require(size <= 7654321, 'Runtime body size limit', 'resource_refused');
      require(bodyEnd === end, 'Incorrect body length', 'validation_refused');
      const groups = u32();
      let locals = parameters;
      for (let i = 0; i < groups; i++) {
        locals += u32();
        require(locals <= 50000, 'Runtime local limit', 'resource_refused');
        require(byte() === 0x7f, 'Expected i32 local');
      }
      while (offset < bodyEnd - 1) {
        const op = byte();
        if (op === 0x20 || op === 0x21) u32();
        else if (op === 0x41) {
          for (let i = 0; i < 5; i++) {
            const b = byte();
            if (b < 128) break;
          }
        } else require([0x45, 0x71, 0x72, 0x73, 0x6a, 0x1b].includes(op), 'Instruction outside selected subset');
      }
      require(byte() === 0x0b, 'Expected body end', 'validation_refused');
    }
    require(offset === end, 'Section boundary mismatch', 'validation_refused');
  }
  require(offset === bytes.length, 'Additional sections are outside selected subset');
  return { parameters, results };
}

function engine(bytes, values, action, { timeoutMs = 10000, signal } = {}) {
  if (!Number.isFinite(timeoutMs) || timeoutMs <= 0 || timeoutMs > 2147483647) {
    return Promise.resolve({ kind: 'resource_refused', message: 'Positive finite deadline required' });
  }
  if (signal?.aborted) return Promise.resolve({ kind: 'interrupted' });
  return new Promise(resolve => {
    const worker = new Worker(new URL('./wasm-worker.mjs', import.meta.url), {
      workerData: { bytes, values, action },
    });
    let settled = false;
    const finish = async result => {
      if (settled) return;
      settled = true;
      clearTimeout(timer);
      signal?.removeEventListener('abort', abort);
      await worker.terminate();
      resolve(result);
    };
    const abort = () => finish({ kind: 'interrupted' });
    const timer = setTimeout(abort, timeoutMs);
    signal?.addEventListener('abort', abort, { once: true });
    worker.once('message', finish);
    worker.once('error', error => finish({ kind: 'execution_failed', message: error.message }));
    worker.once('exit', code => finish({ kind: 'execution_failed', message: `Worker exited (${code})` }));
  });
}

/** Diagnostic bare-engine execution. This bypasses selected syntax/source admission. */
export async function probeEngine(bytes, values, options) {
  if (!rawWords(values)) {
    return { kind: 'abi_refused' };
  }
  return engine(Uint8Array.from(bytes), [...values], 'run', options);
}

export async function loadArtifact(bytes, descriptor, options) {
  let copy;
  try {
    descriptor = structuredClone(descriptor);
    slots(descriptor.input); slots(descriptor.output);
  } catch (error) { return { kind: 'binding_refused', message: error.message }; }
  try {
    copy = typeof bytes === 'string' ? new Uint8Array(await readFile(bytes)) : Uint8Array.from(bytes);
  } catch (error) { return { kind: 'io_error', message: error.message }; }
  if (copy.length > 16 * 1024 * 1024) return { kind: 'resource_refused', message: 'Module exceeds 16 MiB adapter limit' };
  if (createHash('sha256').update(copy).digest('hex') !== descriptor.sha256) {
    return { kind: 'artifact_mismatch' };
  }
  try {
    const validation = await engine(copy, [], 'validate', options);
    if (validation.kind !== 'validated') return validation;
    const signature = selectedSignature(copy);
    if (signature.parameters !== slots(descriptor.input) || signature.results !== slots(descriptor.output)) {
      return { kind: 'binding_refused', message: 'ABI descriptor differs from module signature' };
    }
    return { kind: 'loaded', artifact: {
      async invoke(values, invokeOptions) {
        if (!admitted(descriptor.input, values)) return { kind: 'abi_refused' };
        const result = await engine(copy, [...values], 'run', invokeOptions);
        if (result.kind !== 'result') return result;
        const output = result.values;
        if (!admitted(descriptor.output, output)) return { kind: 'abi_refused' };
        return { kind: 'result', values: output };
      },
    } };
  } catch (error) {
    return { kind: error.kind ?? 'validation_refused', message: error.message };
  }
}

/** Explicit source-state ownership. Initialization is copied once, before any step. */
export async function createStateful(bytes, descriptor, options) {
  let frozen;
  try { frozen = structuredClone(descriptor); }
  catch (error) { return { kind: 'binding_refused', message: error.message }; }
  try {
    if (!admitted(frozen.state, frozen.initial)) return { kind: 'abi_refused' };
  } catch (error) { return { kind: 'binding_refused', message: error.message }; }
  const loaded = await loadArtifact(bytes, {
    sha256: frozen.sha256,
    input: { product: [frozen.input, frozen.state] },
    output: { product: [frozen.output, frozen.state] },
  }, options);
  if (loaded.kind !== 'loaded') return loaded;
  let state = [...frozen.initial], busy = false;
  return { kind: 'loaded', session: {
    snapshot: () => [...state],
    async step(input, stepOptions) {
      if (busy) return { kind: 'resource_refused', message: 'A state transition is already pending' };
      if (!admitted(frozen.input, input)) return { kind: 'abi_refused' };
      busy = true;
      try {
        const result = await loaded.artifact.invoke([...input, ...state], stepOptions);
        if (result.kind !== 'result') return result;
        const n = slots(frozen.output);
        state = result.values.slice(n);
        return { kind: 'result', values: result.values.slice(0, n), state: [...state] };
      } finally { busy = false; }
    },
  } };
}

/** One complete word conversion. Costs count scalar checks, bit visits and writes,
 * not JS instructions, allocation bytes or engine work. Both directions allocate
 * a new result; caller-owned inputs are never retained or changed. */
export function convertWord(values, from, to) {
  if (!['boolean', 'packed'].includes(from) || !['boolean', 'packed'].includes(to)) {
    return { kind: 'unsupported' };
  }
  if (!Array.isArray(values) || values.length !== (from === 'boolean' ? 32 : 1)) {
    return { kind: 'abi_refused' };
  }
  const cost = { validatedSlots: 0, convertedBits: 0, writtenSlots: 0 };
  for (const value of values) {
    cost.validatedSlots++;
    if (!Number.isInteger(value) || value < 0 || value > (from === 'boolean' ? 1 : 0xffffffff)) {
      return { kind: 'abi_refused' };
    }
  }
  const result = [];
  if (from === to) {
    for (const value of values) { result.push(value); cost.writtenSlots++; }
  } else if (to === 'packed') {
    let word = 0;
    for (let i = 0; i < 32; i++) { word += values[i] * 2 ** i; cost.convertedBits++; }
    result.push(word); cost.writtenSlots++;
  } else {
    for (let i = 0; i < 32; i++) {
      result.push((values[0] >>> i) & 1); cost.convertedBits++; cost.writtenSlots++;
    }
  }
  return { kind: 'result', values: result, cost };
}

/** Bounded, caller-selected realization of one word selector. Public invocation
 * uses [canonicalTag, x, y] and returns [selected, x, y] in unsigned words.
 * The cost reports conversion bit visits and actual engine ABI arities only;
 * hashing, validation, worker copies/startup and engine work remain separate. */
export async function loadWordSelector(bytes, { representation, sha256 }, options = {}) {
  if (!['boolean', 'packed'].includes(representation)) return { kind: 'unsupported' };
  const maxSlots = options.maxSlots ?? 1000;
  const parameters = representation === 'packed' ? 3 : 65;
  const results = representation === 'packed' ? 3 : 96;
  if (!Number.isSafeInteger(maxSlots) || maxSlots < 0 || Math.max(parameters, results) > maxSlots) {
    return { kind: 'resource_refused' };
  }
  const wordShape = n => n === 0 ? 'unit' : { product: ['bit', wordShape(n - 1)] };
  const word = representation === 'packed' ? 'i32' : wordShape(32);
  const loaded = await loadArtifact(bytes, { sha256,
    input: { product: ['bit', { product: [word, word] }] },
    output: { product: [word, { product: [word, word] }] },
  }, options);
  if (loaded.kind !== 'loaded') return loaded;
  return { kind: 'loaded', representation, artifact: {
    async invoke(values, invokeOptions) {
      if (!rawWords(values) || values.length !== 3 || values[0] > 1) return { kind: 'abi_refused' };
      let engineInput = values;
      let convertedBits = 0;
      if (representation === 'boolean') {
        const x = convertWord([values[1]], 'packed', 'boolean');
        const y = convertWord([values[2]], 'packed', 'boolean');
        engineInput = [values[0], ...x.values, ...y.values];
        convertedBits += x.cost.convertedBits + y.cost.convertedBits;
      }
      const result = await loaded.artifact.invoke(engineInput, invokeOptions);
      if (result.kind !== 'result') return result;
      let output = result.values;
      if (representation === 'boolean') {
        output = [];
        for (let offset = 0; offset < 96; offset += 32) {
          const word = convertWord(result.values.slice(offset, offset + 32), 'boolean', 'packed');
          if (word.kind !== 'result') return word;
          output.push(word.values[0]); convertedBits += word.cost.convertedBits;
        }
      }
      return { kind: 'result', values: output,
        cost: { convertedBits, marshalledInputs: engineInput.length, marshalledOutputs: result.values.length } };
    },
  } };
}
