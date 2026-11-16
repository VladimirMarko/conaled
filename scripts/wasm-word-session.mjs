import { createStateful, convertWord } from './wasm-host.mjs';

const kinds = ['boolean', 'packed'];
const slots = kind => kind === 'boolean' ? 64 : 2;
const wordShape = n => n === 0 ? 'unit' : { product: ['bit', wordShape(n - 1)] };
const word = kind => kind === 'boolean' ? wordShape(32) : 'i32';

/** Exact raw-state admission and executable conversion. Each result owns fresh
 * arrays; logical counters cover scalar validation, bit visits and result writes. */
export function convertWordState(raw, origin, target) {
  const cost = { validatedSlots: 0, convertedBits: 0, writtenSlots: 0 };
  if (!kinds.includes(origin) || !kinds.includes(target)) return { kind: 'unsupported', cost };
  if (!Array.isArray(raw) || raw.length !== slots(origin)) return { kind: 'abi_refused', cost };
  const state = [];
  let packed = 0;
  // Validate the same scalar we consume. Caller iterators and getters must not
  // substitute different values between admission and conversion.
  for (let index = 0; index < slots(origin); index++) {
    const value = raw[index];
    cost.validatedSlots++;
    if (!Number.isInteger(value) || value < 0 || value > (origin === 'boolean' ? 1 : 0xffffffff)) {
      return { kind: 'abi_refused', cost };
    }
    if (origin === target) {
      state.push(value); cost.writtenSlots++;
    } else if (target === 'packed') {
      packed += value * 2 ** (index % 32);
      cost.convertedBits++;
      if (index % 32 === 31) {
        state.push(packed); cost.writtenSlots++;
        packed = 0;
      }
    } else {
      for (let bit = 0; bit < 32; bit++) {
        state.push((value >>> bit) & 1); cost.convertedBits++; cost.writtenSlots++;
      }
    }
  }
  return { kind: 'result', state, cost };
}

// Only selected descriptor fields cross the ownership boundary. Arbitrary extra
// caller fields, including arrays, are neither cloned nor retained.
function configurationFields(config) {
  return { representation: config?.representation, sha256: config?.sha256 };
}

function migrationCost(sourceSlots) {
  return { events: [], snapshotSlots: 0, validatedSlots: 0, convertedBits: 0,
    writtenSlots: 0, initialCopySlots: 0, activeCopySlots: 0, installations: 0,
    peakOwnedStateSlots: 2 * sourceSlots, artifactBytes: 0 };
}

const typedArray = Object.getPrototypeOf(Uint8Array.prototype);
const byteField = name => Object.getOwnPropertyDescriptor(typedArray, name).get;
const nativeBuffer = byteField('buffer'), nativeOffset = byteField('byteOffset'), nativeLength = byteField('byteLength');

// A native view ignores caller-shadowed metadata and iterators without copying
// bytes. The existing loader owns the actual copy before its first await.
function artifactView(bytes) {
  if (!(bytes instanceof Uint8Array)) return bytes;
  return new Uint8Array(nativeBuffer.call(bytes), nativeOffset.call(bytes), nativeLength.call(bytes));
}

function budgetRefusal(bytes, oldBytes, requiredSlots, options) {
  if (!(bytes instanceof Uint8Array)) return { kind: 'binding_refused', message: 'Supply artifact bytes as Uint8Array' };
  const maxSlots = options.maxOwnedStateSlots ?? 384;
  const maxBytes = options.maxAdapterBytes ?? 48 * 1024 * 1024;
  if (!Number.isSafeInteger(maxSlots) || maxSlots < requiredSlots ||
      !Number.isSafeInteger(maxBytes) || maxBytes < oldBytes + 2 * bytes.byteLength) {
    return { kind: 'resource_refused', requiredOwnedStateSlots: requiredSlots,
      requiredAdapterBytes: oldBytes + 2 * bytes.byteLength };
  }
}

function descriptor(representation, sha256, initial) {
  const shape = word(representation);
  return { sha256, input: shape, output: shape, state: { product: [shape, shape] }, initial };
}

/** A source-word interface to a private between-tick state owner.
 * maxOwnedStateSlots admits named state arrays: current+initial owners,
 * snapshot, converted state and candidate initial/current copies (3S+3T).
 * maxAdapterBytes admits the old loader copy plus target loader/worker byte
 * copies. Caller buffers, recursive ABI slices, shapes, engine storage and GC
 * are external; neither budget claims a physical heap bound. */
export async function createWordSession(bytes, configuration, options = {}) {
  let config;
  try { config = { ...configurationFields(configuration), initial: configuration?.initial }; }
  catch (error) { return { kind: 'binding_refused', message: error.message }; }
  if (!kinds.includes(config?.representation)) return { kind: 'unsupported' };
  try { bytes = artifactView(bytes); }
  catch (error) { return { kind: 'binding_refused', message: error.message }; }
  const refused = budgetRefusal(bytes, 0, 3 * slots(config.representation), options);
  if (refused) return refused;
  const converted = convertWordState(config.initial, 'packed', config.representation);
  if (converted.kind !== 'result') return converted;
  const retainedBytes = bytes.byteLength;
  const loaded = await createStateful(bytes,
    descriptor(config.representation, config.sha256, converted.state), options);
  if (loaded.kind !== 'loaded') return loaded;
  if (options.signal?.aborted) return { kind: 'interrupted' };
  let owner = loaded.session, representation = config.representation, busy = false;
  let artifactBytes = retainedBytes;
  return { kind: 'loaded', session: {
    get representation() { return representation; },
    snapshot() { return convertWordState(owner.snapshot(), representation, 'packed').state; },
    async migrate(targetBytes, configuration, migrationOptions = {}) {
      const sourceSlots = slots(representation), cost = migrationCost(sourceSlots);
      if (busy) return { kind: 'resource_refused', message: 'A transition is already pending', cost };
      // Acquire ownership before descriptor/options accessors can call back here.
      busy = true;
      let installed = false;
      try {
        let target;
        try { target = configurationFields(configuration); }
        catch (error) { return { kind: 'binding_refused', message: error.message, cost }; }
        if (!kinds.includes(target.representation)) return { kind: 'unsupported', cost };
        const settings = { signal: migrationOptions.signal, timeoutMs: migrationOptions.timeoutMs,
          maxOwnedStateSlots: migrationOptions.maxOwnedStateSlots, maxAdapterBytes: migrationOptions.maxAdapterBytes };
        const targetSlots = slots(target.representation), required = 3 * sourceSlots + 3 * targetSlots;
        targetBytes = artifactView(targetBytes);
        const refused = budgetRefusal(targetBytes, artifactBytes, required, settings);
        if (refused) return { ...refused, cost };
        if (settings.signal?.aborted) return { kind: 'interrupted', cost };
        const snapshot = owner.snapshot();
        cost.snapshotSlots = sourceSlots;
        cost.peakOwnedStateSlots = 3 * sourceSlots;
        cost.events.push({ kind: 'snapshot', slots: sourceSlots });
        const converted = convertWordState(snapshot, representation, target.representation);
        Object.assign(cost, converted.cost);
        cost.events.push({ kind: 'validateSource', slots: converted.cost.validatedSlots });
        if (converted.kind !== 'result') return { kind: converted.kind, cost };
        cost.events.push({ kind: 'convert', bits: cost.convertedBits, slots: cost.writtenSlots });
        cost.initialCopySlots = targetSlots;
        cost.peakOwnedStateSlots = 3 * sourceSlots + 2 * targetSlots;
        cost.events.push({ kind: 'cloneInitial', slots: targetSlots });
        cost.artifactBytes = targetBytes.byteLength;
        cost.events.push({ kind: 'hostPrepare', artifactBytes: cost.artifactBytes, stateSlots: targetSlots });
        const prepared = await createStateful(targetBytes,
          descriptor(target.representation, target.sha256, converted.state), settings);
        if (prepared.kind !== 'loaded') return { ...prepared, cost };
        cost.activeCopySlots = targetSlots;
        cost.peakOwnedStateSlots = required;
        cost.events.push({ kind: 'copyActive', slots: targetSlots });
        // Cancellation may arrive after host validation but before this continuation.
        if (settings.signal?.aborted) return { kind: 'interrupted', cost };
        owner = prepared.session;
        representation = target.representation;
        artifactBytes = cost.artifactBytes;
        installed = true;
        cost.installations = 1;
        cost.events.push({ kind: 'install' });
        return { kind: 'migrated', cost };
      } catch (error) {
        return { kind: 'execution_failed', message: error.message, cost };
      } finally {
        if (!installed && cost.events.length) cost.events.push({ kind: 'discardCandidate' });
        busy = false;
      }
    },
    async step(input, stepOptions = {}) {
      if (busy) return { kind: 'resource_refused', message: 'A transition is already pending' };
      const encoded = convertWord([input], 'packed', representation);
      if (encoded.kind !== 'result') return encoded;
      busy = true;
      try {
        const result = await owner.step(encoded.values, stepOptions);
        if (result.kind !== 'result') return result;
        const output = convertWord(result.values, representation, 'packed');
        const state = convertWordState(result.state, representation, 'packed');
        return { kind: 'result', value: output.values[0], state: state.state };
      } finally { busy = false; }
    },
  } };
}
