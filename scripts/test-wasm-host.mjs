import test from 'node:test';
import assert from 'node:assert/strict';
import { createHash } from 'node:crypto';
import { loadArtifact, probeEngine, createStateful } from './wasm-host.mjs';

// Independently specified foreign test module: (func (export "run") (param i32) (result i32) local.get 0).
// Production artifacts must instead come from scripts/WasmEmit.lean.
const identity = Buffer.from('0061736d0100000001060160017f017f030201000707010372756e00000a0601040020000b', 'hex');
const sha256 = bytes => createHash('sha256').update(bytes).digest('hex');
const rawIdentity = { sha256: sha256(identity), input: 'i32', output: 'i32' };

test('raw i32 identity preserves complete unsigned bit patterns', async () => {
  const loaded = await loadArtifact(identity, rawIdentity);
  assert.equal(loaded.kind, 'loaded', JSON.stringify(loaded));
  for (const x of [0, 1, 0x7fffffff, 0x80000000, 0xffffffff]) {
    assert.deepEqual(await loaded.artifact.invoke([x]), { kind: 'result', values: [x] });
  }
});

test('raw i32 rejects coercible values and wrong arity before invocation', async () => {
  const { artifact } = await loadArtifact(identity, rawIdentity);
  for (const input of [[-1], [2 ** 32], [1.5], [NaN], [Infinity], ['1'], [true], [null], [], [0, 1]]) {
    assert.equal((await artifact.invoke(input)).kind, 'abi_refused', String(input));
  }
});

// Five-slot identity, specified directly for ABI tests, not a production encoder.
const identity5 = Buffer.from('0061736d01000000010e0160057f7f7f7f7f057f7f7f7f7f030201000707010372756e00000a0e010c00200020012002200320040b', 'hex');
const nested = { sum: [{ sum: ['bit', 'unit'] }, { product: ['bit', 'bit'] }] };
const nestedValues = [
  [0, 0, 0, 0, 0], [0, 0, 1, 0, 0], [0, 1, 0, 0, 0],
  [1, 0, 0, 0, 0], [1, 0, 0, 0, 1], [1, 0, 0, 1, 0], [1, 0, 0, 1, 1],
];

test('nested sums admit exactly canonical slots, including every inactive payload', async () => {
  const loaded = await loadArtifact(identity5, { sha256: sha256(identity5), input: nested, output: nested });
  assert.equal(loaded.kind, 'loaded');
  for (let bits = 0; bits < 32; bits++) {
    const input = Array.from({ length: 5 }, (_, i) => (bits >> i) & 1);
    const result = await loaded.artifact.invoke(input);
    if (nestedValues.some(v => JSON.stringify(v) === JSON.stringify(input))) {
      assert.deepEqual(result, { kind: 'result', values: input });
    } else assert.equal(result.kind, 'abi_refused', JSON.stringify(input));
  }
  for (let slot = 0; slot < 5; slot++) {
    const input = [0, 0, 0, 0, 0]; input[slot] = 2;
    assert.equal((await loaded.artifact.invoke(input)).kind, 'abi_refused');
  }
});

test('content binding detects valid opcode and export-name mutations', async () => {
  const opcode = Buffer.from(identity); opcode[opcode.length - 3] = 0x41; // constant 0 replaces local.get 0
  const exported = Buffer.from(identity); exported[24] = 0x73; // run -> sun
  for (const mutated of [opcode, exported]) {
    assert.equal(WebAssembly.validate(mutated), true);
    assert.equal((await loadArtifact(mutated, rawIdentity)).kind, 'artifact_mismatch');
  }
});

test('load verifies the intended run export and full signature independently of the digest', async () => {
  const exported = Buffer.from(identity); exported[24] = 0x73;
  assert.equal((await loadArtifact(exported, { ...rawIdentity, sha256: sha256(exported) })).kind, 'binding_refused');
  assert.equal((await loadArtifact(identity, { ...rawIdentity, input: 'unit' })).kind, 'binding_refused');
  assert.equal((await loadArtifact(identity, { ...rawIdentity, output: 'unit' })).kind, 'binding_refused');
});

const trapping = Buffer.from('0061736d01000000010401600000030201000707010372756e00000a05010300000b', 'hex');
const looping = Buffer.from('0061736d01000000010401600000030201000707010372756e00000a0901070003400c000b0b', 'hex');

test('selected adapter refuses foreign instructions while bare engine reports traps and interruption', async () => {
  for (const bytes of [trapping, looping]) {
    assert.equal(WebAssembly.validate(bytes), true);
    const result = await loadArtifact(bytes, { sha256: sha256(bytes), input: 'unit', output: 'unit' });
    assert.equal(result.kind, 'unsupported');
  }
  assert.equal((await probeEngine(trapping, [])).kind, 'execution_failed');
  assert.equal((await probeEngine(looping, [], { timeoutMs: 100 })).kind, 'interrupted');
  assert.equal((await probeEngine(identity, [1], { timeoutMs: 0 })).kind, 'resource_refused');
});

test('loaded artifact owns immutable bytes and ABI descriptors across asynchronous calls', async () => {
  const bytes = Buffer.from(identity5);
  const descriptor = { sha256: sha256(bytes), input: structuredClone(nested), output: structuredClone(nested) };
  const loading = loadArtifact(bytes, descriptor);
  bytes.fill(0); descriptor.input = 'unit'; descriptor.output = 'unit';
  const loaded = await loading;
  assert.equal(loaded.kind, 'loaded');
  const input = [1, 0, 0, 0, 1];
  const running = loaded.artifact.invoke(input);
  input.fill(0);
  assert.deepEqual(await running, { kind: 'result', values: [1, 0, 0, 0, 1] });
});

test('loading distinguishes IO failure from invalid sections, indices and immediates', async () => {
  assert.equal((await loadArtifact('/no/such/conaled-artifact.wasm', rawIdentity)).kind, 'io_error');
  const badLength = Buffer.from(identity); badLength[9] = 5;
  const badLocal = Buffer.from(identity); badLocal[badLocal.length - 2] = 1;
  const badExport = Buffer.from(identity); badExport[28] = 1;
  const badImmediate = Buffer.concat([identity.subarray(0, -2), Buffer.from([0x80, 0x80, 0x80, 0x80, 0x10, 0x0b])]);
  // Adjust enclosing sizes so rejection concerns the immediate rather than truncation.
  badImmediate[30] += 4; badImmediate[32] += 4;
  for (const bytes of [badLength, badLocal, badExport, badImmediate]) {
    assert.equal(WebAssembly.validate(bytes), false);
    assert.equal((await loadArtifact(bytes, { ...rawIdentity, sha256: sha256(bytes) })).kind, 'validation_refused');
  }
});

const twoDelay = Buffer.from('0061736d01000000010a0160037f7f7f037f7f7f030201000707010372756e00000a0a0108002002200020010b', 'hex');
const delayDescriptor = { sha256: sha256(twoDelay), input: 'bit', output: 'bit', state: { product: ['bit', 'bit'] }, initial: [0, 0] };

test('two-delay session initializes once and retains every intermediate output and state', async () => {
  const descriptor = structuredClone(delayDescriptor);
  const loaded = await createStateful(twoDelay, descriptor);
  assert.equal(loaded.kind, 'loaded', JSON.stringify(loaded));
  descriptor.initial.fill(1);
  const { session } = loaded;
  session.snapshot().fill(1);
  assert.deepEqual(session.snapshot(), [0, 0]);
  for (const [input, output, state] of [[1, 0, [1, 0]], [0, 0, [0, 1]], [1, 1, [1, 0]], [1, 0, [1, 1]]]) {
    assert.deepEqual(await session.step([input]), { kind: 'result', values: [output], state });
    assert.deepEqual(session.snapshot(), state);
  }
});

test('refused, interrupted and overlapping calls cannot overwrite committed state', async () => {
  const { session } = await createStateful(twoDelay, delayDescriptor);
  assert.equal((await session.step([2])).kind, 'abi_refused');
  const cancellation = new AbortController();
  const cancelled = session.step([1], { signal: cancellation.signal });
  cancellation.abort();
  assert.equal((await cancelled).kind, 'interrupted');
  assert.deepEqual(session.snapshot(), [0, 0]);
  const first = session.step([1]);
  const overlapping = session.step([0]);
  assert.equal((await overlapping).kind, 'resource_refused');
  assert.deepEqual(await first, { kind: 'result', values: [0], state: [1, 0] });
  assert.deepEqual(await session.step([0]), { kind: 'result', values: [0], state: [0, 1] });
});

test('noncanonical returned output refuses the whole transition without committing returned state', async () => {
  const invalidResult = Buffer.from(twoDelay);
  invalidResult[invalidResult.length - 7] = 0x41;
  const { session } = await createStateful(invalidResult, { ...delayDescriptor, sha256: sha256(invalidResult) });
  assert.equal((await session.step([1])).kind, 'abi_refused');
  assert.deepEqual(session.snapshot(), [0, 0]);
});
