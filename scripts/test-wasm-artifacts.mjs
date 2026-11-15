import test from 'node:test';
import assert from 'node:assert/strict';
import { readFile } from 'node:fs/promises';
import { createHash } from 'node:crypto';
import { loadArtifact, createStateful, probeEngine } from './wasm-host.mjs';

const directory = process.env.WASM_ARTIFACTS;
if (!directory) throw new Error('Set WASM_ARTIFACTS to the output of scripts/WasmEmit.lean');
const word = n => n === 0 ? 'unit' : { product: ['bit', word(n - 1)] };
const bits = n => Array.from({ length: 32 }, (_, i) => Number((n >> BigInt(i)) & 1n));
async function artifact(name, descriptor) {
  const bytes = await readFile(`${directory}/${name}.wasm`);
  return { bytes, descriptor: { ...descriptor, sha256: createHash('sha256').update(bytes).digest('hex') } };
}

test('native selector retains all 96 bits through overflow and every carry length', async () => {
  const { bytes, descriptor } = await artifact('selector32', {
    input: { product: ['bit', { product: [word(32), word(32)] }] },
    output: { product: [word(32), { product: [word(32), word(32)] }] },
  });
  const loaded = await loadArtifact(bytes, descriptor);
  assert.equal(loaded.kind, 'loaded', JSON.stringify(loaded));
  const pairs = [[0n, 0n], [0x80000000n, 0xffffffffn], [0x12345678n, 0x87654321n]];
  for (let k = 0n; k <= 32n; k++) pairs.push([(1n << k) - 1n, 1n]);
  for (const [x, y] of pairs) for (const tag of [0, 1]) {
    const expected = tag ? (x + y) & 0xffffffffn : x ^ y;
    assert.deepEqual(await loaded.artifact.invoke([tag, ...bits(x), ...bits(y)]),
      { kind: 'result', values: [...bits(expected), ...bits(x), ...bits(y)] });
  }
});

const nested = { sum: [{ sum: ['bit', 'unit'] }, { product: ['bit', 'bit'] }] };
// Rows are the source case analysis, independent of emitted instructions.
const nestedRows = [
  [[0, 0, 0, 0, 0], [0, 0]], [[0, 0, 1, 0, 0], [1, 0]],
  [[0, 1, 0, 0, 0], [0, 1]], [[1, 0, 0, 0, 0], [1, 0]],
  [[1, 0, 0, 0, 1], [1, 1]], [[1, 0, 0, 1, 0], [0, 0]],
  [[1, 0, 0, 1, 1], [0, 1]],
];

test('native nested case preserves the free variable and refuses every malformed Boolean payload', async () => {
  const { bytes, descriptor } = await artifact('nested', {
    input: { product: ['bit', nested] },
    output: { product: [{ product: ['bit', 'bit'] }, 'bit'] },
  });
  const loaded = await loadArtifact(bytes, descriptor);
  assert.equal(loaded.kind, 'loaded', JSON.stringify(loaded));
  for (const free of [0, 1]) for (let mask = 0; mask < 32; mask++) {
    const payload = Array.from({ length: 5 }, (_, i) => (mask >> i) & 1);
    const row = nestedRows.find(([input]) => input.every((x, i) => x === payload[i]));
    const result = await loaded.artifact.invoke([free, ...payload]);
    if (row) assert.deepEqual(result, { kind: 'result', values: [...row[1], free] });
    else {
      assert.equal(result.kind, 'abi_refused');
      // Inactive-payload discipline belongs to the adapter, not Wasm validation.
      assert.equal((await probeEngine(bytes, [free, ...payload])).kind, 'result');
    }
  }
  for (let i = 0; i < 6; i++) {
    const raw = [0, 0, 0, 0, 0, 0]; raw[i] = 2;
    assert.equal((await loaded.artifact.invoke(raw)).kind, 'abi_refused');
  }
});

test('native unit has no arguments/results and raw noncanonical tags stay outside the source ABI', async () => {
  const unit = await artifact('unit', { input: 'unit', output: 'unit' });
  const loadedUnit = await loadArtifact(unit.bytes, unit.descriptor);
  assert.equal(loadedUnit.kind, 'loaded');
  assert.deepEqual(await loadedUnit.artifact.invoke([]), { kind: 'result', values: [] });
  assert.equal((await loadedUnit.artifact.invoke([0])).kind, 'abi_refused');
  const not = await artifact('not', { input: 'bit', output: 'bit' });
  const loadedNot = await loadArtifact(not.bytes, not.descriptor);
  assert.equal(loadedNot.kind, 'loaded');
  assert.deepEqual(await loadedNot.artifact.invoke([0]), { kind: 'result', values: [1] });
  assert.deepEqual(await loadedNot.artifact.invoke([1]), { kind: 'result', values: [0] });
  for (const raw of [2, 0x80000000, 0xffffffff]) {
    assert.equal((await loadedNot.artifact.invoke([raw])).kind, 'abi_refused');
    assert.deepEqual(await probeEngine(not.bytes, [raw]), { kind: 'result', values: [0] });
  }
});

test('native two-delay preserves every intermediate output/state and commits only admitted success', async () => {
  const { bytes, descriptor } = await artifact('two-delay', {
    input: 'bit', output: 'bit', state: { product: ['bit', 'bit'] }, initial: [0, 0],
  });
  const loaded = await createStateful(bytes, descriptor);
  assert.equal(loaded.kind, 'loaded');
  const { session } = loaded;
  descriptor.initial.fill(1);
  let old = 0, recent = 0;
  for (const input of [1, 0, 1, 1, 0, 0, 0, 1, 0]) {
    assert.deepEqual(session.snapshot(), [old, recent]);
    assert.equal((await session.step([2])).kind, 'abi_refused');
    assert.equal((await session.step([input], { timeoutMs: 0 })).kind, 'resource_refused');
    const controller = new AbortController(); controller.abort();
    assert.equal((await session.step([input], { signal: controller.signal })).kind, 'interrupted');
    assert.deepEqual(session.snapshot(), [old, recent]);
    assert.deepEqual(await session.step([input]), { kind: 'result', values: [recent], state: [input, old] });
    recent = old; old = input;
    assert.deepEqual(session.snapshot(), [old, recent]);
  }
  // The public initialized client starts at false/false; arbitrary admitted
  // initial pairs also exercise all eight input/state transitions.
  for (const a of [0, 1]) for (const b of [0, 1]) for (const input of [0, 1]) {
    const result = await createStateful(bytes, { ...descriptor, initial: [a, b] });
    assert.deepEqual(await result.session.step([input]),
      { kind: 'result', values: [b], state: [input, a] });
  }
});
