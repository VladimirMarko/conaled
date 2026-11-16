import test from 'node:test';
import assert from 'node:assert/strict';
import { readFile } from 'node:fs/promises';
import { createHash } from 'node:crypto';

const bits = x => Array.from({ length: 32 }, (_, i) => (x >>> i) & 1);
test('state conversion retains both asymmetric words and refuses malformed states', async () => {
  const { convertWordState } = await import('./wasm-word-session.mjs');
  const raw = [...bits(0x80000001), ...bits(0xffffffff)];
  const converted = convertWordState(raw, 'boolean', 'packed');
  assert.equal(converted.kind, 'result');
  assert.deepEqual(converted.state, [0x80000001, 0xffffffff]);
  assert.deepEqual(convertWordState(converted.state, 'packed', 'boolean').state, raw);
  assert.equal(converted.cost.convertedBits, 64);
  for (const bad of [[], raw.slice(1), [...raw, 0], raw.map((v, i) => i === 20 ? 2 : v)]) {
    assert.equal(convertWordState(bad, 'boolean', 'packed').kind, 'abi_refused');
  }
  for (const bad of [[0], [0, 1, 2], [-1, 0], [2 ** 32, 0], [0, 1.5]]) {
    assert.equal(convertWordState(bad, 'packed', 'boolean').kind, 'abi_refused');
  }
});

const directory = process.env.WASM_ARTIFACTS;
test('conversion validates the indexed scalars it consumes exactly once', async () => {
  const { convertWordState } = await import('./wasm-word-session.mjs');
  const hidden = Array(64).fill(2);
  hidden[Symbol.iterator] = function* () {};
  assert.equal(convertWordState(hidden, 'boolean', 'packed').kind, 'abi_refused');
  for (const origin of ['boolean', 'packed']) for (const target of ['boolean', 'packed']) {
    const raw = Array(origin === 'boolean' ? 64 : 2).fill(0);
    let reads = 0;
    Object.defineProperty(raw, 0, { get() { return ++reads === 1 ? 0 : -1; } });
    const result = convertWordState(raw, origin, target);
    assert.equal(result.kind, 'result');
    assert.equal(reads, 1);
    assert.deepEqual(result.state, Array(target === 'boolean' ? 64 : 2).fill(0));
  }
});

async function artifact(representation) {
  assert.ok(directory, 'Set WASM_ARTIFACTS to the native emitter output');
  const bytes = await readFile(`${directory}/word-delay-${representation}.wasm`);
  return { bytes, descriptor: { representation, sha256: createHash('sha256').update(bytes).digest('hex') } };
}
const seed = [0x12345678, 0xffffffff];
async function start(representation, initial = seed, options) {
  const { createWordSession } = await import('./wasm-word-session.mjs');
  const a = await artifact(representation);
  const loaded = await createWordSession(a.bytes, { ...a.descriptor, initial }, options);
  assert.equal(loaded.kind, 'loaded', JSON.stringify(loaded));
  return loaded.session;
}

test('actual artifacts observe both seeded registers and overflow at every tick', async () => {
  for (const representation of ['boolean', 'packed']) {
    const session = await start(representation);
    assert.deepEqual(session.snapshot(), seed);
    assert.equal(session.representation, representation);
    for (const [input, output, state] of [
      [1, 0, [1, 0x12345678]],
      [0xaaaaaaaa, 0xbcdf0122, [0xaaaaaaaa, 1]],
      [0xffffffff, 0, [0xffffffff, 0xaaaaaaaa]],
    ]) {
      const result = await session.step(input);
      assert.equal(result.kind, 'result');
      assert.equal(result.value, output);
      assert.deepEqual(result.state, state);
      assert.deepEqual(session.snapshot(), state);
    }
  }
});

test('live migration both ways and back preserves empty and complete future suffixes', async () => {
  for (const origin of ['boolean', 'packed']) {
    const target = origin === 'boolean' ? 'packed' : 'boolean';
    const session = await start(origin);
    await session.step(1); await session.step(0xaaaaaaaa);
    for (const representation of [target, origin, target]) {
      const a = await artifact(representation);
      const result = await session.migrate(a.bytes, a.descriptor);
      assert.equal(result.kind, 'migrated');
      assert.equal(session.representation, representation);
      assert.deepEqual(session.snapshot(), [0xaaaaaaaa, 1]);
    }
    for (const [input, value, state] of [
      [0xffffffff, 0, [0xffffffff, 0xaaaaaaaa]],
      [0x55555555, 0xffffffff, [0x55555555, 0xffffffff]],
      [7, 6, [7, 0x55555555]],
    ]) assert.deepEqual(await session.step(input), { kind: 'result', value, state });
  }
});

test('migration budgets refuse before copying and failed preparation retains its charged work', async () => {
  const session = await start('boolean');
  await session.step(1);
  const a = await artifact('packed');
  const refused = await session.migrate(a.bytes, a.descriptor, { maxOwnedStateSlots: 197 });
  assert.equal(refused.kind, 'resource_refused');
  assert.deepEqual(refused.cost.events, []);
  assert.deepEqual(session.snapshot(), [1, 0x12345678]);
  const mismatch = await session.migrate(a.bytes, { ...a.descriptor, sha256: '0'.repeat(64) });
  assert.equal(mismatch.kind, 'artifact_mismatch');
  assert.equal(mismatch.cost.snapshotSlots, 64);
  assert.equal(mismatch.cost.convertedBits, 64);
  assert.equal(mismatch.cost.initialCopySlots, 2);
  assert.equal(mismatch.cost.activeCopySlots, 0);
  assert.equal(mismatch.cost.installations, 0);
  assert.equal(session.representation, 'boolean');
  const accepted = await session.migrate(a.bytes, a.descriptor, { maxOwnedStateSlots: 198 });
  assert.equal(accepted.kind, 'migrated');
  assert.equal(accepted.cost.peakOwnedStateSlots, 198);
  assert.equal(accepted.cost.activeCopySlots, 2);
  assert.equal(accepted.cost.installations, 1);
});

test('malformed conversion reports validation work before failure without hidden codec copies', async () => {
  const { convertWordState } = await import('./wasm-word-session.mjs');
  const raw = [...bits(1), ...bits(2)]; raw[40] = 2;
  const bad = convertWordState(raw, 'boolean', 'packed');
  assert.equal(bad.kind, 'abi_refused');
  assert.deepEqual(bad.cost, { validatedSlots: 41, convertedBits: 40, writtenSlots: 1 });
});

test('caller mutations cannot alter descriptors, snapshots, results or a pending owner transfer', async () => {
  const { createWordSession } = await import('./wasm-word-session.mjs');
  const a = await artifact('packed');
  const config = { ...a.descriptor, initial: [...seed] };
  const creating = createWordSession(a.bytes, config);
  config.initial.fill(0); config.representation = 'boolean'; config.sha256 = 'bad'; a.bytes.fill(0);
  const loaded = await creating;
  assert.equal(loaded.kind, 'loaded');
  const session = loaded.session;
  const snapshot = session.snapshot(); snapshot.fill(0);
  assert.deepEqual(session.snapshot(), seed);
  const result = await session.step(1); result.state.fill(0);
  assert.deepEqual(session.snapshot(), [1, 0x12345678]);
  const target = await artifact('boolean');
  const moving = session.migrate(target.bytes, target.descriptor);
  target.descriptor.representation = 'packed'; target.descriptor.sha256 = 'bad'; target.bytes.fill(0);
  assert.equal((await moving).kind, 'migrated');
  assert.equal(session.representation, 'boolean');
  assert.deepEqual(session.snapshot(), [1, 0x12345678]);
});

test('exclusive owner rejects concurrent ticks and migrations and recovers after interruption', async () => {
  const session = await start('packed');
  const target = await artifact('boolean');
  const tick = session.step(1);
  assert.equal((await session.migrate(target.bytes, target.descriptor)).kind, 'resource_refused');
  assert.equal((await session.step(2)).kind, 'resource_refused');
  assert.equal((await tick).kind, 'result');
  const abort = new AbortController();
  const moving = session.migrate(target.bytes, target.descriptor, { signal: abort.signal });
  assert.equal((await session.step(2)).kind, 'resource_refused');
  assert.equal((await session.migrate(target.bytes, target.descriptor)).kind, 'resource_refused');
  abort.abort();
  const interrupted = await moving;
  assert.equal(interrupted.kind, 'interrupted');
  assert.equal(interrupted.cost.installations, 0);
  assert.equal(session.representation, 'packed');
  assert.deepEqual(session.snapshot(), [1, 0x12345678]);
  assert.deepEqual(await session.step(0xaaaaaaaa),
    { kind: 'result', value: 0xbcdf0122, state: [0xaaaaaaaa, 1] });
  assert.equal((await session.migrate(target.bytes, target.descriptor)).kind, 'migrated');
});

test('bad bytes, binding, state and deadlines refuse without resetting a live continuation', async () => {
  const { createWordSession } = await import('./wasm-word-session.mjs');
  const target = await artifact('packed');
  for (const initial of [[], [0], [-1, 0], [0, 1.5], [0, 2 ** 32]]) {
    assert.equal((await createWordSession(target.bytes, { ...target.descriptor, initial })).kind, 'abi_refused');
  }
  const session = await start('boolean');
  await session.step(1); await session.step(0xaaaaaaaa);
  const broken = Uint8Array.of(0, 1, 2);
  for (const [bytes, config, options, expected] of [
    [broken, { ...target.descriptor, sha256: createHash('sha256').update(broken).digest('hex') }, {}, 'validation_refused'],
    [target.bytes, { ...target.descriptor, representation: 'boolean' }, {}, 'binding_refused'],
    [target.bytes, target.descriptor, { timeoutMs: 0 }, 'resource_refused'],
    [target.bytes, target.descriptor, { maxAdapterBytes: 0 }, 'resource_refused'],
    [target.bytes, target.descriptor, { signal: AbortSignal.abort() }, 'interrupted'],
  ]) {
    assert.equal((await session.migrate(bytes, config, options)).kind, expected);
    assert.equal(session.representation, 'boolean');
    assert.deepEqual(session.snapshot(), [0xaaaaaaaa, 1]);
  }
  for (const bad of [-1, 0.5, 2 ** 32, NaN]) assert.equal((await session.step(bad)).kind, 'abi_refused');
  assert.deepEqual(await session.step(0xffffffff),
    { kind: 'result', value: 0, state: [0xffffffff, 0xaaaaaaaa] });
});

test('adapter byte admission uses the retained copy even if caller resizes its buffer', async () => {
  const { createWordSession } = await import('./wasm-word-session.mjs');
  const a = await artifact('packed'), b = await artifact('boolean');
  const buffer = new ArrayBuffer(a.bytes.length, { maxByteLength: a.bytes.length });
  const bytes = new Uint8Array(buffer); bytes.set(a.bytes);
  const creating = createWordSession(bytes, { ...a.descriptor, initial: seed });
  buffer.resize(0);
  const loaded = await creating;
  assert.equal(loaded.kind, 'loaded');
  assert.equal((await loaded.session.migrate(b.bytes, b.descriptor,
    { maxAdapterBytes: 2 * b.bytes.length })).kind, 'resource_refused');
  const targetBuffer = new ArrayBuffer(b.bytes.length, { maxByteLength: b.bytes.length });
  const target = new Uint8Array(targetBuffer); target.set(b.bytes);
  const moving = loaded.session.migrate(target, b.descriptor);
  targetBuffer.resize(0);
  assert.equal((await moving).kind, 'migrated');
  assert.equal((await loaded.session.migrate(a.bytes, a.descriptor,
    { maxAdapterBytes: 2 * a.bytes.length })).kind, 'resource_refused');
});

test('descriptor and option accessors cannot reenter an owner transition', async () => {
  const session = await start('packed'), a = await artifact('boolean');
  let attemptedTick;
  const config = { sha256: a.descriptor.sha256, get representation() {
    attemptedTick = session.step(99);
    return 'boolean';
  } };
  const moving = session.migrate(a.bytes, config);
  assert.equal((await attemptedTick).kind, 'resource_refused');
  assert.equal((await moving).kind, 'migrated');
  assert.deepEqual(session.snapshot(), seed);
  const b = await artifact('packed');
  let attemptedMigration;
  const second = session.migrate(b.bytes, b.descriptor, { get maxOwnedStateSlots() {
    attemptedMigration = session.migrate(b.bytes, b.descriptor);
    return 384;
  } });
  assert.equal((await attemptedMigration).kind, 'resource_refused');
  assert.equal((await second).kind, 'migrated');
  assert.deepEqual(session.snapshot(), seed);
});

test('several live prefixes and round trips agree with an independent delayed input sequence', async () => {
  const inputs = [0, 0x80000000, 0xffffffff, 1, 0xaaaaaaaa, 0x55555555, 0x12345678, 7];
  const initial = [0xf0f0f0f0, 0x87654321];
  const delayed = [initial[1], initial[0], ...inputs];
  const artifacts = { boolean: await artifact('boolean'), packed: await artifact('packed') };
  for (const origin of ['boolean', 'packed']) {
    const session = await start(origin, initial);
    for (let i = 0; i < inputs.length; i++) {
      for (const representation of [origin === 'packed' ? 'boolean' : 'packed', origin]) {
        const a = artifacts[representation];
        assert.equal((await session.migrate(a.bytes, a.descriptor)).kind, 'migrated');
      }
      const expected = Number((BigInt(inputs[i]) + BigInt(delayed[i])) % (1n << 32n));
      const result = await session.step(inputs[i]);
      assert.deepEqual(result, { kind: 'result', value: expected,
        state: [inputs[i], i === 0 ? initial[0] : inputs[i - 1]] });
    }
  }
});

test('a throwing descriptor releases only its own admission guard', async () => {
  const session = await start('packed'), target = await artifact('boolean');
  const failure = await session.migrate(target.bytes, { get representation() { throw new Error('bad descriptor'); } });
  assert.equal(failure.kind, 'binding_refused');
  assert.deepEqual(failure.cost.events, []);
  assert.deepEqual(await session.step(1), { kind: 'result', value: 0, state: [1, 0x12345678] });
});

test('caller-shadowed byte metadata cannot bypass adapter storage admission', async () => {
  const { createWordSession } = await import('./wasm-word-session.mjs');
  const a = await artifact('packed');
  Object.defineProperty(a.bytes, 'byteLength', { value: 0 });
  assert.equal((await createWordSession(a.bytes, { ...a.descriptor, initial: seed },
    { maxAdapterBytes: 0 })).kind, 'resource_refused');
  const session = await start('packed');
  const b = await artifact('boolean');
  Object.defineProperty(b.bytes, 'byteLength', { value: 0 });
  assert.equal((await session.migrate(b.bytes, b.descriptor,
    { maxAdapterBytes: 48 })).kind, 'resource_refused');
  assert.deepEqual(session.snapshot(), seed);
});
