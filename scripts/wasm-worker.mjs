import { parentPort, workerData } from 'node:worker_threads';

// No filesystem access or source-state ownership: the parent supplies exact bytes.
let module;
try {
  module = new WebAssembly.Module(workerData.bytes);
} catch (error) {
  parentPort.postMessage({ kind: 'validation_refused', message: error.message });
}
if (module) {
  if (workerData.action === 'validate') parentPort.postMessage({ kind: 'validated' });
  else {
    try {
      const instance = new WebAssembly.Instance(module, {});
      if (typeof instance.exports.run !== 'function') throw new Error('Missing run function');
      const result = instance.exports.run(...workerData.values.map(x => x | 0));
      const values = Array.isArray(result) ? result : result === undefined ? [] : [result];
      if (values.some(x => !Number.isInteger(x) || x < -2147483648 || x > 2147483647)) {
        throw new Error('Result is not an exact i32 value');
      }
      parentPort.postMessage({ kind: 'result', values: values.map(x => x >>> 0) });
    } catch (error) {
      parentPort.postMessage({ kind: 'execution_failed', message: error.message });
    }
  }
}
