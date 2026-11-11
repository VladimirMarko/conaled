#!/usr/bin/env python3
"""Bounded public-protocol timings; these are not intrinsic conversion costs."""
import argparse
import json
import hashlib
import platform
import subprocess
import time
import runpy
from pathlib import Path

Client = runpy.run_path(str(Path(__file__).with_name("test-migration-service.py")))["Client"]


def sample(variant, length, wait):
    start = time.perf_counter_ns()
    client = Client('redundant' if variant == 'redundant' else 'delay')
    try:
        initial = client.command(b'q')
        startup = time.perf_counter_ns() - start
        assert initial == [b'C:q:' + (b'r' if variant == 'redundant' else b'd') +
                           b':0:idle:-:-:0']
        assert client.command(b'1') == [b'C:accepted']
        assert client.command(b'e') == [b'C:evaluated']
        pause_start = time.perf_counter_ns()
        assert client.command(b'r' if variant == 'migrated' else b'q')[0].startswith(b'C:')
        assert client.command(b'w') == [b'C:refused']
        wait_start = time.perf_counter_ns()
        time.sleep(wait)
        sink_wait = time.perf_counter_ns() - wait_start
        assert client.command(b'p') == [b'B:0', b'C:published']
        assert client.command(b't') == [b'C:tick-committed']
        quiescent = time.perf_counter_ns()
        prepared = client.command(b'm' if variant == 'migrated' else b'q')
        after_prepare = time.perf_counter_ns()
        committed = client.command(b'o' if variant == 'migrated' else b'q')
        after_commit = time.perf_counter_ns()
        if variant == 'migrated':
            assert prepared == [b'C:prepared'] and committed == [b'C:migrated']
        previous = 1
        suffix_start = time.perf_counter_ns()
        for index in range(length):
            value = index % 2
            assert client.command(bytes([48 + value])) == [b'C:accepted']
            assert client.command(b'e') == [b'C:evaluated']
            assert client.command(b'p') == [b'B:' + bytes([48 + previous]), b'C:published']
            assert client.command(b't') == [b'C:tick-committed']
            previous = value
        suffix_end = time.perf_counter_ns()
        final = client.command(b'q')
        kind = b'd' if variant == 'delay' else b'r'
        assert final == [b'C:q:' + kind + b':' + bytes([48 + previous]) +
                         b':idle:' + bytes([48 + (length - 2) % 2]) + b':-:0']
        client.close()
        return dict(variant=variant, suffix_length=length, success=True,
                    startup_ns=startup, request_to_quiescence_ns=quiescent-pause_start,
                    explicit_sink_wait_ns=sink_wait, preparation_roundtrip_ns=after_prepare-quiescent,
                    commit_roundtrip_ns=after_commit-after_prepare,
                    total_admission_pause_ns=after_commit-pause_start,
                    suffix_ns=suffix_end-suffix_start,
                    pause_plus_suffix_ns=suffix_end-pause_start)
    finally:
        client.cleanup()


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument('--output', required=True)
    parser.add_argument('--repetitions', type=int, default=3)
    parser.add_argument('--lengths', type=int, nargs='+', default=[16, 64])
    parser.add_argument('--sink-wait', type=float, default=0.01)
    args = parser.parse_args()
    if not 1 <= args.repetitions <= 10 or any(not 2 <= n <= 4096 for n in args.lengths):
        parser.error('use 1..10 repetitions and suffix lengths 2..4096')
    if not 0 <= args.sink_wait <= 1:
        parser.error('sink wait must be between 0 and 1 seconds')
    result = dict(protocol='migration-byte-v1', clock='perf_counter_ns',
                  identities={'delay': 'FRPSpec.Indefinite.delay',
                              'redundant': 'FRPSpec.MigrationPair.redundant',
                              'migrated': 'delay to redundant after pending first tick retires'},
                  host=platform.uname()._asdict(),
                  source_revision=subprocess.check_output(['git', 'rev-parse', 'HEAD'], text=True).strip(),
                  source_sha256={name: hashlib.sha256(Path(name).read_bytes()).hexdigest()
                      for name in ['Applications/FRP/MigrationPair.lean',
                                   'Applications/FRP/Migration.lean',
                                   'Applications/FRP/MigrationIO.lean',
                                   'scripts/migration-service.lean',
                                   'scripts/test-migration-service.py',
                                   'scripts/benchmark-migration-service.py']},
                  toolchain=subprocess.check_output(['lean', '--version'], text=True).strip(),
                  affinity=sorted(__import__('os').sched_getaffinity(0)),
                  repetitions=args.repetitions, lengths=args.lengths,
                  sink_wait_seconds=args.sink_wait,
                  workload='first input1; pending refusal and finite wait; alternating suffix starting0',
                  interpretation='command round trips include Python, pipe IO, Lean adapter and scheduling; '
                                 'baseline query commands occupy request/prepare/commit positions',
                  samples=[])
    for repetition in range(args.repetitions):
        for length in args.lengths:
            # Rotate order to reduce systematic startup/temperature order bias.
            variants = ['delay', 'redundant', 'migrated']
            variants = variants[repetition % 3:] + variants[:repetition % 3]
            for variant in variants:
                result['samples'].append(dict(repetition=repetition,
                                              **sample(variant, length, args.sink_wait)))
    with open(args.output, 'w') as stream:
        json.dump(result, stream, indent=2)
        stream.write('\n')


if __name__ == '__main__':
    main()
