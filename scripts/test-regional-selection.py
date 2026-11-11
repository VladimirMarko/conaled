#!/usr/bin/env python3
"""Public executable observations against an independent two-state machine."""
import subprocess
import argparse
import json
from pathlib import Path

parser = argparse.ArgumentParser()
parser.add_argument("--measurements", type=Path)
args = parser.parse_args()

result = subprocess.run(['lake', 'env', 'lean', '--run', 'scripts/regional-selection-main.lean'],
                        text=True, capture_output=True)
if result.returncode:
    raise RuntimeError(result.stdout + result.stderr)
rows = [line.split('|') for line in result.stdout.splitlines() if '|' in line]
runs = 0
for row in rows:
    if row[0] == 'run':
        _, name, seed, word, output, final = row
        state = [ch == '1' for ch in seed]
        expected = []
        for pair in word.split(',') if word else []:
            expected.append(''.join('0' if b else '1' for b in state))
            # Six inputs: false, true, (false,false), (false,true), (true,false), (true,true).
            state = [int(ch) in (1,4) for ch in pair]
        assert output == ','.join(expected), row
        assert final == ''.join('1' if b else '0' for b in state), row
        runs += 1
assert runs == 1296, runs
comparisons = [r for r in rows if r[0] in {"comparison", "fixed", "direct"}]
assert len(comparisons) == 5
assert all(r[-1] == "11,01,10" for r in comparisons), comparisons
checks = {row[1]: row[2] for row in rows if row[0] == 'check'}
for name in ['epoch-change', 'old-session', 'stale-protocol', 'stale-budget', 'stale-catalog',
             'wrong-implementation', 'incomplete', 'empty', 'valid-fallback', 'bad-fallback',
             'joint-budget', 'unsupported', 'invalid-port', 'validation-path-cost', 'fallback-cost',
             'duplicate-epoch', 'mismatched-sample']:
    assert checks.get(name) == 'true', (name, checks)
print(f'{runs} independent continued runs; {len(checks)} admission/evidence/lifecycle checks passed')

if args.measurements:
    observations = {
        "implementation": "regional-v1",
        "target": "Lean interpreter; modeled cells separate from timing",
        "workload": "fixture: three joint ticks, false/false initial state",
        "requirements": {"capacity": 10000, "protocol": 1, "ordered": True, "finite_waits": True},
        "policy_epochs": "Synthetic correctness fixtures, not measured training data",
        "timing": "IO.monoNanosNow nanoseconds; one diagnostic sample per case, no performance inference",
        "regional_costs": [dict(candidate=r[1], tick_work_bound=int(r[2]), storage_cells=int(r[3]))
                           for r in rows if r[0] == 'cost'],
        "selected": [dict(candidate=r[1], installation_bill=int(r[2]), preparation_ns=int(r[3]),
                          execution_ns=int(r[4]), outputs=r[5]) for r in rows if r[0] == 'comparison'],
        "fixed": [dict(candidate=r[1], preparation_ns=int(r[2]), execution_ns=int(r[3]), outputs=r[4])
                  for r in rows if r[0] == 'fixed'],
        "direct": [dict(execution_ns=int(r[1]), outputs=r[2]) for r in rows if r[0] == 'direct'],
        "execution_bills": [dict(candidate=r[1], three_ticks_and_observation=int(r[2]))
                            for r in rows if r[0] == 'execution-bill'],
        "oracle_runs": runs,
        "checks": checks,
    }
    args.measurements.write_text(json.dumps(observations, indent=2) + "\n")
