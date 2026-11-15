#!/usr/bin/env python3
"""Record actual post-observation and stable comparison, once, without Lean."""
from pathlib import Path
from datetime import datetime, timezone
import hashlib
import json
import os
import subprocess
import time

OWN = Path(__file__).resolve().parent
CTRL = OWN.parents[1]
BASE = CTRL.parent
OBS = CTRL / 'provenance/chapter02-complete-receiving-input-observations-20261104-attempt1'
PREP = CTRL / 'provenance/chapter02-receiving-type-qualification-preparation-20261104'
FULL = CTRL / 'provenance/chapter02-complete-receiving-full-attempt1-20261104'
Q = '2da5708478a1d943a9214b5b386ec2db16cd9eca'

def now():
    return datetime.now(timezone.utc).isoformat()

def fp(path):
    b = path.read_bytes()
    return {'path': str(path), 'bytes': len(b), 'sha256': hashlib.sha256(b).hexdigest()}

def save(path, value):
    with path.open('x') as stream:
        stream.write(json.dumps(value, indent=2) + '\n')
        stream.flush()
        os.fsync(stream.fileno())

def main():
    terminal = json.loads((OWN / 'owned-terminal.json').read_text())
    sequence = json.loads((OWN / 'execution-result.json').read_text())
    assert terminal['actual_exit'] == 0 and terminal['candidate'] == Q
    assert sequence['status'] == 'all-eleven-closed-zero' and len(sequence['completed_profiles']) == 11
    bound = []
    for path, digest in [
        (CTRL / 'tooling/capture_statement_inputs.py', '4df281f3f427ec462a6973b9177fcc3f825b57b19fa8e205780f17cfaa89b5b7'),
        (PREP / 'ObservationOnly.lean', 'd7c61fc87c597ff2d263e30c6848b0057ad59d43e104c99a15af7de074ef341d'),
        (PREP / 'compare_receiving_v2.py', '84a6d52d489c88efa0ddc155ba88bd4fdd2472042b898a3a95843509049f7f0b'),
        (OBS / 'pre-inputs.json', '6e915cd019a10381fb096fece62bdbd9964f189a446024825a71daabc808a2a3'),
        (OWN / 'execution-result.json', '03f2e85aade3002429b926355284f31362d01e8f96c830b2c3edf7d274fe7a48')]:
        row = fp(path)
        assert row['sha256'] == digest
        bound.append(row)
    post, comparison = OBS / 'post-inputs.json', OBS / 'stable-comparison.json'
    assert not post.exists() and not comparison.exists()
    commands = [
        ('post-observation', ['python3', str(CTRL / 'tooling/capture_statement_inputs.py'), '--project', str(BASE / 'conaled-ch01-review'), '--candidate', Q, '--program', str(PREP / 'ObservationOnly.lean'), '--output', str(post), '--compare', str(OBS / 'pre-inputs.json')], post),
        ('stable-comparison', ['python3', str(PREP / 'compare_receiving_v2.py'), '--control', str(CTRL), '--full-result', str(FULL / 'result.json'), '--receiver-pre', str(OBS / 'pre-inputs.json'), '--receiver-post', str(post), '--output', str(comparison)], comparison)]
    save(OWN / 'post-sequence-start.json', {'started_utc': now(), 'candidate': Q, 'bound_inputs': bound, 'parent_terminal': fp(OWN / 'owned-terminal.json'), 'method': fp(Path(__file__)), 'carrier_never_executed_by_Lean': True})
    for label, argv, product in commands:
        started, tick = now(), time.monotonic()
        log = OWN / (label + '.log')
        with log.open('xb') as output:
            result = subprocess.run(argv, cwd=CTRL, stdin=subprocess.DEVNULL, stdout=output, stderr=subprocess.STDOUT, check=False)
        record = {'started_utc': started, 'completed_utc': now(), 'actual_exit': result.returncode, 'elapsed_seconds': time.monotonic() - tick, 'argv': argv, 'log': fp(log), 'product': fp(product) if product.exists() else None, 'observed_by': '/root synchronous subprocess return; no automatic retry'}
        save(OWN / (label + '-execution.json'), record)
        print(json.dumps(record), flush=True)
        if result.returncode != 0:
            raise SystemExit(result.returncode if result.returncode > 0 else 128 - result.returncode)
        if label == 'post-observation':
            assert json.loads(post.read_text())['unchanged'] is True
    save(OWN / 'post-sequence-result.json', {'completed_utc': now(), 'actual_exit': 0, 'candidate': Q, 'actual_post_stable': True, 'post': fp(post), 'comparison': fp(comparison), 'independent_qualification_pending': True, 'type_credit': 0})

if __name__ == '__main__':
    main()
