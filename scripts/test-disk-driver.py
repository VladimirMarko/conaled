#!/usr/bin/env python3
"""Black-box JSON driver checks with exact rational observations and real execution."""
import copy
from fractions import Fraction
import json
import pathlib
import subprocess
import tempfile

ROOT = pathlib.Path(__file__).resolve().parents[1]
BASE = json.loads((ROOT / 'tests/disk-driver/refine.json').read_text())


def run(request, status='success'):
    with tempfile.NamedTemporaryFile(mode='w', suffix='.json') as f:
        json.dump(request, f)
        f.flush()
        p = subprocess.run(['python3', 'scripts/run-disk-driver.py', f.name], cwd=ROOT,
                           text=True, capture_output=True, timeout=30)
    r = json.loads(p.stdout)
    assert r['status'] == status, (p.returncode, p.stderr, r)
    if status in ('success', 'failure'):
        assert r['work']['attempted'] <= r['work']['charged'] <= request['work'], r
        assert r['work']['attempted'] == r['work']['accepted'] + r['work']['rejected'], r
        assert rat(r['elapsed']) == sum((rat(o['duration']) for o in r['trace']), Fraction()), r
        for observation in r['trace']:
            if observation['kind'] == 'command':
                assert len(observation['samples']) == observation['subdivisions'], r
                assert observation['samples'][-1]['time'] == observation['end_time'], r
        if status == 'success':
            assert r['pending'] == 0, r
            assert rat(r['final']['error']) <= rat(request['tolerance']), r
    return r


def rat(value):
    return Fraction(int(value[0]), int(value[1]))


def request(**changes):
    result = copy.deepcopy(BASE)
    result.update(changes)
    return result


r = run(BASE)
assert r['elapsed'] == ['1', '1024'], r
assert r['final']['error'] == ['160251', '8589934592'], r
assert r['work']['attempted'] == 3 and r['work']['charged'] == 5, r
assert r['trace'][0]['subdivisions'] == 2, r
# Accuracy retry spends real work but commits neither its clock nor its packet.
r = run(request(rounds=1), 'failure')
assert r['failure'] == 'accuracy-unmet' and r['work']['attempted'] == 1, r
assert r['final'] == r['initial'] and r['trace'] == [] and r['elapsed'] == ['0','1'], r
r = run(request(work=2), 'failure')
assert r['failure'] == 'work-exhausted' and r['work']['attempted'] == 1, r
assert r['final'] == r['initial'] and r['elapsed'] == ['0','1'], r
r = run(request(work=0), 'failure')
assert r['work']['attempted'] == 0 and r['failure'] == 'work-exhausted', r
move = BASE['commands'][0]
turn = {'kind':'turn', 'speed':['1','1'], 'duration':['1','1024']}
word = [move, turn, move]
r = run(request(commands=word, tolerance=['1','8192']))
assert r['elapsed'] == ['3','1024'], r
assert r['final']['error'] == ['124247487','1099511627776'], r
assert [o['control']['kind'] for o in r['trace']] == ['move','turn','move'], r
# The first motion crosses the apex in the independently checked exact fixture.
assert rat(r['trace'][0]['source']['position'][0]) < 0 < rat(r['trace'][0]['target']['position'][0]), r
# A mid-request chart change rotates positions AND frames. Body controls and budgets stay fixed.
g = run(request(commands=[move, {'kind':'relabel','quarter_turns':1}, turn, move], tolerance=['1','8192']))
assert g['final']['error'] == r['final']['error'] and g['elapsed'] == r['elapsed'], g
assert g['work']['attempted'] == r['work']['attempted'], g
assert g['work']['charged'] == r['work']['charged'] + 1, g
for field in ('position','frame'):
    x,y = map(rat, r['final'][field])
    assert list(map(rat,g['final'][field])) == [-y,x], (field,r,g)
assert g['trace'][1]['source'] == r['trace'][0]['target'], g
assert g['trace'][1]['quarter_turns'] == 1, g
zero = dict(move, duration=['0','1'])
r = run(request(commands=[zero], tolerance=['0','1']))
assert r['final'] == r['initial'] and r['elapsed'] == ['0','1'], r
r = run(request(commands=[{'kind':'hold','duration':['1','1024']}], tolerance=['1','8192']))
assert r['final']['position'] == r['initial']['position'], r
assert r['final']['frame'] == r['initial']['frame'], r
assert r['final']['error'] == ['39','1048576'], r
# Earlier committed work survives a subsequent failure, including its nonzero error.
r = run(request(commands=word, work=2, tolerance=['1','8192']), 'failure')
assert len(r['trace']) == 1 and r['pending'] == 2 and r['elapsed'] == ['1','1024'], r
assert r['final']['error'] == ['39','1048576'], r
r = run(request(commands=[dict(move,duration=['1','4'])], tolerance=['1','1'], rounds=3), 'failure')
assert r['failure'] == 'domain-check' and r['work']['rejected'] > 0, r
assert r['final'] == r['initial'] and r['elapsed'] == ['0','1'], r
r = run(request(packet_bits=64), 'failure')
assert r['failure'] == 'packet-bit-limit', r
assert r['work']['attempted'] > 0 and r['final'] == r['initial'], r
for bad in (request(initial='unproved'), request(rounds=0), request(commands=[dict(move,duration=['-1','2'])]),
            request(tolerance=['1','0']), request(commands=[{'kind':'unknown'}]), request(work=129), request(commands=[dict(move,velocity=[['2','1'],['0','1']])]),
            request(commands=[{'kind':'relabel','quarter_turns':4}])):
    run(bad, 'input_error')
# Invalid JSON and oversized byte frames are rejected before mathematical execution.
for raw in ('{not json', ' ' * 65537):
    with tempfile.NamedTemporaryFile(mode='w', suffix='.json') as f:
        f.write(raw)
        f.flush()
        p = subprocess.run(['python3', 'scripts/run-disk-driver.py', f.name], cwd=ROOT,
                           text=True, capture_output=True, timeout=30)
        assert json.loads(p.stdout)['status'] == 'input_error', p.stdout
print('PASS: exact refinement, failures, retained error/work, apex crossing, word, C4 event, zero, hold and input controls')
