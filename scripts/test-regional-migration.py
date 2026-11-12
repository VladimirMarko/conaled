#!/usr/bin/env python3
"""Independent public adapter fixtures for quiescent regional reconfiguration."""
import subprocess


def run(commands):
    result = subprocess.run(['lake', 'env', 'lean', '--run', 'scripts/regional-migration-main.lean'],
                            input=commands, text=True, capture_output=True, check=True)
    return result.stdout.splitlines()


def business(lines):
    return [line for line in lines if line.startswith('B:')]


assert business(run('abcq')) == ['B:11', 'B:01', 'B:10']
assert business(run('asm bgm chmq'.replace(' ', ''))) == ['B:11', 'B:01', 'B:10']
assert run('asm bgm chmq'.replace(' ', ''))[-1] == 'Q:01:checked/checked:0:0'
assert 'C:throttled' in run('smgm')
assert business(run('sa xbc'.replace(' ', ''))) == ['B:11', 'B:10']  # frozen a; then b,c
assert 'C:frozen' in run('sa')
assert 'C:capacity' in run('z')
assert 'C:allocation' in run('f')
assert 'C:validation' in run('v')
assert 'C:stale' in run('j')
assert business(run('afbc')) == ['B:11', 'B:01', 'B:10']
assert business(run('apmbc')) == ['B:11', 'B:01', 'B:10']
assert 'C:unsupported' in run('u')
print('regional migration public fixtures passed')
