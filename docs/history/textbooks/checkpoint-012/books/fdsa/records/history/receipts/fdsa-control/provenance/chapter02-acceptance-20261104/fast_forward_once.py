#!/usr/bin/env python3
"""Perform only the exact local FF after held final reviews and actual verification."""
from pathlib import Path
from datetime import datetime, timezone
import hashlib
import json
import os
import subprocess

OWN = Path(__file__).resolve().parent
CTRL = OWN.parents[1]
BASE = CTRL.parent
WT = BASE / 'conaled-ch01-review'
MAIN = BASE / 'conaled'
Q = '2da5708478a1d943a9214b5b386ec2db16cd9eca'
L = '726cb9a9b9ff4444a7614383de4fb336e8804aa7'
IMMEDIATE = CTRL / 'provenance/chapter02-complete-immediate-verification-20261104-attempt1'

def now():
    return datetime.now(timezone.utc).isoformat()

def load(path):
    return json.loads(path.read_text())

def fp(path):
    data = path.read_bytes()
    return {'path': str(path), 'bytes': len(data), 'sha256': hashlib.sha256(data).hexdigest()}

def check(row):
    actual = fp(Path(row['path']))
    assert actual['bytes'] == row['bytes'] and actual['sha256'] == row['sha256'], row['path']

def save(path, record):
    with path.open('x') as stream:
        stream.write(json.dumps(record, indent=2) + '\n')
        stream.flush()
        os.fsync(stream.fileno())

def git(path, *args):
    return subprocess.check_output(['git', '--no-optional-locks', '-C', str(path), *args], text=True).strip()

def main():
    assert not (OWN / 'fast-forward-result.json').exists()
    gate = load(OWN / 'root-gate-reconciliation.json')
    assert gate['candidate'] == Q and gate['ready_for_immediate_verification'] is True
    assert gate['both_final_axes_passed_held'] is True and gate['unresolved_findings'] == 0
    for row in gate['bound_files']:
        check(row)
    prior = load(OWN / 'prepared-fast-forward-preflight.json')
    terminal = load(IMMEDIATE / 'owned-terminal.json')
    result = load(IMMEDIATE / 'result.json')
    closure = load(IMMEDIATE / 'closed-evidence-reconciliation.json')
    assert terminal['actual_exit'] == result['exit_code'] == 0
    assert result['candidate'] == result['final_head'] == Q and result['final_status'] == '' and result['state'] == 'passed'
    assert closure['complete_closed_log'] is True and closure['candidate'] == Q
    native = load(IMMEDIATE / 'native-records/result.json')
    assert native['command'] == ['./check.sh', '--verify-candidate', 'HEAD'] and native['cwd'] == str(WT)
    assert native['lean_threads'] == '1' and native['passed'] is True and native['exit_code'] == 0
    assert native['timed_out'] is False and native['recorder_error'] is None
    assert fp(IMMEDIATE / 'verification.json')['sha256'] == 'fb794d107281f07ec8470de0f4af0028b1a78c1b774d0e01f742221063493aca'
    assert git(WT, 'rev-parse', 'HEAD') == Q and git(WT, 'status', '--porcelain=v1', '--untracked-files=all') == ''
    assert git(MAIN, 'rev-parse', 'HEAD') == L and git(MAIN, 'symbolic-ref', '--short', 'HEAD') == 'work/fdsa-book'
    assert git(MAIN, 'status', '--porcelain=v1', '--untracked-files=all') == prior['accepted_worktree_status']
    assert git(MAIN, 'for-each-ref', '--format=%(objectname) %(refname) %(symref)').splitlines() == prior['refs_before']
    check(prior['unrelated_file'])
    assert git(WT, 'rev-parse', 'HEAD^{tree}') == prior['candidate_tree']
    subprocess.run(['git', '--no-optional-locks', '-C', str(MAIN), 'merge-base', '--is-ancestor', L, Q], check=True)
    started = now()
    command = ['git', '-C', str(MAIN), 'merge', '--ff-only', Q]
    save(OWN / 'fast-forward-start.json', {'started_utc': started, 'candidate': Q, 'accepted_before': L, 'command': command, 'root_gate': fp(OWN / 'root-gate-reconciliation.json'), 'immediate_terminal': fp(IMMEDIATE / 'owned-terminal.json'), 'immediate_closure': fp(IMMEDIATE / 'closed-evidence-reconciliation.json'), 'method': fp(Path(__file__))})
    with (OWN / 'fast-forward.log').open('xb') as stream:
        actual = subprocess.run(command, stdin=subprocess.DEVNULL, stdout=stream, stderr=subprocess.STDOUT, check=False)
    outcome = {'started_utc': started, 'completed_utc': now(), 'actual_exit': actual.returncode, 'command': command, 'log': fp(OWN / 'fast-forward.log')}
    save(OWN / 'fast-forward-actual-exit.json', outcome)
    if actual.returncode != 0:
        raise SystemExit(actual.returncode if actual.returncode > 0 else 128 - actual.returncode)
    assert git(MAIN, 'rev-parse', 'HEAD') == Q and git(MAIN, 'rev-parse', 'HEAD^{tree}') == prior['candidate_tree']
    assert git(MAIN, 'status', '--porcelain=v1', '--untracked-files=all') == prior['accepted_worktree_status']
    expected = [line.replace(L + ' refs/heads/work/fdsa-book', Q + ' refs/heads/work/fdsa-book') for line in prior['refs_before']]
    after_refs = git(MAIN, 'for-each-ref', '--format=%(objectname) %(refname) %(symref)').splitlines()
    assert after_refs == expected
    check(prior['unrelated_file'])
    for old in prior['worktrees_before']:
        path = Path(old['worktree'])
        assert git(path, 'rev-parse', 'HEAD') == (Q if path == MAIN else old['HEAD'])
        assert git(path, 'status', '--porcelain=v1', '--untracked-files=all') == old['status']
    outcome.update(accepted_commit=Q, accepted_tree=prior['candidate_tree'], previous_accepted_commit=L, root_gate=fp(OWN / 'root-gate-reconciliation.json'), immediate_result=fp(IMMEDIATE / 'result.json'), refs_after=after_refs, all_other66_refs_preserved=True, all_other14_worktree_heads_statuses_preserved=True, unrelated_file_preserved=True, no_push_or_GitHub_mutation=True)
    save(OWN / 'fast-forward-result.json', outcome)
    print(json.dumps({'actual_exit': actual.returncode, 'accepted_commit': Q, 'completed_utc': outcome['completed_utc'], 'record': fp(OWN / 'fast-forward-result.json')}), flush=True)

if __name__ == '__main__':
    main()
