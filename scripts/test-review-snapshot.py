#!/usr/bin/env python3
"""Public CLI regressions in disposable real Git repositories; no Lean required."""
import errno
import json
import os
from pathlib import Path
import subprocess
import sys
import tempfile
import time
import unittest

CLI = Path(__file__).with_name('review_snapshot.py')


class Snapshots(unittest.TestCase):
    def setUp(self):
        self.temp = tempfile.TemporaryDirectory()
        self.addCleanup(self.temp.cleanup)
        self.home = Path(self.temp.name)
        self.repo = self.home / 'repo'
        self.repo.mkdir()
        self.git('init', '-q')
        self.git('config', 'user.email', 'test@example.invalid')
        self.git('config', 'user.name', 'Test')
        self.write('task', 'old\n')
        self.write('unrelated', 'old\n')
        self.git('add', '.')
        self.git('commit', '-qm', 'initial')
        self.initial = self.git('rev-parse', 'HEAD').strip()
        self.count = 0

    def git(self, *args, check=True, input=None):
        p = subprocess.run(['git', '-C', str(self.repo), *args], input=input,
                           text=True, capture_output=True)
        if check:
            self.assertEqual(p.returncode, 0, p.stderr)
        return p.stdout

    def write(self, name, text):
        p = self.repo / name
        p.parent.mkdir(parents=True, exist_ok=True)
        p.write_text(text)

    def call(self, operation, manifest=None, ok=True, **flags):
        self.count += 1
        argv = [sys.executable, str(CLI), operation, '--repo', str(self.repo)]
        if manifest is not None:
            path = self.home / f'manifest{self.count}.json'
            path.write_text(json.dumps(manifest))
            argv += ['--manifest', str(path)]
        for k, v in flags.items():
            argv += ['--' + k.replace('_', '-'), str(v)]
        p = subprocess.run(argv, capture_output=True, text=True)
        if ok:
            self.assertEqual(p.returncode, 0, p.stdout + p.stderr)
            return json.loads(p.stdout)
        self.assertNotEqual(p.returncode, 0, p.stdout)
        self.assertNotIn('"status": "ok"', p.stdout)
        return p.stderr

    def record(self, name, result):
        p = self.home / (name + '.json')
        p.write_text(json.dumps(result))
        return p

    def unchanged_state(self):
        return (self.git('rev-parse', 'HEAD'), self.git('symbolic-ref', 'HEAD'),
                (self.repo / '.git/index').read_bytes(),
                {str(p.relative_to(self.repo)): p.read_bytes()
                 for p in self.repo.rglob('*') if p.is_file() and '.git' not in p.parts})

    def test_dirty_start_and_candidate_have_correct_ancestry(self):
        self.write('unrelated', 'preexisting staged\n')
        self.git('add', 'unrelated')
        self.write('unrelated', 'preexisting unstaged\n')
        manifest = {'scope': ['task', 'new'], 'entries': {}, 'exclude': []}
        before = self.unchanged_state()
        base = self.call('baseline', manifest)
        self.assertEqual(self.unchanged_state(), before)
        self.write('task', 'implemented\n')
        self.write('new', 'new implementation\n')
        before = self.unchanged_state()
        candidate = self.call('candidate', {**manifest, 'entries': {
            'task': {'source': 'live'}, 'new': {'source': 'live'}}},
            record=self.record('base', base))
        self.assertEqual(self.unchanged_state(), before)
        self.assertEqual(set(self.git('diff', '--name-only', base['base'] + '...' +
                                     candidate['candidate']).splitlines()), {'task', 'new'})
        self.assertEqual(self.git('show', candidate['candidate'] + ':unrelated'),
                         'preexisting unstaged\n')
        sibling = self.git('commit-tree', candidate['tree'], '-p', self.initial,
                           input='old broken sibling\n').strip()
        self.assertIn('unrelated', self.git('diff', '--name-only', base['base'] + '...' + sibling))

    def test_takeover_mixed_content_and_final_comparison(self):
        self.write('task', 'user change\nearly task\n')
        self.git('add', 'task')
        self.write('task', 'user change\nlate task\n')
        manifest = {'scope': ['task'], 'entries': {}, 'exclude': []}
        observed = self.call('observe', manifest)['sources']['task']
        projected = self.home / 'baseline-content'
        projected.write_text('user change\nold task\n')
        base = self.call('baseline', {**manifest, 'entries': {'task': {
            'source': 'file', 'file': str(projected), 'mode': '100644',
            'expected': observed}}})
        self.assertEqual((self.repo / 'task').read_text(), 'user change\nlate task\n')
        candidate = self.call('candidate', {**manifest, 'entries': {
            'task': {'source': 'live'}}}, record=self.record('base', base))
        record = self.record('candidate', candidate)
        self.assertIn('+late task', self.git('diff', base['base'], candidate['candidate']))
        self.call('compare', manifest, record=record, accepted='LIVE')
        self.write('unrelated', 'changed after review\n')
        self.call('compare', manifest, record=record, accepted='LIVE')
        self.write('task', 'new unrelated\nlate task\n')
        projected.write_text('user change\nlate task\n')
        new_observed = self.call('observe', manifest)['sources']['task']
        projection = {**manifest, 'entries': {'task': {'source': 'file',
            'file': str(projected), 'mode': '100644', 'expected': new_observed}}}
        self.call('compare', projection, record=record, accepted='LIVE')
        self.write('task', 'new unrelated\nchanged task AFTER projection\n')
        self.assertIn('identity', self.call('compare', projection, ok=False,
                                         record=record, accepted='LIVE'))
        self.assertIn('mismatch', self.call('compare', manifest, ok=False,
                                         record=record, accepted='LIVE'))

    def test_ticket_rebase_and_full_integration_scope(self):
        self.git('checkout', '-qb', 'ticket-b')
        self.write('task', 'B change\n')
        self.git('add', 'task'); self.git('commit', '-qm', 'B')
        b = self.git('rev-parse', 'HEAD').strip()
        self.git('checkout', '-qb', 'integration', self.initial)
        self.write('task', 'A conflict\n'); self.write('a-only', 'A work\n')
        self.git('add', '.'); self.git('commit', '-qm', 'A')
        integration = self.git('rev-parse', 'HEAD').strip()
        self.git('checkout', 'ticket-b')
        self.git('merge', integration, check=False)
        self.write('task', 'A plus B resolution\n')
        self.git('add', 'task'); self.git('commit', '-qm', 'incorporate A')
        candidate = self.git('rev-parse', 'HEAD').strip()
        manifest = {'scope': ['task'], 'entries': {}, 'exclude': []}
        before = self.unchanged_state()
        ticket = self.call('validate', manifest, base=integration, candidate=candidate,
                          mode='ticket', incorporated=integration, original_base=self.initial)
        self.assertEqual(self.unchanged_state(), before)
        self.assertEqual(ticket['candidate'], candidate)
        self.assertEqual(self.git('diff', '--name-only', ticket['base'] + '...' + candidate), 'task\n')
        full = self.call('validate', {**manifest, 'scope': ['task', 'a-only']},
                         base=self.initial, candidate=candidate, mode='integration')
        self.assertEqual(set(self.git('diff', '--name-only', full['base'] + '...' + candidate).split()),
                         {'task', 'a-only'})
        self.call('validate', manifest, ok=False, base=integration, candidate=b, mode='ticket',
                  incorporated=integration)
        self.call('validate', manifest, ok=False, base=self.initial, candidate=candidate)
        self.call('validate', manifest, ok=False, base=self.initial, candidate=candidate,
                  mode='ticket', incorporated=integration)
        self.call('compare', manifest, record=self.record('ticket', ticket), accepted=candidate)
        self.write('task', 'later resolution\n'); self.git('add', 'task')
        self.git('commit', '-qm', 'changed resolution')
        self.call('compare', manifest, ok=False, record=self.record('ticket2', ticket), accepted='HEAD')

    def test_correction_rounds_keep_base_and_prior_candidates(self):
        manifest = {'scope': ['task'], 'entries': {}, 'exclude': []}
        base = self.call('baseline', manifest)
        self.write('task', 'first\n')
        capture = {**manifest, 'entries': {'task': {'source': 'live'}}}
        first = self.call('candidate', capture, record=self.record('base', base))
        self.write('task', 'corrected\n')
        second = self.call('candidate', capture, record=self.record('first', first))
        self.assertEqual(first['base'], second['base'])
        self.assertEqual(self.git('show', first['candidate'] + ':task'), 'first\n')
        self.assertEqual(self.git('show', second['candidate'] + ':task'), 'corrected\n')
        self.call('validate', manifest, ok=False, base=first['candidate'],
                  candidate=second['candidate'], record=self.record('first-fixed', first))

    def test_retention_and_release_are_owned_and_compare_and_swap(self):
        manifest = {'scope': ['task'], 'entries': {}, 'exclude': []}
        base = self.call('baseline', manifest)
        self.write('task', 'retained\n')
        first = self.call('candidate', {**manifest, 'entries': {'task': {'source': 'live'}}},
                          record=self.record('base', base))
        other = self.call('candidate', {**manifest, 'entries': {'task': {'source': 'live'}}},
                          record=self.record('base2', base))
        record = self.record('first', first)
        self.git('reflog', 'expire', '--expire=now', '--all')
        self.git('gc', '--prune=now')
        self.assertEqual(self.git('show', first['candidate'] + ':task'), 'retained\n')
        before = self.unchanged_state()
        target = next(r for r in first['retention'] if r.endswith('/candidate'))
        old = first['retention'][target]
        self.git('update-ref', target, self.initial, old)
        self.assertIn('retention', self.call('release', ok=False, record=record))
        self.assertEqual(self.unchanged_state(), before)
        self.git('update-ref', target, old, self.initial)
        forged = dict(first)
        forged['retention'] = {'refs/heads/master': self.initial}
        self.call('release', ok=False, record=self.record('forged', forged))
        self.call('release', record=record)
        self.assertEqual(self.unchanged_state(), before)
        for ref, oid in other['retention'].items():
            self.assertEqual(self.git('rev-parse', ref).strip(), oid)
        self.assertEqual(self.git('rev-parse', 'HEAD').strip(), self.initial)
        self.call('release', ok=False, record=record)

    def test_incomplete_and_unsafe_manifests_fail_without_touching_checkout(self):
        manifest = {'scope': ['task'], 'entries': {}, 'exclude': []}
        self.write('untracked', 'must classify\n')
        before = self.unchanged_state()
        self.assertIn('untracked', self.call('baseline', manifest, ok=False))
        self.assertEqual(self.unchanged_state(), before)
        for bad in ['../escape', '.git/config', '/absolute', 'task/../other']:
            self.call('baseline', {**manifest, 'scope': [bad], 'exclude': ['untracked']}, ok=False)
            self.assertEqual(self.unchanged_state(), before)
        base = self.call('baseline', {**manifest, 'exclude': ['untracked']})
        self.write('task', 'later task\n')
        candidate = self.call('candidate', {**manifest, 'exclude': ['untracked']},
                              record=self.record('base', base))
        self.assertEqual(self.git('show', candidate['candidate'] + ':task'), 'later task\n')
        before = self.unchanged_state()
        self.call('candidate', {**manifest, 'entries': {'unrelated': {'source': 'live'}}},
                  ok=False, record=self.record('base2', base))
        self.call('validate', manifest, ok=False, base='not-a-ref', candidate='HEAD')
        self.assertEqual(self.unchanged_state(), before)

    def test_modes_symlinks_deletions_and_non_ascii_paths(self):
        name = 'new space\nλ'
        manifest = {'scope': ['task', 'link', name], 'entries': {}, 'exclude': []}
        base = self.call('baseline', manifest)
        (self.repo / 'task').unlink()
        self.write(name, 'binary\x00data\n')
        (self.repo / name).chmod(0o755)
        (self.repo / 'link').symlink_to('unrelated')
        before = self.unchanged_state()
        candidate = self.call('candidate', manifest, record=self.record('base', base))
        self.assertEqual(self.unchanged_state(), before)
        tree = self.git('ls-tree', '-rz', candidate['candidate'])
        self.assertIn('100755 blob', tree)
        self.assertIn('120000 blob', tree)
        self.assertEqual(self.git('show', candidate['candidate'] + ':link'), 'unrelated')
        self.assertNotIn('\ttask\x00', tree)
        self.call('compare', manifest, record=self.record('candidate', candidate), accepted='LIVE')

    def test_source_identity_separates_live_exclusions_from_candidate(self):
        manifest = {'scope': ['task'], 'entries': {}, 'exclude': []}
        base = self.call('baseline', manifest)
        self.write('task', 'new\n'); self.write('unrelated', 'excluded NEW input\n')
        candidate = self.call('candidate', manifest, record=self.record('base', base))
        self.assertEqual(self.git('show', candidate['candidate'] + ':unrelated'), 'old\n')
        self.assertNotEqual(candidate['source_identity'], candidate['content_identity'])
        self.assertEqual(candidate['entries']['task']['mode'], '100644')
        self.assertIn('unrelated', candidate['excluded'])

    def test_changed_input_during_capture_fails_without_usable_receipt(self):
        manifest = {'scope': ['task'], 'entries': {}, 'exclude': []}
        observed = self.call('observe', manifest)['sources']['task']
        fifo = self.home / 'content-pipe'
        os.mkfifo(fifo)
        manifest['entries']['task'] = {'source': 'file', 'file': str(fifo),
                                       'mode': '100644', 'expected': observed}
        path = self.home / 'race-manifest.json'
        path.write_text(json.dumps(manifest))
        process = subprocess.Popen([sys.executable, str(CLI), 'baseline', '--repo', str(self.repo),
                                    '--manifest', str(path)], stdout=subprocess.PIPE, stderr=subprocess.PIPE,
                                   text=True)
        self.addCleanup(lambda: process.poll() is None and process.kill())
        deadline = time.monotonic() + 10
        while True:
            try:
                fd = os.open(fifo, os.O_WRONLY | os.O_NONBLOCK)
                break
            except OSError as error:
                if error.errno != errno.ENXIO or time.monotonic() > deadline:
                    raise
                time.sleep(0.01)
        self.write('task', 'concurrent change\n')
        with os.fdopen(fd, 'wb') as writer:
            writer.write(b'projected content\n')
        stdout, stderr = process.communicate(timeout=10)
        self.assertNotEqual(process.returncode, 0, stdout)
        self.assertIn('inconsistent capture', stderr)
        self.assertEqual(stdout, '')
        self.assertEqual((self.repo / 'task').read_text(), 'concurrent change\n')

    def test_committed_candidate_in_linked_worktree_preserves_index_and_branch(self):
        self.write('task', 'committed\n'); self.git('add', 'task')
        self.git('commit', '-qm', 'implementation')
        candidate = self.git('rev-parse', 'HEAD').strip()
        original = self.repo
        linked = self.home / 'linked'
        self.git('worktree', 'add', '-b', 'review-worktree', str(linked), candidate)
        self.repo = linked
        index = Path(self.git('rev-parse', '--path-format=absolute', '--git-path', 'index').strip())
        before = (index.read_bytes(), self.git('rev-parse', 'HEAD'), self.git('symbolic-ref', 'HEAD'))
        result = self.call('validate', {'scope': ['task'], 'entries': {}, 'exclude': []},
                           base=self.initial, candidate=candidate)
        self.assertEqual(result['candidate'], candidate)
        self.assertEqual(before, (index.read_bytes(), self.git('rev-parse', 'HEAD'), self.git('symbolic-ref', 'HEAD')))
        self.assertEqual(self.git('log', '--format=%H', '--all').splitlines().count(candidate), 1)
        self.repo = original

    def test_validate_rejects_ignored_projection_and_duplicate_manifest_fields(self):
        manifest = {'scope': ['task'], 'entries': {'task': {'source': 'live'}}, 'exclude': []}
        self.call('validate', manifest, ok=False, base='HEAD', candidate='HEAD')
        path = self.home / 'duplicates.json'
        path.write_text('{"scope":["task"],"scope":["unrelated"],"entries":{},"exclude":[]}')
        p = subprocess.run([sys.executable, str(CLI), 'baseline', '--repo', str(self.repo),
                            '--manifest', str(path)], text=True, capture_output=True)
        self.assertNotEqual(p.returncode, 0, p.stdout)
        self.assertIn('duplicate', p.stderr)

    def test_ignored_input_requires_explicit_scope_and_bad_expected_identity_fails(self):
        self.write('.gitignore', 'ignored\n')
        self.git('add', '.gitignore'); self.git('commit', '-qm', 'ignore fixture')
        self.write('ignored', 'explicit ignored artifact\n')
        manifest = {'scope': ['task', 'ignored'], 'entries': {}, 'exclude': []}
        base = self.call('baseline', manifest)
        self.assertEqual(self.git('show', base['base'] + ':ignored'), 'explicit ignored artifact\n')
        content = self.home / 'projected'
        content.write_text('projection\n')
        before = self.unchanged_state()
        self.call('candidate', {**manifest, 'entries': {'task': {'source': 'file',
                  'file': str(content), 'mode': '100644', 'expected': None}}},
                  ok=False, record=self.record('base', base))
        self.assertEqual(self.unchanged_state(), before)

    def test_modes_cannot_silently_change_full_spec_base(self):
        manifest = {'scope': ['task'], 'entries': {}, 'exclude': []}
        self.write('task', 'first\n'); self.git('add', 'task'); self.git('commit', '-qm', 'first')
        tip = self.git('rev-parse', 'HEAD').strip()
        self.call('validate', manifest, ok=False, base=tip, candidate=tip,
                  original_base=self.initial, mode='integration')
        self.call('baseline', manifest, ok=False, mode='ticket')

    def test_unmerged_index_is_rejected_and_preserved(self):
        self.git('checkout', '-qb', 'side')
        self.write('task', 'side\n'); self.git('add', 'task'); self.git('commit', '-qm', 'side')
        side = self.git('rev-parse', 'HEAD').strip()
        self.git('checkout', '-qb', 'other', self.initial)
        self.write('task', 'other\n'); self.git('add', 'task'); self.git('commit', '-qm', 'other')
        self.git('merge', side, check=False)
        before = self.unchanged_state()
        self.assertIn('unresolved', self.call('baseline', {'scope': ['task'], 'entries': {}, 'exclude': []}, ok=False))
        self.assertEqual(self.unchanged_state(), before)

    def test_irrelevant_options_and_foreign_records_fail_explicitly(self):
        manifest = {'scope': ['task'], 'entries': {}, 'exclude': []}
        self.call('baseline', manifest, ok=False, candidate='HEAD')
        base = self.call('baseline', manifest)
        record = self.record('base', base)
        self.call('candidate', manifest, ok=False, record=record, base='HEAD')
        forged = dict(base)
        forged['candidate'] = 'not-a-commit'
        self.call('compare', manifest, ok=False, record=self.record('forged', forged))
        invalid = self.home / 'invalid-record'
        invalid.write_text('[]')
        message = self.call('release', ok=False, record=invalid)
        self.assertNotIn('Traceback', message)


if __name__ == '__main__':
    unittest.main()
