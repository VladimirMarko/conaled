"""Disposable filesystem tests; never run a compiler or a real cache handoff."""
from pathlib import Path
import importlib.util
import hashlib
import json
import subprocess
import sys
import tempfile
import unittest

sys.dont_write_bytecode = True
ROOT = Path(__file__).resolve().parents[2]


def load(name, path):
    spec = importlib.util.spec_from_file_location(name, path)
    module = importlib.util.module_from_spec(spec)
    spec.loader.exec_module(module)
    return module


migration = load('output_migration', Path(__file__).with_name('migrate-accepted-outputs.py'))
guard = load('fixture_stock_parser', ROOT / 'conaled/scripts/lake_integrity.py')


class Fixture:
    """Known opaque bytes; the fixture verifier is not the real Lake hasher."""

    def __init__(self, root):
        self.root = root
        self.source = root / 'source'
        self.target = root / 'target'
        self.source.mkdir()
        self.target.mkdir()
        self.journal = root / 'migration.jsonl'
        self.modules = ['Fixture.One', 'Fixture.Two']
        self.contents = {}
        self.tracked = set()
        for module in self.modules:
            relative = module.replace('.', '/') + '.lean'
            self.tracked.add(relative)
            for checkout in [self.source, self.target]:
                path = checkout / relative
                path.parent.mkdir(parents=True, exist_ok=True)
                path.write_text('-- identical fixture source\n')
            descriptions = {'m': False, 'o': ['0000000000000000.olean'],
                            'i': '0000000000000000.ilean', 'c': '0000000000000000.c'}
            for extension in ['olean', 'ilean', 'c']:
                path = guard.artifact_path(self.source, module, extension)
                self.put(path, (module + ':' + extension + ':known fixture bytes').encode())
                self.put(path.with_name(path.name + '.hash'), b'ordinary-sidecar\n')
            trace = guard.artifact_path(self.source, module, 'trace')
            self.put(trace, json.dumps({'schemaVersion': '2025-09-10',
                                       'outputs': descriptions}).encode())
        self.setup = self.source / '.lake/build/ir/Fixture/One.setup.json'
        self.setup.write_bytes(b'reproducible setup must remain')
        self.approval = self.source / '.lake/verification.json'
        self.approval.write_bytes(b'fixture record must remain, never copy')

    def put(self, path, data):
        path.parent.mkdir(parents=True, exist_ok=True)
        path.write_bytes(data)
        self.contents[str(path.relative_to(self.source))] = data

    def verify(self, checkout, names):
        # This deliberately uses literal fixture bytes, not Lake's hash output.
        for module in names:
            for path, _ in guard.expected_artifacts(checkout, module):
                relative = str(path.relative_to(checkout))
                if path.read_bytes() != self.contents[relative]:
                    return {module: 'fixture bytes differ'}, 3 * len(names)
        return {}, 3 * len(names)

    def run(self, **options):
        verifier = options.pop('verify', self.verify)
        arguments = dict(tracked_source=self.tracked, tracked_target=self.tracked,
                         context={'fixture': True}, available_bytes=lambda: 1024 ** 3)
        arguments.update(options)
        return migration.migrate_batches(self.source, self.target, self.journal,
                                         guard, verifier, **arguments)

    def intact_source(self):
        return all((self.source / name).is_file() and
                   (self.source / name).read_bytes() == data
                   for name, data in self.contents.items())

    def complete_target(self):
        return all((self.target / name).is_file() and
                   (self.target / name).read_bytes() == data
                   for name, data in self.contents.items())

    def records(self):
        return [json.loads(line) for line in self.journal.read_text().splitlines()]

    def metadata(self, relative, value):
        path = self.root / 'session' / relative
        path.parent.mkdir(parents=True, exist_ok=True)
        data = json.dumps(value, sort_keys=True).encode() if not isinstance(value, bytes) else value
        path.write_bytes(data)
        return {'path': relative, 'sha256': hashlib.sha256(data).hexdigest()}

    def acceptance(self):
        """Synthetic fixture bookkeeping only; never an actual donor acceptance."""
        head = '1' * 40
        verification = self.metadata('validation/fixture-verification.json', {
            'format': 1, 'result': 'passed', 'candidate': head, 'dependencies': {},
            'compiler': 'Synthetic fixture compiler', 'mode': 'incremental',
            'completed_at': '2026-01-01T00:00:00+00:00'})
        self.approval.write_bytes((self.root / 'session' / verification['path']).read_bytes())
        common = {'candidate': head, 'checkout': 'source', 'status': 'finished',
                  'exit_code': 0, 'head_after': head, 'clean_after': True}
        full = self.metadata('validation/fixture-full.json', {
            **common, 'argv': ['./check.sh', '--candidate', 'HEAD'],
            'verification_record_exists': True, 'verification_evidence': verification['path'],
            'ended_at': '2026-01-01T00:00:01+00:00'})
        final = self.metadata('validation/fixture-final.json', {
            **common, 'argv': ['./check.sh', '--verify-candidate', 'HEAD'],
            'verification_sha256': verification['sha256'],
            'ended_at': '2026-01-01T00:00:02+00:00'})
        reviews = {}
        for axis in ['standards', 'spec']:
            reviews[axis] = []
            for scope in ['fixture-one', 'fixture-two']:
                report = self.metadata('reviews/' + axis + '-' + scope + '.md',
                                       (axis + ' / ' + scope + ': synthetic report, no actual review.').encode())
                reviews[axis].append({'scope': scope, 'outcome': 'Passed', 'candidate': head,
                                      'report': report})
        receipt = {'schema': 1, 'candidate': head, 'checkout': 'source', 'accepted': True,
                   'accepted_at': '2026-01-01T00:00:03+00:00', 'full_check': full,
                   'verification': verification, 'final_verification': final, 'reviews': reviews}
        return receipt, self.metadata('validation/fixture-acceptance.json', receipt)

    def plan(self):
        return {'schema': 1, 'source': {'checkout': 'source', 'candidate': '1' * 40},
                'target': {'checkout': 'target', 'candidate': '2' * 40},
                'accepted_donor': {'path': 'validation/absent.json', 'sha256': '0' * 64}}


class MigrationTests(unittest.TestCase):
    def setUp(self):
        self.directory = tempfile.TemporaryDirectory(prefix='output-migration-fixture-', dir=ROOT)
        self.addCleanup(self.directory.cleanup)
        self.fixture = Fixture(Path(self.directory.name))

    def test_success_retains_every_verified_target_byte_and_unrelated_source_record(self):
        result = self.fixture.run()
        self.assertEqual(result['status'], 'completed')
        self.assertTrue(self.fixture.complete_target())
        self.assertTrue(all(not (self.fixture.source / name).exists()
                            for name in self.fixture.contents))
        self.assertEqual(self.fixture.setup.read_bytes(), b'reproducible setup must remain')
        self.assertEqual(self.fixture.approval.read_bytes(), b'fixture record must remain, never copy')
        self.assertFalse((self.fixture.target / '.lake/verification.json').exists())
        self.assertEqual(self.fixture.records()[-1]['state'], 'completed')

    def test_target_verification_failure_preserves_complete_source_and_failed_journal(self):
        def rejecting_verifier(checkout, names):
            if checkout == self.fixture.target:
                return {'Fixture.One': 'independent fixture rejection'}, 6
            return self.fixture.verify(checkout, names)

        with self.assertRaisesRegex(RuntimeError, 'Target output verification failed'):
            self.fixture.run(verify=rejecting_verifier)
        self.assertTrue(self.fixture.intact_source())
        self.assertTrue(self.fixture.complete_target())
        states = [entry['state'] for entry in self.fixture.records()]
        self.assertNotIn('source-retirement-started', states)
        self.assertEqual(states[-1], 'failed')

    def test_retirement_failure_preserves_verified_target_and_exact_known_progress(self):
        def failing_remove(path):
            if path.name.endswith('.hash'):
                raise OSError('fixture deletion failure')
            path.unlink()

        with self.assertRaisesRegex(OSError, 'fixture deletion failure'):
            self.fixture.run(remove_file=failing_remove)
        self.assertTrue(self.fixture.complete_target())
        records = self.fixture.records()
        self.assertIn('target-verified', [x['state'] for x in records])
        self.assertIn('source-retirement-started', [x['state'] for x in records])
        self.assertEqual(records[-1]['retired_paths'], ['.lake/build/lib/lean/Fixture/One.trace'])
        self.assertTrue((self.fixture.source / '.lake/build/lib/lean/Fixture/One.olean').exists())
        before = self.fixture.journal.read_bytes()
        with self.assertRaisesRegex(RuntimeError, 'Prior journal exists'):
            self.fixture.run()
        self.assertEqual(self.fixture.journal.read_bytes(), before)
        self.assertTrue(self.fixture.complete_target())

    def test_copy_failure_keeps_all_donor_files_and_preserves_partial_target_for_diagnosis(self):
        def failing_copy(source, target):
            if target.name.endswith('.hash'):
                target.write_bytes(b'partial fixture output')
                raise OSError('fixture copy failure')
            migration.copy_exclusive(source, target)

        with self.assertRaisesRegex(OSError, 'fixture copy failure'):
            self.fixture.run(copy_file=failing_copy)
        self.assertTrue(self.fixture.intact_source())
        self.assertEqual((self.fixture.target / '.lake/build/lib/lean/Fixture/One.olean.hash').read_bytes(),
                         b'partial fixture output')
        self.assertFalse((self.fixture.target / '.lake/build/lib/lean/Fixture/One.trace').exists())
        self.assertNotIn('source-retirement-started', [x['state'] for x in self.fixture.records()])
        self.assertEqual(self.fixture.records()[-1]['state'], 'failed')

    def test_existing_target_generation_is_skipped_as_a_whole(self):
        preserved = self.fixture.target / '.lake/build/lib/lean/Fixture/One.olean'
        preserved.parent.mkdir(parents=True)
        preserved.write_bytes(b'existing target generation')
        result = self.fixture.run()
        self.assertEqual(result['groups'], 1)
        self.assertEqual(result['skipped_groups'], 1)
        self.assertEqual(preserved.read_bytes(), b'existing target generation')
        for relative, content in self.fixture.contents.items():
            if '/One.' in relative:
                self.assertEqual((self.fixture.source / relative).read_bytes(), content)
                if not relative.endswith('One.olean'):
                    self.assertFalse((self.fixture.target / relative).exists())
            else:
                self.assertFalse((self.fixture.source / relative).exists())
                self.assertEqual((self.fixture.target / relative).read_bytes(), content)

    def test_insufficient_reserve_refuses_before_creating_any_target_output(self):
        with self.assertRaisesRegex(RuntimeError, 'Insufficient space'):
            self.fixture.run(available_bytes=lambda: migration.MIN_RESERVE + migration.JOURNAL_LIMIT - 1)
        self.assertTrue(self.fixture.intact_source())
        self.assertFalse((self.fixture.target / '.lake/build').exists())
        self.assertEqual(self.fixture.records()[-1]['state'], 'failed')

    def test_source_change_during_copy_stops_without_retiring_any_donor_path(self):
        def changing_copy(source, target):
            migration.copy_exclusive(source, target)
            source.write_bytes(b'externally changed fixture source')

        with self.assertRaisesRegex(RuntimeError, 'Captured file changed'):
            self.fixture.run(copy_file=changing_copy)
        self.assertTrue(all((self.fixture.source / relative).is_file()
                            for relative in self.fixture.contents))
        self.assertEqual(self.fixture.records()[-1]['retired_paths'], [])
        self.assertNotIn('target-verified', [x['state'] for x in self.fixture.records()])

    def test_source_verification_failure_leaves_both_generations_untouched(self):
        with self.assertRaisesRegex(RuntimeError, 'Source output verification failed'):
            self.fixture.run(verify=lambda checkout, names: ({'Fixture.One': 'fixture source rejection'}, 6))
        self.assertTrue(self.fixture.intact_source())
        self.assertFalse((self.fixture.target / '.lake/build').exists())
        self.assertEqual(self.fixture.records()[-1]['state'], 'failed')

    def test_symlinked_target_build_is_rejected_before_journal_or_copy(self):
        foreign = self.fixture.root / 'other-fixture-directory'
        foreign.mkdir()
        (self.fixture.target / '.lake').mkdir()
        (self.fixture.target / '.lake/build').symlink_to(foreign, target_is_directory=True)
        with self.assertRaisesRegex(RuntimeError, 'Symlink'):
            self.fixture.run()
        self.assertTrue(self.fixture.intact_source())
        self.assertEqual(list(foreign.iterdir()), [])
        self.assertFalse(self.fixture.journal.exists())

    def test_missing_accepted_donor_receipt_is_rejected_without_transfer(self):
        session = self.fixture.root / 'session'
        (session / 'validation').mkdir(parents=True)
        with self.assertRaisesRegex(RuntimeError, 'Missing accepted donor receipt'):
            migration.validate_acceptance(session, self.fixture.source, 'source', '1' * 40,
                                          {'path': 'validation/absent.json', 'sha256': '0' * 64})
        self.assertTrue(self.fixture.intact_source())
        self.assertFalse((self.fixture.target / '.lake/build').exists())
        self.assertFalse(self.fixture.journal.exists())

    def test_acceptance_binds_both_axes_separate_scopes_and_exact_stock_record(self):
        receipt, reference = self.fixture.acceptance()
        result = migration.validate_acceptance(self.fixture.root / 'session', self.fixture.source,
                                               'source', '1' * 40, reference)
        self.assertEqual(result['receipt'], receipt)
        self.assertEqual(len(result['evidence']), 8)
        self.assertEqual(result['source_verification']['sha256'], receipt['verification']['sha256'])
        self.assertTrue(self.fixture.intact_source())
        self.assertFalse(self.fixture.journal.exists())

    def test_incomplete_reviews_changed_reports_and_mismatched_final_record_reject(self):
        session = self.fixture.root / 'session'
        for failure in ['blocked', 'scope', 'report', 'final', 'live']:
            with self.subTest(failure=failure):
                receipt, reference = self.fixture.acceptance()
                expected = 'Independent review remains incomplete or mismatched'
                if failure == 'blocked':
                    receipt['reviews']['standards'][0]['outcome'] = 'Blocked'
                elif failure == 'scope':
                    receipt['reviews']['spec'].pop()
                    expected = 'Independent review scopes do not match'
                elif failure == 'report':
                    (session / receipt['reviews']['spec'][0]['report']['path']).write_bytes(b'changed report')
                    expected = 'Evidence hash differs'
                elif failure == 'final':
                    final = json.loads((session / receipt['final_verification']['path']).read_bytes())
                    final['verification_sha256'] = '0' * 64
                    receipt['final_verification'] = self.fixture.metadata('validation/fixture-final.json', final)
                    expected = 'Final verification does not bind'
                else:
                    self.fixture.approval.write_bytes(b'changed synthetic success record')
                    expected = 'Live source success record differs'
                reference = self.fixture.metadata('validation/fixture-acceptance.json', receipt)
                with self.assertRaisesRegex(RuntimeError, expected):
                    migration.validate_acceptance(session, self.fixture.source, 'source', '1' * 40, reference)
                self.assertTrue(self.fixture.intact_source())
                self.assertFalse(self.fixture.journal.exists())

    def test_plan_reader_confines_paths_rejects_duplicate_keys_and_preserves_reserve_floor(self):
        plan = self.fixture.plan()
        self.fixture.metadata('validation/fixture-plan.json', plan)
        parsed, _ = migration.read_plan(self.fixture.root, 'fixture-plan.json')
        self.assertEqual(parsed['reserve_bytes'], 320 * 1024 * 1024)
        with self.assertRaisesRegex(RuntimeError, 'plan basename'):
            migration.read_plan(self.fixture.root, '../fixture-plan.json')
        plan['reserve_bytes'] = migration.MIN_RESERVE - 1
        self.fixture.metadata('validation/fixture-plan.json', plan)
        with self.assertRaisesRegex(RuntimeError, 'Reserve is below 320MiB'):
            migration.read_plan(self.fixture.root, 'fixture-plan.json')
        self.fixture.metadata('validation/fixture-plan.json', b'{"schema":1,"schema":1}')
        with self.assertRaisesRegex(RuntimeError, 'Duplicate JSON key'):
            migration.read_plan(self.fixture.root, 'fixture-plan.json')
        with self.assertRaisesRegex(RuntimeError, 'Unsafe relative path'):
            migration.evidence(self.fixture.root / 'session',
                               {'path': 'validation/../../elsewhere', 'sha256': '0' * 64}, 'fixture')

    def test_unfinished_target_journal_blocks_changed_plan_identity(self):
        self.fixture.metadata('validation/output-migration-fixture.jsonl',
                              (json.dumps({'state': 'started', 'context': {'target_checkout': 'target'}}) +
                               '\n' + json.dumps({'state': 'failed'}) + '\n').encode())
        with self.assertRaisesRegex(RuntimeError, 'Unfinished target migration'):
            migration.reject_unfinished_target_journals(self.fixture.root, 'target')
        self.assertTrue(self.fixture.intact_source())
        self.assertFalse((self.fixture.target / '.lake/build').exists())

    def test_cli_refuses_missing_acceptance_before_any_external_runtime_or_output_touch(self):
        self.fixture.metadata('validation/fixture-plan.json', self.fixture.plan())
        script = self.fixture.root / 'session/validation/migrate-accepted-outputs.py'
        script.write_bytes(Path(migration.__file__).read_bytes())
        # An empty PATH ensures this synthetic rejection cannot call Git, Lean or Nix.
        result = subprocess.run([sys.executable, str(script), 'fixture-plan.json'],
                                cwd=self.fixture.root, env={'PATH': '', 'PYTHONDONTWRITEBYTECODE': '1'},
                                text=True, stdout=subprocess.PIPE, stderr=subprocess.PIPE, timeout=20)
        self.assertEqual(result.returncode, 1)
        self.assertIn('Missing accepted donor receipt', result.stderr)
        self.assertEqual(result.stdout, '')
        self.assertTrue(self.fixture.intact_source())
        self.assertFalse((self.fixture.target / '.lake/build').exists())
        self.assertEqual(list((self.fixture.root / 'session/validation').glob('output-migration-*.jsonl')), [])


if __name__ == '__main__':
    unittest.main(verbosity=2)
