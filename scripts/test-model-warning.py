#!/usr/bin/env python3
"""Public-command regressions for the optional advisory model monitor."""
import concurrent.futures
import json
from pathlib import Path
import subprocess
import sys
import tempfile
import unittest

SCRIPT = Path(__file__).with_name('model-warning.py')
POLICY = SCRIPT.parent.parent / '.agents/model-policy.json'


class MonitorTests(unittest.TestCase):
    def setUp(self):
        self.temporary = tempfile.TemporaryDirectory()
        self.addCleanup(self.temporary.cleanup)
        self.root = Path(self.temporary.name)
        self.state = self.root / 'state'

    def event(self, model='gpt-6-astra', effort='medium', session='session', turn='turn'):
        transcript = self.root / (session + '.jsonl')
        transcript.write_text(json.dumps({'type': 'session_meta', 'payload': {'id': session}}) + '\n' + json.dumps({'type': 'turn_context', 'payload': {'turn_id': turn, 'model': model, 'effort': effort}}) + '\n')
        return {'hook_event_name': 'UserPromptSubmit', 'cwd': str(self.root), 'session_id': session, 'turn_id': turn, 'model': model, 'transcript_path': str(transcript)}

    def call(self, event, action='hook', extra=()):
        run = subprocess.run([sys.executable, str(SCRIPT), action, '--state-dir', str(self.state), *extra], input=json.dumps(event), text=True, capture_output=True)
        self.assertEqual(run.returncode, 0, run.stderr)
        return json.loads(run.stdout) if run.stdout else {}

    def diagnostic(self, event):
        return self.call(event, 'inspect')

    def test_approved_is_quiet(self):
        event = self.event()
        self.assertEqual(self.call(event), {})
        self.assertEqual(self.diagnostic(event)['status'], 'approved')
        self.assertEqual(self.call(self.event(effort='high', turn='next')), {})
        self.assertEqual(len(list(self.state.glob('*.json'))), 1)

    def test_every_default_configuration(self):
        for entry in json.loads(POLICY.read_text())['approved']:
            for effort in entry['efforts']:
                self.assertEqual(self.diagnostic(self.event(entry['model'], effort))['status'], 'approved')

    def test_unapproved_model_and_effort(self):
        for model, effort in [('gpt-6-sol', 'high'), ('gpt-6-astra', 'low')]:
            event = self.event(model, effort)
            self.assertEqual(self.diagnostic(event)['status'], 'unapproved')
            output = self.call(event)
            self.assertEqual(set(output), {'systemMessage'})
            self.assertEqual(output['systemMessage'], f'🟥 Model configuration outside approved defaults: {model} / {effort}. Work continues.')

    def test_stale_turn_cannot_supply_effort(self):
        event = self.event()
        event['turn_id'] = 'new-turn'
        result = self.diagnostic(event)
        self.assertEqual(result['status'], 'unknown')
        self.assertIsNone(result['effort'])
        self.assertIn('🟧', self.call(event)['systemMessage'])

    def test_model_mismatch_cannot_supply_effort(self):
        event = self.event()
        event['model'] = 'gpt-6-sol'
        self.assertEqual(self.diagnostic(event)['status'], 'unknown')
        self.assertIsNone(self.diagnostic(event)['effort'])

    def test_transcript_session_mismatch_is_unknown(self):
        event = self.event()
        event['session_id'] = 'different-session'
        self.assertEqual(self.diagnostic(event)['status'], 'unknown')

    def test_latest_matching_context_is_authoritative(self):
        event = self.event()
        with Path(event['transcript_path']).open('a') as stream:
            stream.write(json.dumps({'type': 'turn_context', 'payload': {'turn_id': 'turn', 'model': 'gpt-6-astra', 'effort': None}}) + '\n')
        self.assertEqual(self.diagnostic(event)['status'], 'unknown')

    def test_absent_and_partial_metadata(self):
        event = self.event()
        path = Path(event['transcript_path'])
        path.write_text('{"type":"turn_context"')
        self.assertEqual(self.diagnostic(event)['status'], 'unknown')
        path.unlink()
        self.assertEqual(self.diagnostic(event)['status'], 'unknown')
        event.pop('transcript_path')
        self.assertEqual(self.diagnostic(event)['status'], 'unknown')

    def test_missing_identity_is_unknown(self):
        for key in ('session_id', 'turn_id', 'model'):
            event = self.event()
            del event[key]
            self.assertEqual(self.diagnostic(event)['status'], 'unknown')

    def test_transitions_dedup_and_recovery(self):
        event = self.event(effort='low')
        self.assertIn('🟥', self.call(event)['systemMessage'])
        self.assertEqual(self.call(event), {})
        event = self.event(effort='medium', turn='next')
        self.assertEqual(self.call(event)['systemMessage'], '🟩 Model configuration matches approved defaults: gpt-6-astra / medium.')
        self.assertEqual(self.call(event), {})
        event['turn_id'] = 'not-flushed'
        self.assertIn('🟧', self.call(event)['systemMessage'])
        event = self.event(effort='medium', turn='not-flushed')
        self.assertEqual(self.call(event)['systemMessage'], '🟩 Model configuration matches approved defaults: gpt-6-astra / medium.')

    def test_concurrent_sessions_and_duplicate_events(self):
        events = [self.event(effort='low', session=f's{i}') for i in range(6)]
        with concurrent.futures.ThreadPoolExecutor() as pool:
            outputs = list(pool.map(self.call, events + events))
        self.assertEqual(sum(bool(x) for x in outputs), 6)
        states = [json.loads(p.read_text()) for p in self.state.glob('*.json')]
        self.assertEqual({r['session_id'] for r in states}, {e['session_id'] for e in events})

    def test_invalid_policy_warns_without_blocking(self):
        invalid = self.root / 'policy.json'
        invalid.write_text('{}')
        output = self.call(self.event(), extra=['--policy', str(invalid)])
        self.assertEqual(set(output), {'systemMessage'})
        self.assertIn('unavailable', output['systemMessage'])

    def test_no_context_or_blocking_output(self):
        for effort in ('medium', 'low', None):
            output = self.call(self.event(effort=effort))
            self.assertLessEqual(set(output), {'systemMessage'})

    def test_other_hook_event_ignored(self):
        event = self.event(effort='low')
        event['hook_event_name'] = 'Stop'
        self.assertEqual(self.call(event), {})

    def test_install_preserves_existing_and_is_idempotent(self):
        hooks = self.root / 'project with spaces/hooks.json'
        hooks.parent.mkdir()
        old = {'hooks': {'Stop': [{'hooks': [{'type': 'command', 'command': 'existing'}]}]}, 'other': 42}
        hooks.write_text(json.dumps(old))
        command = [sys.executable, str(SCRIPT), 'install', '--hooks-file', str(hooks), '--state-dir', str(self.state)]
        proposed = subprocess.run(command, text=True, capture_output=True, check=True)
        self.assertEqual(json.loads(hooks.read_text()), old)
        expected = json.loads(proposed.stdout)
        for _ in range(2):
            subprocess.run(command + ['--write'], check=True, capture_output=True)
        self.assertEqual(json.loads(hooks.read_text()), expected)
        self.assertEqual(expected['hooks']['Stop'], old['hooks']['Stop'])
        self.assertEqual(expected['other'], 42)
        self.assertIn(sys.executable, expected['hooks']['UserPromptSubmit'][0]['hooks'][0]['command'])


if __name__ == '__main__':
    unittest.main()
