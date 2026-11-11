#!/usr/bin/env python3
"""Independent process-level oracle for the local compiled regional catalog."""
import subprocess
import unittest


class RegionalPlans(unittest.TestCase):
    def test_compiled_runs_and_boundaries(self):
        result = subprocess.run(
            ['lake', 'env', 'lean', '--run', 'scripts/regional-plans-main.lean'],
            text=True, capture_output=True, check=True,
        )
        seen = 0
        alphabet = [False, True, (False, False), (False, True), (True, False), (True, True)]
        for line in result.stdout.splitlines():
            fields = line.split('|')
            if fields[0] == 'run':
                _, cut, seed, tokens, outputs, final = fields
                state = seed == '1'
                expected = []
                for token in tokens:
                    expected.append('0' if state else '1')
                    value = alphabet[int(token)]
                    state = value if isinstance(value, bool) else value[0] and not value[1]
                self.assertEqual(outputs, ''.join(expected), (cut, seed, tokens))
                self.assertEqual(final, '1' if state else '0', (cut, seed, tokens))
                seen += 1
            elif fields[0] == 'boundary':
                _, pair, value = fields
                self.assertEqual(value, {'00': 'reject', '01': '0', '10': '1', '11': 'reject'}[pair])
            elif fields[0] == 'parallel':
                self.assertEqual(fields[1:], ['10,01,11,00', '0'])
            elif fields[0] == 'query':
                self.assertEqual(fields[1:], ['1', '0', '0'])
            elif fields[0] == 'shared':
                self.assertEqual(fields[1:], ['11'])
            elif fields[0] == 'admission':
                self.assertEqual(fields[1:], ['accepted', 'unsupported', 'rejected', 'rejected'])
            else:
                self.fail(f'unexpected output: {line}')
        self.assertEqual(seen, 3 * 2 * (1 + 6 + 36 + 216 + 1296))
        self.assertEqual(sum(line.startswith('boundary|') for line in result.stdout.splitlines()), 4)
        self.assertEqual(sum(line.startswith('parallel|') for line in result.stdout.splitlines()), 3)
        self.assertIn('admission|', result.stdout)
        self.assertEqual(sum(line.startswith('query|') for line in result.stdout.splitlines()), 3)
        self.assertEqual(sum(line.startswith('shared|') for line in result.stdout.splitlines()), 3)


if __name__ == '__main__':
    unittest.main()
