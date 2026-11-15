#!/usr/bin/env python3
"""Native count-parity oracle for compiled bounded fold public runners."""
import subprocess
import unittest


class BoundedFold(unittest.TestCase):
    def test_frozen_fixture_and_continuations(self):
        result = subprocess.run(
            ['lake', 'env', 'lean', '--run', 'scripts/bounded-fold-main.lean'],
            text=True, capture_output=True, check=True,
        )
        lines = result.stdout.splitlines()
        self.assertIn('fixture|0110|1', lines)
        seen = 0
        for line in lines:
            fields = line.split('|')
            if fields[0] == 'run':
                _, seed, batches, outputs, final, resumed, regional = fields
                state = int(seed)
                expected = []
                for batch in batches.split(',') if batches != '-' else []:
                    expected.append(str(state))
                    state = (state + batch.count('1')) % 2
                self.assertEqual(outputs, ''.join(expected))
                self.assertEqual(final, str(state))
                self.assertEqual(resumed, outputs + ':' + final)
                self.assertEqual(regional, ''.join('1' if x == '0' else '0' for x in expected))
                seen += 1
            elif fields[0] == 'fixture':
                self.assertEqual(fields[1:], ['0110', '1'])
            elif fields[0] == 'admission':
                self.assertEqual(fields[1:], ['accepted','rejected','unsupported','0110:1','none'])
            elif fields[0] == 'ingest':
                _, capacity, samples, accepted = fields
                self.assertEqual(accepted, samples if len(samples) <= int(capacity) else 'reject')
            elif fields[0] == 'space':
                _, independent, composed, actual = fields
                self.assertLess(int(independent), int(actual))
                self.assertLessEqual(int(actual), int(composed))
            else:
                self.fail(line)
        self.assertEqual(seen, 2 * (1 + 15 + 225 + 3375))
        self.assertEqual(sum(x.startswith('ingest|') for x in lines), 4 * 31)
        self.assertTrue(any(x.startswith('space|') for x in lines))


if __name__ == '__main__':
    unittest.main()
