#!/usr/bin/env python3
"""Process-level independent Boolean map/delay oracle; no source evaluator."""
import subprocess
import unittest


class StaticFunctionReactive(unittest.TestCase):
    def test_compiled_machine_and_restart(self):
        result = subprocess.run(
            ['lake', 'env', 'lean', '--run', 'scripts/static-function-reactive-main.lean'],
            text=True, capture_output=True, check=False,
        )
        self.assertEqual(result.returncode, 0, result.stdout + result.stderr)
        seen = costs = duplications = regional = seeded = blocked = 0
        for line in result.stdout.splitlines():
            fields = line.split('|')
            if fields[0] == 'run':
                _, name, state, word, outputs, final = fields
                expected = []
                for token in word:
                    expected.append(state)
                    state = format(int(token), '02b')
                    if name in ('neg', 'mask'):
                        state = ''.join('1' if b == '0' else '0' for b in state)
                self.assertEqual(outputs, ','.join(expected), (name, word))
                self.assertEqual(final, state, (name, word))
                seen += 1
            elif fields[0] == 'seeded':
                _, name, output, state = fields
                self.assertEqual(output, '01')
                self.assertEqual(state, '11' if name in ('neg', 'mask') else '00')
                seeded += 1
            elif fields[0] == 'nonexecution':
                self.assertIn(fields[1], ('capacity', 'unsupported'))
                self.assertEqual(fields[2], 'none')
                blocked += 1
            elif fields[0] == 'cost':
                self.assertTrue(all(int(n) > 0 for n in fields[2:]))
                print(line)
                costs += 1
            elif fields[0] == 'duplication':
                _, n, work, nodes = fields
                self.assertEqual(int(nodes), 4 * 2 ** int(n) - 3)
                self.assertGreater(int(work), 0)
                print(line)
                duplications += 1
            elif fields[0] == 'regional':
                _, value, output, state = fields
                expected = not (value[0] == '1' and value[1] == '0')
                self.assertEqual(output, '10')
                self.assertEqual(state, '11' if expected else '00')
                regional += 1
            elif fields[0] == 'admission':
                self.assertEqual(fields[1:], ['accepted', 'capacity', 'unsupported', 'unsupported', 'unsupported'])
            else:
                self.fail(f'unexpected output: {line}')
        self.assertEqual(seen, 5 * 4 * sum(4 ** n for n in range(5)))
        self.assertEqual((costs, duplications, regional), (5, 8, 4))
        self.assertEqual((seeded, blocked), (5, 4))
        self.assertIn('admission|', result.stdout)
        print(f"runs|{seen}")


if __name__ == '__main__':
    unittest.main()
