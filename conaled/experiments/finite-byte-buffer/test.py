"""Public service tests against independently calculated replies (#253)."""
import unittest
import itertools
from adapter import create, Environment

class BufferTests(unittest.TestCase):
    def test_finite_capacity_and_allocation_refusal(self):
        status, b = create(1, True, word_max=1)
        self.assertEqual(status, 'ready')
        self.assertEqual(b.step(('append', 1)), ('accepted', None))
        self.assertEqual(b.step(('append', 0)), ('overflow', None))
        self.assertEqual(b.step(('observe', None)), ('sequence', b'\x01'))
        self.assertEqual(create(1, env=Environment(fail_allocation=True)), ('allocation', None))
        with self.assertRaises(ValueError):
            create(2, word_max=1)

    def test_refusals_preserve_history_and_copy_is_independent(self):
        _, b = create(2)
        self.assertEqual(b.step(('append', 1)), ('accepted', None))
        self.assertEqual(b.step(('append', 0), Environment(fail_allocation=True)), ('allocation', None))
        self.assertEqual(b.step(('observe', None), Environment(fail_output=True)), ('output', None))
        self.assertEqual(b.step(('observe', None)), ('sequence', b'\x01'))
        self.assertEqual(b.convert(Environment(fail_allocation=True)), ('allocation', None))
        status, c = b.convert()
        self.assertEqual(status, 'ready')
        self.assertEqual(c.step(('query', None)), ('summary', 1))
        self.assertEqual(c.step(('append', 1)), ('accepted', None))
        self.assertEqual(c.step(('observe', None)), ('sequence', b'\x01\x01'))
        self.assertEqual(b.step(('observe', None)), ('sequence', b'\x01'))
        self.assertEqual(b.step(('append', 0)), ('accepted', None))
        self.assertEqual(c.step(('observe', None)), ('sequence', b'\x01\x01'))

    def test_full_uint32_boundary_without_large_allocation(self):
        from adapter import successor, MAX_WORD
        self.assertEqual(successor(MAX_WORD - 1, MAX_WORD), MAX_WORD)
        self.assertIsNone(successor(MAX_WORD, MAX_WORD))
        self.assertIsNone(successor(0, 0))
        for size, capacity in ((-1, 1), (2, 1), (0, MAX_WORD + 1)):
            with self.assertRaises(ValueError):
                successor(size, capacity)

    def test_exact_differential_traces(self):
        commands = [('append', 0), ('append', 1), ('query', None), ('observe', None)]
        count = 0
        for capacity in range(4):
            for length in range(6):
                for trace in itertools.product(commands, repeat=length):
                    buffers = [create(capacity, mode, word_max=3)[1] for mode in (False, True)]
                    history = []
                    for command in trace:
                        op, value = command
                        if op == 'append':
                            if len(history) < capacity:
                                history = history + [value]
                                expected = ('accepted', None)
                            else:
                                expected = ('overflow', None)
                        elif op == 'query':
                            expected = ('summary', sum(history) % 2)
                        else:
                            expected = ('sequence', bytes(history))
                        for b in buffers:
                            self.assertEqual(b.step(command), expected)
                            self.assertEqual(b.step(('observe', None)), ('sequence', bytes(history)))
                    for b in buffers:
                        self.assertEqual(b.step(('append', 1), Environment(fail_allocation=True)), ('allocation', None))
                        self.assertEqual(b.step(('observe', None), Environment(fail_output=True)), ('output', None))
                        self.assertEqual(b.step(('observe', None)), ('sequence', bytes(history)))
                        status, c = b.convert()
                        self.assertEqual(status, 'ready')
                        self.assertEqual(c.step(('query', None)), ('summary', sum(history) % 2))
                        self.assertEqual(c.step(('observe', None)), ('sequence', bytes(history)))
                    count += 1
        self.assertEqual(count, 5460)

if __name__ == '__main__':
    unittest.main()
