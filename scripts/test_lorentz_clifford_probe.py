"""Public point/frame and composition controls for the bounded research probe."""
import unittest
from decimal import Decimal, localcontext
import lorentz_clifford_probe as probe


class GeometricControls(unittest.TestCase):
    def setUp(self):
        self.ctx = localcontext()
        self.ctx.__enter__().prec = 80
        self.c = probe.Arithmetic(Decimal)

    def tearDown(self):
        self.ctx.__exit__(None, None, None)

    def pose(self, a=("1/3", "0"), u=("0", "1")):
        return tuple(tuple(self.c.rational(x) for x in part) for part in (a, u))

    def close(self, actual, expected):
        for x, y in zip(probe.flatten(actual), probe.flatten(expected)):
            self.assertLess(abs(x.value - y.value), Decimal("1e-65"))

    def test_independent_frame_and_point(self):
        # At a=1/3 and u=i, h=(1-1/9)i/2=4i/9.
        expected = self.pose(("1/3", "0"), ("0", "4/9"))
        for name in probe.BACKENDS:
            self.close(probe.decode(name, probe.encode(name, self.pose())), expected)

    def test_inverse_and_noncommuting_composition(self):
        p = self.pose()
        q = self.pose(("0", "1/4"), ("3/5", "4/5"))
        unit = self.pose(("0", "0"), ("1", "0"))
        expected = self.pose(("1/11", "0"), ("-48/121", "36/121"))
        for name in probe.BACKENDS:
            x, y = probe.encode(name, p), probe.encode(name, q)
            self.close(probe.decode(name, probe.compose(name, x, probe.inverse(name, x))),
                       probe.decode("pose", unit))
            self.close(probe.decode(name, probe.compose(name, x, y)),
                       expected)
        self.assertGreater(abs(probe.observation_values(probe.decode("pose", probe.compose("pose", p, q)))[0]
                               - probe.observation_values(probe.decode("pose", probe.compose("pose", q, p)))[0]), Decimal("0.01"))

    def test_scalar_redundancy_and_spin_cover(self):
        p = self.pose()
        m = probe.encode("complex", p)
        scaled = [[probe.cmul((self.c.rational("-3"), self.c.rational("2")), z)
                   for z in row] for row in m]
        self.close(probe.decode("complex", m), probe.decode("complex", scaled))
        r = probe.encode("spin", p)
        self.close(probe.decode("spin", r), probe.decode("spin", {k: -v for k, v in r.items()}))

    def test_quarter_turn_changes_frame_and_point(self):
        p = self.pose(("1/3", "1/4"), ("3/5", "4/5"))
        q = self.pose(("0", "0"), ("0", "1"))
        z, h = probe.decode("pose", p)
        expected = ((-z[1], z[0]), (-h[1], h[0]))
        for name in probe.BACKENDS:
            self.close(probe.decode(name, probe.compose(name, probe.encode(name, q), probe.encode(name, p))), expected)

    def test_half_turn_and_cached_sequence(self):
        p = self.pose(u=("-1", "0"))
        self.close(probe.decode("spin", probe.encode("spin", p)), probe.decode("pose", p))
        initial = (("1/3", "0"), ("0", "1"))
        for name in probe.BACKENDS:
            normal, costs = probe.compute(name, 8, initial, Decimal)
            cached, cached_costs = probe.compute(name, 8, initial, Decimal, reuse=True)
            self.assertEqual(normal, cached)
            self.assertEqual(costs["composition"], cached_costs["composition"])
            if name != "pose":
                self.assertLess(sum(cached_costs["conversion"].values()), sum(costs["conversion"].values()))

    def test_signature_duality_and_finite_prefixes(self):
        one = self.c.scalar(1)
        for mask, expected in ((1,-1), (2,1), (4,1)):
            self.assertEqual(probe.gp({mask:one}, {mask:one})[0].value, expected)
        # -X I = X0 e12 - X1 e20 - X2 e01; e20=-e02.
        dual = probe.gp({1:-self.c.scalar(5), 2:-self.c.scalar(3), 4:-self.c.scalar(2)}, {7:one})
        self.assertEqual({i:x.value for i,x in dual.items()}, {6:Decimal(5), 5:Decimal(3), 3:Decimal(-2)})
        initial = (("1/3", "0"), ("0", "1"))
        for n in (0,1,8,64):
            expected, _ = probe.compute("pose", n, initial, Decimal)
            for name in probe.BACKENDS:
                actual, _ = probe.compute(name, n, initial, Decimal)
                self.assertLess(max(abs(x-y) for x,y in zip(actual,expected)), Decimal("1e-65"))

    def test_boundary_and_cutoff_rejected(self):
        for name in probe.BACKENDS:
            with self.assertRaises(ValueError):
                probe.encode(name, self.pose(("1", "0")))
        with self.assertRaises(ValueError):
            probe.workload(65)


if __name__ == "__main__":
    unittest.main()
