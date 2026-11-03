#!/usr/bin/env python3
"""Numerical probe: framed hyperbolic motions and the cone orbifold H^2 // C4.

Python >= 3.9; standard library only. Run: python orbifold_gyro_probe.py

This is an original illustrative prototype, not Hyperbolica source code,
not a formally verified integrator, and not a general orbifold engine.
The disk has curvature -1, with metric ds = 2 |dz| / (1 - |z|^2).
A pose (a,u), |a| < 1, |u| = 1, denotes the isometry
    z -> (a + u*z) / (1 + conjugate(a)*u*z).
The C4 identification acts on BOTH position and frame: (a,u) -> (i*a,i*u).

Mathematical background:
  https://arxiv.org/abs/1303.4785
  https://www.math.shimane-u.ac.jp/memoir/32/kikkawa2.pdf
  https://isa-afp.org/entries/GyrovectorSpaces.html

All residuals below are coordinate residuals in a well-conditioned region,
NOT intrinsic error bounds. Randomized tests are not proofs. The finite C4
labels are exact integers modulo 4; positions and rotations use floating point.
"""
from dataclasses import dataclass
import cmath
import json
import math
import random
from typing import Tuple

Matrix = Tuple[Tuple[complex, complex], Tuple[complex, complex]]
ROOTS_C4 = (1 + 0j, 1j, -1 + 0j, -1j)


def finite_complex(z: complex) -> bool:
    return math.isfinite(z.real) and math.isfinite(z.imag)


def check_disk(z: complex) -> None:
    if not finite_complex(z) or abs(z) >= 1:
        raise ValueError('Expected a finite point strictly inside the unit disk.')


def mobius_add(a: complex, b: complex) -> complex:
    """Nonassociative Mobius addition, with a left-translation convention."""
    check_disk(a)
    check_disk(b)
    return (a + b) / (1 + a.conjugate() * b)


def gyration(a: complex, b: complex) -> complex:
    """Unit-complex rotation satisfying T_a T_b = T_(a+b)_gyro gyr[a,b]."""
    check_disk(a)
    check_disk(b)
    return (1 + a * b.conjugate()) / (1 + a.conjugate() * b)


@dataclass(frozen=True)
class Pose:
    a: complex
    u: complex = 1 + 0j

    def __post_init__(self) -> None:
        check_disk(self.a)
        if not finite_complex(self.u) or abs(abs(self.u) - 1) > 1e-8:
            raise ValueError('Expected a unit-complex frame rotation.')

    def act(self, z: complex) -> complex:
        return mobius_add(self.a, self.u * z)

    def compose(self, other: 'Pose') -> 'Pose':
        """self after other: act(compose(p,q),z) = act(p,act(q,z))."""
        b = self.u * other.a
        return Pose(mobius_add(self.a, b),
                    gyration(self.a, b) * self.u * other.u)

    def matrix(self) -> Matrix:
        """Projective complex 2x2 matrix for an independent composition check."""
        return ((self.u, self.a), (self.a.conjugate() * self.u, 1 + 0j))

    def relabel_c4(self, k: int) -> 'Pose':
        """Change orbifold representative, NOT the physical state."""
        root = ROOTS_C4[k % 4]
        return Pose(root * self.a, root * self.u)


def matrix_product(a: Matrix, b: Matrix) -> Matrix:
    return (
        (a[0][0]*b[0][0] + a[0][1]*b[1][0],
         a[0][0]*b[0][1] + a[0][1]*b[1][1]),
        (a[1][0]*b[0][0] + a[1][1]*b[1][0],
         a[1][0]*b[0][1] + a[1][1]*b[1][1]),
    )


def projective_matrix_error(a: Matrix, b: Matrix) -> float:
    # Normalize by lower-right entry. This is safe for the sampled disk maps.
    return max(abs(a[i][j]/a[1][1] - b[i][j]/b[1][1])
               for i in range(2) for j in range(2))


def pose_error(p: Pose, q: Pose) -> float:
    return max(abs(p.a - q.a), abs(p.u - q.u))


def quotient_pose_error(p: Pose, q: Pose) -> float:
    return min(pose_error(p, q.relabel_c4(k)) for k in range(4))


def random_point(rng: random.Random, radius: float = 0.45) -> complex:
    return radius * math.sqrt(rng.random()) * cmath.exp(2j*math.pi*rng.random())


def random_pose(rng: random.Random) -> Pose:
    return Pose(random_point(rng), cmath.exp(2j*math.pi*rng.random()))


def run_probe(samples: int = 1000, seed: int = 1729) -> dict:
    if samples < 1:
        raise ValueError('samples must be positive')
    rng = random.Random(seed)
    errors = {
        'gyro_only_associativity_defect_max': 0.0,
        'gyroassociative_identity_residual_max': 0.0,
        'framed_associativity_residual_max': 0.0,
        'framed_vs_projective_matrix_residual_max': 0.0,
        'framed_composed_action_residual_max': 0.0,
        'c4_representative_equivariance_residual_max': 0.0,
    }
    for _ in range(samples):
        p, q, r = (random_pose(rng) for _ in range(3))
        a, b, c = p.a, q.a, r.a
        lhs = mobius_add(a, mobius_add(b, c))
        naive_rhs = mobius_add(mobius_add(a, b), c)
        repaired_rhs = mobius_add(mobius_add(a, b), gyration(a,b) * c)
        errors['gyro_only_associativity_defect_max'] = max(
            errors['gyro_only_associativity_defect_max'], abs(lhs-naive_rhs))
        errors['gyroassociative_identity_residual_max'] = max(
            errors['gyroassociative_identity_residual_max'], abs(lhs-repaired_rhs))
        errors['framed_associativity_residual_max'] = max(
            errors['framed_associativity_residual_max'],
            pose_error(p.compose(q).compose(r), p.compose(q.compose(r))))
        errors['framed_vs_projective_matrix_residual_max'] = max(
            errors['framed_vs_projective_matrix_residual_max'],
            projective_matrix_error(p.compose(q).matrix(),
                                    matrix_product(p.matrix(), q.matrix())))
        z = random_point(rng)
        errors['framed_composed_action_residual_max'] = max(
            errors['framed_composed_action_residual_max'],
            abs(p.compose(q).act(z) - p.act(q.act(z))))
        k = rng.randrange(4)
        errors['c4_representative_equivariance_residual_max'] = max(
            errors['c4_representative_equivariance_residual_max'],
            pose_error(p.relabel_c4(k).compose(q),
                       p.compose(q).relabel_c4(k)))

    # Unit-speed geodesic along a diameter from signed distance -1 to +1.
    # The body frame is part of the state; each update acts on the RIGHT.
    dt, nsteps = 0.05, 40
    step = Pose(complex(math.tanh(dt/2)))
    clean = Pose(complex(-math.tanh(0.5)))
    relabeled = clean.relabel_c4(1)
    trajectory_error = 0.0
    exact_geodesic_error = 0.0
    apex_error = None
    for j in range(1, nsteps+1):
        clean = clean.compose(step)
        relabeled = relabeled.compose(step).relabel_c4(rng.randrange(4))
        trajectory_error = max(trajectory_error, quotient_pose_error(clean, relabeled))
        exact = math.tanh((-1 + j*dt)/2)
        exact_geodesic_error = max(exact_geodesic_error, abs(clean.a-exact))
        if j == nsteps//2:
            apex_error = abs(clean.a)

    # A wrong implementation changes representatives of position only.
    p = Pose(0.2+0.1j, cmath.exp(0.3j))
    wrong = Pose(1j*p.a, p.u)
    wrong_after = wrong.compose(Pose(0.08+0.03j))
    right_after = p.compose(Pose(0.08+0.03j))
    wrong_position_residual = min(abs(wrong_after.a-root*right_after.a)
                                  for root in ROOTS_C4)

    # Independent orbit representatives do not give well-defined gyro addition.
    positive = mobius_add(0.2+0j, 0.2+0j)
    canceled = mobius_add(0.2+0j, -0.2+0j)
    for key, value in errors.items():
        if key != 'gyro_only_associativity_defect_max':
            assert value < 1e-12, (key, value)
    assert trajectory_error < 1e-12
    assert exact_geodesic_error < 1e-12
    assert wrong_position_residual > 1e-3
    assert abs(positive-5/13) < 1e-15 and canceled == 0
    return {
        'samples': samples,
        'seed': seed,
        'random_test_max_coordinate_residuals': errors,
        'geodesic_test': {
            'steps': nsteps,
            'time_step': dt,
            'max_quotient_pose_error_with_random_relabelings': trajectory_error,
            'max_position_error_against_exact_geodesic': exact_geodesic_error,
            'distance_from_origin_in_disk_coordinates_at_crossing': apex_error,
        },
        'deliberately_wrong_position_only_relabeling_residual': wrong_position_residual,
        'failure_of_addition_on_independent_orbit_representatives': {
            'a': 0.2,
            'a_gyroplus_a': positive.real,
            'a_gyroplus_minus_a': canceled.real,
        },
        'status': 'All expected checks passed; numerical tests, not formal proofs.',
    }


if __name__ == '__main__':
    print(json.dumps(run_probe(), indent=2))
