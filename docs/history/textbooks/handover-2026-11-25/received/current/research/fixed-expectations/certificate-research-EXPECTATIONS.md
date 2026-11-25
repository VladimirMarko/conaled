# Certificate correspondence expectations, before draft proof checking

Status: authoring assistance, prepared on 24 November 2026. No Lean compiler has
been run for this directory. These are new proposed consumers, not replacements
for any frozen fixture or independent review. The author has read the existing
encoding, verifier, witness, framing and staged finite-machine source; these
expectations are not a blind review of those implementations.

## Required semantic statements

1. `BinaryYes input` must expose exactly two `Shape n` values, the literal
   little-endian threshold list `bs`, and distance at most `value bs`.
2. On the literal encoding of any supplied `s t : Shape n`, membership must be
   equivalent to `Shape.distance s t <= value bs` for the same `s`, `t`, and
   `bs`. Redundant high zero bits remain part of the instance encoding.
3. The certificate relation on a fixed encoded instance must be the actual
   `verifyFramed` Boolean. Its accepted certificates are exactly fixed-bit
   encodings of successful legal traces within the represented threshold.
4. The small-certificate equivalence must use `cert.length <= input.length^2`
   and `(frame input cert).length <= (input.length+1)^2`. No positivity or
   valid-syntax premise may be added to the equivalence on arbitrary `input`.
5. A finite primitive-machine completeness consumer must use the existing
   actual run, retain its full source relation and mapped endpoint, and only
   enlarge its bound. It must not replace the stored step count by the bound.
   Its start is still `trInit`-encoded input; it is not an ordinary-I/O or NP
   result.

## Concrete checks fixed from the encoding and mathematics

| Case | Instance bit length | Certificate bits | Framed length | Expected result |
| --- | ---: | ---: | ---: | --- |
| Two empty trees, `bs=[]`, empty certificate | 20 | 0 | 41 | Accept |
| Two empty trees, `bs=[false,false]`, empty certificate | 28 | 0 | 57 | Accept; preserve threshold width |
| Distinct two-node left/right chains, `bs=[]`, one root right rotation | 52 | 8 | 113 | Reject; no certificate can be accepted at threshold zero |
| Same chains, `bs=[true]`, one root right rotation | 56 | 8 | 121 | Accept |
| Same chains, `bs=[true,false]`, same rotation | 60 | 8 | 129 | Accept with unchanged numeric threshold and larger literal input |
| Raw instance `[]`, any certificate | 0 | Arbitrary | Arbitrary | `BinaryYes []` is false |

These follow from `inputCode_length = 4*n + bs.length + 5` on common-size
shapes, four bits per symbol, a root move's two symbols, and
`frame_length = 2*input.length + cert.length + 1`.

## Numerical bound checks

For the existing fixed-programme primitive bound

```
P_A(N) = 3*(N*N + 10*N + 36)*(1 + A*(2*(N+1+A)+2)),
```

the coefficient expansion is

```
6*A*N^3 + (6*A^2+72*A+3)*N^2
  + (60*A^2+336*A+30)*N + 216*A^2+432*A+108.
```

It is monotone for all natural `A,N`; `A=0` is included. Check values:

| A | N | P_A(N) |
| ---: | ---: | ---: |
| 0 | 0 | 108 |
| 0 | 1 | 141 |
| 1 | 0 | 756 |
| 1 | 1 | 1269 |

At the actual empty-tree frame `N=41`, the first factor before the outer three
is 2127, so `P_A(41)=6381*(1+A*(86+2*A))`. The generic small-certificate size
bound at instance length20 is441, not the exact frame length41. The proposed
consumer may use `P_A((input.length+1)^2)` as a polynomial upper bound, while
retaining the original actual run and its exact stored steps.

No exact primitive running time is predicted here. The eventual ordinary-I/O
prelude/output conversion has its own fixed expectations and costs owned by
the separate I/O work.
