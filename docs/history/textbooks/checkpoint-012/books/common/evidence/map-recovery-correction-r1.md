# Map recovery: correction after focused round 1

Root's focused command on committed candidate
`7d6c8dc30677493f04422483b4836b296292c666` completed with exit 1 in 37.46 seconds.
The actual log remains `intake/maps-focused-r1.log`; the original source handoff
is unchanged. Interface, Invariant, Basic, Examples.OrderedMap and
Examples.SharedTreeMap built successfully. TextbookMaps had not yet elaborated
because two new imported modules failed.

Corrections are limited to the two failed modules:

- `Observations.lean`: specify both input representations, both target semantic
  types and the complete types of the observation functions in the existing
  `Squares.vertical` application. The default-write semantic square's key/value
  type arguments are explicit. This addresses underconstrained elaboration of
  the one-way observation change; its public type and mathematical statement
  are unchanged.
- `AssociationList.lean`: replace deprecated `if_pos`/`if_neg` rewrites by the
  pinned Lean names `ite_eq_left`/`ite_eq_right`. The conditional cases, AList
  laws and proof policy are unchanged.

No assumptions, expected examples or countermodels were weakened. No warning
was suppressed. Root remains sole compiler owner. Source writes are paused
again for the next focused invocation; this correction note claims no new
compiler success or final acceptance.
