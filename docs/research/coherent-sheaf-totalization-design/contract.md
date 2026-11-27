# Contract and foundations assessment

Independent initial assessment for #708, 27 November 2026. Project revision
`f96e378241012feae903d6e06211c26bfe0f94b3`; Mathlib
`56a005855ea17e0b0958f73ec801ae140b0a1679`; Lean `v4.35.0`.

Retain the proposed mathematical capability: classify arbitrary arrows between
coherent local sheaf presentations over changing contexts, with recovery over
the same base. The existing operations determine the remaining coherence; new
sheaf hypotheses are unnecessary. A bounded implementation is justified by the
uniform all-arrow classification and access to cartesian factorization, without
requiring a previously blocked application. However, the proposed direct reuse
of Mathlib strong transformations has an actual universe obstruction. Resolve
that encoding choice before prescribing the exact adapter. The native fibres
and the value universe must remain unchanged.

## Existing mathematics and exact target

In [CoherentSheafOver](/SquareKit/Internal/CoherentSheafOver.lean), write
`CΓ = LocalCode G J Γ`, `SΓ = Sheaf (J.over Γ) (Type w)`, and
`eΓ = sheafOverClassification G J Γ`. Write `EΓ` and `RΓ` for its functor
and inverse, `ηΓ : Id ≅ EΓ ⋙ RΓ` and `εΓ : RΓ ⋙ EΓ ≅ Id` for its unit
and counit. Composition here follows Lean's left-to-right `⋙` convention.
For `σ : Δ ⟶ Γ`, put `Pσ = J.overMapPullback (Type w) σ`.
The existing operation is exactly `Lσ = EΓ ⋙ Pσ ⋙ RΔ`.

`Local` is an independently defined property: every rooted view is a sheaf.
Its containing coherent-diagram category requires invertibility on restriction
squares, while retaining all natural transformations. `decoded_isSheaf` derives
assembled sheafness. `classification` and the dense-site comparison derive `eΓ`;
no field assumes the desired decoder or total equivalence.

The target total has objects `(Γ,Q)` and arrows
`(Δ,Q) ⟶ (Γ,T)` given by `σ : Δ ⟶ Γ` and `Q ⟶ Pσ(T)`.
The code total should have objects `(Γ,A)` and arrows given by `σ` and
`A ⟶ Lσ(B)`. A total decoder must send the latter arrow to

```text
(σ, EΔ.map f ≫ (decodeReindex σ).hom.app B).
```

This classifies every morphism, including noninvertible ones. For each fixed
`σ`, it induces the hom equivalence

```text
(A ⟶ Lσ(B)) ≃ (EΔ(A) ⟶ Pσ(EΓ(B))).
```

Its inverse is obtained by composing with `decodeReindex σ` inverse and using
fullness of `EΔ`; faithfulness supplies both inverse laws. This derivation is
paper-level here. Compatibility with identity and composition is essential to
the claimed total equivalence, rather than an optional further property.

The deliverable should expose an equivalence of the two totals, both functors'
projection equations, and vertical unit/counit components. It should recover
the original categories as categorical fibres and preserve cartesian arrows in
both directions. The fully packaged equivalence's unit needs its own base
identity theorem: `Equivalence.mk` may adjust the supplied unit. The existing
[family bridge](/SquareKit/Internal/CoherentFamilyFibration.lean) explicitly
handles this distinction. Preservation does not assert equality of selected
cartesian lifts or chosen pullbacks.

## Remaining coherence is derivable

The following are already implemented in `CoherentSheafOver`:

- `reindexId : L(id) ≅ Id` and `reindexComp : Lσ ⋙ Lτ ≅ L(τ ≫ σ)`.
- `decodeReindex : Lσ ⋙ EΔ ≅ EΓ ⋙ Pσ`.
- `decodeReindex_id` and `decodeReindex_comp`, with naturality in arbitrary
  code maps supplied by the natural isomorphism definitions.

Mathlib's sheaf system is packaged in
[`Sites/PseudofunctorSheafOver.lean`](https://github.com/leanprover-community/mathlib4/blob/56a005855ea17e0b0958f73ec801ae140b0a1679/Mathlib/CategoryTheory/Sites/PseudofunctorSheafOver.lean),
which imports `Sites/Over.lean`. Its `mapComp` uses the inverse of
`overMapPullbackComp`. The local system must likewise use the inverse of
`reindexComp`, with the contravariant argument order. These source files were
inspected locally; the pinned GitHub page was also accessed on 27 November 2026.

The outstanding proof obligations are:

1. The two unit equations and associativity equation for `L`, with the
   equality transports for base identity/composition. These are precisely the
   three inputs to Mathlib's `LocallyDiscrete.mkPseudofunctor`. Apply the
   faithful decoder at the final context componentwise, rewrite with the two
   existing decoder compatibility theorems, then use the corresponding sheaf
   coherence and naturality. This derives the constraints already selected by
   `reindexId` and `reindexComp`; arbitrary replacements would need checking.
2. The decoder as a strong transformation, wherever universes permit that
   packaging. Its identity/composition equations are the existing theorems;
   its compatibility with locally discrete 2-cells follows by equality
   elimination.
3. The inverse transformation and invertible recovery modifications. A
   candidate inverse comparison is
   `Pσ ⋙ RΔ ≅ RΓ ⋙ Lσ`, obtained by whiskering `εΓ.symm` on the right
   with `Pσ ⋙ RΔ`. Its coherence and the modification equations for `ηΓ`
   and `εΓ` follow from naturality and the equivalence triangle identities.
   These are derived obligations, not additional caller assumptions.
4. Lift the comparisons to total functors and natural isomorphisms. Mathlib
   supplies total map identity/composition comparisons;
   [CoGrothendieckMap](/SquareKit/CoGrothendieckMap.lean) supplies action on
   modifications and preservation of arbitrary cartesian arrows for strong
   transformations in a common Cat universe.

This is a paper derivation, not a checked implementation. It identifies a
finite set of equations and their premises. The existing #705 implementation
cannot be substituted directly: its fibres are diagrams over `Γ.Elements`,
its reindexing is strict precomposition, and its inverse has a strict
naturality comparison. None of those simplifications identifies the present
local sheaf fibres.

## Hypotheses and universes

General substitution needs `B : Type u` with `Category.{v} B`,
`D : Type a` with `Category.{b} D`, `G : B ⥤ D`, a topology `J` on `D`,
fullness and faithfulness of `G`, cover density of `CostructuredArrow.toOver G Γ`
for **every** context, and the stated limits in `Type w` of each structured
arrow shape, again for every context. Totalization ranges over all of `D`;
pointwise hypotheses for one chosen context do not suffice. The existing
Substitution section already has the uniform assumptions.

No base pullbacks, subcanonicity, or sheafification hypothesis is needed:
`overMapPullback` is precomposition along `Over.map σ`, whose continuity is
proved. The represented-display comparison separately needs `J.Subcanonical`
and currently uses `Type b`, matching the hom universe of `D`. Claiming its
current equivalence for an arbitrary independent `Type w` would strengthen the
actual implementation. Display totalization also needs a compatible comparison
with base substitution; fibrewise `codeDisplayClassification` alone does not
provide that further pseudonaturality theorem.

A checked signature probe gives these simplified universe maxima:

| Fibre | Object universe | Hom universe |
|---|---|---|
| `LocalCode G J Γ` | `max u v b (w+1)` | `max u v b w` |
| `Sheaf (J.over Γ) (Type w)` | `max a b (w+1)` | `max a b w` |

The ordinary functor `eΓ.functor` accepts these different universes. The direct
expression `eΓ.functor.toCatHom` **fails** with all five universe parameters
independent, because `Functor.toCatHom` requires both categories in one
`Cat.{hom,object}`. Mathlib's `StrongTrans` and `CoGrothendieck.map`, and the
local modification helper, have the same common-Cat condition. Equalizing
site universes or replacing the value type by a larger `Type` would change the
contract and is not an acceptable silent repair.

Two bounded choices preserve the mathematics. Explicitly lift objects and homs
to a common Cat universe, transport the indexed systems, then expose recovery
to the native fibres; or retain the two native pseudofunctors and define the
ordinary total functors heterogeneously from the displayed arrow formula. The
latter needs direct functor/recovery proofs or a small heterogeneous extension
of the helper. It does not require a new category of transformations. The
former should hide lifts from clients while proving the connection back to the
original operations. Mathlib has `ULiftHomULiftCategory.equiv`; a naive chain
of those equivalences also failed typeclass synthesis in this assessment, so a
passing lift adapter is not established here.

## Tests that distinguish the contract

The [existing sheaf examples](/Examples/CoherentSheafOver.lean) contain
`pairProjection`, `diagonal`, `pairDisplay`, and a noninvertible `collapse`.
For `p : Bool×Bool ⟶ Bool` and `d : Bool ⟶ Bool×Bool`, test both actual
base composites: `d ≫ p = id`, while `p ≫ d` sends `(true,false)` to
`(true,true)`. Construct total arrows using the cartesian lifts and the vertical
map corresponding to `collapse`. Check their composition, decoded fibre map,
and recovery naturality as total arrows, including the base projection.
An identity-base assertion alone would miss the reversed order.

The noninvertibility check should be justified for these particular base
changes. Reindexing along an arbitrary arrow need not reflect isomorphisms.
Here `d* ∘ p* ≅ Id` makes `p*` reflect them; the round trip can therefore
retain the collapse obstruction. This is a paper justification for the proposed
test, not an already checked total-arrow theorem.

Add an abstract compositional case: for arbitrary substitutions `σ, τ, υ`
and arbitrary compatible fibre maps, compare the two triple pastings through
the public total functor, and use cartesian factorization to classify a lift of
a composite. This establishes access to shared universal-property proofs and
checks the pentagon's consequences beyond a Boolean closed computation. A
fibre map reconstructed from the sheaf side should round-trip under the hom
equivalence above. These checks make the uniform author capability concrete;
they do not measure productivity.

Retain `support_map_not_iso`: at the bottom topology every represented
restriction of its map is invertible while the original map is not. That
refutes replacing cover density with subcanonicity. Retain the coherent-family
counterexample to recovery without invertible restriction comparisons. Add a
universe-polymorphic signature check before closed specializations, since the
Boolean example cannot reveal the common-Cat obstruction. A small example
with value universe different from the site hom universe must remain accepted.

## Alternatives and recommendation boundary

The strongest retain case is that a single coherent classification of changing
base arrows supplies composition, recovery naturality and cartesian
factorization for independently supplied local presentations. It connects the
local author interface to Mathlib's fibre API and proves uniform reuse of the
sheaf mathematics. A closed client or a pre-existing duplicated proof is not a
prerequisite for that mathematical capability.

The smallest useful alternative is to use the existing sheaf total directly,
with `eΓ` only at fibre entry and exit. This avoids code pseudofunctor packaging
and preserves all sheaf total arrows, but does not give a code total whose
morphisms use the native `reindex`, nor a reusable total recovery theorem for
those native arrows. A category induced on pairs `(Γ,A)` by the decoded sheaf
objects is another small construction; connecting its homs to native
`A ⟶ Lσ B` still requires the hom equivalence and composition compatibility
above. Merely renaming that category would not establish native recovery.

Recommend the native total-arrow contract and a bounded universe-resolution
checkpoint. Prefer deriving its coherence once from the existing equivalences
and sheaf pseudofunctor; do not require a universal fibration framework or
completion of #723. #723 can own later extraction of recurring coherence
proofs. The choice between explicit lifting and a heterogeneous total helper
should be made with a passing universe-polymorphic signature and an abstract
compositional example. No evidence here chooses a generally cheaper encoding.

This result would not establish stackification, arbitrary-category-valued local
sheaf recovery, preservation of dependent higher cells, strict equality of
chosen pullbacks, or recovery without locality/density. All these extend the
stated contract. No source or tracker edits were made by this assessment.

## Reproducible checked probe and validation limits

The source inspection above covers the named project modules, the full
Substitution section, the local total-map helper, and the cited Mathlib
pseudofunctor/Grothendieck/fibre definitions. The coherence construction and
proposed clients are paper-level. No adapter was implemented, no integrated
build or axiom audit was run, and existing `.olean` files were reused for these
isolated elaboration probes. The expected failure is evidence about the direct
encoding, not a failed mathematical theorem.

Save the following as `/tmp/sheaf-universes.lean` in the pinned checkout:

```lean
import SquareKit.Internal.CoherentSheafOver
import Mathlib.CategoryTheory.Sites.PseudofunctorSheafOver
open CategoryTheory SquareKit.CoherentSheafOver
universe u v a b w
variable {B : Type u} [Category.{v} B] {D : Type a} [Category.{b} D]
variable (G : B ⥤ D) (J : GrothendieckTopology D) (Γ : D)
variable [G.Full] [G.Faithful]
variable [∀ Γ : D, (CostructuredArrow.toOver G Γ).IsCoverDense (J.over Γ)]
variable [∀ (Γ : D) (X : (Over Γ)ᵒᵖ),
  Limits.HasLimitsOfShape
    (StructuredArrow X (CostructuredArrow.toOver G Γ).op) (Type w)]
set_option pp.universes true in
#check Cat.of (LocalCode.{u,v,w} G J Γ)
set_option pp.universes true in
#check Cat.of (Sheaf (J.over Γ) (Type w))
set_option pp.universes true in
#check (sheafOverClassification G J Γ).functor
set_option pp.universes true in
#check (sheafOverClassification G J Γ).functor.toCatHom
```

Run without Lake writes, using the checkout's existing artifacts:

```sh
direnv exec . python3 - <<'PY'
from pathlib import Path
import os, subprocess
paths = [Path('.lake/build/lib/lean')]
paths += sorted(Path('.lake/packages').glob('*/.lake/build/lib/lean'))
env = dict(os.environ, LEAN_PATH=':'.join(str(p.resolve()) for p in paths))
result = subprocess.run(['lean', '/tmp/sheaf-universes.lean'], env=env)
raise SystemExit(result.returncode)
PY
```

The actual first signature printed was
`Cat.{max (max (max b u) v) w, max (max (max u v) (w + 1)) b}`;
the sheaf signature was
`Cat.{max (max a b) w, max (max (max (w + 1) a b) w) b}`.
The last check exited with code 1 and `Application type mismatch`: the
argument had `Functor` with source hom/object maxima
`max (max (max b u) v) w` / `max (max (max b u) v) (w + 1)`
and target maxima `max (max a b) w` / `max (max a b) (w + 1)`,
while `Functor.toCatHom` expected
`CategoryTheory.Functor.{?u.72, ?u.72, ?u.71, ?u.71} ?m.50 ?m.51`.

A separate exploratory probe imported `Category.ULift` and tried
`(liftCode.symm.trans eΓ).trans liftSheaf`, with
`liftCode = ULiftHomULiftCategory.equiv.{H,U,max u v b w,max u v b (w+1)} CΓ`,
`liftSheaf = ULiftHomULiftCategory.equiv.{H,U,max a b w,max a b (w+1)} SΓ`,
`H = max u v a b w`, and `U = max u v a b (w+1)`.
It failed to synthesize `Category.{H,U} (ULiftHom (ULift CΓ))` during the
chain's elaboration. This leaves explicit instance management or another
encoding to a later bounded implementation; it does not disprove lifting.
