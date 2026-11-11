# Set/class judgments and their interpretation contract

Research and implementation specification for
[#443](https://github.com/VladimirMarko/conaled/issues/443), 2026-11-11.
All proposed syntax, source rules, adapters and acceptance theorems below remain
unimplemented. This report selects an experiment to discuss, not a new
foundation, dependency, toolchain or kernel axiom.

Compare native Lean inference with an opt-in source fragment that distinguishes
sets from classes. For the first checked slice, use set-sized images of class
functions and an ordinal successor-family consumer. This exercises membership,
quantification, replacement and a proper-class rejection using existing Mathlib.
Surreal arithmetic and cuts supply the larger author corpus. Their realization
as internally represented sets needs a separate comparison theorem; the
presence of a host `Surreal` type does not provide it.

## Evidence and existing boundaries

Inspection baseline: conaled `a3d7b37e6bfff729bdc61951f0cdc1e7889760d6`, Lean
`v4.35.0`, Mathlib `56a005855ea17e0b0958f73ec801ae140b0a1679`. Mathlib source
links below use that exact revision. Source inspection establishes the named
definitions and proof bodies, not a fresh compilation or audit result.

The [published #442 audit](combinatorial-games-surreal-audit.md) owns upstream
coverage and compatibility. It records `vihdzp/combinatorial-games` at
`e8c95387dc4270cb965ef3c06c305a986691cec2` and the Lean 4.35 candidate
`d949bd1fd3355d23175b8ed0834e0bb166e5fd3b`. It supplies ordered-field and
small-cut evidence, infinite/infinitesimal examples, and the missing
cross-universe comparisons. No external library is adopted here, and native
integration need not wait for this frontend.

The mathematical references are Schleicher–Stoll,
[*An Introduction to Conway's Games and Numbers*, math/0410026v2][surreal-paper],
§§2–4, and Gitman–Hamkins,
[*Open determinacy for class games*, 1509.01099v2][recursion-paper], especially
Definition 6 and §4. The former distinguishes class collections from set-sized
options. The latter distinguishes elementary transfinite recursion with
class-valued stages from ordinary set-valued recursion. These are primary
mathematical sources, not imported Lean proofs. No full named class theory is
inferred from the representations below.

The current [language direction](../language-direction.md) requires meaningful
reasoning and interpretation, with bookkeeping absorbed where possible.
Several existing contracts constrain this proposal:

| Existing source | Reusable result and limit |
|---|---|
| [GuardedTheory](../../SquareKit/GuardedTheory.lean) | `Derivation.sound` interprets finite guarded equational/Horn derivations in a supplied `Model`; `Derivation.substitute` and `Hom.eval` expose substitution and preservation. `Atom` has equality and predicates, not first-order binders. Adding a class predicate to this signature would not supply universal quantification or comprehension. |
| [Internal/Logic](../../SquareKit/Internal/Logic.lean) | `FormulaCore` and `Derives` have sorted atoms, equality, conjunction and existential quantification, with substitution. Their current regular fragment lacks the implication and universal quantification needed here. Preserve its existing interpretations instead of silently enlarging every model's obligations. |
| [InterpretationRoutes](../../SquareKit/Internal/InterpretationRoutes.lean) | `derivation`, `preserve`, `substitution`, `existential_route` and `reindex_comp` concern component selection among existing Set interpretations. They do not construct set/class universes or reflect arbitrary formulas. |
| [NestedSetting](../../SquareKit/Internal/NestedSetting.lean) and its [record](internal-setting-construction.md) | `argumentEquiv`, `first_generic_recovery`, `second_generic_recovery`, `comparison_comp` concern a context-varying finite geometric presentation. They are evidence for retaining substitution and selected data, not a universal internal class theory. |
| [GuardedJudgmentBoundaries](../../Examples/GuardedJudgmentBoundaries.lean) | `no_source_equality` rejects reflecting equality observed in one interpretation into source equality. The set/class checker must retain this distinction. |
| Mathlib [ModelTheory/Syntax][syntax] and [Semantics][semantics] | `FirstOrder.Language.BoundedFormula` includes `falsum`, `equal`, `rel`, `imp`, `all`; `BoundedFormula.Realize` and substitution results provide an existing first-order semantic target. Here “bounded” counts bound variables; it does not mean all quantifiers are bounded by a set. |

Reuse the first-order syntax/semantics where its binder contract fits; decide
between a translation to that syntax and a small sorted extension after a
checked substitution example. GuardedTheory remains useful for finite operation
obligations. Neither existing soundness theorem can be cited as the unproved
soundness theorem of the proposed richer source. This is a mismatch for
[#235](https://github.com/VladimirMarko/conaled/issues/235), not a reason to
weaken the requested corpus. No existing ordinary Lean or regular-language
client needs migration for the proposed experiment.

## What pinned Mathlib constructs

| Declaration | Inspected contract |
|---|---|
| [PSet][pset] | `PSet.{u} : Type (u+1)` has a `Type u` index and a recursively indexed family. `PSet.Equiv` is extensional equivalence. `PSet.Lift : PSet.{u} → PSet.{max u v}` uses `ULift` recursively; `embed` lives at `max (u+1) v`, and `lift_mem_embed` places each lifted old pre-set in it. This is not yet a quotient/class transport theorem. |
| [ZFSet][zfset] | `ZFSet.{u}` is the quotient of `PSet.{u}`, also in `Type (u+1)`. `toSet`/the `SetLike` instance expose membership; `ext` proves extensionality. `small_coe (a)` witnesses `Small.{u} {x // x ∈ a}`. `sep`, `mem_sep`, `image`, `mem_image`, `range`, `mem_range`, `pair`, `pair_inj`, `mem_sUnion`, and `inductionOn` support explicit operations. |
| Replacement representation | `ZFSet.image f a` requires `[ZFSet.Definable₁ f]`. This means a lift of `f` to pre-sets, **not** first-order syntactic definability. `Classical.allZFSetDefinable` supplies this classically for every host function. Alternatively `ZFSet.range f` requires a `Small.{u}` index type; set elements supply that via `small_coe`. A source derivation cannot use host definability as a substitute for its own rule premises. |
| [ZFClass][zfclass] | `ZFClass := Set ZFSet`. `ZFClass.CMem A B` means `∃ a : ZFSet, ↑a = A ∧ a ∈ B`; only represented sets can be members. `cmem_univ` characterizes set representation; `univ_notCMem_univ` proves no universal set. This is host representation of classes, not a theorem that classes are internal sets. |
| Size comparison | `ZFSet.coeEquiv : ZFSet.{u} ≃ {A : Set ZFSet.{u} // Small.{u} A}` connects represented sets and host-small subclasses in this particular construction. It does not identify these notions for every abstract model. |
| [Ordinals][ordinal] | `ZFSet.IsOrdinal`, `isOrdinal_succ`, `Ordinal.toZFSet`, `toZFSet_mem_toZFSet_iff`, `toZFSet_add_one`, `rank_toZFSet`, `ZFSet.IsOrdinal.toZFSet_rank_eq`, and `Ordinal.toZFSetIso` connect internal von Neumann ordinals to `Ordinal.{u}`. [Class.lean][zfclass]'s `ZFSet.isOrdinal_notCMem_univ` proves that all internal ordinals form a proper class. |

`ZFClass` is a predicate type and therefore admits more host predicates than
an elementary source grammar can name. Quantification in Lean over all such
predicates is not automatically an admitted source class quantifier. Likewise,
`ZFClass.fval` is defined via `iota` with a default when the description is not
unique. It does not establish that an arbitrary graph is a total function.
The proposed source application rule must require existence and uniqueness.
These distinctions follow directly from [Class.lean][zfclass].

## Two contracts to compare

**Native contract.** An author writes ordinary theorems about
`Surreal.{u}`, or about `ZFSet.{u}`/`ZFClass.{u}` when internal membership is
needed. Lean infers compatible universe levels, implicit parameters and
available `Small` instances. `∀ x : Surreal.{u}, …` ranges over the whole
native carrier at that level. An arbitrary `s : Set Surreal.{u}` is a host
predicate, not necessarily `u`-small. Cuts require both smallness witnesses
and left/right separation. A new universe map must be constructed with laws;
universe inference cannot manufacture it. Native set/class reasoning is already
possible directly through Mathlib, without a new parser.

**Encoded source contract.** An opt-in block selects a mathematical setting
and a declared rule profile. Authors use set variables, class expressions and
membership judgments. Proofs elaborate to derivations whose interpretation is
proved sound in every supplied realization of that profile. An internal class
can be proper while its semantic carrier is a Lean type. The language does not
quantify over all Lean universes or erase mathematical size conditions.

For both routes “all surreals” must name the setting: all native `Surreal.{u}`,
or all set-coded numbers satisfying the selected internal predicate `No`.
Neither denotes a finite or birthday-restricted fragment unless the author
asks for one. A theorem that identifies these two collections is additional
comparison evidence. The native route already handles arithmetic ergonomically;
the proposed source route must earn its extra machinery through reusable
set/class derivations and comparisons, not prettier braces.

## Proposed bounded judgments and rule profiles

The following is a mathematical specification, not implemented syntax. Use
`SetObj` and `ClassObj` as source categories, distinct from Lean `Set` and
`Type`. A context contains set variables, class parameters and elementary
assumptions. Finite signatures may add operations and relations with explicit
domain/closure premises. There is no universal structure record containing
all arithmetic, cut and recursion laws.

| Judgment or abbreviation | Proposed meaning and admission rule |
|---|---|
| `Γ ⊢ a : SetObj`; `Γ ⊢ A : ClassObj` | Distinct formation judgments. A set has an extent `ext(a)` as a class. There is no unconditional reverse coercion. |
| `a ∈ A`; `a ∈ b` | Membership of a set in a class; the second abbreviates `a ∈ ext(b)`. Class equality is extensional over set elements. A class on the left of membership requires a set-representation witness first; no class can be an element merely because it has a host type. |
| `SetSized(A)` | `∃ a : SetObj, ∀ x : SetObj, x ∈ A ↔ x ∈ a`. `Proper(A)` abbreviates its negation. This is internal representability, not a hard-coded host universe inequality. A retained witness permits a checked conversion to a set. |
| `Γ ⊢ φ : Formula`; `Γ ; Δ ⊢ φ` | Finite first-order formulas with set equality/membership, declared relation atoms, `⊥, ∧, ∨, →, ∀x:SetObj, ∃x:SetObj`, and derived negation/iff. Derivations use explicit logical rules, equality substitution and admitted profile rules. No constructor accepts semantic truth in one model as a source proof. |
| Restricted quantifiers | `∀x∈A, φ` means `∀x:SetObj, x∈A → φ`; similarly for existential conjunction. A class parameter may be proper; its elements are still sets. All-number quantification requires no set containing all numbers. |
| Elementary class comprehension | `{x : SetObj | φ}` is a class, with `y∈{x|φ} ↔ φ[y/x]`. The finite formula may quantify over sets and use class parameters. It contains no object-language quantifiers over classes and no self-referential class binder. Substitution must avoid capture. |
| Class parameters and functions | Theorems may be schematic in class parameters. There is no object-language `∀A:ClassObj` or `∃A:ClassObj` in this first fragment. A class graph `F` uses encoded pairs; `FunctionOn(F,A,B)` asserts `∀x∈A, ∃!y∈B, pair(x,y)∈F`. `F(x)` is guarded notation for this unique value, admitted only with `x∈A`. |

A class may have a proper-class domain or graph while every function value is
a set. Use relational graph formulas in the core; elaborate guarded function
notation through unique-value evidence. This avoids making `fval`'s default
appear as a proved application. Function composition requires compatible
codomains and domain evidence. Global choice is not a rule of this fragment.

Separate the following mathematical capabilities, using ordinary Lean
parameters/proofs in semantic realizations, never new kernel `axiom` commands:

- **Extents and elementary classes:** set/class extensionality, membership of
  extents, elementary comprehension, empty set and pairing as needed. Logical
  inference can be intuitionistic; a classical source profile may separately
  expose excluded middle. The proposed slice needs no excluded-middle rule,
  though its Mathlib realization uses the permitted host classical principles.
- **Separation:** from a set `a` and an elementary `φ`, obtain a set with
  elements exactly `x∈a ∧ φ(x)`. This makes subclasses of a represented set
  set-sized, with a witness, rather than merely labeling them small.
- **Functional replacement:** for an elementary graph `F` and a set `a`,
  `∀x∈a, ∃!y:SetObj, F(x,y)` entails
  `∃b:SetObj, ∀y, y∈b ↔ ∃x∈a, F(x,y)`.
  Named class-graph parameters are allowed in `F`. No image of an arbitrary
  proper-class domain is declared set-sized. Uniqueness avoids selecting
  among multiple possible images; a nonfunctional collection principle would
  need its own assumptions.
- **Domain laws:** an additive group law only requests the group operations,
  closure and laws on its class. Order, field, and separated-cut existence
  are separate extensions. Interpolation does not require a choice of the
  simplest number. Canonical Conway cuts additionally require a supplied
  constructor and its simplicity/representation theorem.

This finite grammar with rule schemas is not a claim to have formalized GB,
GBC, NBG, KM or complete ZFC. In particular it omits class quantifiers, global
choice and a source theorem asserting arbitrary class recursion. The stronger
host predicate representation must not silently enlarge its source rules.

### Recursion requirements

The first slice uses no mathematical recursion beyond the host recursion
interpreting finite syntax/derivations. Its ordinal successor operation uses
`insert a a`, not transfinite recursion.

For a later set-valued recursion on a set domain, require a well-founded
relation, a total extensional step operation, and replacement/collection
sufficient to assemble the previous values as a set graph. For a class domain,
a proposed restricted rule must additionally state that predecessor closures
are sets, that each stage is set-valued, and that the resulting class graph is
admissible in the selected profile. Those are mathematical hypotheses to prove,
not consequences of a host `WellFounded` instance. A recurrence with
class-valued stages or unrestricted class dependencies is outside that rule.
Gitman–Hamkins Definition 6 discusses the stronger ETR principle; even a
set-length recurrence can require it when its stages are classes.
[Primary source, §4][recursion-paper].

Conway recursion in the native upstream library is already implemented over
its well-founded game representation. To reuse it for internal `No`, either
prove a comparison that transports that recursion and its size conditions, or
formalize a suitable internal set-valued construction. Neither path is
provided by merely adding a `recursion` keyword. Full elementary class
recursion remains an explicit foundational alternative for #289/#36 to assess,
not an assumed prerequisite of the first slice.

## Derivability, realization and external comparison

Keep three deliverables separate:

1. **Source derivability.** `Derives T Γ φ` records a finite derivation from
   the selected rule profile `T` and assumptions `Γ`. An elaborator returns
   this evidence or outstanding obligations. It does not decide theoremhood.
2. **Sound interpretation.** Prove, for all realizations `M` satisfying `T`,
   all well-sorted valuations `ρ`, and all derivations `d`,
   `Satisfies M ρ Γ → Realize M ρ φ`. Also prove renaming/substitution laws
   for terms, class expressions, formulas and derivations. For the initial
   profile, construct `M_ZF` using `ZFSet.{u}`, `ZFClass.{u}`, extents,
   membership and the declarations above. Prove every used profile rule,
   rather than trusting a model record with unfilled fields.
3. **External comparison.** A separate theorem identifies the interpretation
   of each client with an independent native meaning. Ordinals have a
   candidate comparison via `Ordinal.toZFSetIso`; surreals still need set
   codes and a theorem relating their equality/order/arithmetic/cuts to
   native `Surreal.{u}`. Agreement in one model is not source reflection.

Even a checked conditional soundness theorem does not construct a model.
Constructing the proposed bounded `M_ZF` does not constitute a claimed
consistency proof for an entire named class theory. No such model construction
or consistency result is delivered by this report. Nor does a failure to find
an encoding establish that Lean cannot host the intended mathematics.

In `M_ZF`, elementary class comprehension interprets as a predicate; separation
uses `ZFSet.sep`. For functional replacement, use unique existence to define
a function on the element subtype of `a`, then use `small_coe` and
`ZFSet.range`. Its `mem_range` gives the required biconditional. A later
adapter can express the same construction using `image` and a proved
`Definable₁` instance. This is a concrete proof plan with noncomputable host
choice disclosed. It does not add source global choice or syntactic
definability of arbitrary Lean functions.

## Author corpus and exact obligations

All blocks below are proposed author-facing notation. Names of capabilities
are specification labels, not current Lean declarations. Internal `No` must
come from an explicitly supplied surreal realization, not from naming an
arbitrary class with an ordered-field structure. Until the encoding/comparison
is proved, the `No` examples are conditional source contracts.

**All-number arithmetic.**

```text
in setting M with No.additiveGroup
  theorem cancel : forall x in No, x + (-x) = 0
```

The quantified values range over every number in the chosen setting, with no
birthday bound. Only additive-group closure and inverse laws are required.
The stronger class-level distributivity example
`∀x,y,z∈No, x*(y+z)=x*y+x*z` requests ring laws, not inverses or cut closure.
A source derivation should retain those requirements so it can be reused for
another class group/ring. Native comparisons are respectively `add_neg_cancel`
and `mul_add` at `Surreal.{u}` once a realization exists. This does not require
constructing a set of all triples of numbers; the binders are nested set
quantifiers with membership guards.

**Separated set-sized cuts.**

```text
L R : SetObj
left_numbers  : forall l in L, l in No
right_numbers : forall r in R, r in No
separated     : forall l in L, forall r in R, l < r
obtain c in No with (forall l in L, l < c) and (forall r in R, c < r)
```

This requests the separated-set-cut existence capability. A canonical
`c := {L | R}` additionally requests the selected Conway constructor contract.
The native target is `Surreal.ofSets` with `[Small.{u} L'] [Small.{u} R']`,
separation and its two strict comparison laws from #442. The interpretation
must prove the decoded images `L'`, `R'` are small and preserve membership
and strict order. Merely knowing `L` and `R` are host predicates is insufficient.

**A family with substantive size evidence.**

```text
I : SetObj
f : ClassFunction I No
L := { f(i) | i in I }
```

Functional replacement produces a represented set and its exact membership
law; ordinary authors should not supply host lifts or shrink equivalences.
For `J : ClassObj`, the same expression produces a class. To use it as cut
options, supply `SetSized(J)`, or prove the image is contained in a represented
set `B` and use separation. The latter can succeed when `J` itself is proper,
for example a constant map with known singleton image. Thus `SetSized(J)` is
a sufficient input rule, not a necessary condition on every image.
For a family over ordinals below a given `α`, the bound identifies a represented
index set via `Ordinal.toZFSet`; over **all** ordinals it supplies no such bound.
A theorem giving a birthday bound for a family may discharge size, but that
bound is additional mathematics and may not be inferred from a field law.

**Second client: ordinal successors.**

```text
A : SetObj
ordinal_elements : forall a in A, a in Ord
B := { a union {a} | a in A }
prove forall b in B, b in Ord
prove forall b, b in B iff exists a in A, b = a union {a}
```

Use the same replacement and membership derivation as the surreal-family
example, with ordinal closure furnished by `ZFSet.isOrdinal_succ`. Compare
`a∪{a}` with `insert a a`; native `Ordinal.toZFSet_add_one` identifies it
with successor. No class-field or external game dependency is needed.

### Negative and boundary controls

| Request | Required outcome, not a generic type mismatch |
|---|---|
| `let S : SetObj := No` | Emit `requires SetSized(No): provide a representing set and membership equivalence`. With the separated-cut extension, derive `Proper(No)`: if a set contained exactly all numbers, its cut against the empty right set would yield a number strictly above itself. This is a proposed derivation from explicit cut existence and irreflexive order, not an already constructed surreal model. |
| `cut No empty` | First report missing set-representation evidence for the left options, even though right separation is vacuous. In a profile proving `Proper(No)`, close the rejection by contradiction. Do not resize the setting automatically to make the formerly proper class small. |
| `let S : SetObj := Ord` | In the constructed Mathlib interpretation, reject with `ZFSet.isOrdinal_notCMem_univ` via soundness. This is the first slice's concrete proper-class control. It is not a finite-ordinal test. |
| `cut {x in No | 0 < x} {0}` | Size evidence alone would not help: expose the obligation `∀l∈L, l < 0`, which conflicts with the left predicate if it contains a positive number. Both size and separation are required. |
| Class comprehension containing `exists C : ClassObj, ...` | Reject as outside elementary comprehension. It is an unsupported source form, not a claim that all interpretations refute the formula. |
| `F(x)` without `FunctionOn` or domain evidence | Expose totality/uniqueness or membership obligation. Do not use `ZFClass.fval_ex`, which only says the default-valued description is set-representable. |
| `transport theorem M to N` without a route | Report the missing translation/interpretation contract, supported formula fragment and size witness map. Equal notation or matching cardinalities does not supply these laws. |

Separate rejection of unsupported syntax, unresolved mathematical obligations,
and proved impossibility under a profile. If inconsistent assumptions are
supplied, source logic may derive anything; diagnostics cannot promise
consistency checking. The positive singleton-image example prevents the
implementation from rejecting every class-indexed family indiscriminately.

## Inference and size-aware transport

Infer host level metavariables, implicit universe maxima, existing `Small`
instances, extents of known sets, finite sets, and represented-domain images
through registered proved rules. Hide `ULift`, `Shrink` and quotient wrappers
inside a chosen interpretation when the expected type and registered map
uniquely determine them. Report an ambiguity when distinct routes are available
without a comparison. Never choose a stronger theory, resize a setting, invent
a bound, or assume replacement merely to make a term elaborate.

A proposed route from `M` to `N` consists of source translation `τ`, maps on
interpreted sets/classes and a comparison on environments. Its requirements
depend on the judgments transported:

- For atomic membership and equality comparisons, require
  `x∈_M A ↔ j(x)∈_N J(A)` and preservation/reflection of the relevant equality.
  Extents must satisfy `J(ext_M(a)) = ext_N(j(a))`. Forward-only maps have a
  weaker contract and cannot advertise these biconditionals.
- Send every retained set-representation witness to a representation of the
  translated class, with its membership equivalence. For source `A={x|φ}`,
  establish the comprehension comparison in the advertised domain; a direct
  image generally ranges only over `j`'s image, whereas target comprehension
  may contain new elements. Full set quantifiers need equivalences, suitable
  elementary embeddings or a relativized translation with proved adequacy.
- Require `j(x+y)=j(x)+j(y)`, zero/negation and any used multiplication/inverse
  laws, plus strict-order comparison, for arithmetic transport. For cut
  existence the mapped witness needs only the relevant membership/order laws;
  preservation of the **canonical** cut additionally needs a simplicity law.
- Prove substitution compatibility and identity/composition coherence for the
  retained witnesses, not just equality of final truth values. Universal or
  negative statements do not transport along arbitrary homomorphisms.

A separating paper example is the ordered-additive-monoid embedding
`ℕ → ℤ`: it preserves addition, zero and order on old elements, but does not
transport `∀x, 0 ≤ x` to all target elements. Its image-relative translation
does preserve that statement. A transport test must distinguish these two
quantifier contracts.

Properness deserves a separate check. A lower-universe class may become a set
in a larger host construction; `PSet.embed` already demonstrates the relevant
size phenomenon for pre-sets. Thus membership/order preservation on old
elements does not imply preservation of `Proper(A)` or all-number
quantification. Either restrict the contract, prove reflection of represented
sethood, or relativize the target's “set” and quantifiers to the old setting.
The missing native surreal lifts in #442 must not be filled by syntax inference.

## Direct Lean comparison and unresolved choices

| Matched contract | Direct Lean author obligations | Proposed source obligations |
|---|---|---|
| All-number cancellation | `x : Surreal.{u}` and the existing additive group theorem. Usually no explicit lift appears. | Select a realized number class and additive-group capability; bind `x∈No`. The current native route has less infrastructure for this task. |
| Generic set image | `a : ZFSet.{u}`, `f` on its element subtype; `ZFSet.range` and `mem_range`, with `small_coe`. | Set and function-graph declarations; a replacement derivation and inferred representation witness. Same totality and codomain obligations. |
| Separated cut | Native option sets, two `Small` instances and strict separation. | Set-sized option evidence, number membership and strict separation; the adapter proves the same native obligations once. No mathematical premise disappears. |
| Ordinal family | `IsOrdinal` assumptions, `insert a a`, `range`, then `toZFSet_add_one`/rank comparisons. | Reuse the generic image proof and specialize the closure law; the same external comparison remains necessary. |
| New size/setting | An explicit map with required preservation laws. | A registered route may hide routine map applications, but must expose its missing law or unsupported judgment. |

This paper corpus contains no completion-time, repair-cost or productivity
measurements. #116 owns surface alternatives; #117 owns matched author trials
after the contract and a baseline implementation are frozen. Ordinary Lean
clients and existing internal-language imports remain usable without opting in.

The proposed first slice favors a bounded encoded derivation with a constructed
`M_ZF` interpretation because it can test real properness and representation
witnesses now. Direct Lean helpers are the mandatory comparison, and may be the
better interface for some clients. Definable-class models over a set theory,
an explicitly axiomatized two-sorted class theory, and an algebraic set-theory
or categorical account with small maps remain foundational alternatives.
Their admissible classes, logical strength and transport rules differ; this
report neither proves them equivalent nor selects one for the whole language.
A larger choice requires owner discussion under #36/#235/#289. In particular,
there is no decision to adopt full class quantification or ETR.

## Dependency-ordered implementation specification

These are proposed follow-ups, not new tracker issues or implementation
authorization. Root coordination owns independent review.

1. **Freeze the bounded profile and substitution target (#443 successor,
   #235/#290).** Specify the grammar, elementary-comprehension restriction,
   replacement schema and relational class-function notation above. Reuse
   Mathlib first-order syntax/semantics or prove a translation from a sorted
   source, without replacing existing regular/Horn APIs. Acceptance: capture-
   avoiding substitution under a set binder and a comprehension binder has a
   proved realization law; a class quantifier in comprehension is rejected.
   This records a local representation choice, not a universal foundation.
2. **Smallest checked vertical slice (same owner; after step 1).** Source
   example: the generic image membership/replacement derivation, followed by
   the ordinal successor-family corpus example. Checker: retain an explicit
   `Derives` certificate and prove `Derives.sound` for the chosen profile;
   if an executable certificate checker is added, prove successful checking
   returns a derivation. Construct `M_ZF` and discharge every rule used,
   using `small_coe`, `range`, `mem_range`, `sep` and pairing as needed.
   External consumer: prove the interpreted image of
   `{β.toZFSet | β < α}` under `a ↦ insert a a` has exactly the members
   `{(β+1).toZFSet | β < α}`, for arbitrary `α : Ordinal.{u}`. Use
   `Ordinal.mem_toZFSet_iff` and `toZFSet_add_one`. This is an infinite-family
   contract when `α` is infinite. Reject a set of **all** internal ordinals
   by interpreting a hypothetical derivation and applying
   `ZFSet.isOrdinal_notCMem_univ`; also reject a missing function-domain
   certificate. Check a singleton-image positive control. Required inputs:
   existing pinned Mathlib, step 1's logic and explicit model proofs. No
   surreal dependency or class recursion is needed.
3. **Surreal interpretation (owner #441/#443, after a separate adoption
   decision and #442 compatibility work).** Supply set codes for native
   numbers or construct internal numbers, prove their class predicate is the
   intended `No`, and prove equality, order, group/ring and separated-cut
   comparison with the native APIs. Do not treat a class of equivalent game
   presentations as canonical set-coded values without a quotient/coding
   theorem. An alternative is a proved sign-sequence coding, whose available
   source revision differs between the upstream candidates in #442. Acceptance:
   interpret the all-number arithmetic and cut corpus, recover native laws,
   prove the decoded option images small, and validate the conditional
   all-surreal-set rejection in this realization. No claim to the whole
   class field follows from step 2 alone.
4. **Transport and author experiment (#235/#289/#290, then #116/#117).** Add
   one size-changing route only with its stated fragment, witness and
   quantifier comparisons. Retain an unsupported-transport control and test
   composition. Freeze direct Lean and opt-in author interfaces for the same
   corpus before comparing effort. Investigate broader class logic/recursion
   separately if the corpus needs it; report exact extra principles instead
   of importing host strength invisibly.

For formal successors, use example-driven development and statement review,
including quantifier order, the representation witness and the non-small
controls. Add public checked examples through `SquareApplications.lean`.
Run README's applicable `./check.sh --candidate HEAD` and
`./check.sh --verify-candidate HEAD`, with fresh acceptance for dependency or
tooling changes and Nix checks if tooling changes. The exhaustive proof audit
must retain only `propext`, `Classical.choice` and `Quot.sound`; object-theory
rules are inductive constructors and model obligations, not new kernel axioms.
Independent Standards/Spec review remains required. This research report
requires source/statement/link/whitespace validation only and claims no build.

Open owners are explicit: #442/#441 for compatible native library reuse and
native size maps; #443 for the source/interpretation specification and coding
bridge; #235/#289/#290 with #36 for foundational alternatives and transport;
#116/#117 for surface comparison and author evidence. The unresolved surreal
coding and class recursion choices do not block the ordinal vertical slice.

[pset]: https://github.com/leanprover-community/mathlib4/blob/56a005855ea17e0b0958f73ec801ae140b0a1679/Mathlib/SetTheory/ZFC/PSet.lean
[zfset]: https://github.com/leanprover-community/mathlib4/blob/56a005855ea17e0b0958f73ec801ae140b0a1679/Mathlib/SetTheory/ZFC/Basic.lean
[zfclass]: https://github.com/leanprover-community/mathlib4/blob/56a005855ea17e0b0958f73ec801ae140b0a1679/Mathlib/SetTheory/ZFC/Class.lean
[ordinal]: https://github.com/leanprover-community/mathlib4/blob/56a005855ea17e0b0958f73ec801ae140b0a1679/Mathlib/SetTheory/ZFC/Ordinal.lean
[syntax]: https://github.com/leanprover-community/mathlib4/blob/56a005855ea17e0b0958f73ec801ae140b0a1679/Mathlib/ModelTheory/Syntax.lean
[semantics]: https://github.com/leanprover-community/mathlib4/blob/56a005855ea17e0b0958f73ec801ae140b0a1679/Mathlib/ModelTheory/Semantics.lean
[surreal-paper]: https://arxiv.org/html/math/0410026v2
[recursion-paper]: https://arxiv.org/html/1509.01099v2
