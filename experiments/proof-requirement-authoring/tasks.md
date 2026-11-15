# Frozen author tasks for #293

Read `Examples/ProofRequirementSupport.lean`. It contains concrete completed
source proofs and target operations. Publish your own useful, named sufficient
requirement interface and a generic proof or construction, then justify both
target interpretations and obtain their results through that generic artifact.
Structures, named predicates and ordinary theorem parameters are all allowed.
Do not assume the requested conclusion as an interface field. No globally
weakest interface is required. Use Lean equality throughout.

## E: reversal of three blocks

Start with `Source.reverseBlocks`, including its complete proof body. Replace
the concrete carrier, append and reversal by arbitrary `A`, `m : A → A → A`
and `f : A → A`. The required conclusion, for every `x y z : A`, is:

```lean
f (m x (m y z)) = m (m (f z) (f y)) (f x)
```

Interpret it in `(List Nat, Targets.listOp, Targets.listFlip)` and
`(Bool, Targets.boolOp, Targets.boolFlip)`. Prove the model obligations.
Keep checked empty-list and nonempty-list applications, with the latter using
`x=[1,2], y=[3], z=[4,5]` and expected result `[5,4,3,2,1]`; retain a Boolean
application at `x=true,y=false,z=true` with expected result `false`.

Account separately for the source's ambient assumption, dependencies used by
the proof body, and any proof changes you make to weaken requirements. Retain
an original-dependency replay if you change the argument, then check the changed
generic proof too. Explain why the two proofs have the same required conclusion.

Reject the target `(Bool, Targets.badOp, Targets.boolFlip)` by a checked concrete
failure at `x=true,y=false,z=false`; identify which proposed interface obligation
fails. This task is held out from #286's published E/W solutions.

## W: selected witness through an observation

Start with `Source.selected` and `Source.selected_value`. Generalize the carrier
to `A`, observation result to `B`, append to `m`, empty to `e`, and length to
`observe : A → B`. For every `x : A`, construct:

```lean
{ y : A // observe y = observe (m x e) }
```

Its first projection must equal the supplied `x`, not an arbitrary witness.
Publish named sufficient requirements and prove this projection theorem.
Obtain the list interpretation with `listOp`, `listUnit`, `listObserve`, and the
Boolean interpretation with `boolOp`, `boolUnit`, `boolObserve`. Retain checked
applications at `[]`, `[1,2]`, and `true`, whose selected values remain those
inputs. The list specialization must equal `Source.selected` as subtype data.
If your proof changes its dependencies, identify and replay that change.

Use `A=B=Nat, m=Nat.add, e=1, observe=id, x=0` to show that a witness exists
while the required selection is impossible; identify the missing law.
For the successful list interpretation at `[1]`, construct the alternative
witness `[2]` with the same length property. Check that their first projections
differ. Show that erasing either witness to `Nonempty` of this same subtype
cannot support a function recovering the first projection of every witness.
This is a calibration-derived task: #286's selected-witness argument is adapted
with a noninjective observation to make erasure rejection nonvacuous. It is not
a second independent held-out observation.

## Allowed material and deliverables

Read only this task, the public support source, `conduct.md`, your route prompt,
the frozen `guidance/` copies, `manifest.json`, `check_attempt.py`, and the pinned environment,
Lean/Mathlib/dependency sources in your assigned handoff.
Existing library lemmas and tactics are allowed; no external browsing, repository
history, sibling directories, other author attempts or coordinator references.
The assisted route also receives `dependency-ledger.md`; the manual route does
not. Do not create helpers in the frozen support source.

Before repairs, save every Lean attempt and compiler output under a fresh name.
Finish with the source path of your best checked artifact, a command transcript,
and `outcome.md`: requirements, interpretations, proof changes, negative checks,
statement review, remaining failures, assistance and unavailable metadata.
