# Measured difference-list closures: bounded design preflight

Recorded 2026-11-02 before implementation. Source/API preparation and
implementation-side design assessment only; no Lean result or chapter acceptance.

Scope: reusable closure creation/application observations for C02-110/111,
with later actual `asc` and scanner correspondence retained in Chapter 2.
Sources inspected: the pinned book pp.21–22; Isabelle
`Natural_Mergesort.thy` at `f86f290225eebcc52c1ae7dba2e098f405f51c21`;
Batteries `DList.Basic` and `DList.Lemmas` at
`66e469188fe07963e5cf666c7d4433f45b8131c5`; and conaled's `Measured`,
`CallCount`, `Workload` and `Sequences.OrderedSummary` interfaces.

## Reuse and model

Use the ordinary function type `List α -> Measured (List α) Nat`, not a new
DList datatype, syntax tree or executor. Separate the value contract
`Rep f prefix := forall suffix, (f suffix).1 = prefix ++ suffix` from the
application observation `AppCost f k := forall suffix, (f suffix).2 = k`.
The latter quantifies over every suffix because composition feeds the output
of the second function to the first.

Charged identity and singleton-prefix callbacks each have application cost
one. Composition is `fun suffix => tick (bind (g suffix) f)`, so its actual
observation is `cost(g suffix)+cost(f(value(g suffix)))+1`. It executes g
before f while representing `prefix_f ++ prefix_g`. Under the two cost
contracts this is `k+l+1` over natural observations.

Separate creation operations return the corresponding function with
construction observation one. They capture fixed-size references and do not
apply the callbacks. This is a declared abstract capture tariff, not a theorem
about a compiler, allocation size, processor instructions or host-language
runtime. Scanner/control work receives its own later observation.

The existing `Batteries.DList` record is the value representation. Its
invariant follows from Rep at the empty and arbitrary suffixes; use its
existing toList/append/push laws and `ofList_toList` for value bridges. No
payload equality, order or inhabitance is required. Existing batch fusion
and `Resources.run_state` are available where their hypotheses fit; they
do not supply the new resource laws by themselves.

## Material distinctions

1. **Creation events differ from invocation occurrences.** Composing a stored
   f with itself creates one new closure but invokes f twice when applied.
   Starting from charged identity, m repeated self-compositions have creation
   work `m+1` and application work `2^(m+1)-1`, while representing the empty
   prefix. An arbitrary shared allocation history is not a linear bound on
   later application work. If the inventory says representation size, retain
   the unfolded occurrence interpretation or an explicit application contract.
2. **Charged identity is only a value identity.** Composing with it adds two
   application entries. Do not install a measured-builder Monoid instance
   that would erase these costs. The existing DList value laws remain valid.
3. **Batteries push is fused.** It is `fun t => f (a :: t)`. The chosen model
   uses explicit composition with a singleton callback, so the standard push
   correspondence is a value theorem, not a transfer of exact observations.
4. **The source asc seed is singleton.** `Natural_Mergesort.runs` starts with
   `(#) a` and eventually applies the builder to `[last]`. An ascending run
   of length r >= 2 has r-2 extensions after its singleton seed and application
   weight `1+2*(r-2)=2*r-3` in this tariff. Empty/singleton runs bypass that path.
   Prove the later source-to-model recurrence before using this count.
5. **Materialization is not memoized.** Applying the same stored builder twice
   pays two application observations. A cache of its result would be a
   different computation, with its own sharing contract.

## Seed-general construction and expected cases

Each compositional push creates one singleton and one composition, charging
two construction events. Starting from an already supplied f with Rep f prefix
and AppCost f k, m pushes add construction work `2*m`, represent
`prefix ++ items`, and have final application cost `k+2*m`.

Including initial identity creation gives construction and one-application
counts both `2*n+1`. Construction then one application costs `4*n+2`;
construction then two applications costs `6*n+3`. These formulas preserve a
nonempty suffix without traversing it in this model. At n=3 the split is 7+7,
or 7+7+7, with duplicate payloads retained in order.

Retain order-sensitive singleton composition (`[1]`, `[2]`, suffix `[9]`),
constant construction charge with arbitrarily expensive callbacks, empty and
singleton cases, `Empty` payloads, an arbitrary seed contract, repeated
materialization, and empty-prefix identity/self-composition histories.

The architecture contributor independently inspected these APIs and cases
and found this sufficient for the reusable conditional model, subject to the
five distinctions above. It performed no edits, compiler, Git or control-file
operations. This assessment is not a final independent review. C02-109's
ordinary append/reverse comparison, actual asc representation bounds and
C02-112's full scanner/merge-dispatch observation remain chapter obligations.
