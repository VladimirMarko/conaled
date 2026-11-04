# Construction and observation author trials

Frozen interface revision: `5e5b039` (full SHA in setup record). Issue #279;
methodology follows #249/#117. These trials concern existing Lean interfaces,
not alternative surfaces or #286's proof extraction. Tasks and mathematical
reference results below are frozen before dispatch. Authors did not implement
the selected interfaces and receive no conversation fork. Public source, docs
and examples at the frozen revision are available; other authors' files,
coordinator solutions and private review records are excluded.

## Task A: indexed vector construction

Use `IndexedCompositionalExamples.Vectors` from `Examples/IndexedCompositional`.
The native contract is `Fin n → Nat`, with exact coordinates and length, including
n=0. Define a compound constructor `frame a b t = cons a (double (cons b t))`,
changing length n to n+2. This new client uses existing admitted constructors;
it does not claim to add a new primitive signature.

For arbitrary n, a, b and v : Vec n, prove every coordinate of
`read (rule.lift native) (frame a b (.leaf v))` equals the independent vector
`Fin.cases a (Fin.cases (2*b) (fun k => 2*v k))`. Give matching proofs:

- Direct: native `read`, `rule.lift`, constructor/observer equations and coordinate
  case analysis. Do not use `correct`, `read_morphism`, `Rule.fold_morphism`, the
  bridge `observations`, or a theorem proving the full requested client result.
- Shared: the existing all-term correctness/morphism interface. The proof must
  visibly connect to its public result, with the same assumptions and conclusion.

Reuse public `substituted` to replace v by its complete cons syntax (`expand`),
preserving the same coordinates. This step may use `substituted` in both routes.
Retain an empty-tail case and a nonempty case yielding `[7,22,26]` for a=7,b=11,
v=[13]. Also recover 22 at index 1 of the established `double (cons 7 (cons 11 nil))`
client through its public theorem.

The mathematical reference is fixed: cons prepends without changing its tail;
double multiplies every coordinate by 2. Frame therefore yields a,2*b,then2*v.
Expanding a vector into cons syntax preserves all its coordinates. Head-only or
Boolean agreement does not satisfy either route. State the compound client's
scope rather than calling it arbitrary constructor-extension support.

## Task B: an exact parser observation extension

Use `SquareKit.ObservationExtension` and the native witness parser. For arbitrary
`P : Language Char`, define the old contract on `Parser P` as exact agreement of
`parse` at every word. Add the new observer
`pairObservation p = (p.parse [], p.parse ['a'])`, with result type
`Decision (P []) × Decision (P ['a'])`.

Prove compatibility, equivalence of the extended and old contracts, and quotient
descent with the representative computation theorem, through matching routes:

- Direct: prove pair equality from the old hypotheses, use native `Quotient.lift`,
  and prove extension/recovery directly. Do not use the shared compatibility,
  factor, extend-equivalence or descent helpers.
- Shared: use `compatible_of_factor` with meaning `fun p w => p.parse w`, then
  `extend_iff`, `descend`, `descend_mk`. Discharge their premises; do not assume
  the requested compatibility or final result.

Instantiate with the nullable-star parser `star (union epsilon (atom 'a'))`.
Retain actual decisions at both words, show that the empty observation selects
the native empty list, and reuse an established native parser/trie exact lookup
theorem for the nonempty observation.

Switch only the old contract to Boolean recognition. Reuse the ambiguous epsilon
alternatives in `Examples.ObservationExtension.Parsing` and prove the pair
observer separates their first components despite recognition agreement. Identify
the failed compatibility law; do not weaken the successful exact-agreement task.

The mathematical reference is fixed: equality at all words implies equality at
both selected words, hence their ordered pair. Quotient descent requires this
compatibility. The ambiguous epsilon parsers select opposite Sum tags, which
refutes recognition compatibility regardless of the second observation. Preserve
the distinct dependent result types at the two words.

## Conditions and retained evidence

Two fresh authors each attempt both tasks/routes. Author A order: A-direct,
A-shared, B-direct, B-shared. Author B: B-shared, B-direct, A-shared, A-direct.
Earlier routes and public examples can inform later ones; this is counterbalanced
exposure, not independent observations of each route.

Each author has 15 minutes wall-clock from recorded start, or stops at completion.
Record start/end, actually exposed model/configuration metadata, commands,
diagnostics, attempts, assistance, imports and checked status. Hidden serving
revision, tokens and pricing remain unavailable. Inherit the model configuration
without overrides, external calls or nested agents.

Use `direnv exec .` and the frozen toolchain in the assigned isolated checkout.
Do not modify library files. Save each attempt and compiler output before fixing
it, and retain an honest partial result on timeout. Sorry/admit/new axioms cannot
count as success. Record environment failures separately from proof failures.
Only the coordinator may supply assistance; all interventions are logged.

Compare mathematical prerequisites, internal concepts, wrappers/casts, imports,
recurring obligations and diagnostics. Distinguish mathematics, interfaces/docs,
Lean encoding and author limitations. Do not infer human usability, causal
productivity or general model capability. A bounded interface/doc fix requires
freezing a new revision and rerunning affected tasks while preserving originals;
a larger proposed change needs scoped ownership and recovery requirements.
