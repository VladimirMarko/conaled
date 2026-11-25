# Conventional polynomial contract150 — uncompiled research

The two Lean files are complete source drafts without admissions or extra axioms,
but **have not been compiled or independently reviewed**. Root owns the active
whole150 check and all subsequent compiler commands. This helper changed no
repository source, build outputs, metadata, settings, captures or acceptance.

## Purpose and actual dependency

`ConventionalPolynomialDecider150.lean` follows the existing
`PolynomialBooleanDecider` bundle but permits an arbitrary finite input alphabet.
It fixes finite work/control types, a blank, three distinct start/accept/reject
controls, an injective nonblank per-letter input map, the existing real
PrintMove transition semantics, exact terminal-domain law and a single exponent.
Its run field requires actual `EvalsToInTime` execution on every literal word;
constructors must prove it. There is no assumed polynomial-time predicate.

Generic active-transition totality and stopping are derived from the exact
none-iff law. `Accepts` means actual `StateTransition.eval` membership at the
accept control. The iff theorem connects the bounded witness to reachability,
then uses deterministic terminal uniqueness (`Part.mem_unique`) to exclude a
second spurious accepting run. The finite-run-to-reachability helper is a small
induction on the recorded number of actual optional transitions. The existing
`MarkedInput.lean` private `live_iteration_reaches` already uses this induction
internally; its public `normalized_eval` is specialized to the marked-input
machine. Root identified that lineage and this helper then read the private
proof and its public consumer. This draft exposes the generic EvalsTo-facing
conversion for conventional clients, not a newly discovered semantic principle.
At installation, consider placing the reusable conversion with the common
transition API and routing the existing private client through it; that owner
change is outside this uncompiled draft and requires its own source-scope review.

`ofNative` reuses the existing Boolean-input `printMove_run` and the checked
normal-form theorem for its `2*p+1` polynomial. It widens only the actual target
allowance. This provides a reusable existing API client of the new contract;
it does not replace the original richer native/target theorem or its clients.

`DelimiterConventionalContract150.lean` supplies every field from current149d
and the passed composition150a. Its full-run refinement still exposes both
actual witnesses, complete input/output tapes, exact simulationTime+1 and the
relative <=2*native.steps+1 bound. A smaller class-facing bundle intentionally
forgets this choice of native witness and final tape; no inverse recovery is
claimed. A closed Unit-register value fixes its classical equality before all
raw words, showing the finite contract is populated without extra caller data.

The actual accepted language is connected to the existing arbitrary-raw
`GeneralProof1.verifyDelimited_accept_iff`; no parser proof is duplicated.
Missing and repeated delimiters reject universally. `BinaryYes` retains the
original cert.length <= input.length^2 witness and the separate literal-pair
length <= I^2+I+1 observation. All three source symbols are distinct and nonblank.
No conventional NP/NTM equivalence, indexed transition-table export, exact
diameter, sharper space, source-row qualification or receiving acceptance is
claimed by this draft.

## Freeze and later compilation

EXPECTATIONS.json was written before either source file, and remains unchanged.
MANIFEST.json gives exact source and direct parent identities plus canonical
packet routes. The short research imports are staging aliases, not new modules
installed in C147. To form a normal external carrier, retain the exact complete
post-import source bodies in order and supply normal project imports. Existing
composition150 reassembly already reconstructs all its canonical parents.
Append the generic draft body, then the concrete draft body, and the supplied
focused queries. Add the normal import
`Applications.Resources.TuringSimulation.PolynomialDeciderPrintMove` alongside
those needed by the existing composition. Do not copy or fabricate products,
set caller LEAN_PATH, repair traces/caches, or change elaboration/resource limits.

The focused query plan is 24 readable / 7 expanded / 11 selected root reports,
plus two expanded definition prints. Full module installation, original-axis
review and whole/audit/verify/compare gates remain separate. The proposed69-owner
integration plan predates this new draft and must not be silently treated as
including it; any later scope extension needs a fresh complete baseline/capture.

## Reading limits

This helper freshly read the small relevant owner files and selected PrintMove,
StateTransition, Protocol and Prelude definitions. The initial attempt to print
the entire cumulative requirements was truncated; no complete fresh reading is
claimed. Primary Cook definition reading is attributed to root, not this helper.
Original requirements, findings, checkpoints and existing proof bodies remain
unchanged. Only source-level inspection and exact file binding were performed.
