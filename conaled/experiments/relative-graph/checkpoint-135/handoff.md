# Issue 135 material-blocker handoff

This is an audited implementation checkpoint, not a completion or review candidate. No commit, push, tracker mutation, master edit, peer-worktree edit, or shared dependency-package mutation was performed.

## Preserved source and validation

Nine new files under experiments/relative-graph: EmissionEncoding, CheckerReduction, AcceptanceStages, EmissionSemantics, EmittedGraph, EmittedEnvironment, EmittedComparison, EmittedClosed, AndPositivityStages. All are untracked in workstream/128 at fixed base ad8e7a56de5027eed620486fe63f154eecdd3cd3. checkpoint-source contains exact copies; checkpoint-provenance.json is provenance only.

Ran `direnv exec . python3 /home/vlad/.local/state/conaled-supervision/2026-10-25/128/135/validate-checkpoint.py`. The script invokes lean -o for each of these nine modules in dependency order into fresh checkpoint-build, reading unchanged selected upstream state134/con-leche and main native caches. checkpoint-validation.json records exact module results, elapsed time, and individual checkpoint-logs paths. All nine exited0; each exhaustive #audit_graph_module passed with only Quot.sound/Classical.choice/propext (some use fewer). No full main rebuild was run because main sources were unchanged. No forbidden admission/native acceptance axioms were introduced. No full candidate/review cycle was requested or run.

## What is checked

Actual producer-generated types and proof bodies are encoded with a successful roundtrip, including helper applications and native z,x binder order. The generic formula/code/source correspondence is proved with explicit SetTheory/model/primitive premises and separated operations/laws/compatibility. Native producer emit_typed/emit_denotes are explicitly included in emission_comparison. Native helper bodies come from the exact pinned snapshot; helper completeness and canonical primitive signature equality are checked. Concrete expected emitted environment supplies primitive records/laws. EmittedClosed.closedTruth obtains the two actual emitted theorem memberships from Model.mem, specializes their exact telescope through shared ClosedGraph.specialize, and transports shifted encoded conclusions; it does not substitute an independently handwritten graph proof. This is conditional on a Model of the expected environment, whose construction remains blocked by acceptance.

Staging certificates: exact Cached Eq installation/acceptance; pure fuel32 And former and constructor outputs, positivity context/uniformity; exact constructor crest/inferred type; symbolic-fuel ordinary-field certificates; exact two-field nestFields result; guard and closed-telescope certificates. CheckerReduction.depthGo_spec proves memo validity preservation and structural depth equality, specialized to empty in depth_eq. It does not claim independence of arbitrary invalid memo contents. Examples check forall depth2 and annotated free-variable depth1.

## Material blocker and limits

There is no kernel-checked whole-family checker success theorem. Actual finite-fuel reference-checker execution at64 accepted the canonical emitted family diagnostically (EmittedExecution.lean), but execution is not a proof. Exact environment equality was not established from that execution. Cached whole-family success also remains OPEN and must never be inferred from reference/model soundness.

The first nontrivial inductive installer (And) still lacks a complete composed acceptance certificate. Individual phase equalities compile quickly. Whole-pass/root cbv attempts reached bounded timeouts. Structural selector equations fixed a measured packed Expr.data reduction obstacle; depth_eq removes memoized HashMap depth calculation. Named root transition simplification reaches guard/bookkeeping output with constructor-normal-form state; ordinary rewrite matching can miss named-vs-normalized definitions even though Meta.isDefEq confirms argument equality. Several opaque probes also spend time printing enormous failed goals, so those wall timeouts are not reduction infeasibility evidence. Named output joins (`#[].push x` vs `#[x]`) and subsequent exact-push/discriminant composition attempts still timed out20–30s. This is a measured proof-engineering obstacle, not an impossibility conclusion. No more local variants were started after supervisor directed bounded preservation.

Useful latest probes: AndRootPostSimp.lean shows state after main named transition; AndRootLastGoal.lean/AndRootRemaining.lean record final bookkeeping goal (historical imports may now have duplicate names due retaining successful declarations); AndRootPush.lean and AndRootDiscriminant.lean are final bounded variants without duplicate declarations; AndCrestFieldExact.lean and AndRootTailCerts.lean supplied independently checked pieces now retained in AndPositivityStages. The retained source modules and fresh logs are authoritative success evidence.

## Remaining obligations

1. Compose actual pure reference checker acceptance across And/Exists installers, all encoded native helper definitions, and both actual emitted declarations; prove exact final environment contract. Existing pieces only cover part of And.
2. Apply and freshly audit checkDeclsPure_sound_of and Model.ofEnvModelM with explicit SetTheory, using concrete acceptance (not a hypothetical h). reference-model-route.md contains exact theorem chain.
3. Join concrete constructed model with the already checked generic/source/native/actual-record semantic comparisons; retain required application/rejection cases for this actual canonical family.
4. Integrate experiment reproduction/documentation, perform final statement review and full affected experiment checks, then supervisor Standards/Spec review. Do not close issue135 from this checkpoint.
5. Track exported Cached.checkDecls equation separately if the permitted pure route completes; no such follow-up issue was created by this worker.

No owned build/check process remains running when this worker returns. Budget last observed fresh normal50%; use authoritative budget.json before more work.
