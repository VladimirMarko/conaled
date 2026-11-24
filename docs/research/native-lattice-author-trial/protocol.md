# Frozen author trial #692

Frozen before author assignment. Baseline a38e05358d47f1739aa2f1fbcae8f9cc0d120f86. No baseline/library edits during either attempt. Independent fresh-context authors, configured gpt-6-astra/high by repository model policy. Same task and budgets; routes differ as specified. Host runtime details unavailable beyond selected configuration; do not self-attest or poll model metadata.

## Independent mathematical task

Use the lattice of integers with its usual order. Construct the order isomorphism e : Int ≃o Int whose function sends z to z + 3 (inverse z - 3). For arbitrary x ≤ y, transport the dependent ordered pair (x,y,proof) to (x+3,y+3,proof). Prove the whole pair recovers under inverse transport and the numerical gap second-minus-first is unchanged. The selected strict pair (-2,4) must give (1,7), retain strictness, and show a nonidentity observation e 0 = 3 ≠ 0. Check meet and join preservation. As a rejecting control prove negation z ↦ -z is not monotone on ordinary Int (0 ≤ 1 witnesses reversal); the native route must also reject that bijection as preserving the admitted lattice model. These expectations come from integer arithmetic/order, independently of native API implementation.

## Routes

Direct author: implement with ordinary Lean/Mathlib OrderIso and subtype dependent pairs. Do not read native implementation, sibling attempt or native research reports. Do not use the native bridge to prove your direct transport. Public Mathlib sources in pinned dependencies are allowed.

Native author: independently construct the same isomorphism and observations through the frozen public admitted lattice API. Use actual source/target admissions, law-bearing path, complete selected-equivalence recovery and whole-path recovery in BOTH native models, then actual native-path dependent ordered-pair transport and whole solution recovery. Prove agreement with the direct mathematical value and gap theorem, and compare decoded complete dependent values across models. Do not equate independently selected ua paths. Existing Examples.LatticeTransportBridge, NativeLatticeTransport, NativeLatticeTransportCases, NativeGeometricLatticeTransport and their dependencies/docs are permitted. Independent implementation of common setup is part of client cost; no access to sibling author's results.

## Success and limits

Common success: checked full ordinary target and rejecting control, no sorry/admit/axiom/native_decide/kernel bypass. Native extra success: all additional native contracts above. Failure is valid trial evidence and is not repaired retroactively. Diagnose a failure as mathematical only with proof/separating evidence; unsuccessful encoding or budget exhaustion establishes only that failed attempt.

Each author has 20 minutes elapsed from assignment, at most 25 Lean invocations, each bounded to 30 seconds, cumulative Lean wall time at most 8 minutes. Start with default maxRecDepth 512/maxHeartbeats 200000; local measured experiments up to depth1024/heartbeats1000000 permitted and must be retained. No library edits or transparency/kernel bypass. No web/external-agent help. Clarification of ambiguous task/environment allowed; orchestrator supplies no proof/API hints. Stop when complete or any bound reached. Retain all attempted file versions before each compile, command output, exit status, monotonic elapsed/user/system/peak RSS if available, clock start/end, failed approaches and assistance. Preserve independently authored code and report separately. Shared Lean lock /tmp/conaled-native-followups-lake.lock; time waiting for lock reported separately if material. Repository shell via direnv exec ., invoke Lean against external scratch paths; do not mutate baseline/imported artifacts. Final checked file emitted olean to external directory.

This is one bounded agent-author observation per route, not a human/general productivity experiment. Prior library preparation (#621/#691) is excluded from measured client effort and must remain explicit. No change to task or criteria after assignments; missing contracts tracked separately with fresh held-out work after repair.
