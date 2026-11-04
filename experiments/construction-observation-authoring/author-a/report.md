# Author A trial report

All four routes passed the assigned focused Lean check in the required order:
A-direct, A-shared, B-direct, B-shared. The final source is
`Examples/ConstructionObservationAuthorA.lean`, namespace
`ConstructionObservationAuthorA`. No library or import-root file was edited.
No commit was created. The coordinator owns the full build and proof audit;
this report claims only the focused check recorded in attempt 07.

## Conditions and metadata

- Start: 2026-11-04T17:19:22Z, retained in `start.txt`. End is in `end.txt`.
  The 15-minute budget was not exhausted. Protocol and environment guidance
  were read before recording start; proof authoring followed the start.
- Checkout HEAD: `21eaedeed1c78f58437b05a0197b12bcc386c9bb`.
  The task described frozen public interfaces as `5e5b039`; I did not resolve
  that abbreviated interface revision separately.
- Lean: 4.35.0, x86_64-unknown-linux-gnu, release commit
  `eb6cafb7290e8bd5f2937522d8d804f58f02bafc`.
- Exposed agent identity: developer instructions describe Codex based on GPT-6.
  The exact served model identifier/version, serving revision, reasoning setting,
  sampling configuration, token use, prices and costs were not exposed to me.
  I inherited the supplied configuration and made no model overrides.
- Local bash and tool execution were available. Lean commands used the inherited
  Nix/direnv shell and isolated prebuilt cache. The initial assignment reported
  successful public-import builds; I did not rerun that build.
- Assistance: only the coordinator's initial task assignment, protocol, and
  public source/docs/examples. No later coordinator intervention, other author
  evidence, private solutions, external calls, or nested agents were used.
  Earlier routes informed later ones, as permitted by the counterbalanced design.
- Skills: example-driven development and prose guidance. This was assigned work
  in an existing implementation loop; no additional review workflow was started.

## Attempts

The `attempts` directory retains each pre-compilation source and full compiler
log, with command, UTC times and exit status.

| Attempt | Stage | Result |
|---|---|---|
| 01 | A-direct and universal expanded version | Pass |
| 02 | Unchanged A-direct source after failed ambient Python edit | Pass; no A-shared evidence |
| 03 | A-shared, both routes' concrete cases, existing double client | Pass |
| 04 | B-direct universal contract and quotient | Fail: ambiguous `Language`, cascading errors |
| 05 | B-direct with concrete star and ambiguity cases | Fail: same unqualified name remained |
| 06 | B-direct after qualifying `LanguageWitnesses.Language` | Pass |
| 07 | B-shared added to all prior successful work | Pass |

Attempts 04 and 05 contain compiler recovery warnings about declarations using
`sorry`. Those are failed elaborations, not successful admissions. No explicit
`sorry`, `admit`, or axiom was introduced, and the final check has no warnings.
The ambient `python3` command failure is separate from Lean proof diagnostics;
see `environment-events.txt`. Read/edit commands and their timing limitations
are documented in `commands.md`.

## Task A outcomes

`frame` composes the admitted `cons` and `double` constructors, with length
`n + 2`. It does not extend the primitive signature or establish arbitrary
constructor-extension support.

The independent target vector is `Fin.cases a (Fin.cases (2*b) (fun j => 2*v j))`.
`frame_direct` proves equality at every `Fin (n+2)` coordinate for arbitrary
`n`, `a`, `b`, and `v`. It first proves native leaf reading and doubling by
induction on length. Constructor and observer equations reduce definitionally;
`Fin.cases` separates heads from tails. This route does not invoke `correct`,
`read_morphism`, `fold_morphism`, or an observation bridge.

`frame_shared` has the same quantifiers and conclusion. Its first step rewrites
with the public all-term theorem `correct`, then reduces the concrete algebra
by coordinate cases. `frame_direct_expanded` and `frame_shared_expanded` both
use public `substituted` on the entire frame term, so the vector leaf is replaced
by complete `expand` syntax while preserving every coordinate.

Both routes retain an arbitrary-coordinate empty-tail theorem and the complete
nonempty vector `[7,22,26]`, represented by `List.ofFn`. `established_client`
recovers index 1 = 22 for `double (cons 7 (cons 11 nil))` via public `correct`.
The original public concrete example is anonymous, so there is no named
specialized theorem to cite; `correct` supplies its public all-term result.

## Task B outcomes

For every witness language `P`, `exactAgreement P` relates two parsers exactly
when their full decisions agree at every word. The observer retains the
product `Decision (P []) × Decision (P ['a'])`, with no Boolean erasure or
identification between the two fibres.

The direct route proves compatibility by `Prod.ext` from the two old-contract
instances. It proves the extended relation equivalent to the old relation by
constructing and projecting the conjunction. `descend_direct` uses native
`Quotient.lift`, supplying pair equality directly; `descend_direct_mk` is its
representative computation theorem. `recovery_direct` recovers any old word.

The shared route uses `compatible_of_factor` with meaning `fun p w => p.parse w`.
Its meaning-compatibility obligation is `funext h`, its semantic observer selects
the two words, and its square is definitional equality. It then invokes
`extend_iff`, `descend`, and `descend_mk` explicitly. `recovery_shared` uses the
proved equivalence to recover arbitrary old observations. Neither route assumes
the requested compatibility or final equality.

The nullable-star specialization is `star (union epsilon (atom 'a'))`.
`star_empty` gives the actual decision selecting the empty list of parses;
`star_empty_list` confirms that native list is empty. `star_a` gives the actual
singleton parse with the right union tag. `star_a_lookup` reuses public
`WitnessTrie.lookup_unfold` at depth 1 for exact equality of the nonempty
observation. Both quotient routes compute to this exact pair of decisions.

The Boolean-contract counterexample reuses the public ambiguous epsilon parsers,
`old_agreement`, and `selected_different`. Pair equality would imply equality
of first components by `congrArg Prod.fst`, contradicting their opposite Sum tags.
`recognition_pair_incompatible` identifies the failed law: recognition agreement
would have to imply equality of the exact pair. The successful exact-contract
task remains unchanged.

## Statement review and author obligations

The vector statements quantify all valid coordinates, including the empty-tail
case. Finite indices enforce the changed length. The target arithmetic comes
from prepending `a`, then doubling the prepended `b` and the original tail.
Concrete list equality checks all three coordinates, rather than a head alone.
Substitution applies to the same frame syntax and preserves its coordinate
contract. There are no additional vector hypotheses or casts.

The parser setoid explicitly proves reflexivity, symmetry and transitivity of
pointwise decision equality. Quantification over all words is unrestricted.
The dependent output types are preserved through quotient descent. Compatibility
is established from the old relation, not postulated. The concrete star parser
supplies an inhabitant, so these conclusions are not based on an empty domain.
The counterexample changes only the old relation to recognition and uses the
same polymorphic pair observer.

Direct imports are `Examples.IndexedCompositional`,
`Examples.ObservationExtension`, and `Applications.Languages.WitnessTrie`.
The observation-extension module is available transitively through the public
example import. Client wrappers are `frame`, two input vectors, the exact
setoid, pair observer, two quotient functions, and the concrete parser/witness
names. No universe lifts, dependent casts, new primitive equations, or new
compatibility instances for the vector signature were needed.

## Interpretation of the observed effort

The mathematical prerequisites were elementary: induction over length,
coordinate decomposition, function extensionality, equality of products, and
quotient well-definedness. The exact parser compatibility has no unresolved
mathematical obstacle. Boolean compatibility genuinely fails because recognition
forgets witness tags.

The direct vector route required knowing how the lifted successor state of
`double` reduces. The shared route reused the already proved all-term contract
and needed only reduction of the client meaning. The shared parser route added
factorization terminology and a function-extensionality premise; the direct
pair/quotient argument was already short. Both remained within the same exact
contract. These are observations about this author and task, not a causal
productivity comparison.

The concrete failure was Lean name resolution combined with my unqualified
`Language` spelling. Public examples already qualify the witness language, so
this does not establish a missing mathematical interface or documentation gap.
I retained the second failed attempt rather than rewriting its history; it
repeated the same mistake while adding cases. The ambient Python failure was
an author workflow error, corrected by the prescribed development shell.
No interface change is proposed from this trial. No human-usability or general
model-capability claim follows from these results.
