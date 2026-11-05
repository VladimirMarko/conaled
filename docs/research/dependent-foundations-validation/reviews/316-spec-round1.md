# #316 Spec review, round 1

**Outcome: Passed. Findings: 0. Worst severity: none.**

The candidate satisfies #316 through its explicitly permitted precise-prerequisite outcome. It constructs and checks the frozen consumer in an external dependent source theory, identifies a substantive remaining Lean construction, and assigns that construction to #322. It does not claim to have constructed the Lean interpretation or passed the dependent higher adoption gate.

## Scope and requirements

- Base and merge base: `f0773fee8fa40214c67606c46ba8c41eed8e674b`.
- Candidate: `d7d2beeea699bccc2f7eb0fee7f8fa52e6718186`.
- Candidate tree: `a3baf0c1f6213e135371f9f1ee428fc144c6162c`.
- Checkout: `/tmp/conaled-314-320/316`; HEAD and merge base verified, working tree clean.
- Diff: `git diff f0773fee8fa40214c67606c46ba8c41eed8e674b...d7d2beeea699bccc2f7eb0fee7f8fa52e6718186`.
- Scope: all 13 added files, no exclusions. Commits `ca54f31` and `d7d2bee`.
- Requirements: full saved `specs/316.json`, `specs/orchestration.md`, coordination `specs/321.json`, and the unchanged frozen `docs/research/dependent-coherence-discovery/292-external-memo.md`. Specification identities are retained in `316-review.md`.
- Successor ownership: supplied review record and `records/322-coordination.md`; #322 owns the direct construction under #289, while #321 owns the distinct cubical/source-compatibility route. No tracker mutation or nested workflow was performed.

This review applies the mathematical statement-review criteria from EDD to the Agda claims. Standards review is a separate axis. No prior Spec findings existed; no `316-SPEC-*` identifiers were needed.

## Requirement assessment

### Model feasibility and source claims

The comparison in `docs/research/dependent-higher-identity.md:19` distinguishes strict higher groupoids, Kan fibrations followed by local universes, a chosen simplicial universe, and fibrant cubical families. Its selection remains an investigation decision. It separates existence results from required mechanized inhabitants and does not infer that an ordinary groupoid implementation is a higher model.

Primary-source checks support the material claims:

- Warren's Theorem 7.1 interprets dependent products, sums, and identity types using strict omega-groupoids. The candidate correctly leaves finite-dimensional closure as an additional obligation. [Warren](https://mawarren.net/papers/crmp1295.pdf).
- Lumsdaine–Warren Theorem 4.2.2 and Examples 4.2.5 support the Kan/local-universe route; its hypotheses include the relevant factorization and stability structure. The candidate does not substitute the repository's Type-family example for those hypotheses. [Lumsdaine–Warren](https://arxiv.org/pdf/1411.1736v2).
- Kapulkin–Lumsdaine Theorem 2.3.4 uses one inaccessible for the constructor-closed classifier and another for the internal universe. The candidate does not claim either is a lower bound for the universe-free consumer. [Kapulkin–Lumsdaine](https://arxiv.org/pdf/1211.2851v5).
- CCHM §9.1 explicitly distinguishes Path from an identity construction with judgmental J computation. The candidate's cubical prerequisite preserves that distinction. [CCHM](https://arxiv.org/pdf/1611.02108v1).
- Garner's `Id-disc2` rule makes a second identity reflexive; excluding that particular truncation is justified, without excluding strict 2-groupoids as semantic closed types. [Garner, Table 2](https://arxiv.org/pdf/0808.2122v2).

The inspected local `SplitFamily.identityFamily` uses discrete fibers on hom sets, and `TwoLoop.lean` explicitly supplies an algebraic, nondependent fragment. The pinned HoTTLean `IdObj` likewise uses `Discrete` on a hom type. Its Hurewicz framework does not supply a higher inhabitant merely by exposing an abstract interface. These boundaries match the report. [Pinned HoTTLean Id](https://raw.githubusercontent.com/sinhp/HoTTLean/31133dd5b25226ea897f8aa5e2e43b61392459eb/HoTTLean/Groupoids/Id.lean), [Hurewicz construction](https://raw.githubusercontent.com/sinhp/HoTTLean/31133dd5b25226ea897f8aa5e2e43b61392459eb/HoTTLean/Model/Unstructured/Hurewicz.lean).

### Generic derivation, motives, and substitutions

`FrozenMemo.agda:12` quantifies an arbitrary motive at an independent universe level and checks the reflexive J computation. Inspection of the pinned `Cubical.Data.Equality.Base` confirms that J, transport, composition, ap, and apd are defined by elimination of inductive `Agda.Builtin.Equality`. This is not an implicit use of Lean proof-irrelevant equality or an assumption of UIP.

`Memo` has arbitrary `A : Type a` and `B : A → Type b`. Its `v` performs transport along `p` then `q`; `η` has the frozen orientation, and `W` is an actual dependent sum whose second component refers to the chosen value. The dependent context records retain all endpoints, both paths, the second identity `h`, the last path, and the family element.

The definitions of `σ`, `τ`, and the independently written `σ∘τ` match the frozen assignments. `first-apd` and `second-apd` include transport in `K`, not only equalities between the endpoints of `η`. `w-twice` and `apd-twice` compare the successively substituted terms with the direct assignment. Their reflexivity proofs are meaningful here: the expressions are independently assembled substitutions into a term and its dependent type.

The source realization uses Agda's dependent functions and records for contexts, extension, reindexing, and substitution. It does not supply a new syntactic soundness theorem. This limit is explicit. The successor still requires contextual J for every admitted motive and finite dependent tail; the candidate does not replace that obligation with the selected transport motive.

### Higher witness and erasure control

`FrozenMemo.agda:110` proves conjugation with both endpoint comparisons in the required order. Its reflexive case is inverse cancellation. `PathFamily` defines the actual representable identity family, its transport map `T`, and the comparison `β` by identity elimination, then specializes the general conjugation theorem.

`HigherWitness.agda` supplies an inhabited, nonvacuous instance. I inspected the pinned `coHomK`, `Kn≃ΩKn+1∙`, and `PathIsoEq` definitions. The two pointed loop comparisons start at `(ℤ,0)` and end at the second inductive identity type of the chosen basepoint. Conversion occurs at both loop layers. The basepoint comparison is retained in `double-identities`; `decode-zero` and `encode-refl` use it to establish the reflexivity observation.

`encode-decode`, `encode-h`, and the integer discriminator prove `h ≠ refl` for the constructed `h = decode 1`; no nontriviality assumption is supplied. `w-twice-h` and `apd-twice-h` instantiate the generic substitution laws at that same `h`. `observed` is the required conjugate of `ap_T(h)`, `observation` consumes `PathFamily.observation`, and the integer observation and erasure rejection follow through that connection. The detector is therefore attached to the admitted dependent argument, rather than to an unrelated two-loop algebra. No claim requires `apd_η(h)` itself to be nontrivial.

Univalence, HITs, and truncation support this external parameter construction. The generic argument does not thereby acquire those as source-language requirements. The report correctly allows a future model to provide another suitable parameter.

### Nonconstant transport

`Monodromy.agda` uses the pinned circle integer cover. The single-loop step increments an integer, and the two-loop computation is derived using generic `Memo.η`. The first projection of the full substituted pair is 3 for the selected input and 2 when the first loop is erased. Both full-pair and transported-witness substitution comparisons consume the generic results. This supplies the nonconstant observation in a separate allowed parameter instance.

### Substance of the missing construction

The missing theorem at `docs/research/dependent-higher-identity.md:196` is sufficiently concrete for the permitted outcome. It requires constructed higher families and sections, Grothendieck extension, reindexing, Σ and open Id, dimension closure, and arbitrary-motive contextual J with computation and substitution. These are obligations to build, not assumed fields used to obtain an apparent completed model.

I independently checked the displayed first test. For `B²ℤ`, the representable fiber has one object and integer arrows; the base 2-cell `m` acts by the natural transformation with component `m`. The displayed extension boundary gives a 2-cell from arrow `a` to arrow `b` exactly when `a = b + m`, so `m = a − b`. This preserves the selected second identity in the dependent family.

For a strict natural transformation from the constant endofunctor to the identity, its sole component `c` would satisfy `c = a + c` for every integer arrow. Setting `a = 1` contradicts cancellation. Allowing the appropriate 2-cell comparisons avoids that false strict equality. This is a concrete failed implementation shortcut. It does not prove the whole proposed model impossible, or prove its contextual J construction complete.

The successor milestones retain the unresolved pasting, section, β, substitution, and finite-tail obligations. They explicitly require interpreting this consumer, including its dependent pair, higher detector, and negative control. The report feeds the exact source contract to #315, model-route implications to #318, limits to #319, and the closed higher-adoption gate to #320. It does not resume #107, select #108's theorem, or activate #260.

## Validation status

**Established for this candidate's isolated source-test scope.**

I inspected the checked-in receipt, reproduction script, manifest, source closure evidence, and candidate-specific validation report `316-validation-d7d2beeea699bccc2f7eb0fee7f8fa52e6718186.json`. The latter records exact unchanged task blobs, authored inputs, archives, compiler pins, source hashes, and relevant repository inputs after integration. The supplied evidence supports reuse of the successful fresh run completed at `2026-11-04T23:37:08Z`.

The recorded command uses the pinned compiler, an explicit library registry, `--no-default-libraries`, `--safe`, `--no-allow-unsolved-metas`, `--no-allow-incomplete-matches`, and `--ignore-interfaces`. It exited 0. The closure comprises 229 fresh progress entries and six additional compiler-owned imports verified against setup source pins, totaling 235 modules. The candidate-specific artifact checks also cover log/graph identity, local links, Python compilation/help, and whitespace.

No specific concern warranted another full source check, so none was run by this reviewer. No integrated Lean source or shared build configuration changes are in scope; an integrated Lean build/audit is neither required for these isolated artifacts nor claimed.

Safe source checking trusts Agda and its cubical primitive rules. The library's `--no-import-sorts`, guardedness, and suppression of `UnsupportedIndexedMatch` are disclosed. The report correctly identifies the experimental indexed-inductive transport/conversion boundary documented by Agda. The import graph covers whole modules rather than minimal proof dependencies. This validation is not a Lean kernel audit, a semantics proof for Agda, or evidence that the Lean higher-adoption gate has passed. [Agda 2.8.0.2 indexed inductive types](https://agda.readthedocs.io/en/v2.8.0.2/language/cubical.html#indexed-inductive-types).

## Findings and disposition

No unresolved Spec findings. The remaining Lean construction is explicitly allowed as an owned successor by the frozen acceptance criteria, and the candidate supplies substantive mathematical and checked partial evidence for that disposition. Approval applies only to the candidate and scope above.

Base: `f0773fee8fa40214c67606c46ba8c41eed8e674b`. Candidate: `d7d2beeea699bccc2f7eb0fee7f8fa52e6718186`. Spec: **Passed**, 0 findings, worst severity none. Standards: not assessed by this reviewer.
