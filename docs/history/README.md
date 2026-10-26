# Historical discussions and experiments

These files preserve ChatGPT discussions and supplied artifacts from the
repository's origins and later application explorations. They explain where
implementations came from and record ideas for further work. The original
documents are preserved unchanged.

## Origins

- [Orbifold artifacts](orbifold/README.md) preserve a discussion of synthetic
  orbifolds, simulation, and generalized gyrovector geometry, plus a numerical
  Python probe. The annotations link current research and distinguish the
  experiment from a verified implementation.
- [FRP artifacts](frp/README.md) preserve a pre-repository conversation, two
  untypechecked Lean drafts, explanatory notes, and a Python counterexample.
  The import note links the repaired, checked copies and records their limits.
- [compiling-with-squares-chat.md](compiling-with-squares-chat.md) records the first chat, which led to `CompilingWithSquares.zip`. That archive contained the source tree and `CompilingWithSquares.bundle`, the Git history on which this repository is based. The imported baseline is commit `ceb4d6a39032c3e15d5fc80bd60a02a955b08788`, also tagged `applications-v2`; the earlier `foundation-v1` tag was preserved too.
- [compiling-with-squares-possibilities.md](compiling-with-squares-possibilities.md) records a second ChatGPT Pro chat exploring the implementation and possible project directions. The Lean toolchain was unavailable in that session. Its claims about the code therefore carry less authority than a successful check of the relevant source revision.
- [denotational-design-source-register.md](denotational-design-source-register.md) comes from the same second chat and records research sources and design discussion. It gives its research date as 2026-10-13 and states that the uploaded Lean archive was inspected but not rebuilt.

During repository initialization, all 76 non-bundle files in the ZIP were compared with committed files and matched byte for byte. The bundle's history and both release tags were also preserved. This established that the archive's contents had been imported; it was not a new Lean build.

## Algorithm Design with Haskell (#149)

[Preserved textbook snapshots](algorithm-design-haskell/README.md) retain the
complete checkpoint 233 preview, its archive checksum and a per-file manifest.
The mathematical library, source correspondence and kernel experiments remain
available independently of the original Downloads location. The collection
records how to add a later snapshot and connect changed source declarations to
the reconstruction without replacing earlier evidence. See the
[assessment and reconstruction plan](../research/adwh-preview-233-assessment.md)
for current reuse recommendations and validation limits.

## Internal-language frontend experiment (#36)

[Frontend.lean](internal-language-frontends/Frontend.lean) preserves the checked
frontend comparison made on 2026-10-18 while decomposing
[#36](https://github.com/VladimirMarko/conaled/issues/36). It was developed against
repository revision `173be7d` with the pinned Lean 4.35.0 and Mathlib dependencies,
then copied unchanged from `/tmp/conaled-36-frontends/Frontend.lean`. The temporary
path in its embedded run command records its original location. To check the
preserved copy from the repository root, run:

```sh
direnv exec . lake env lean docs/history/internal-language-frontends/Frontend.lean
```

The experiment compares direct derivation constructors with a shallow interface
of named rules on graph composition. The shallow proof can produce an explicit
restricted derivation or target Set validity directly. It includes Set soundness,
substitution under binders, checked examples, a mixed-style ordinary relational
client, and statement review. Its local transitive axiom audit checks all
kernel-safe declarations owned by the file against the repository whitelist.
The original run checked 213 such declarations and passed.

This supports trying named rule lemmas over an explicit derivation core in the
first implementation slice. It does not settle the production interface: the
experiment is single-sorted, has only a subset of regular rules, and still exposes
variable indices. It supplies no presheaf interpretation, square comparison,
performance measurements, or proof of ordinary import-cost neutrality. See the
[current research note](../research/internal-languages-lean.md#first-experiment-internal-graphs-external-squares)
for the broader experiment's obligations.

This file is retained as design evidence, outside the public library and normal
source-coverage check, like the other historical Lean artifacts. Replacing its
code in a future implementation is not a reason to discard the comparison.

## How to use these records

The [reconciled extension list](../extensions.md) collects the possibilities
discussion into issue scopes, applying Prompt 2's corrections and Response 2's
reformulation. Use it instead of Response 1's superseded implementation sequence.

The discussions remain useful as evidence of what was asked, proposed, and reported in those sessions. They are starting points for understanding the project's motivation and investigating future directions. A proposal here does not by itself establish an adopted requirement or architectural decision for this repository.

Claims about implemented features, proofs, limitations, or verification results apply only to the version under discussion. The first chat describes successive stages of development, so even an earlier statement in that chat may have been superseded before the final archive. Check the corresponding source and Git history when relying on a claim. For claims about the current code, inspect and check the current revision with its declared Lean toolchain. Historical verification reports describe their original runs, not later changes.

The second chat's code assessments require particular care because that session could not run Lean. Its proposed directions can still inform design work, but feasibility and correctness need to be established when pursuing them.

The source register records the research available at its stated date. Follow its references and check the primary sources before relying on an attribution or technical claim; retrieval status and links can change. Chat-specific attachment links, including `sandbox:` links, refer to the original sessions and need not resolve from this repository.

The recovered Tabula white paper, WP003, is now [preserved locally with its provenance](../references/tabula/README.md). The source register's statement that PDFs were not bundled describes the original research package.

Keep these documents as historical records. Record later corrections, decisions, and verified results in current project documentation, with the relevant source revision or evidence, rather than rewriting the original discussions to describe today's state.
