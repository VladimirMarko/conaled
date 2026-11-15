# Phase A source and exposure log

Researcher: `/root/coherence_discovery`. Date: 2026-11-04. Output: `292-external-memo.md` in this directory. This log accompanies the freeze; the hash manifest is separate to avoid a self-referential hash.

## Exposure boundary

The first file read was `/tmp/conaled-291-294/specs/292-external-brief.md`. Before that read, the researcher had the task assignment and the session's user-supplied `AGENTS.md` instructions and environment metadata. These disclose the repository name and location, that it is a planned Lean monorepo extending Conal Elliott's work, procedural skill names, and documentation paths. The assignment itself names local universes and requests an independent comparison. These are unavoidable prior exposures; this is not a statistically blind process.

The only repository files read during Phase A were the generic procedural resources explicitly allowed by the assignment:

- `.agents/skills/research/SKILL.md`
- `.agents/skills/no-ai-slop/SKILL.md`
- `.agents/skills/no-ai-slop/references/ai-writing-detection.md`

No repository implementation, domain/architecture documentation, README, tracker issue, orchestration specification, historical example, existing shortlist, or other agent's memo was read. No project command or implementation was run. No shared worktree file was changed. The output files were written outside the repository as instructed. The background research assignment fulfills the research skill's delegation step; no recursive implementation loop or sub-agent was started.

The dependent transport example and its two substitutions were formulated before choosing a candidate local representation. Source discovery then verified the transport lemma and compared the semantic accounts. The supplied brief's mention of local universes influenced the search terms and candidate set.

## Primary sources actually consulted

| Source | Consulted material | Use and limitation |
|---|---|---|
| [Lumsdaine–Warren, Local universes](https://arxiv.org/pdf/1411.1736) | Definitions 3.1.1–3.1.3; Theorem 3.4.1; Lemma 2.4.2; §4.1 | Exact construction hypotheses and transfer limitations. The author-hosted PDF returned HTTP 502; arXiv full text succeeded. |
| [Awodey, Natural models](https://arxiv.org/pdf/1406.3219) | §1; Proposition 20; Theorem 32 and Remark 34 | CwF/presheaf interface and identity-structure obligations. General construction is explicitly related to LU, so not treated as independent evidence for another strictification theorem. |
| [Kapulkin–Lumsdaine, Simplicial model](https://arxiv.org/pdf/1211.2851) | §§1.3–1.4; constructor and universe results; model statement | Fixed-universe contextual construction and higher model existence. Used arXiv v5, 2018, rather than attributing the three-author 2014 draft as the final paper. |
| [Clairambault–Dybjer, Biequivalence](https://arxiv.org/pdf/1112.3456) | Introduction; CwF and pseudo-morphism discussion; statement of the extensional correspondence | Boundary of LCCC equivalence claims. Not used as evidence for unrestricted intensional equality. |
| [Hofmann–Streicher, Groupoid interpretation](https://people.csail.mit.edu/jgross/personal-website/papers/academic-papers-local/agroupoidinterpretationoftypetheroy.pdf) | Identity interpretation; §5.1 UIP countermodel | Primary paper hosted by a third party. Integer-action test is the researcher's chosen specialization. |
| [HoTT Book, first-edition-82-g578b85c](https://hott.github.io/book/hott-online-82-g578b85c.pdf) | Lemma 2.3.9; Corollary 8.5.2 | Transport composition and a known higher witness setting. The book's theorem concerning spheres has additional assumptions, kept separate from the generic identity-elimination derivation. |
| [Bauer–Haselwarter–Lumsdaine, General definition](https://arxiv.org/pdf/2009.05539) | Definitions 5.12, 6.20 and surrounding metatheorem discussion | Rule admission requirements. No claim that all the paper's metatheorems were mechanically verified. |
| [Warren, Strict ω-groupoid interpretation](https://mawarren.net/papers/crmp1295.pdf) | Abstract and available full-text access | Considered an alternative higher-dimensional setting. Not relied on for the final example or a detailed theorem claim. |
| [Dybjer, Internal type theory](https://www.cse.chalmers.se/~peterd/papers/InternalTT.pdf) | Search-index abstract | Direct PDF returned HTTP 403. No detailed theorem was attributed to inaccessible text; Awodey's accessible primary paper supplied the CwF connection. |

Search results also exposed third-party summaries, Wikipedia/nLab-style entries, bibliographic indexes, and a 2026 path-category paper. Those were not used as authority for the memo's technical claims. The 2026 paper was not investigated enough to make its comparison a recommendation.

## Query log

Queries were issued in the following thematic order, with exact query strings retained here:

1. `Lumsdaine Warren local universes model overlooked coherence construction dependent type theories LF theorem`
2. `Hofmann 1994 interpretation type theory locally cartesian closed categories split fibrations coherence`
3. `Kapulkin Lumsdaine simplicial model univalent foundations theorem dependent type theory coherence`
4. `Dybjer internal type theory categories with families 1995 pdf`
5. `Hofmann Streicher groupoid interpretation type theory pdf`
6. `Hofmann interpretation type theory locally cartesian closed categories pdf 1995`
7. `Awodey natural models homotopy type theory representable natural transformation pdf 2014`
8. `site.homotopytypetheory.org "Lemma 2.3.9"`
9. `site.arxiv.org "strictification" "pseudo-stable" "type" Gambino Larrea`

After search discovery, direct opens and in-document searches were used to inspect theorem statements and definitions. Some tool responses included irrelevant secondary results. Claims in the memo link directly to primary sources. No search snippet was used to strengthen an unverified theorem statement.

## Validation and limits

The memo is a read-only architecture investigation. No Lean build, proof audit, or implementation review was appropriate at this stage, and none was attempted. The formulas, substitution directions, and separation of generic assumptions from example-model assumptions received manual review. The proposed judgment-interpretation theorem is labeled an obligation rather than reported as established. Exact supporting source locations are included, and access failures are disclosed above.

The memo and this log are frozen by their SHA256 values in `292-external-freeze.sha256`. Any later local-context analysis must be a separate artifact; these frozen files must not be revised to match project history.
