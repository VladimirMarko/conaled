# Cousot and Cousot: abstract interpretation, 1977

This reference preserves the supplied scan and a corrected transcription of
**§§5–9 and Appendix 12** of Patrick Cousot and Radhia Cousot,
*Abstract Interpretation: A Unified Lattice Model for Static Analysis of
Programs by Construction or Approximation of Fixpoints*, POPL 1977, pp. 238–252.
The transcription is intended for reading and citation alongside the scan.
“Corrected” means OCR errors were checked and corrected; it does not mean the
paper's mathematics has been corrected or formally verified.

## Read the source and transcription

The [unaltered source PDF](source.pdf) remains authoritative. Page headings in
the transcription link to that PDF. Printed p. 238 is PDF page 2; the first PDF
page is the proceedings cover. A PDF viewer that ignores a `#page=` link can
use the page numbers in this table.

| Transcription | Printed pages | PDF pages | Coverage |
|---|---|---|---|
| [Sections 5–6](sections-5-6.md) | 240–243 | 4–7 | Abstract interpretations, typology, examples, consistency and deductive semantics |
| [Sections 7–8](sections-7-8.md) | 243–245 | 7–9 | Lattice of interpretations, proof and examples, evaluation, termination and performance analysis |
| [Section 9](section-9.md) | 245–250 | 9–14 | Increasing/decreasing approximation, widening, interval example and comparison of methods |
| [Appendix 12](appendix-12.md) | 251–252 | 15–16 | Hypotheses H1–H4, lemmas L1–L4, theorems T1/T2 and proofs |

The selected sections include their prose, equations, proof steps, examples
and diagrams. §§1–4, the conclusion, acknowledgements and bibliography are
available in the retained scan but are not transcribed here. The editorial
notation guide below identifies prerequisites from §§3–4. Original citations
such as `Tarski[55]` refer to the paper's bibliography on printed pp. 250–251.

The [source-inspection note](../../research/cousot-1977-source-inspection.md)
records our mathematical reading; the
[external comparison](../../research/external-language-comparison.md) records
proposed experiments. Neither is part of the authors' text.

## Transcription conventions

The transcription follows the scan's two-column reading order. Paragraphs
continue across page boundaries where necessary. Line wrapping, line-end word
division and ordinary spacing are normalized. Markdown headings and list layout
replace the printed layout; mathematical expressions use LaTeX. Original wording,
including awkward grammar and apparent mistakes, is retained. Editorial notes
are labelled explicitly and do not silently repair an argument.

- An overbar is represented by `\overline{...}` and a tilde by
  `\widetilde{...}`. Braces delimit the whole accented expression. For example,
  $\widetilde{\overline{\underline{\mathrm{Int}}}}$ retains the lift, abstract
  interpretation bar and identifier underline separately. A decorated order
  symbol is not replaced by an undecorated one.
- Visible source underlines are retained with `\underline{...}`. Their occurrence
  on identifiers and pseudocode words is not treated as permission to erase
  them. Underlining, overbars and tildes remain separate, even when a renderer
  spaces them differently from the typewritten source.
- Named identifiers use roman text in mathematics, with their original spelling.
  The small open-circle operation is written `\circ`; joins and meets printed
  as union/intersection shapes are written `\cup` and `\cap`. Widening is
  written `\nabla`, retaining the downward-triangle form. These are typesetting
  choices, not identification of differently named operations.
- The source's top and bottom glyphs use `\top` and `\bot`. The set of
  interpretations is written $\mathcal I$ to distinguish it from an individual
  interpretation $I$. The one-element interpretation on p. 244 has a T-shaped
  upper-bound glyph, rendered $\top_{\mathcal I}$; its sole element is the
  printed roman capital $\mathrm I$. See the local editorial note.
- Original diagram crops preserve geometry and faint marks. Their searchable
  descriptions are explicitly editorial; the crops decide any disagreement.
  Crops are rendered directly from the retained PDF, without redrawing or
  removing marks. [Figure provenance](figures/manifest.json) records source
  pages, crop coordinates and file hashes.
- `[Uncertain reading: ...]` flags an unresolved reading at its point of use.
  An apparent source error is labelled separately from OCR uncertainty.
  Plausibility of a mathematical correction is not evidence that the scan
  actually prints it.

The Markdown source remains readable without a math renderer, but viewing it
with LaTeX math support makes accent scope and nested formulas easier to inspect.
The original scan is the fallback for any rendering ambiguity.

## Notation prerequisites from earlier sections

This table is **editorial explanation**, not a transcription of §§3–4. It is
included so that the selected sections can be read without guessing what the
program-specific names mean. The page links lead to their definitions.

| Notation | Definition or role in the paper | Source |
|---|---|---|
| $2^S$; $S^0$ | $2^S$ is a set of subsets. $S^0$ adjoins bottom and top to a set, placing every original element between them. The superscript zero is not cardinality or iteration. | [p. 239, §3.2](source.pdf#page=3) |
| Nodes, Arcs | A finite flowchart has entry, assignment, test, junction and exit nodes. Arcs are ordered pairs of connected nodes. | [pp. 238–239, §3.1](source.pdf#page=2) |
| $\underline{\mathrm{origin}}$, $\underline{\mathrm{end}}$ | Source and destination node of an arc. | [p. 239, §3.1](source.pdf#page=3) |
| $\underline{\mathrm{a\text{-}pred}}$, $\underline{\mathrm{a\text{-}succ}}$ | Sets of incoming/outgoing arcs of a node; `a-succ-t` and `a-succ-f` name a test's true/false outgoing arcs. The source sometimes identifies a singleton set with its element. | [pp. 238–239](source.pdf#page=2) |
| Ident, Expr, Bexpr; $\underline{\mathrm{id}}$, $\underline{\mathrm{expr}}$, $\underline{\mathrm{test}}$ | Identifier/expression categories; the assigned identifier, right-hand expression and Boolean test belonging to the corresponding node. | [p. 239](source.pdf#page=3) |
| Values, Env | Values is a semantic lattice. $\mathrm{Env}=\mathrm{Ident}^0\to\mathrm{Values}$ holds identifier bindings. | [p. 239, §3.2](source.pdf#page=3) |
| I-states; $\underline{\mathrm{n\text{-}state}}$ | Initial states; the deterministic next-state function. Its superscript $n$ means repeated function application. | [pp. 239–240](source.pdf#page=3) |
| Contexts, Context-Vectors | $\mathrm{Contexts}=2^{\mathrm{Env}}$ collects sets of environments at a program point. A context vector assigns a context to each arc, with domain $\mathrm{Arcs}^0$. | [p. 240, §4](source.pdf#page=4) |
| $\underline{\mathrm{n\text{-}context}}$, $\underline{\mathrm{F\text{-}cont}}$ | The former computes one arc's context from a context vector. The latter packages those results into a context-vector functional. | [p. 240, §4](source.pdf#page=4) |
| $\widetilde f$ | Pointwise lift of $f$ to arc-indexed vectors; tilde scope identifies exactly what is lifted. | [p. 242, §6](sections-5-6.md) |
| $\alpha$, $\gamma$ | Abstraction and concretization maps with the paper's stated monotonicity, retraction, extensivity and transfer hypotheses. | [§6](sections-5-6.md), [Appendix H2/H3](appendix-12.md) |

## Provenance and verification scope

- Public source: [author-hosted PDF](https://www.di.ens.fr/~cousot/COUSOTpapers/publications.www/CousotCousot-POPL-77-ACM-p238--252-1977.pdf).
- [Author's bibliographic page](https://www.di.ens.fr/~cousot/COUSOTpapers/POPL77.shtml).
- The user supplied this scan; it was preserved without modification on 2026-11-04.
- File size: 941,105 bytes; 16 PDF pages.
- SHA-256: `5d2956eed13b2d40f6e15c2087fb870c3dea54a332fe46ee07cea608ca417238`.

The PDF has no text layer. Tesseract 5.5.2 drafts were used for navigation,
then the retained text and formulas were compared with Poppler 26.06.0 page
renders, using enlarged crops for ambiguous marks. OCR drafts are not retained
as evidence of correctness. Page references, math syntax, links and asset hashes
receive mechanical checks; those checks do not verify mathematical truth.
Source-comparison review checks transcription fidelity separately from the
paper's correctness. Local uncertainty annotations remain part of the result.

This is a third-party source and a transcription of it. Copyright remains with
the original rights holders; no repository license is granted for the paper,
its extracted diagrams or transcribed text. Editorial explanations and research
assessments are identified separately.
