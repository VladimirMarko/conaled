# Denotational design: research source register

Research date: 2026-10-13.

This is a source register and architectural decision record, not a modified or newly verified Lean release. The uploaded Lean archive was inspected but not rebuilt. URLs below are research locators; linked PDFs are not bundled. “Full text recovered” means the web research tool retrieved the document, not that its bytes were downloaded into this package. Retrieval failures do not imply that a document is unavailable elsewhere.

## 1. Tabula white papers

| Document | Date / identifier | Retrieval status | Locator |
|---|---|---|---|
| Spacetime Architecture | 2010; vendor listing published 2010-03-16 | Vendor-authored title and abstract located; complete original white paper not recovered | https://www.eetimes.com/spacetime-architecture/ |
| A Cost Effective Way to Design Next Generation Communications Infrastructure Equipment | 2010; vendor listing published 2010-03-16 | Vendor-authored title and abstract located; complete paper not recovered | https://www.eetimes.com/a-cost-effective-way-to-design-next-generation-communications-infrastructure-equipment/ |
| Challenges of High-Speed Ethernet at 100G, 400G and Beyond — The Spacetime Perspective | Tabula, 2013; WP003, V1.0; Marc Miller and Danny Thom | Full 32-page PDF recovered; architectural diagrams inspected | https://web.archive.org/web/20130525050113if_/http://www.tabula.com:80/products/pdf/WP003.pdf |
| Timing Closure Made Easier with Stylus Software | WP004 | Title and official product-page description recovered; PDF retrieval failed | Original: http://www.tabula.com/products/pdf/WP004.pdf |
| The System Validation Challenge White Paper | DesignInsight_WP.pdf | Listed on archived official DesignInsight page; PDF retrieval failed | Original: http://www.tabula.com/technology/pdf/DesignInsight_WP.pdf |
| How Reducing Verification and Validation Time Can Improve Profitability | Semico / Tabula DesignInsight | Listed on archived official DesignInsight page; PDF retrieval failed; business/verification context rather than core architecture | Original: http://www.tabula.com/technology/pdf/Semico%20Tabula%20DesignInsight_WP.pdf |

This is the identified public core corpus, not a claim to have recovered every customer-portal, internal, or revision-specific document.

### Official pages supporting the register

- Archived company home: https://web.archive.org/web/20150324001331/http://www.tabula.com/
- Architecture: https://web.archive.org/web/20150325182938/http://www.tabula.com/technology/technology.php
- ABAX2: https://web.archive.org/web/20150305091833/http://www.tabula.com/products/abax_22nm.php
- Stylus, including WP004 listing: https://web.archive.org/web/20150328204454/http://www.tabula.com/products/stylus.php
- DesignInsight, including both white-paper listings: https://web.archive.org/web/20150318022424/http://www.tabula.com/technology/designinsight.php

### Supplementary architecture material — not all white papers

- Tom R. Halfhill, *Tabula’s Time Machine: Rapidly Reconfigurable Chips Will Challenge Conventional FPGAs*, Microprocessor Report, 2010-03-29. Full 14-page vendor-hosted reprint recovered. **Secondary reporting, not a Tabula-authored architecture specification.** https://web.archive.org/web/20150108233323if_/http://www.tabula.com/news/M11_Tabula_Reprint.pdf
- Steve Teig, *Function, Latency, Bandwidth, Power: Towards A Better Computer*, ICS 2013 keynote. Official abstract recovered. https://www.ics-conference.org/archive/ics2013/keynote.php.html ; DOI: 10.1145/2464996.2465447
- Steve Teig, FPL 2012 keynote slides. Search-indexed locator; full retrieval failed: https://www.fpl2012.org/Presentations/Keynote_Steve_Teig.pdf
- Conal Elliott, *Haskell to hardware via CCCs*, 2013. Author’s account: https://conal.net/blog/posts/haskell-to-hardware-via-cccs/
- Conal Elliott, *From Haskell to Hardware via CCCs*, 2014 slides: https://www.cs.ox.ac.uk/ralf.hinze/WG2.8/32/slides/conal.pdf
- ABAX Product Family Overview / brochure. Locator only, PDF not recovered: http://www.tabula.com/products/Abax_ProductBrochure.pdf
- DesignInsight brochure PB030. Listed on official page; PDF not recovered: http://www.tabula.com/technology/pdf/PB030.pdf

### Primary technical patent disclosures

These are technical research sources, not a patent-clearance or legal-status assessment.

- US7342415B2, *Configurable IC with interconnect circuits that also perform storage operations*. Full text retrieved. https://patents.google.com/patent/US7342415B2/en
- US7872496B2, *Method of mapping a user design defined for a user design cycle to an IC with multiple sub-cycle reconfigurable circuits*. Full text retrieved. https://patents.google.com/patent/US7872496B2/en
- US20150040094A1, *Sequential delay analysis by placement engines*. Full text retrieved. https://patents.google.com/patent/US20150040094A1/en

## 2. FPGA overlays and functional-language processors

- *An Area-Efficient FPGA Overlay using DSP Block based Time-multiplexed Functional Units* (2016). Full PDF and results table inspected. https://arxiv.org/abs/1606.06460 ; https://arxiv.org/pdf/1606.06460
- Craig Ramsay and Robert Stewart, *Heron: Modern Hardware Graph Reduction*, IFL 2023 proceedings, published 2024. Full paper and evaluation inspected. https://pure.hw.ac.uk/ws/portalfiles/portal/141745379/3652561.3652564.pdf ; DOI: 10.1145/3652561.3652564
- *Cloaca: A Concurrent Hardware Garbage Collector for Non-strict Functional Languages*, Haskell 2024. Official abstract retrieved; full PDF not recovered in this session. https://researchportal.hw.ac.uk/en/publications/cloaca-a-concurrent-hardware-garbage-collector-for-non-strict-fun/ ; DOI: 10.1145/3677999.3678277
- *From Haskell to a New Structured Combinator Processor* (KappaMutor), TFP 2025. Author’s summary retrieved; full paper not recovered in this session. https://cramsay.co.uk/publications/kappa_mutor/ ; DOI: 10.1007/978-3-031-99751-8_7
- *Ouros: A Dataflow-Driven Processor for Lazy Functional Programming Languages*, ASAP 2026, published 2026-09-23. Official abstract and bibliographic record retrieved; linked full PDF failed to load. https://researchportal.hw.ac.uk/en/publications/ouros-a-dataflow-driven-processor-for-lazy-functional-programming/ ; DOI: 10.1109/ASAP71856.2026.00023
- Ouros artifact listing: https://researchportal.hw.ac.uk/en/datasets/dataset-for-ouros-a-dataflow-driven-processor-for-lazy-functional/ ; DOI: 10.17861/e2cb3082-8753-4296-9ccf-de4b0fcc80bd . Listing retrieved; artifact not executed.
- Project publication index: https://haflang.github.io/publications.html

Benchmark interpretation: compare identical workloads, precision, I/O conditions, and baselines. Distinguish clock frequency, initiation interval, latency, throughput, resource use, and GC overhead. The cited papers do not establish one universal FPGA-overlay slowdown.

## 3. Felix and denotational architecture

The following `main` files were inspected during this research. A future parity audit must pin a commit; this register does not pretend the moving branch URLs constitute a reproducible revision pin.

- README: https://raw.githubusercontent.com/conal/felix/main/readme.md
- Raw structures: https://raw.githubusercontent.com/conal/felix/main/src/Felix/Raw.agda
- Laws: https://raw.githubusercontent.com/conal/felix/main/src/Felix/Laws.agda
- Homomorphisms: https://raw.githubusercontent.com/conal/felix/main/src/Felix/Homomorphism.agda
- Law transport: https://raw.githubusercontent.com/conal/felix/main/src/Felix/MakeLawful.agda
- General comma construction: https://raw.githubusercontent.com/conal/felix/main/src/Felix/Construct/Comma/Type.agda
- Comma module: https://raw.githubusercontent.com/conal/felix/main/src/Felix/Construct/Comma.agda
- Haskell Interlude episode 62 transcript: https://haskell.foundation/podcast/62/
- Type Class Morphisms: https://conal.net/papers/type-class-morphisms/
- Compiling Embedded Languages: https://conal.net/papers/jfp-saig/
- Timely Computation: https://conal.net/papers/timely-computation/paper.pdf

Parity means supported structures, morphisms, equivalences, and proved laws—not copying API spellings or treating unfinished upstream interfaces as completed theorems. Felix's raw feedback operation requires a well-formedness witness. Its generic closed-structure law transport still contains TODOs. These facts require distinct entries in a parity matrix.

## 4. Higher-order calculus and integration

- Conal Elliott, *Higher-order, higher-order automatic differentiation*. Early incomplete draft: https://conal.net/papers/higher-order-ad/
- Mathieu Huot, Sam Staton, Matthijs Vákár, *Correctness of Automatic Differentiation via Diffeologies and Categorical Gluing*: https://arxiv.org/abs/2001.02209
- Mathieu Huot, Sam Staton, Matthijs Vákár, *Higher Order Automatic Differentiation of Higher Order Functions*: https://arxiv.org/abs/2101.06757
- Matthijs Vákár, *Reverse AD at Higher Types: Pure, Principled and Denotationally Correct*: https://pmc.ncbi.nlm.nih.gov/articles/PMC7984537/
- J. R. B. Cockett and J.-S. P. Lemay, *Integral Categories and Calculus Categories*: https://arxiv.org/abs/1707.08211
- G. S. H. Cruttwell, J.-S. P. Lemay, Rory B. B. Lucyshyn-Wright, *Integral and differential structure on the free C-infinity-ring modality*: https://arxiv.org/abs/1902.04555

Mathlib interfaces to audit against the project's pinned release, not assume present from current documentation:

- https://leanprover-community.github.io/mathlib4_docs/Mathlib/Analysis/Calculus/IteratedDeriv/Defs.html
- https://leanprover-community.github.io/mathlib4_docs/Mathlib/MeasureTheory/Integral/Prod.html
- https://leanprover-community.github.io/mathlib4_docs/Mathlib/MeasureTheory/Integral/IntervalIntegral/FundThmCalculus.html

## 5. Proposed decision record — not implemented changes

1. Defer new surface syntax and product-specific toolchains. Agents can construct existing typed objects.
2. Prioritize a commit-pinned Felix capability/proof matrix and general representation/law-transport infrastructure.
3. Keep exact mathematical denotations separate from executable representations and their certified error or observation relations.
4. Do not impose fixed-width words, global clock ticks, graph reduction, one graph IR, ready/valid, or a particular storage discipline on the core.
5. Treat real-time signals, causal event models, clocked streams, and physical communication assumptions as explicitly related models, rather than silently equating them.
6. Require well-posedness or causality evidence for feedback. The mere availability of categorical composition does not establish arbitrary feedback validity.
7. Keep graphs, bitvectors, protocol adapters, schedules, and FPGA overlays as optional representations/experiments.
8. Develop general higher-order derivatives and integration from exact semantics, with explicit smoothness, integrability, domain, and computability hypotheses.
9. Distinguish smooth functions from analytic functions: an infinite jet at one point need not determine a smooth function nearby.
10. Evaluate architecture families and certified transformations before selecting an expensive end-to-end hardware product.

Unresolved: complete original 2010 Tabula white papers; WP004 and DesignInsight full texts; full Ouros/KappaMutor review and reproducible benchmarks; exhaustive Felix parity audit; full physical cost models; executable general analytic realizers. None of these is claimed completed here.
