# Felix independent caller trial, issue 25

All three task files checked under the assigned environment. Formal source was frozen after round 9. Fresh reproduction with `--ignore-interfaces` and independent review remain coordinator work; this report does not claim those checks have happened.

The first clock observation immediately after task receipt was 2026-11-11 15:17:57 UTC. Round 9 finished at 15:26:06.561792 UTC, 489.561792 seconds later. There were no waiting exclusions, coordinator interventions, delegated work, external research, or other-route reads. Reporting after source freeze is recorded separately in the append-only log. The coordinator's receipt timestamp can conservatively refine the start observation. Nine actual source-feedback rounds were used, against the 60-round and 180-minute limits.

## Artifacts and checked status

| Task | First attempt | Final author check | Scope |
| --- | --- | --- | --- |
| 1 | Round 1 checked `Core.agda`; the first full package attempt, round 2, failed on implicit summand dimensions | Round 3, exit 0 | Raw natural matrices, finite-sum action, local preservation, library-transported category/cartesian laws, non-strict dimension-to-type comparison |
| 2 | Round 4 failed on a missing ambient map instance in a public field projection | Round 5, exit 0 | Public functor, comparison and cartesian-preservation composition; arbitrary matrix/vector action and product observations |
| 3 | Round 6 failed on positional hidden constructor arguments | Round 9, exit 0 | General comma with distinct matrix/function sources, doubling connectors, universal shear/swap squares, both composition orders, and arbitrary-dimension products/projections |

`Core.agda`, `Task1.agda`, `Task2.agda`, and `Task3.agda` are final source. `result.json` records their SHA-256 hashes, line counts, pins and timing. `snapshots/01` through `snapshots/09` retain frozen source for every compiler invocation and full `compiler.log` files. `attempts.jsonl` records exact checker commands, hashes, start/end timestamps, exit statuses, repair notes and the stop decision. `run.py` is the original caller-written evidence harness. Noncompiler reading and editing are described in notes and in the session tool transcript; the artifact log is not a complete timestamped transcript of every shell read.

Each author invocation used this command shape, replacing the final filename as recorded in the log:

```sh
nix develop /home/vlad/Code/felix --command agda --no-libraries \
  -i /tmp/conaled-wave-20261111/25-authors/felix-output \
  -i /tmp/conaled-wave-20261111/25-authors/felix-baseline/src \
  -i /tmp/conaled-wave-20261111/25-environment/stdlib-src \
  /tmp/conaled-wave-20261111/25-authors/felix-output/Task3.agda
```

The assigned manifest identifies Agda 2.8.0, standard library 2.3 and Felix `6f36d28097db7ea5f5df3263db3e8be08f74e490`. Protocol and manifests were read at `71bf7817b7383821f04ed3c85ea88ec920cc153a`. Author iterations reused matching interfaces. No production source, interface definition, dependency pin or tooling configuration was changed. Generated Agda interfaces were written by the checker. Full standard-library `UnsupportedIndexedMatch` warnings are retained; they concern Cubical transport computation. All four caller modules use `--safe --without-K`, with no holes, admissions or postulates.

## Encoding and equality

The protocol permits equivalent finite-index encodings. Here `V n = Vec ℕ n`, an inductive finite vector, rather than the literal function type `Fin n → ℕ`. `Core.toCoordinates` is lookup and `fromCoordinates` is tabulation. `coordinates-roundtrip` proves the function roundtrip pointwise at every finite index; `vector-roundtrip` proves the vector roundtrip by propositional equality. Both reuse named pinned standard-library theorems. This avoids introducing function extensionality.

Matrices are vectors of rows: `Mat n m = Vec (V n) m`. `dot` recursively sums all coordinate products. `act` applies that dot product to each row. `compose b a` forms each output row as the finite linear combination of rows of `a` with coefficients from a row of `b`, the usual natural-number matrix product. No entry-equality recovery is used.

`Dim n m` wraps an arbitrary total function `V n → V m`; there is no linearity restriction on these arrows. Its semantic equivalence is pointwise propositional equality of output vectors. Matrix equivalence is induced through `act`, again pointwise over every input vector. The final category is Felix's ordinary types/functions category with pair products. This experiment does not claim to retain the literal function representation of coordinate vectors or postulate extensional equality of Agda functions.

## One-time setup and provenance

All caller definitions and proofs were authored during the trial. No existing application example was copied. Imported Felix definitions and proofs are consumed through public APIs. Pinned Nat arithmetic and Vec conversion/append lemmas are identified by the source imports and proof terms.

`Core.agda` has 102 lines including comments and whitespace. It supplies the vector conversion, zero/add/scale/dot operations, matrix operations, finite arithmetic preservation lemmas, and split/join. The local facts are `shuffle`, `dot-zero`, `dot-add`, `dot-scale`, `dot-combine`, `act-compose`, `act-zero-prefix`, `act-identity`, `dot-append`, row-padding action lemmas, projection/pairing action, and both comparison inverse laws. These are application setup, not baseline generic infrastructure.

`Task1.agda` has 102 lines. Its raw `Category`/`Cartesian` records expose operations separately from equality and laws. `Homomorphismₒ`, `Homomorphism`, `H-equiv`, `CategoryH`, `ProductsH`, `StrongProductsH`, and `CartesianH` package the two interpretations. For both Dim and Mat, `MakeLawful.LawfulCategoryᶠ` and `LawfulCartesianᶠ` supply the general laws. `transported-assoc` and `transported-projection` consume those public law records; neither reproves the matrix laws directly. All terminal dimensions are zero and all dimension products are addition.

The dimension-to-type comparison uses append and take/drop. Its inverse proofs and projection preservation are substantive coordinate facts: the target pair product was not substituted for dimension addition. The matrix-to-dimension comparison is identity because those two categories share dimension objects and chosen products.

## Incremental work

`Task2.agda` has 48 lines. `_∘H_`, `_∘-CategoryH_`, `compose-ProductsH`, and `_∘-CartesianH_` build the composite. The composite comparison reduces to the already checked split/join comparison, so `dimStrong` supplies its inverse laws without another proof. This is specific to the first interpretation's identity comparison; no claim about arbitrary strong-comparison composition is made. Public preservation projections establish the action, composition, both product projections and simultaneous product observations. The only repair registered the composite map as an instance for those field projections.

`Task3.agda` has 105 lines. New caller work consists of the identity interpretation on the distinct type/function source; two-dimensional shear/swap functions and matrices; their local action and doubling-commutation proofs; and comma observations. `Comma _⇾_ Mat _⇾_` is the public general construction. `object n` has connector `scale 2` for every dimension. `L` and `R` retain distinct matrix and function fields. `C.comma-cat.comp` constructs both orders. Their commuting semantic statements come from the public `↻` field; matrix and function observations use public `f₁` and `f₂`. The closed examples establish `(1,2) ↦ (2,3)` and `(1,2) ↦ (3,1)` through the universal matrix/function agreement results.

`C.comma-products` constructs the product objects and projection squares under the supplied preservation/strength instances. All product-connector and projection observations quantify over arbitrary dimensions and vectors. The product's type-side object is `V n × V m`, while its matrix-side object has dimension `n + m`. Its connector doubles each part of the split input. This is a general comma caller, not a function-only or identity-connector specialization.

## Failures and repairs

Round 2 could not infer the two summands from their sum in `join-split`; explicitly supplying the dimensions fixed it. Round 4 required the ambient composite `Homomorphism` when projecting a `CategoryH` field, despite the map already occurring in the record's type. Round 6 interpreted positional hidden arguments of the re-exported comma constructor as universe parameters; naming `τ₁` and `τ₂` fixed it. Round 7 needed a second natural-number right-unit rewrite because multiplication by one and the trailing finite-sum zero each introduced `+ 0`. Round 8 could not recover the component comma connectors from a product object; explicitly supplying `a = object n` and `b = object m` to the public product projections fixed the remaining metas. An unused rewrite warning was removed in that same repair. All failed source and diagnostics are retained.

## Statement review and representation locality

The local arithmetic statements quantify over arbitrary lengths and vectors, including empty vectors. Matrix arrows have the required input/output orientation; `compose b a` acts as `b` after `a`. Identity, projection and pairing action proofs have the corresponding all-input conclusions. The two comparison inverse statements have opposite domains, vectors and pairs, and do not assume the desired equality. Induced equivalence compares actions, not matrix entries. Library transport therefore establishes semantic laws under the intended equivalence.

The concrete comma action proofs identify the shear and swap independently of the commuting-square condition. Their two numeric examples distinguish order. Doubling has an exercised nonidentity value `(1,2) ↦ (2,4)`. Product projection statements inspect both source fields and their commuting semantic squares. No new formal theorem is justified by an uninhabited premise or an unchecked placeholder.

Changing coordinate representation would affect the concrete definitions and local lemmas in Core, Task1's raw dimension operations/comparison and matrix interpretation, and Task3's pattern-based shear/swap/action proofs and coordinate observations. Task2's generic composition expressions depend on the packages rather than row representation; its concrete observation statements still mention `act`, append and split. The public comma composition calls and generic product construction likewise depend on packaged preservation, while the product observations depend on the coordinate interface. No production generic declaration was changed or recreated.

Each task is supported on the examined dimensions under the disclosed equivalent encoding and equality. No unsupported library capability was demonstrated, so there is no demonstrated-gap follow-up from this author. This is one author attempt; it establishes neither comparative productivity nor library-wide capability parity. Final acceptance requires the coordinator's fresh reproduction and independent Standards/Spec review of this scope assessment.
