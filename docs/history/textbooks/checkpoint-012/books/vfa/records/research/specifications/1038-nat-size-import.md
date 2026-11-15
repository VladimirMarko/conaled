# Local #1038 — explicit natural-size lemma import

Source: the user-authorized full VFA/conaled integration task and the completed
2026-11-04 fresh validation failure, recorded in
`validation/1037-fresh-failure.json`. This is a necessary cross-cutting correction
within the existing Preface/Perm implementation/review loop.

The fixed enclosing review base remains
`7c1b4a3fd55f9aeeab3fe7850e2d20000836bfcd`; the failing candidate is
`c988f183887896c00b09aaff9077a6ea7fb8d68f`. The clean source file
`Examples/IndefiniteService.lean` is byte-identical to its fixed-base version.
Its existing unbounded-bit-size example refers to `Nat.size_pow`, defined by
the exact pinned Mathlib in `Mathlib/Data/Nat/Size.lean`, without importing that
module. The actual fresh run reported an unknown identifier at module 603 after
602 successful ordinary module compilations; it produced no fresh verification
record and did not reach the exhaustive audit.

## Required correction and acceptance

- Add the explicit `Mathlib.Data.Nat.Size` import to the example.
- Preserve every existing theorem statement, proof body, case and assumption.
  The intended claim remains that no natural number bounds the bit-size of all
  natural numbers, using the witness `2 ^ bound` with size `bound + 1`.
- Retain exact Lean/Mathlib pins and the unchanged native kit. Extend the
  candidate-specific dependency acquisition roots and closure for this explicit
  import; do not claim the old 671-root inventory covers changed source.
- Perform a focused check of the existing failing proof with its required
  import, then establish a new full fresh build/audit and all retained formal
  gates for the corrected immutable candidate. Focused evidence is not a gate
  replacement and prior partial runs cannot be combined into full success.
- Both existing independent review axes assess the full enclosing candidate,
  reusing unchanged-source analysis and reviewing this additional file and
  relevant validation inputs. Keep ST-002 and SP-VAL-001 open until their actual
  completed evidence supports resolution.
- Keep source, failure and correction evidence, local tickets and environment
  instructions in small immediately uploaded recovery checkpoints. No GitHub
  writes and no next-chapter implementation before prior acceptance.
