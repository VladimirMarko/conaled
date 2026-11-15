# Rounded recurrence: example correction 2 and focused pass

Source and this additive provenance are held for the existing whole-book loop.
This is the continuation of C03-039–044; all 83 Chapter 3 obligations remain.

## Exact candidate

- Candidate: `95406b83968e5b438e206c06f9797804664e0170`.
- Tree: `f3d740547c9e85689561647a9592737738e0230c`.
- Parent: `4badcd5a7cab38aed7ff6c178c0649ae8ec63228`.
- Original full-scope base: `c1cefe45f5e1b54ffa0fdd9e72b4a8a0c76b6fd5`.
- Branch/worktree: `work/fdsa-ch03-rounded-recurrence` / `conaled-ch02-natural-runs`.
- Local commit: `fix(examples): match rounded recurrence numeral casts (#174)`.
  Actual commit and staged whitespace check: `618ce3`, exit 0; command-local
  ChatGPT identity. Working tree clean.

Only Examples/RoundedRecurrenceBounds.lean changes: two local proof equalities
now use `((6 : Nat) : ℝ)` and `((21 : Nat) : ℝ)`, matching the exact unfolded
roundedQuarter equations. Nat.ceil_eq_iff and the original norm_num proofs
remain. No public header, expected result or recursive definition changes.
The file is 7,295 bytes / 162 LF lines, SHA-256
`18275f597cf579edf0db6785d0910e76dcc9cff084566ced73cd0da8828c0135`.

All 35 public headers are byte-identical to immediate parent 4badcd5. Across
the original 4e022bf candidate, only the already recorded root alpha rename
`prefix` to `hprefix` changes header text. Its mathematical premise and position
are unchanged. The current inventory includes that corrected header in full;
it does not claim byte identity with the old reserved-token spelling.

## Actual focused outcome

Root's exact-candidate attempt 3 passed both Bounds targets. Owned session
80278 is CLOSED with actual exit 0, terminal `731351`, root full-log/readback
closure `f03613`. The complete 2,065-byte outer log has SHA-256
`bbd749fe1f415ef0ae8e5de988be621811e798cc3b05f5d656fad7679586128f`.
The complete native body is 1,776 bytes, SHA-256
`b2431c8279058507d42cd91cfe096e02dda08066587e895673972674e1b31b0b`,
and matches the outer body at byte offset 133. This author read the complete
log, terminal, result and closure at `9a4c15` and rehashed them read-only.
Only the usual module-system import advisories occurred.

The focused targets are Applications.Resources.RoundedRecurrenceBounds and
Examples.RoundedRecurrenceBounds; the unchanged algebra prerequisite replayed.
This is focused elaboration, not the complete candidate check, proof audit,
actual-type inspection, either independent review or Chapter 3 acceptance.
The run's saved verification record is the prior accepted XR c1cefe45 record;
it is not a verification certificate for this new candidate. This successful
outcome supersedes the pending focus fields written before feedback arrived.

Both earlier failing attempts and the root's reserved-binder correction remain
intact. Attempt 2 had built the core and then failed only at the two literal
cast rewrites; its complete log was read at `0140fa`. All 32 prior implementation
and root-correction provenance files, and all attempt 2 run records, were
rehashed unchanged before and after the correction.

## Complete preserved formal scope

The four-module rounded package remains 35 public names: 34 theorems and one
noncomputable definition. No authored private declarations, anonymous examples
or instances were added. All other 33 authored declaration source blocks are
byte-identical to the immediate parent. Generated declarations still require
the later exhaustive audit.

The full sharp induction and exact cutoff, actual finite-prefix supremum,
source slope maximum, real existence and natural-valued corollary are retained.
Signed f, offsets, constant toll and intercept remain supported; the slope
threshold is nonstrict. No constants or hypotheses were weakened.

Every connected case remains: zero source witnesses/equality slope; negative
intercept and signed offsets; negative constant toll; the actual well-founded
roundedQuarter recurrence and values 1,6,13,48 at 0,5,6,21; its sharp bound
24n+6; its real and natural existential clients; and the precise noncontracting
affine-step obstruction. The scalar is not a selector or a measured cost.
The F recurrence and selector bridge remain separate original obligations.

## Prepared review and recovery inputs

- `statements35-inventory.json` rebinds all four source blobs, all 35 raw headers,
  and all source blocks to this candidate and the parent. Type-level let
  expressions in the exact-witness theorem headers are retained in full.
- `Statements35-candidate3.lean` contains the same complete ordered 35 explicit
  @ checks and supported printer settings; it names this candidate and remains
  unexecuted. Its SHA-256 is
  `835b572ba2f6e18d8ceeec53d7efe977d0eed3347ab223280e289d4e2bc346f3`.
- `statement-review.json` preserves the entire previous mathematical assessment
  and explicitly covers the alpha rename and the two proof normalization sites.
- `input-bindings.json` rechecks every previously bound source/instruction/API
  input, binds current source and program, and points to actual focus evidence.
- `root-attempt2-feedback.json` and `root-attempt3-feedback.json` retain exact
  failure/success scopes and complete saved-record identities.

No Lean/Lake/compiler, hydration, runtime or dependency change was performed
by this author. No GitHub mutations, pushes, canonical controls or tickets were
written. Root retains the sole compiler role and full acceptance workflow.
Only Nix is waived; all remaining gates stay mandatory. Final readback and
preservation identities are in `readback-and-hold.json`.
