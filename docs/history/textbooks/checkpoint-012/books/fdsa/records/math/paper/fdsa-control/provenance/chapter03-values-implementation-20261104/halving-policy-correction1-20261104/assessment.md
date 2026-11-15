# C03-HALVING-ELAB-001 — first actual compiler correction

Successor **41f46040eeaf1b2c6d21b00dec4c20b9d44c5ce7**, tree
**5a6ec07b60e37e7c87749a0b79d372a0b169310d**, directly descends from the
failed candidate e40d1f7fa71e51946b29bf1415067240e7cc369a. The full Chapter3
review base remains 2da5708478a1d943a9214b5b386ec2db16cd9eca. This is a
proof-only correction in the existing C03-080 loop, with all 83 Chapter3 rows
and every prior scope obligation retained.

## Actual evidence and diagnosis

The exact first focused attempt is recorded in
`provenance/chapter03-halving-policy-focused-attempt1-20261104/`.
Owned session67421 is CLOSED with actual exit1, terminal f871cf; root's
complete log/closure read is1fcd97. Author read the complete 10191-byte outer
log at6398ec and the complete closure, terminal, result and request atf057ba.
The outer SHA256 is
6f29382bcd15fad321b8c91bb776e08134ed40158f6d1bad08d27ac36b3029a4.
The native9884-byte body has SHA256
950b30502d058ad334e91858391e7ba2c4f096ef1261f127ce4d28cb98f72a58;
its exact bytes occur in the closed outer log at offset151. Both recorded
process exits are1. No historical session was polled.

The sole concrete source diagnostic is at
`Applications/Resources/HalvingSelection.lean:126:61`: the equal-branch
`simp only` list in `runWith_tariff` contains an unused `Nat.mul_one`.
This is an actual warning-as-error lint failure. It does not establish a
mathematical statement failure, and it does not establish success of the other
two requested modules, which remain to be checked. The inherited verification
record refers to accepted XR c1cefe45f5e1b54ffa0fdd9e72b4a8a0c76b6fd5 and
is not evidence for either C080 candidate.

The successor removes only `, Nat.mul_one` from that one simp argument list.
The other occurrences of `Nat.mul_one` in the two recursive branches are
unchanged. No linter, warning, proof restriction, mathematical assumption,
resource coefficient, definition or expected result was weakened. The full
740-byte patch is retained in `source.diff`.

## Full original-scope statement and case assessment

All60 public raw headers and their hashes agree exactly with the authoritative
v2 source inventory. This includes the complete `pivot_halving` header with
its named argument `(α := α)`, retaining the C03-HALVING-PREP-001 correction.
The same namespaces, universes, variables, imports and printing options are
preserved. All three definition blocks, all31 example theorem blocks and the
other59 declaration blocks are byte-identical. Only the proof block of
`Resources.HalvingSelection.runWith_tariff` changes.

The full original source/statement/case assessment in
`halving-policy-review-note.md`, with `halving-policy-review-addendum.md`,
continues to apply to all60 names. Its retained root source/binding reads
780ff9,7127a8,024c07 and1f3ce0 are not relabelled as independent acceptance
reviews or as compiler results for this successor.

In particular, the actual executor, pivot construction and index-length
observation are unchanged. The duplicate-aware halving claims, valid rank and
adequate administrative-fuel premises, separate entries and edges, actual
scan bounds and actual source tariff are unchanged. The uniform coefficients
still precede payload types, lists, fuel and ranks. Every original finite
expectation remains exact: size-eight calls147, size-seven calls111,
early-equal calls39, lower-branch calls57, duplicate calls44 and singleton
calls19 with one active invocation and zero edges. Empty and invalid value
semantics, growing range-family cases and the all-integer-input uniform
application are unchanged. No Nodup or element-domain assumption was added.

All18 prior authored source files, all nine exact received dependencies and
the two other C080 modules are byte-identical:29 other source files in total.
The old candidate, original failed log, original inventories including the
preserved preparation-method finding, original type input, original assessment
and all prior provenance remain intact. This correction does not alter shared
entrypoints, reconstruction maps, canonical controls, tickets or other agents'
sources. The authored inventory remains462 public names and seven named
private helpers; no new declaration was introduced. Generated/private roots
and received dependency sources remain in the later full audit scope.

## Immutable binding and remaining gates

`statements-inventory.json` binds the unchanged60 complete headers and the one
updated proof/source identity to this successor. It is a lexical source
inventory, not an emitted-type claim. `HalvingPolicyStatements-candidate2.lean`
changes only the candidate-identifying comment of the previous input; its
three imports, supported print options and all60 explicit `#check @name`
requests remain exact. The previous input is retained without relabelling.

The staged Git whitespace check passed and the source worktree is clean.
No author Lean/Lake, type capture, compiler, cache or environment command ran.
The corrected candidate is pending root's actual focused check of the same
three targets: Applications.Resources.HalvingSelection,
Applications.Resources.MedianPolicy and Examples.MedianPolicy. It has no
focused-success, full-check, exhaustive-audit, complete-type, independent-axis
or acceptance credit. Root remains sole serial qualified compiler owner;
all later immutable-candidate, full review and immediate-verification gates
remain mandatory. The author returns held after saving this handoff.
