# XR01-ELAB-001 — absolute-value parser correction

## Immutable successor

Candidate **`c1cefe45f5e1b54ffa0fdd9e72b4a8a0c76b6fd5`**, tree **`b62fe504a38948e61c6377a4e7661b639c28c08c`**, is a clean local successor of **`4df3bc95b96342250c9b3ff946773449e308e11b`** on `work/fdsa-affine-integration` in the same author worktree. Accepted Chapter 2 remains `2da5708478a1d943a9214b5b386ec2db16cd9eca`. The prior five-path preparation package, both earlier 21 inputs, original draft and all original requirements/findings remain unchanged.

The exact source delta is one removed ASCII space in `Examples/AffineRecurrence.lean` at line 108:

```diff
-    -((2 : Int) ^ 2) ≤ 0 ∧ | -((2 : Int) ^ 2)| = 4 := by
+    -((2 : Int) ^ 2) ≤ 0 ∧ |-((2 : Int) ^ 2)| = 4 := by
```

This touches the written theorem header, so it is not described as a proof-body-only edit. The name, integer argument, nonpositive inequality, conjunction, absolute-value intention, expected value four and `norm_num` proof remain the same. All 21 public names, every other header/body, imports/options and all other parent paths are unchanged. The core still has the original d64 blob.

The example file changes from 5,165 to 5,164 bytes, retaining 142 lines. Its new blob is `a370ee598cb5f43a1ea9af2560cec30d053ed708`, SHA `6734b0a54ffdcf81de3c3ec2520618011aa8bab357690c6cca6117174ec4abcf`. Full before/after identity and the actual local commit result are retained in this package; `source.diff` is the complete change.

## Actual diagnostic and pinned syntax

The root-owned focused command at 4df closed with actual exit 1, owned terminal `40f51a`; its core built in 5.9s but the example target failed. The complete 3,800-byte outer log has SHA `6d0b02515abb300fef8abf747e3845ee091ce3ec6281506c093c3c1aa16b0a53` and contains one error header: `Examples/AffineRecurrence.lean:108:27: expected no space before`. The complete log, closed reconciliation, recorder result, native start/result and actual owned terminal were read. These records retain the aggregate failure and do not establish a complete XR pass.

Pinned Mathlib revision `56a005855ea17e0b0958f73ec801ae140b0a1679`, `Mathlib/Algebra/Order/Group/Unbundled/Abs.lean:43`, declares:

```lean
macro:max atomic("|" noWs) a:term noWs "|" : term => `(abs $a)
```

The `noWs` following the opening bar requires adjacency to the argument. Removing that space supplies the intended absolute-value syntax without changing its expression. The complete source file hash and exact read boundary 29–48 are bound in `before-and-diagnosis.json`. No parser, Lean, Lake, compiler or cache command was run by this author. Stock import warnings remain in the actual log; no warning setting, module mode or linter was changed.

## Rebound complete type inspection

The separate **`Statements21.lean`** in this correction package is prepared, unexecuted, and binds `c1cefe45f5e1b54ffa0fdd9e72b4a8a0c76b6fd5`. Compared with the held 4df program, only the candidate in its preparation comment changes. Both imports, all 21 explicit-`@` commands and all six approved printer options are byte-identical. The original 1,474-byte draft program remains intact.

`statements21-inventory.json` binds all 21 names to the corrected source blobs and retains the complete original five-path scope. Only position 18's raw header changes; its new header SHA is `5760846efc5140d1c9fc2d4b71e9f107608a53f5f1c544cbd09f442ca1e7e747`. The one-byte header change is recorded explicitly; no actual printed-type equality is assumed. Pinned option semantics remain in the held original preparation's `printer-option-source.json`, linked by exact hash. Actual output must still be checked for omissions and diagnostics.

The required focused targets remain `Applications.Resources.AffineRecurrence` and `Examples.AffineRecurrence`. Root alone owns subsequent serial native compilation and receiving-input capture. This successor still needs its actual focused results, complete 21 types, applicable full guarded check/audit, both original full-scope axes and immediate candidate verification before any accepted integration. No type/full-check/acceptance credit is granted here.

## Readback and hold

The entire 142-line source was read before the repair, and the complete corrected source plus exact diff and rebound input are read back before the final receipt. Every other source byte is mechanically equal to the parent. All 19 payloads and receipt of the initial preparation were rehashed before modification and remain held. The correction is a new Conventional Commit with command-local `ChatGPT <chatgpt@openai.com>` and issue 174; no old commit was rewritten.

All source and this correction package are held after final readback. No accepted-ref, global-control, ticket/review, runtime, dependency, compiler-output or prior-record mutation is included.
