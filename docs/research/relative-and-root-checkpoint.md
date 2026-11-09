# Exact And root checkpoint

Source base: 8a1dea6af52405878701d040c1646791913f9698.
Pinned ConLeche: 8e166ca53cd1f864b63c13cc1d326d38316d00ea, clean private copy.
The unchanged preserved phase files compiled into private output before this run.
No shared checkout or dependency graph edits.

AndAcceptanceRoot.root proves exactly:
`nestRoot (fueledOps .verified 32) indsResult.1 ctx holes ctorResult.1 {} = .ok rootResult`.
The names refer to the original AcceptanceStages.Reference and
AndPositivityStages definitions. rootResult's exact ctorNfs push, field kinds,
crest and other NestState fields are retained. `post` names the exact state;
ctors_one and root_one are equations of actual upstream functions, not an
alternate checker. Small joins handle levels, hi, constructor substitution,
structural depth/fuel, inferred sort and closing the field telescope.

Historical initial run reported exit 0 and whole-file 0.837155s in the tool transcript.
The development runner subsequently overwrote AndAcceptanceRoot.log. The timings
below are historical transcript observations without their original retained log;
they are not the final reproducible validation/timing record. Exhaustive current
module audit: 107 safe roots, only Quot.sound/Classical.choice/propext.

| Declaration | Proof generation | Checked declaration insertion | Type rendering | Tree nodes |
|---|---:|---:|---:|---:|
| constructors | 9.468165ms | 180.794978ms | 1.620624ms | 6964 |
| root | 2.601852ms | 0.239047ms | 0.619402ms | 141 |

Generation measures type/proof elaboration, synthetic-metavariable synthesis and
instantiation. Insertion uses Lean.addDecl with Elab.async explicitly false;
it validates the proof against the declared type, including kernel checking and
normal environment-insertion overhead. It is not just Kernel.check inference
without expected-type comparison. Rendering separately pretty-prints the type
with pp.deepTerms.threshold=3 and caps displayed characters at1024. Node count
is Expr.sizeWithoutSharing, a tree count, not a DAG/memory-size measurement.
Import/startup and other lemma work are only in whole-file wall time.

Preserved failures: AcceptanceComposition-initial.log (symbolic Except.pure
unfolding gap) and AndAcceptanceRoot-option-failure.log (unsupported pp.maxDepth
option; declarations checked but file failed, not claimed as successful). The
second clean run corrects the option. No root timeout occurred with symbolic
composition. Historical timeouts cannot be attributed to kernel cost from this.

Statement review: bind_ok composes actual Except successes for arbitrary types;
ctors_one requires actual nodup/crest/type/sort/field/guard equations and retains
the full pushed output state; root_one sequences exactly one member's constructor
list and final empty tail. Concrete constructors establishes all premises from
existing certificates and small joins. The root is fully closed, with no checker
success premise or output-agreement assumption. No axiom/native_decide shortcut.

This checkpoint proves only the exact And positivity root. It does not yet prove
the complete And installer, Exists, helpers, actual emitted declaration family,
final environment, model construction or Cached.checkDecls acceptance. Root is
audited before expanding to those tasks. Development uses inherited pinned
upstream outputs; final fresh isolated dependency closure remains required.
