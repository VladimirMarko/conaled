# Alternatives assessed before interface design (#461)

The frozen contracts are in [construction-transport-contracts.md](construction-transport-contracts.md).
This comparison precedes the new formal experiments.

[Hinze, Wu and Gibbons, *Unifying Structured Recursion Schemes*, §§3–5](https://www.cs.ox.ac.uk/jeremy.gibbons/publications/urs.pdf)
derive adjoint folds using an adjunction and a distributive law. Their treatment
includes accumulating folds and distinguishes inductive from coinductive data.
This is a candidate for unifying future recursion frontends, including richer
contexts, rather than reducing every recursion principle to a diagonal.
Our finite list client already has a fold and its preservation theorem. Supplying
adjunctions and liftings adds obligations without yet removing a repeated proof
in that client. We defer that generalization rather than reject its mathematics.

[Gibbons, *Fission for Program Comprehension*, §§2.3–2.6](https://www.cs.ox.ac.uk/jeremy.gibbons/publications/fission.pdf)
uses a local algebra equation to justify fold fusion. The discussion distinguishes
finite lists from infinite inputs and notes strictness conditions in its Haskell
setting. The native finite-list route already captures the relevant proof:
`ListFoldCompiler.compiled_fusion` and `Resources.reweight_run` derive the
whole computation from local preservation laws. Observation matters: value
fusion does not establish equality of the accumulated resource component.
We will compose resource maps on actual transitions instead of adding a second
fold induction or demanding diagonal representation.

[Milius and Litak, *Guard Your Daggers and Traces*, §§2–4](https://arxiv.org/html/1603.05214)
formulate guarded fixpoint operators using a pointed endofunctor and examine
uniqueness, uniformity, and guarded trace. Unique guarded solutions satisfy
their equational axioms; an arbitrary selected fixed point is a weaker input.
This provides a possible categorical replacement for an ad hoc shared recursion
interface. Our client already has coordinate guardedness and unique solutions,
so the immediate experiment can reuse native solution interpretation and expose
the same solution through selected feedback. A full categorical comparison would
need the later functor and trace laws, which `SelectedFeedback` does not assert.

The proposed experiment therefore keeps native existence principles and shares
only their existing preservation arguments. #444's maps additionally require
all-input diagonal representation. An equation at one selected witness alone
does not supply that contract. We will check that mismatch explicitly, and test
image restriction and a selected-row extension certificate independently of the
practical clients. Neither technique claims a weakest coverage condition.

This is a bounded comparison, not an exhaustive survey of recursion semantics.
Computable recursion retains partial evaluation and uniform program witnesses;
the accepted `AssemblyCutFold.exists_fold_program` already supplies a uniform
program through `Code.fixed_point₂`. `UniformOperation.reconstruction` needs an
explicit naturality law, and `no_equivariant_choice` prohibits replacing it with
unrestricted selection. Neither adjoint folds nor guarded fixed points supplies
these computability or naturality obligations for free. #235 owns broader
interface investigation; #109 owns additional source recursion support.
