import Squares
import Compiler
import SquareCompiler
import FirstOrder
import Dependent

/-!
An integrated build and an explicit audit of the principal proof boundaries.
The output lists Lean foundational dependencies; an empty list is reported
as "does not depend on any axioms". No result should mention `sorryAx`.
-/

#print axioms Squares.compose_assoc
#print axioms Squares.curry_uncurry
#print axioms Squares.curry_natural
#print axioms Squares.no_boolean_identity_square
#print axioms CategoricalCompiler.compile_sound
#print axioms CategoricalCompiler.closed_beta
#print axioms SquareCompiler.compile_commutes
#print axioms SquareCompiler.compile_apply_commutes
#print axioms SquareCompiler.incrementTwice_correct
#print axioms FirstOrderCompiler.compile_sound
#print axioms FirstOrderCompiler.everyTerm_additive
#print axioms FirstOrderCompiler.no_exponential
#print axioms DependentSquares.TermCert.reindex
#print axioms DependentSquares.sectionCert
#print axioms DependentSquares.pi_subst
#print axioms DependentSquares.pi_eta_cwf
#print axioms DependentSquares.RelTerm.lambda
#print axioms DependentSquares.RelTerm.apply
#print axioms DependentSquares.RelTerm.pair
#print axioms DependentSquares.RelTerm.second
#print axioms DependentSquares.Example.tightenCert
#print axioms DependentSquares.Example.appliedCert
#print axioms DependentSquares.Example.pairedCert

-- Execute the actual runtime function component of the compiled lambda.
#eval ((CategoricalCompiler.compile
  (SquareCompiler.target SquareCompiler.taggedNat SquareCompiler.primitives)
  SquareCompiler.incrementTwice).impl ()).val.1 (41, false)

-- Execute the dependent application and dependent pair projections.
#eval (DependentSquares.Example.appliedCert.code 8).1.val
#eval ((DependentSquares.Example.pairedCert.first.code 8).1.val,
       (DependentSquares.Example.pairedCert.second.code 8).1.val)
