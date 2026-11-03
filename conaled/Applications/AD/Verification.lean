import Applications.AD.Generalized
import Applications.AD.HigherOrder
import Applications.AD.Jets

/-! Kernel axiom audit for the AD applications. There are no added axioms. -/

#print axioms Applications.AD.DMap.comp
#print axioms Applications.AD.tangent_correct
#print axioms Applications.AD.continuation_comp
#print axioms Applications.AD.continuation_pair
#print axioms Applications.AD.adjoint_square_comp
#print axioms Applications.AD.gradient_correct
#print axioms Applications.AD.FirstOrder.compile_hasFDerivAt
#print axioms Applications.AD.FirstOrder.sharedPolynomial_derivative
#print axioms Applications.AD.Generalized.compile_differentiable
#print axioms Applications.AD.Generalized.compile_derivative
#print axioms Applications.AD.Generalized.compile_reverse_correct
#print axioms Applications.AD.Generalized.modes_agree
#print axioms Applications.AD.Generalized.sharedPolynomial_reverse
#print axioms Applications.AD.HigherOrder.eval_related
#print axioms Applications.AD.HigherOrder.compileDual_hasDerivAt
#print axioms Applications.AD.HigherOrder.compileCurveSquare
#print axioms Applications.AD.HigherOrder.higherOrder_hasDerivAt
#print axioms Applications.AD.Jets.jet_correct
#print axioms Applications.AD.Jets.jet_leibniz
#print axioms Applications.AD.Jets.towerMulSquare
#print axioms Applications.AD.Jets.compile_jet_correct
