import EmissionSemantics

/-! The relative graph family is generated from the actual native producer.
The telescope is A B C f g z x; helper applications remain in both bodies.
No hand-constructed graph proof is used by this family. -/
namespace EmittedGraph
open SquareKit.Internal EmissionEncoding ConLeche

def forwardType : ConLeche.Expr :=
  (encode (GraphEmissionPure.emitCore GraphTarget.forwardDeclaration).1).getD (.bvar 0)
def forwardProof : ConLeche.Expr :=
  (encode (GraphEmissionPure.emitCore GraphTarget.forwardDeclaration).2).getD (.bvar 0)
def backwardType : ConLeche.Expr :=
  (encode (GraphEmissionPure.emitCore GraphTarget.backwardDeclaration).1).getD (.bvar 0)
def backwardProof : ConLeche.Expr :=
  (encode (GraphEmissionPure.emitCore GraphTarget.backwardDeclaration).2).getD (.bvar 0)

theorem forward_encoded :
    encode (GraphEmissionPure.emitCore GraphTarget.forwardDeclaration).1 = some forwardType ∧
    encode (GraphEmissionPure.emitCore GraphTarget.forwardDeclaration).2 = some forwardProof := by
  exact ⟨rfl, rfl⟩
theorem backward_encoded :
    encode (GraphEmissionPure.emitCore GraphTarget.backwardDeclaration).1 = some backwardType ∧
    encode (GraphEmissionPure.emitCore GraphTarget.backwardDeclaration).2 = some backwardProof := by
  exact ⟨rfl, rfl⟩

theorem forward_native_identity :
    (decode forwardType).map CoreSyntax.Expr.toLean =
      some (GraphEmissionPure.emit GraphTarget.forwardDeclaration).1 ∧
    (decode forwardProof).map CoreSyntax.Expr.toLean =
      some (GraphEmissionPure.emit GraphTarget.forwardDeclaration).2 :=
  emitted_identity _ _ _ forward_encoded.1 forward_encoded.2

theorem backward_native_identity :
    (decode backwardType).map CoreSyntax.Expr.toLean =
      some (GraphEmissionPure.emit GraphTarget.backwardDeclaration).1 ∧
    (decode backwardProof).map CoreSyntax.Expr.toLean =
      some (GraphEmissionPure.emit GraphTarget.backwardDeclaration).2 :=
  emitted_identity _ _ _ backward_encoded.1 backward_encoded.2

end EmittedGraph
#audit_graph_module
