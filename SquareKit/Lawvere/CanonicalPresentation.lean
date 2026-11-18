import SquareKit.Lawvere.Universal

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
noncomputable section
namespace SquareKit.Lawvere.Operations
universe u
variable (O : Operations.{u})
def canonicalPresentation : Presentation.{u} where
  Symbol := Σ n, O.Op n
  arity := Sigma.fst
  Equation := (Σ n, Fin n) ⊕ (Σ n, Σ m, O.Op n × (Fin n → O.Op m))
  variableCount := Sum.elim Sigma.fst (fun x => x.2.1)
  lhs := Sum.rec (fun x => .node ⟨x.1, O.var x.2⟩ FinitaryTerm.leaf)
    (fun x => .node ⟨x.2.1, O.subst x.2.2.1 x.2.2.2⟩ FinitaryTerm.leaf)
  rhs := Sum.rec (fun x => .leaf x.2)
    (fun x => .node ⟨x.1, x.2.2.1⟩ (fun i => .node ⟨x.2.1, x.2.2.2 i⟩ FinitaryTerm.leaf))

def canonicalAssignment : O.canonicalPresentation.Assignment O where
  op s := s.2
  laws e := by
    cases e with
    | inl x => exact O.subst_var _
    | inr x =>
      change O.subst _ O.var = O.subst _ (fun i => O.subst _ O.var)
      simp only [O.subst_var]

def decode : O.canonicalPresentation.operations.Map O :=
  O.canonicalPresentation.interpretation O.canonicalAssignment.op O.canonicalAssignment.laws

def encode : O.Map O.canonicalPresentation.operations where
  map t := O.canonicalPresentation.symbol ⟨_,t⟩
  map_var i := Quotient.sound ((Presentation.Equal.equation (P := O.canonicalPresentation)) (Sum.inl ⟨_,i⟩))
  map_subst {m n} t σ := by
    have h : O.canonicalPresentation.symbol ⟨m,O.subst t σ⟩ =
        Quotient.mk (O.canonicalPresentation.setoid m)
          (.node ⟨n,t⟩ (fun i => .node ⟨m,σ i⟩ FinitaryTerm.leaf)) :=
      Quotient.sound ((Presentation.Equal.equation (P := O.canonicalPresentation)) (Sum.inr ⟨n,m,t,σ⟩))
    exact h.trans (O.canonicalPresentation.mk_node _ _)

@[simp] theorem decode_encode {n} (t : O.Op n) : O.decode.map (O.encode.map t) = t :=
  O.canonicalPresentation.interpretation_symbol O.canonicalAssignment ⟨n,t⟩

theorem encode_decode : O.decode.comp O.encode = Map.id _ := by
  apply (O.canonicalPresentation.assignmentEquiv _).symm.injective
  apply Presentation.Assignment.ext
  funext s
  change O.encode.map (O.decode.map (O.canonicalPresentation.symbol s)) = _
  rw [show O.decode.map (O.canonicalPresentation.symbol s) = s.2 from
    O.canonicalPresentation.interpretation_symbol O.canonicalAssignment s]
  rfl
end SquareKit.Lawvere.Operations

namespace SquareKit.Lawvere.Operations
universe u v
variable (O : Operations.{u})
def canonicalMapEquiv (R : Operations.{v}) : O.canonicalPresentation.operations.Map R ≃ O.Map R where
  toFun F := O.encode.comp F
  invFun G := O.decode.comp G
  left_inv F := by
    apply Map.ext
    intro n t
    change F.map (O.encode.map (O.decode.map t)) = F.map t
    exact congrArg F.map (congrArg (fun H : O.canonicalPresentation.operations.Map _ => H.map t) O.encode_decode)
  right_inv G := by
    apply Map.ext
    intro n t
    change G.map (O.decode.map (O.encode.map t)) = G.map t
    rw [decode_encode]
end SquareKit.Lawvere.Operations
