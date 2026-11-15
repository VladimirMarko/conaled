import SquareKit.Internal.Cubical.FaceContexts

/-! Full endpoint faces reflect literal equality in the free De Morgan interval. -/
namespace SquareKit.Cubical
namespace PartialDimension

def endpointExpr (b : Bool) : Expr α := if b then .one else .zero

theorem eval_endpoint_reflects (e : Expr α) : ∀ b,
    eval (fun _ => none) e = some b → Expr.Conv e (endpointExpr b) := by
  induction e with
  | zero => intro b h; cases b <;> cases h; exact .refl _
  | one => intro b h; cases b <;> cases h; exact .refl _
  | var i => intro b h; cases h
  | neg e ih =>
    intro b h
    have he : eval (fun _ => none) e = some (!b) :=
      (by decide : ∀ x b, neg x = some b → x = some (!b)) _ _ h
    have hi := Expr.Conv.neg (ih (!b) he)
    cases b
    · exact hi.trans .neg_one
    · exact hi.trans .neg_zero
  | meet e f ih jh =>
    intro b h
    cases b
    · have he : eval (fun _ => none) e = some false ∨ eval (fun _ => none) f = some false :=
        (by decide : ∀ x y, meet x y = some false → x = some false ∨ y = some false) _ _ h
      rcases he with he | hf
      · exact (Expr.Conv.meet (ih false he) (.refl f)).trans
          ((Expr.Conv.meet_comm _ _).trans (.meet_zero _))
      · exact (Expr.Conv.meet (.refl e) (jh false hf)).trans (.meet_zero _)
    · have he : eval (fun _ => none) e = some true ∧ eval (fun _ => none) f = some true :=
        (by decide : ∀ x y, meet x y = some true → x = some true ∧ y = some true) _ _ h
      exact (Expr.Conv.meet (ih true he.1) (jh true he.2)).trans (.meet_one _)
  | join e f ih jh =>
    intro b h
    cases b
    · have he : eval (fun _ => none) e = some false ∧ eval (fun _ => none) f = some false :=
        (by decide : ∀ x y, join x y = some false → x = some false ∧ y = some false) _ _ h
      exact (Expr.Conv.join (ih false he.1) (jh false he.2)).trans (.join_zero _)
    · have he : eval (fun _ => none) e = some true ∨ eval (fun _ => none) f = some true :=
        (by decide : ∀ x y, join x y = some true → x = some true ∨ y = some true) _ _ h
      rcases he with he | hf
      · exact (Expr.Conv.join (ih true he) (.refl f)).trans
          ((Expr.Conv.join_comm _ _).trans (.join_one _))
      · exact (Expr.Conv.join (.refl e) (jh true hf)).trans (.join_one _)

end PartialDimension

namespace Face

def endpoint {I : Cube} (r : Cube.Hom I ⟨1⟩) (b : Bool) : Carrier I.dimension :=
  substitute r (atom 0 b)

theorem full_endpoint_iff {I : Cube} (r : Cube.Hom I ⟨1⟩) (b : Bool) :
    Full (endpoint r b) ↔ r = Cube.endpoint I b := by
  refine Quotient.inductionOn r ?_
  intro r
  constructor
  · intro h
    have he : PartialDimension.eval (fun _ => none) (r 0) = some b := of_decide_eq_true h
    apply Quotient.sound
    intro i
    have hi : i = 0 := Fin.eq_zero i
    subst i
    exact PartialDimension.eval_endpoint_reflects (r 0) b he
  · intro h
    have he := Quotient.exact h 0
    have hs := PartialDimension.sound (fun _ => none) he
    change decide (PartialDimension.eval (fun _ => none) (r 0) = some b) = true
    apply decide_eq_true
    exact hs.trans (by cases b <;> rfl)

theorem endpoint_substitute {I J : Cube} (f : Cube.Hom I J) (r : Cube.Hom J ⟨1⟩) (b : Bool) :
    substitute f (endpoint r b) = endpoint (Cube.comp f r) b := substitute_comp f r _

end Face

namespace Presheaf
open CategoryTheory
universe u

def Cofibration.endpoint {Γ : Context.{u}} (r : Term (interval Γ)) (b : Bool) : Cofibration Γ where
  app I := TypeCat.ofHom (fun x => ⟨Face.endpoint (r.val (Γ.elementsMk I x)).down b⟩)
  naturality I J f := by
    apply ConcreteCategory.hom_ext
    intro x
    let p : Γ.elementsMk I x ⟶ Γ.elementsMk J (Γ.map f x) := Functor.Elements.homMk f rfl
    have h := congrArg ULift.down (r.property p)
    change Cube.comp f.unop (r.val (Γ.elementsMk I x)).down = (r.val (Γ.elementsMk J (Γ.map f x))).down at h
    change ULift.up (Face.endpoint (r.val (Γ.elementsMk J (Γ.map f x))).down b) =
      ULift.up (Face.substitute f.unop (Face.endpoint (r.val (Γ.elementsMk I x)).down b))
    rw [Face.endpoint_substitute,h]

theorem Cofibration.full_endpoint {Γ : Context.{u}} (r : Term (interval Γ)) (b : Bool) (x : Γ.Elements) :
    (Cofibration.endpoint r b).full x ↔ r.val x = (Presheaf.endpoint Γ b).val x := by
  change Face.Full (Face.endpoint (r.val x).down b) ↔ _
  rw [Face.full_endpoint_iff]
  exact ⟨fun h => congrArg ULift.up h, fun h => congrArg ULift.down h⟩

theorem Cofibration.endpoint_reindex {Γ Δ : Context.{u}} (r : Term (interval Γ)) (b : Bool) (σ : Δ ⟶ Γ) :
    (Cofibration.endpoint r b).reindex σ = Cofibration.endpoint (r.reindex σ) b := rfl

end Presheaf
end SquareKit.Cubical
