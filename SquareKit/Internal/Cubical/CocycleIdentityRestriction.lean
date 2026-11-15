import SquareKit.Internal.Cubical.CocycleIdentityObservation
import SquareKit.Internal.Cubical.IdentityEvaluation

/-! Repeated identity evaluation commutes with every formal cube restriction. -/
noncomputable section
namespace SquareKit.Cubical.CategoryCocycles
open CategoryTheory Presheaf

abbrev FirstIdentityFamily (Γ : Context.{0}) :=
  normalizedIdentity (cocycleFamily Γ) (zeroTerm Γ) (zeroTerm Γ)
abbrev FirstIdentityPoint (Γ : Context.{0}) := normalizedIdentityRefl (zeroTerm Γ)

theorem secondElementValue_map {Γ : Context.{0}} {x y : Γ.Elements} (f : x ⟶ y)
    (p : (SecondIdentityFamily Γ).obj x) (r s : (interval Γ).obj x) :
    cocycles.map f.hom (secondElementValue p r s) =
      secondElementValue ((SecondIdentityFamily Γ).map f p) ((interval Γ).map f r) ((interval Γ).map f s) :=
  (LocalIdentity.eval_map f (p.eval r) s).trans
    (congrArg (fun q : (FirstIdentityFamily Γ).obj y => q.eval ((interval Γ).map f s))
      (LocalIdentity.eval_map f p r))

theorem secondValue_map {Γ : Context.{0}} (t : Term (SecondIdentityFamily Γ))
    {x y : Γ.Elements} (f : x ⟶ y) (r s : (interval Γ).obj x) :
    cocycles.map f.hom (secondValue t x r s) =
      secondValue t y ((interval Γ).map f r) ((interval Γ).map f s) :=
  (secondElementValue_map f (t.val x) r s).trans
    (congrArg (fun p => secondElementValue p ((interval Γ).map f r) ((interval Γ).map f s)) (t.property f))

theorem secondElementValue_left {Γ : Context.{0}} {x : Γ.Elements}
    (p : (SecondIdentityFamily Γ).obj x) (s : (interval Γ).obj x) (b : Bool) :
    secondElementValue p ((endpoint Γ b).val x) s = zeroCocycle (Over x.obj.unop) := by
  cases b
  · exact (congrArg (fun q : (FirstIdentityFamily Γ).obj x => q.eval s) p.eval_zero).trans
      (LocalIdentity.eval_refl (zeroTerm Γ) x s)
  · exact (congrArg (fun q : (FirstIdentityFamily Γ).obj x => q.eval s) p.eval_one).trans
      (LocalIdentity.eval_refl (zeroTerm Γ) x s)

theorem secondElementValue_right {Γ : Context.{0}} {x : Γ.Elements}
    (p : (SecondIdentityFamily Γ).obj x) (r : (interval Γ).obj x) (b : Bool) :
    secondElementValue p r ((endpoint Γ b).val x) = zeroCocycle (Over x.obj.unop) := by
  cases b
  · exact (p.eval r).eval_zero
  · exact (p.eval r).eval_one

def thirdValue {Γ : Context.{0}} {a b : Term (SecondIdentityFamily Γ)}
    (h : Term (normalizedIdentity (SecondIdentityFamily Γ) a b)) (x : Γ.Elements)
    (r s t : (interval Γ).obj x) : CubeCocycle x.obj.unop :=
  secondElementValue ((h.val x).eval r) s t

theorem thirdValue_map {Γ : Context.{0}} {a b : Term (SecondIdentityFamily Γ)}
    (h : Term (normalizedIdentity (SecondIdentityFamily Γ) a b))
    {x y : Γ.Elements} (f : x ⟶ y) (r s t : (interval Γ).obj x) :
    cocycles.map f.hom (thirdValue h x r s t) =
      thirdValue h y ((interval Γ).map f r) ((interval Γ).map f s) ((interval Γ).map f t) := by
  have e := (LocalIdentity.eval_map f (h.val x) r).trans
    (congrArg (fun p : (normalizedIdentity (SecondIdentityFamily Γ) a b).obj y =>
      p.eval ((interval Γ).map f r)) (h.property f))
  exact (secondElementValue_map f ((h.val x).eval r) s t).trans
    (congrArg (fun p => secondElementValue p ((interval Γ).map f s) ((interval Γ).map f t)) e)

theorem thirdValue_zero {Γ : Context.{0}} {a b : Term (SecondIdentityFamily Γ)}
    (h : Term (normalizedIdentity (SecondIdentityFamily Γ) a b)) (x : Γ.Elements)
    (s t : (interval Γ).obj x) :
    thirdValue h x ((endpoint Γ false).val x) s t = secondValue a x s t :=
  congrArg (fun p => secondElementValue p s t) (h.val x).eval_zero

theorem thirdValue_one {Γ : Context.{0}} {a b : Term (SecondIdentityFamily Γ)}
    (h : Term (normalizedIdentity (SecondIdentityFamily Γ) a b)) (x : Γ.Elements)
    (s t : (interval Γ).obj x) :
    thirdValue h x ((endpoint Γ true).val x) s t = secondValue b x s t :=
  congrArg (fun p => secondElementValue p s t) (h.val x).eval_one

theorem thirdValue_middle {Γ : Context.{0}} {a b : Term (SecondIdentityFamily Γ)}
    (h : Term (normalizedIdentity (SecondIdentityFamily Γ) a b)) (x : Γ.Elements)
    (r t : (interval Γ).obj x) (e : Bool) :
    thirdValue h x r ((endpoint Γ e).val x) t = zeroCocycle (Over x.obj.unop) :=
  secondElementValue_left ((h.val x).eval r) t e

theorem thirdValue_right {Γ : Context.{0}} {a b : Term (SecondIdentityFamily Γ)}
    (h : Term (normalizedIdentity (SecondIdentityFamily Γ) a b)) (x : Γ.Elements)
    (r s : (interval Γ).obj x) (e : Bool) :
    thirdValue h x r s ((endpoint Γ e).val x) = zeroCocycle (Over x.obj.unop) :=
  secondElementValue_right ((h.val x).eval r) s e

end SquareKit.Cubical.CategoryCocycles
