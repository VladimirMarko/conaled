import SquareKit.Internal.Cubical.TypeFormers

/-! The represented interval and its natural De Morgan connection. -/
namespace SquareKit.Cubical
open CategoryTheory

namespace Cube

def endpoint (I : Cube) (b : Bool) : Hom I ⟨1⟩ :=
  ofRaw (fun _ => if b then .one else .zero)

def meet {I : Cube} (r s : Hom I ⟨1⟩) : Hom I ⟨1⟩ :=
  Quotient.map₂ (fun r s k => Expr.meet (r k) (s k))
    (by
      intro r r' h s s' k i
      exact Expr.Conv.meet (h i) (k i)) r s

@[simp] theorem comp_endpoint {I J : Cube} (f : Hom I J) (b : Bool) :
    comp f (endpoint J b) = endpoint I b := by
  refine Quotient.inductionOn f ?_
  intro f
  cases b <;> rfl

theorem comp_meet {I J : Cube} (f : Hom I J) (r s : Hom J ⟨1⟩) :
    comp f (meet r s) = meet (comp f r) (comp f s) := by
  refine Quotient.inductionOn₃ f r s ?_
  intro f r s
  rfl

@[simp] theorem meet_zero {I : Cube} (r : Hom I ⟨1⟩) :
    meet r (endpoint I false) = endpoint I false := by
  refine Quotient.inductionOn r ?_
  intro r
  exact Quotient.sound (fun i => Expr.Conv.meet_zero (r i))

@[simp] theorem meet_one {I : Cube} (r : Hom I ⟨1⟩) :
    meet r (endpoint I true) = r := by
  refine Quotient.inductionOn r ?_
  intro r
  exact Quotient.sound (fun i => Expr.Conv.meet_one (r i))

end Cube

namespace Presheaf
universe u

/-- The interval in context is the represented interval lifted to the family universe. -/
def interval (Γ : Context.{u}) : Family Γ where
  obj e := ULift.{u} (Cube.Hom e.obj.unop ⟨1⟩)
  map f := TypeCat.ofHom (fun r => ⟨Cube.comp f.hom.unop r.down⟩)
  map_id x := by
    apply ConcreteCategory.hom_ext
    intro r
    exact congrArg ULift.up (@Category.id_comp Cube _ x.obj.unop ⟨1⟩ r.down)
  map_comp f g := by
    apply ConcreteCategory.hom_ext
    intro r
    exact congrArg ULift.up (Category.assoc g.hom.unop f.hom.unop r.down)

def endpoint (Γ : Context.{u}) (b : Bool) : Term (interval Γ) where
  val x := ⟨Cube.endpoint x.obj.unop b⟩
  property f := congrArg ULift.up (Cube.comp_endpoint f.hom.unop b)

def endpointSub (Γ : Context.{u}) (b : Bool) : Γ ⟶ total (interval Γ) :=
  pair (𝟙 Γ) (endpoint Γ b)

def intervalMeet {Γ : Context.{u}} (r s : Term (interval Γ)) : Term (interval Γ) where
  val x := ⟨Cube.meet (r.val x).down (s.val x).down⟩
  property f := by
    have hr := congrArg ULift.down (r.property f)
    have hs := congrArg ULift.down (s.property f)
    apply congrArg ULift.up
    exact (Cube.comp_meet f.hom.unop _ _).trans (congrArg₂ Cube.meet hr hs)

@[simp] theorem intervalMeet_zero {Γ : Context.{u}} (r : Term (interval Γ)) :
    intervalMeet r (endpoint Γ false) = endpoint Γ false := by
  apply Term.ext
  intro x
  exact congrArg ULift.up (Cube.meet_zero _)

@[simp] theorem intervalMeet_one {Γ : Context.{u}} (r : Term (interval Γ)) :
    intervalMeet r (endpoint Γ true) = r := by
  apply Term.ext
  intro x
  exact congrArg ULift.up (Cube.meet_one _)

@[simp] theorem interval_reindex {Γ Δ : Context.{u}} (σ : Δ ⟶ Γ) :
    reindex (interval Γ) σ = interval Δ := rfl

@[simp] theorem endpoint_reindex {Γ Δ : Context.{u}} (σ : Δ ⟶ Γ) (b : Bool) :
    Term.reindex (endpoint Γ b) σ = endpoint Δ b := rfl

theorem intervalMeet_reindex {Γ Δ : Context.{u}} (r s : Term (interval Γ)) (σ : Δ ⟶ Γ) :
    Term.reindex (intervalMeet r s) σ = intervalMeet (Term.reindex r σ) (Term.reindex s σ) := rfl

end Presheaf
end SquareKit.Cubical
