import SquareKit.Internal.Cubical.IdentitySubstitution
import SquareKit.Internal.Cubical.IntervalScaling
import SquareKit.Internal.Cubical.Conversion

/-! Contract an identity toward its initial endpoint, recording the extra zero
face so that the contraction starts at strict reflexivity. -/
namespace SquareKit.Cubical.Presheaf
open CategoryTheory
universe u

namespace IdentityContraction
variable {Γ : Context.{u}} {A : Family Γ} {a b : Term A}

def underlying (p : Term (identity A a b)) :
    Term (path (reindex A (projection (interval Γ))) a b) := Term.map (identityPath A a b) p

def point (p : Term (identity A a b)) : Term (reindex A (projection (interval Γ))) :=
  pathApp (underlying p)

theorem point_zero (p : Term (identity A a b)) :
    (point p).reindex (endpointSub Γ false) = a := pathApp_zero (underlying p)

theorem point_one (p : Term (identity A a b)) :
    (point p).reindex (endpointSub Γ true) = b := pathApp_one (underlying p)

def path (p : Term (identity A a b)) :
    Term (Presheaf.path (reindex (reindex A (projection (interval Γ)))
      (projection (interval (total (interval Γ))))) (a.reindex (projection (interval Γ))) (point p)) :=
  pathLam ((point p).reindex (scaleInterval Γ))
    (by
      apply Term.ext
      intro x
      let y := (projection (interval Γ)).mapElements.obj x
      change (p.val y).path.val.val (𝟙 _) ⟨Cube.meet x.val.2.down (Cube.endpoint x.obj.unop false)⟩ = a.val y
      have he := congrArg (fun s : Cube.Hom x.obj.unop ⟨1⟩ =>
        (show A.obj y from (p.val y).path.val.val (𝟙 _) (show (interval Γ).obj y from ULift.up s)))
        (Cube.meet_zero x.val.2.down)
      exact he.trans ((p.val y).path.property (𝟙 _)).1)
    (by
      apply Term.ext
      intro x
      let y := (projection (interval Γ)).mapElements.obj x
      exact congrArg (fun s : Cube.Hom x.obj.unop ⟨1⟩ =>
        (show A.obj y from (p.val y).path.val.val (𝟙 _) (show (interval Γ).obj y from ULift.up s)))
        (Cube.meet_one x.val.2.down))

def face (p : Term (identity A a b)) : Cofibration (total (interval Γ)) :=
  ((identityFace p).reindex (projection (interval Γ))).join (intervalFace Γ false)

theorem path_constant (p : Term (identity A a b)) (x : (total (interval Γ)).Elements)
    (h : (face p).full x) (r : (interval (total (interval Γ))).obj x) :
    ((path p).val x).val.val (𝟙 _) r = (a.reindex (projection (interval Γ))).val x := by
  let y := (projection (interval Γ)).mapElements.obj x
  change (p.val y).path.val.val (𝟙 _) ⟨Cube.meet x.val.2.down r.down⟩ = a.val y
  rcases (Cofibration.full_join _ _ x).mp h with hp | hz
  · exact (p.val y).constant (𝟙 _) hp _
  · have he := (Cofibration.full_endpoint (generic (interval Γ)) false x).mp hz
    have hd := congrArg ULift.down he
    have hm : Cube.meet x.val.2.down r.down = Cube.endpoint x.obj.unop false :=
      (congrArg (fun s => Cube.meet s r.down) hd).trans (Cube.zero_meet r.down)
    exact (congrArg (fun s : Cube.Hom y.obj.unop ⟨1⟩ => (show A.obj y from (p.val y).path.val.val (𝟙 _) (show (interval Γ).obj y from ULift.up s))) hm).trans
      ((p.val y).path.property (𝟙 _)).1

def contract (p : Term (identity A a b)) :
    Term (identity (reindex A (projection (interval Γ)))
      (a.reindex (projection (interval Γ))) (point p)) :=
  identityIntro (path p) (face p) (path_constant p)

theorem contract_face (p : Term (identity A a b)) : identityFace (contract p) = face p := rfl

def atZero (p : Term (identity A a b)) : Term (identity A a a) :=
  (Term.map (identityReindex (reindex A (projection (interval Γ)))
    (a.reindex (projection (interval Γ))) (point p) (endpointSub Γ false))
    ((contract p).reindex (endpointSub Γ false))).convert
      (congrArg (identity A a) (point_zero p))

theorem atZero_refl (p : Term (identity A a b)) : atZero p = identityRefl a := by
  apply Term.convert_eq
  apply Term.hext (congrArg (identity A a) (point_zero p))
  intro x
  apply IdentityElement.hext_right (point_zero p)
  · apply PiElement.ext
    intro y f r
    change (p.val y).path.val.val (𝟙 _) ⟨Cube.meet (Cube.endpoint y.obj.unop false) r.down⟩ = a.val y
    exact (congrArg (fun s : Cube.Hom y.obj.unop ⟨1⟩ => (show A.obj y from (p.val y).path.val.val (𝟙 _) (show (interval Γ).obj y from ULift.up s))) (Cube.zero_meet r.down)).trans
      ((p.val y).path.property (𝟙 _)).1
  · apply Face.Carrier.ext
    intro ρ
    change ((identityFace p).app x.obj x.val).down.holds ρ || true = true
    exact Bool.or_true _

def atOne (p : Term (identity A a b)) : Term (identity A a b) :=
  (Term.map (identityReindex (reindex A (projection (interval Γ)))
    (a.reindex (projection (interval Γ))) (point p) (endpointSub Γ true))
    ((contract p).reindex (endpointSub Γ true))).convert
      (congrArg (identity A a) (point_one p))

theorem atOne_self (p : Term (identity A a b)) : atOne p = p := by
  apply Term.convert_eq
  apply Term.hext (congrArg (identity A a) (point_one p))
  intro x
  apply IdentityElement.hext_right (point_one p)
  · apply PiElement.ext
    intro y f r
    have hm : Cube.meet (Cube.endpoint y.obj.unop true) r.down = r.down := by
      refine Quotient.inductionOn r.down ?_
      intro r
      exact Quotient.sound (fun i => (Expr.Conv.meet_comm _ _).trans (.meet_one _))
    have hp := congrArg (fun q => q.path.val.val (𝟙 _) r) (p.property f)
    change (p.val x).path.val.val (f ≫ 𝟙 _) r = (p.val y).path.val.val (𝟙 _) r at hp
    change (p.val y).path.val.val (𝟙 _) ⟨Cube.meet (Cube.endpoint y.obj.unop true) r.down⟩ =
      (p.val x).path.val.val f r
    simp only [Category.comp_id] at hp
    exact (congrArg (fun s : Cube.Hom y.obj.unop ⟨1⟩ => (show A.obj y from
      (p.val y).path.val.val (𝟙 _) (show (interval Γ).obj y from ULift.up s))) hm).trans hp.symm
  · apply Face.Carrier.ext
    intro ρ
    change ((p.val x).face.holds ρ || false) = (p.val x).face.holds ρ
    exact Bool.or_false _

theorem contract_reindex {Δ : Context.{u}} (p : Term (identity A a b)) (σ : Δ ⟶ Γ) :
    Term.map (identityReindex (reindex A (projection (interval Γ)))
      (a.reindex (projection (interval Γ))) (point p) (liftSub (interval Γ) σ))
      ((contract p).reindex (liftSub (interval Γ) σ)) =
    contract (Term.map (identityReindex A a b σ) (p.reindex σ)) := rfl

end IdentityContraction
end SquareKit.Cubical.Presheaf
