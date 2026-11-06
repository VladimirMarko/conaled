import SquareKit.Internal.Cubical.FaceRestriction

/-! Restrict a context element along a partial assignment, including evidence
that it lies on the specified face. -/
namespace SquareKit.Cubical.Presheaf
open CategoryTheory
universe u

theorem Cofibration.value_natural {Γ : Context.{u}} (φ : Cofibration Γ) {x y : Γ.Elements}
    (f : x ⟶ y) : Face.substitute f.hom.unop (φ.app x.obj x.val).down = (φ.app y.obj y.val).down := by
  have h := congrArg ULift.down (φ.naturality_apply f.hom x.val)
  change (φ.app y.obj (Γ.map f.hom x.val)).down = _ at h
  rw [f.map_val] at h
  exact h.symm

def Cofibration.restrictedElement {Γ : Context.{u}} (φ : Cofibration Γ) (x : Γ.Elements)
    (ρ : Face.Assignment x.obj.unop.dimension) (h : (φ.app x.obj x.val).down.holds ρ = true) :
    (restrictContext φ).Elements :=
  (restrictContext φ).elementsMk x.obj ⟨Γ.map (Quiver.Hom.op (Face.restriction ρ)) x.val, by
    have he := congrArg ULift.down (φ.naturality_apply (Quiver.Hom.op (Face.restriction ρ)) x.val)
    change (φ.app x.obj (Γ.map (Quiver.Hom.op (Face.restriction ρ)) x.val)).down = _ at he
    change Face.Full (φ.app x.obj (Γ.map (Quiver.Hom.op (Face.restriction ρ)) x.val)).down
    rw [he]
    change (φ.app x.obj x.val).down.holds (Face.assignmentMap (Face.restriction ρ) (fun _ => none)) = true
    rw [Face.assignmentMap_restriction_none]
    exact h⟩

def Cofibration.restrictedRefinement {Γ : Context.{u}} (φ : Cofibration Γ) (x : Γ.Elements)
    (ρ τ : Face.Assignment x.obj.unop.dimension) (r : Face.Refines ρ τ)
    (h : (φ.app x.obj x.val).down.holds ρ = true) :
    φ.restrictedElement x ρ h ⟶ φ.restrictedElement x τ ((φ.app x.obj x.val).down.stable ρ τ r h) :=
  Functor.Elements.homMk (Quiver.Hom.op (Face.restriction τ)) (by
    apply Subtype.ext
    change Γ.map (Quiver.Hom.op (Face.restriction τ))
      (Γ.map (Quiver.Hom.op (Face.restriction ρ)) x.val) = Γ.map (Quiver.Hom.op (Face.restriction τ)) x.val
    rw [← Γ.map_comp_apply]
    exact congrArg (fun f : x.obj ⟶ x.obj => Γ.map f x.val)
      (congrArg Quiver.Hom.op (Face.restriction_refinement ρ τ r)))

theorem Cofibration.holds_natural {Γ : Context.{u}} (φ : Cofibration Γ) {x y : Γ.Elements}
    (f : x ⟶ y) (ρ : Face.Assignment y.obj.unop.dimension) :
    (φ.app y.obj y.val).down.holds ρ = (φ.app x.obj x.val).down.holds (Face.assignmentMap f.hom.unop ρ) :=
  congrArg (fun q : Face.Carrier y.obj.unop.dimension => q.holds ρ) (φ.value_natural f).symm

def Cofibration.restrictedArrow {Γ : Context.{u}} (φ : Cofibration Γ) {x y : Γ.Elements}
    (f : x ⟶ y) (ρ : Face.Assignment y.obj.unop.dimension)
    (h : (φ.app y.obj y.val).down.holds ρ = true) :
    φ.restrictedElement x (Face.assignmentMap f.hom.unop ρ) ((φ.holds_natural f ρ).symm.trans h) ⟶
      φ.restrictedElement y ρ h :=
  Functor.Elements.homMk (Quiver.Hom.op (Cube.comp (Face.restriction ρ) f.hom.unop)) (by
    apply Subtype.ext
    let L := Cube.comp (Face.restriction ρ) f.hom.unop
    let R := Face.restriction (Face.assignmentMap f.hom.unop ρ)
    change Γ.map (Quiver.Hom.op L) (Γ.map (Quiver.Hom.op R) x.val) =
      Γ.map (Quiver.Hom.op (Face.restriction ρ)) y.val
    calc
      _ = Γ.map (Quiver.Hom.op (Cube.comp L R)) x.val :=
        (Γ.map_comp_apply (Quiver.Hom.op R) (Quiver.Hom.op L) x.val).symm
      _ = Γ.map (Quiver.Hom.op L) x.val := congrArg
        (fun k : Cube.Hom y.obj.unop x.obj.unop => Γ.map (Quiver.Hom.op k) x.val)
          (Face.restriction_after f.hom.unop ρ)
      _ = Γ.map (Quiver.Hom.op (Face.restriction ρ)) (Γ.map f.hom x.val) :=
        Γ.map_comp_apply f.hom (Quiver.Hom.op (Face.restriction ρ)) x.val
      _ = _ := congrArg (Γ.map (Quiver.Hom.op (Face.restriction ρ))) f.map_val)

end SquareKit.Cubical.Presheaf
