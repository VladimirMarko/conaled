import SquareKit.Internal.Cubical.CubeProducts
import SquareKit.Internal.Cubical.PartialSections

/-! A generic fresh interval above any generalized context element. -/
namespace SquareKit.Cubical.Presheaf
open CategoryTheory
universe u

abbrev dropOpp (I : Cubeᵒᵖ) : I ⟶ Opposite.op (Cube.extend I.unop) :=
  @Quiver.Hom.op Cube _ _ _ (Cube.drop I.unop)
abbrev specializeOpp (I : Cubeᵒᵖ) (r : Cube.Hom I.unop ⟨1⟩) : Opposite.op (Cube.extend I.unop) ⟶ I :=
  @Quiver.Hom.op Cube _ _ _ (Cube.pair (Cube.identity I.unop) r)

def freshExtension {Γ : Context.{u}} (x : Γ.Elements) : (total (interval Γ)).Elements :=
  (total (interval Γ)).elementsMk (Opposite.op (Cube.extend x.obj.unop))
    ⟨Γ.map (dropOpp x.obj) x.val,⟨Cube.fresh x.obj.unop⟩⟩

theorem specialize_base {Γ : Context.{u}} (x : Γ.Elements) (r : (interval Γ).obj x) :
    Γ.map (specializeOpp x.obj r.down)
      (Γ.map (dropOpp x.obj) x.val) = x.val := by
  have hc : (dropOpp x.obj) ≫ (specializeOpp x.obj r.down) = 𝟙 x.obj :=
    congrArg (@Quiver.Hom.op Cube _ _ _) (Cube.pair_drop (Cube.identity x.obj.unop) r.down)
  calc
    _ = (Γ.map (dropOpp x.obj) ≫ Γ.map (specializeOpp x.obj r.down)) x.val := rfl
    _ = Γ.map (dropOpp x.obj ≫ specializeOpp x.obj r.down) x.val :=
      congrArg (fun f => f x.val) (Γ.map_comp (dropOpp x.obj) (specializeOpp x.obj r.down)).symm
    _ = x.val := by rw [hc,Γ.map_id]; rfl

def specializeInterval {Γ : Context.{u}} (x : Γ.Elements) (r : (interval Γ).obj x) :
    freshExtension x ⟶ extendObj (interval Γ) x r :=
  Functor.Elements.homMk (specializeOpp x.obj r.down) (by
    change (⟨Γ.map (specializeOpp x.obj r.down)
      (Γ.map (dropOpp x.obj) x.val),
      ULift.up (Cube.comp (Cube.pair (Cube.identity x.obj.unop) r.down) (Cube.fresh x.obj.unop))⟩ : (total (interval Γ)).obj x.obj) = ⟨x.val,r⟩
    rw [specialize_base,Cube.pair_fresh]
    cases r
    rfl)

abbrev constantFamily (Γ : Context.{u}) (S : Type u) : Family Γ := (Functor.const Γ.Elements).obj S

/-- A section with constant coefficients cannot change along a fresh interval. -/
theorem constant_section_interval {Γ : Context.{u}} {S : Type u}
    (a : Term (constantFamily (total (interval Γ)) S)) (x : Γ.Elements)
    (r s : (interval Γ).obj x) : a.val (extendObj (interval Γ) x r) = a.val (extendObj (interval Γ) x s) :=
  (a.property (specializeInterval x r)).symm.trans (a.property (specializeInterval x s))

/-- The same rigidity holds on an arbitrary face pulled back from the base. -/
theorem constant_partial_interval {Γ : Context.{u}} {S : Type u} {φ : Cofibration Γ}
    (a : PartialSection (constantFamily (total (interval Γ)) S) (φ.reindex (projection (interval Γ))))
    (x : Γ.Elements) (h : φ.full x) (r s : (interval Γ).obj x) :
    a.val (extendObj (interval Γ) x r) h = a.val (extendObj (interval Γ) x s) h := by
  let q : x ⟶ Γ.elementsMk (Opposite.op (Cube.extend x.obj.unop)) (Γ.map (dropOpp x.obj) x.val) :=
    Functor.Elements.homMk (dropOpp x.obj) rfl
  have hf : (φ.reindex (projection (interval Γ))).full (freshExtension x) := φ.full_natural q h
  exact (a.property (specializeInterval x r) hf).symm.trans (a.property (specializeInterval x s) hf)

end SquareKit.Cubical.Presheaf
