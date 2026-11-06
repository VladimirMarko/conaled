import SquareKit.Internal.Cubical.CocycleSquareWitness
import SquareKit.Internal.Cubical.CocycleFamily

/-! The boundary square as a natural section at any two interval coordinates. -/
namespace SquareKit.Cubical.CategoryCocycles
open CategoryTheory Presheaf

noncomputable def zeroTerm (Γ : Context.{0}) : Term (cocycleFamily Γ) where
  val x := zeroCocycle (Over x.obj.unop)
  property _ := rfl

noncomputable def squareTerm {Γ : Context.{0}} (r s : Term (interval Γ)) :
    Term (cocycleFamily Γ) where
  val x := cocycles.map (Quiver.Hom.op (Cube.pair (s.val x).down (r.val x).down)) squareCocycle
  property {x y} f := by
    have hr := congrArg ULift.down (r.property f)
    have hs := congrArg ULift.down (s.property f)
    change cocycles.map f.hom (cocycles.map (Quiver.Hom.op (Cube.pair (s.val x).down (r.val x).down)) squareCocycle) = _
    have e : Cube.comp f.hom.unop (Cube.pair (s.val x).down (r.val x).down) =
        Cube.pair (s.val y).down (r.val y).down := by
      exact (Cube.comp_pair _ _ _).trans (congrArg₂ Cube.pair hs hr)
    exact (cocycles.map_comp_apply (Quiver.Hom.op (Cube.pair (s.val x).down (r.val x).down)) f.hom squareCocycle).symm.trans
      (congrArg (fun α : y.obj.unop ⟶ (⟨2⟩ : Cube) => cocycles.map α.op squareCocycle) e)

theorem squareTerm_reindex {Γ Δ : Context.{0}} (r s : Term (interval Γ)) (σ : Δ ⟶ Γ) :
    (squareTerm r s).reindex σ = squareTerm (r.reindex σ) (s.reindex σ) := rfl

theorem squareTerm_left_endpoint {Γ : Context.{0}} (s : Term (interval Γ)) (b : Bool) :
    squareTerm (endpoint Γ b) s = zeroTerm Γ := by
  apply Term.ext
  intro x
  have e : Cube.comp (s.val x).down (verticalEdge b) =
      Cube.pair (s.val x).down (Cube.endpoint x.obj.unop b) := by
    simp only [verticalEdge,Cube.comp_pair,Cube.comp_endpoint]
    exact congrArg (fun f => Cube.pair f (Cube.endpoint x.obj.unop b)) (@Category.comp_id Cube _ x.obj.unop ⟨1⟩ (s.val x).down)
  change cocycles.map (Quiver.Hom.op (Cube.pair (s.val x).down (Cube.endpoint x.obj.unop b))) squareCocycle = _
  rw [← e]
  change cocycles.map ((verticalEdge b).op ≫ (Quiver.Hom.op (s.val x).down)) squareCocycle = _
  exact (cocycles.map_comp_apply (verticalEdge b).op (Quiver.Hom.op (s.val x).down) squareCocycle).trans
    (congrArg (fun z => cocycles.map (Quiver.Hom.op (s.val x).down) z) (squareCocycle_vertical b))

theorem squareTerm_right_endpoint {Γ : Context.{0}} (r : Term (interval Γ)) (b : Bool) :
    squareTerm r (endpoint Γ b) = zeroTerm Γ := by
  apply Term.ext
  intro x
  have e : Cube.comp (r.val x).down (horizontalEdge b) =
      Cube.pair (Cube.endpoint x.obj.unop b) (r.val x).down := by
    simp only [horizontalEdge,Cube.comp_pair,Cube.comp_endpoint]
    exact congrArg (Cube.pair (Cube.endpoint x.obj.unop b)) (@Category.comp_id Cube _ x.obj.unop ⟨1⟩ (r.val x).down)
  change cocycles.map (Quiver.Hom.op (Cube.pair (Cube.endpoint x.obj.unop b) (r.val x).down)) squareCocycle = _
  rw [← e]
  change cocycles.map ((horizontalEdge b).op ≫ (Quiver.Hom.op (r.val x).down)) squareCocycle = _
  exact (cocycles.map_comp_apply (horizontalEdge b).op (Quiver.Hom.op (r.val x).down) squareCocycle).trans
    (congrArg (fun z => cocycles.map (Quiver.Hom.op (r.val x).down) z) (squareCocycle_horizontal b))

end SquareKit.Cubical.CategoryCocycles
