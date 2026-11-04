import SquareKit.Internal.PathTransport.DisplayCategory
import SquareKit.RepresentedFamilies

/-! The current model yields the independent representability presentation.
Recovering projection, generic variable and pairing is checked pointwise. The
primitive signature and identity eliminator are not part of that presentation. -/
namespace SquareKit.Internal.PathTransport.Typed.StructuralModel
open CategoryTheory
universe u
set_option backward.isDefEq.respectTransparency false
variable (M : StructuralModel.{u})

def indexedFamilies : SquareKit.IndexedFamilies M.ContextCat where
  Ty := M.Family
  Tm := M.Section
  pullTy := M.subTy
  pullTm := M.subTm
  ty_id := M.subTy_id
  ty_comp := M.subTy_comp
  tm_id := M.subTm_id
  tm_comp := M.subTm_comp

def representation : M.indexedFamilies.Representation where
  ext := M.extend
  decode A Δ := {
    toFun := fun f => ⟨M.compSub (M.weaken _ A) f,
      cast (congrArg (M.Section Δ) (M.subTy_comp A (M.weaken _ A) f))
        (M.subTm (M.genericVariable _ A) f)⟩
    invFun := fun e => M.pairSub A e.1 e.2
    left_inv := M.pair_eta A
    right_inv := fun e => Sigma.ext (M.weaken_pair A e.1 e.2)
      ((cast_heq _ _).trans (M.variable_pair A e.1 e.2))
  }
  natural A f g := by
    apply Sigma.ext
    · exact (M.comp_assoc _ _ _).symm
    · apply (cast_heq _ _).trans
      apply (M.subTm_comp _ _ _).symm.trans
      apply HEq.trans _ (cast_heq _ _).symm
      exact (M.subTm_congr (M.subTy_comp A (M.weaken _ A) f)
        (cast_heq _ _).symm g)

@[simp] theorem representation_projection {Γ} (A : M.Family Γ) :
    M.representation.projection A = M.weaken Γ A := M.comp_id_right _

theorem representation_generic {Γ} (A : M.Family Γ) :
    HEq (M.representation.generic A) (M.genericVariable Γ A) :=
  (cast_heq _ _).trans (M.subTm_id _)

@[simp] theorem representation_pair {Γ Δ} (A : M.Family Γ)
    (f : M.Substitution Δ Γ) (t : M.Section Δ (M.subTy A f)) :
    M.representation.pair A f t = M.pairSub A f t := rfl

/-- The independent uniqueness law recovers the old pairing naturality theorem. -/
theorem pairing_from_representability {Γ Δ Θ} (A : M.Family Γ)
    (f : M.Substitution Δ Γ) (t : M.Section Δ (M.subTy A f)) (g : M.Substitution Θ Δ) :
    M.compSub (M.pairSub A f t) g = M.pairSub A (M.compSub f g)
      (cast (congrArg (M.Section Θ) (M.subTy_comp A f g)) (M.subTm t g)) :=
  M.representation.pair_natural A f t g

end SquareKit.Internal.PathTransport.Typed.StructuralModel
