import SquareKit.SplitSheafCoherence
import SquareKit.SheafRelation

/-! Experimental constant split families. Their fibers are actual sections of
an ordinary sheaf, so reindexing is strictly independent of the base section. -/
noncomputable section
namespace SquareKit.SplitSheaf
open CategoryTheory Limits
universe u v w
variable {C : Type u} [Category.{v} C] {J : GrothendieckTopology C}
variable (B Γ : Sheaf J (Type w))

def constantFamily : Γ.obj.Elements ⥤ Type w := Functor.Elements.π Γ.obj ⋙ B.obj

def constantTotalIso : SplitPresheaf.Ext (constantFamily B Γ) ≅ (SheafRelation.product Γ B).obj where
  hom := { app _ := ↾fun x => (x.1, x.2) }
  inv := { app _ := ↾fun x => ⟨x.1, x.2⟩ }

def constant : Ty Γ where
  family := constantFamily B Γ
  isSheaf := (Presheaf.isSheaf_of_iso_iff (J := J) (constantTotalIso B Γ)).2
    (SheafRelation.product Γ B).property

variable {Γ} {Δ Ξ : Sheaf J (Type w)}
@[simp] theorem constant_sub (σ : Δ ⟶ Γ) : tySub (constant B Γ) σ = constant B Δ := rfl

def constantValue : Ext (constant B Γ) ⟶ B := ⟨{ app _ := ↾fun x => x.2 }⟩

def constantTerm (b : Γ ⟶ B) : Tm (constant B Γ) where
  val x := b.hom.app x.obj x.val
  natural f := (NatTrans.naturality_apply b.hom f.hom _).symm.trans
    (congrArg (b.hom.app _) f.map_val)

def constantPair (σ : Δ ⟶ Γ) (b : Δ ⟶ B) : Δ ⟶ Ext (constant B Γ) :=
  pair (constant B Γ) σ (constantTerm B b)

@[simp] theorem constantPair_p (σ : Δ ⟶ Γ) (b : Δ ⟶ B) :
    constantPair B σ b ≫ p (constant B Γ) = σ := rfl
@[simp] theorem constantPair_value (σ : Δ ⟶ Γ) (b : Δ ⟶ B) :
    constantPair B σ b ≫ constantValue B = b := rfl
@[simp] theorem constant_lift_value (σ : Δ ⟶ Γ) :
    lift (constant B Γ) σ ≫ constantValue B = constantValue B := rfl

theorem constantPair_natural (σ : Δ ⟶ Γ) (b : Δ ⟶ B) (τ : Ξ ⟶ Δ) :
    constantPair B (τ ≫ σ) (τ ≫ b) = τ ≫ constantPair B σ b := rfl

theorem constant_ext (f g : Δ ⟶ Ext (constant B Γ))
    (hp : f ≫ p _ = g ≫ p _) (hb : f ≫ constantValue B = g ≫ constantValue B) : f = g := by
  ext U x
  apply Sigma.ext
  · exact congrArg (fun k => k.hom.app U x) hp
  · exact heq_of_eq (congrArg (fun k => k.hom.app U x) hb)

end SquareKit.SplitSheaf
