import SquareKit.Internal.PathTransport.ChangingTailComparison

/-! Ordinary-groupoid comparison contexts. The comparison is a functor, not
an equivalence; families carry arbitrary natural transformations. -/
noncomputable section
namespace SquareKit.Internal.PathTransport.GroupoidModel.Comparison
open CategoryTheory CategoryTheory.Functor
universe u

/-- Two contexts with their selected comparison on objects and arrows. -/
structure Context where
  left : Grpd.{u,u}
  right : Grpd.{u,u}
  map : left ⥤ right

/-- A simultaneous substitution preserves the selected comparison strictly. -/
@[ext] structure Substitution (Δ Γ : Context.{u}) : Type (u+1) where
  left : Δ.left ⥤ Γ.left
  right : Δ.right ⥤ Γ.right
  commutes : left ⋙ Γ.map = Δ.map ⋙ right

namespace Substitution

def id (Γ : Context.{u}) : Substitution Γ Γ := ⟨𝟭 _, 𝟭 _, rfl⟩

def comp {Γ Δ Θ : Context.{u}} (σ : Substitution Δ Γ) (τ : Substitution Θ Δ) :
    Substitution Θ Γ where
  left := τ.left ⋙ σ.left
  right := τ.right ⋙ σ.right
  commutes := by rw [CategoryTheory.Functor.assoc, σ.commutes, ← CategoryTheory.Functor.assoc,
    τ.commutes]; rfl

@[simp] theorem comp_id_left {Γ Δ : Context.{u}} (σ : Substitution Δ Γ) :
    comp (id Γ) σ = σ := by ext <;> rfl
@[simp] theorem comp_id_right {Γ Δ : Context.{u}} (σ : Substitution Δ Γ) :
    comp σ (id Δ) = σ := by ext <;> rfl
@[simp] theorem comp_assoc {Γ Δ Θ Ξ : Context.{u}}
    (σ : Substitution Δ Γ) (τ : Substitution Θ Δ) (υ : Substitution Ξ Θ) :
    comp (comp σ τ) υ = comp σ (comp τ υ) := by ext <;> rfl

end Substitution

/-- A dependent family compares independently specified groupoid fibers. -/
@[ext] structure Family (Γ : Context.{u}) where
  left : Γ.left ⥤ Grpd.{u,u}
  right : Γ.right ⥤ Grpd.{u,u}
  map : left ⟶ Γ.map ⋙ right

namespace Family
variable {Γ : Context.{u}}

/-- Comprehension applies the fiber map and then changes the base. -/
def extend (A : Family Γ) : Context.{u} where
  left := @Grpd.of (Extend A.left) Groupoid.ofIsGroupoid
  right := @Grpd.of (Extend A.right) Groupoid.ofIsGroupoid
  map := Grothendieck.map (whiskerRight A.map Grpd.forgetToCat) ⋙
    Grothendieck.pre (A.right ⋙ Grpd.forgetToCat) Γ.map

def weaken (A : Family Γ) : Substitution A.extend Γ where
  left := GroupoidModel.weaken A.left
  right := GroupoidModel.weaken A.right
  commutes := rfl

end Family

/-- A section includes its two ordinary interpretations and equality of their
comparison functors. The equality retains the entire arrow action. -/
@[ext] structure Section {Γ : Context.{u}} (A : Family Γ) : Type (u+1) where
  left : GroupoidModel.Section A.left
  right : GroupoidModel.Section A.right
  commutes : left.familyImage A.map = right.reindex Γ.map

namespace Section
variable {Γ : Context.{u}} {A : Family Γ}

def lift (s : Section A) : Substitution Γ A.extend :=
  ⟨s.left.lift, s.right.lift, congrArg
    (fun t => t.lift ⋙ Grothendieck.pre (A.right ⋙ Grpd.forgetToCat) Γ.map) s.commutes⟩

@[simp] theorem lift_weaken (s : Section A) :
    Substitution.comp A.weaken s.lift = Substitution.id Γ := by ext <;> rfl

end Section
end SquareKit.Internal.PathTransport.GroupoidModel.Comparison
