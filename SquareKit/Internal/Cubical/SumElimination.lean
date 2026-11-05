import SquareKit.Internal.Cubical.TypeFormers

/-! Dependent sum elimination as a change between two actual comprehension
contexts. The motive may depend on both components of the pair. -/
namespace SquareKit.Cubical.Presheaf
open CategoryTheory
universe u

def sigmaPack {Γ : Context.{u}} (A : Family Γ) (B : Family (total A)) :
    total B ⟶ total (sigma A B) where
  app _ := TypeCat.ofHom (fun z => ⟨z.1.1, z.1.2, z.2⟩)
  naturality _ _ _ := rfl

def sigmaUnpack {Γ : Context.{u}} (A : Family Γ) (B : Family (total A)) :
    total (sigma A B) ⟶ total B where
  app _ := TypeCat.ofHom (fun z => ⟨⟨z.1, z.2.1⟩, z.2.2⟩)
  naturality _ _ _ := rfl

@[simp] theorem sigmaPack_unpack {Γ : Context.{u}} (A : Family Γ)
    (B : Family (total A)) : sigmaPack A B ≫ sigmaUnpack A B = 𝟙 (total B) := rfl

@[simp] theorem sigmaUnpack_pack {Γ : Context.{u}} (A : Family Γ)
    (B : Family (total A)) :
    sigmaUnpack A B ≫ sigmaPack A B = 𝟙 (total (sigma A B)) := rfl

/-- Interpret a body in Γ.A.B in an arbitrary motive over Γ.(Σ A B). -/
def sigmaElim {Γ : Context.{u}} {A : Family Γ} {B : Family (total A)}
    {C : Family (total (sigma A B))} (b : Term (reindex C (sigmaPack A B))) :
    Term C := b.reindex (sigmaUnpack A B)

@[simp] theorem sigmaElim_beta {Γ : Context.{u}} {A : Family Γ}
    {B : Family (total A)} {C : Family (total (sigma A B))}
    (b : Term (reindex C (sigmaPack A B))) :
    (sigmaElim b).reindex (sigmaPack A B) = b := rfl

@[simp] theorem sigmaElim_eta {Γ : Context.{u}} {A : Family Γ}
    {B : Family (total A)} {C : Family (total (sigma A B))} (t : Term C) :
    sigmaElim (t.reindex (sigmaPack A B)) = t := rfl

/-- Packing commutes with every base substitution, including both dependent
components of its lifted context map. -/
theorem sigmaPack_reindex {Γ Δ : Context.{u}} (A : Family Γ)
    (B : Family (total A)) (σ : Δ ⟶ Γ) :
    sigmaPack (reindex A σ) (reindex B (liftSub A σ)) ≫ liftSub (sigma A B) σ =
      liftSub B (liftSub A σ) ≫ sigmaPack A B := rfl

end SquareKit.Cubical.Presheaf
