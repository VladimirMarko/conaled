import SquareKit.Internal.Cubical.Filling
import SquareKit.Internal.Cubical.PartialSums

/-! Fill a dependent pair by filling its first component, then its second
component along that actual first filler. -/
namespace SquareKit.Cubical.Presheaf
open CategoryTheory
universe u

def sigmaFilling {Γ : Context.{u}} {A : Family Γ} {B : Family (total A)}
    (F : Filling A) (hF : F.Lawful) (G : Filling B) : Filling (sigma A B) where
  fill p φ b :=
    let a := F.fill p φ (OpenBox.sigmaFst (B := reindex B (liftSub A p)) b)
    let ha := (hF.fills p φ (OpenBox.sigmaFst (B := reindex B (liftSub A p)) b))
    let c := G.fill (pair p a) φ (OpenBox.sigmaSnd (B := reindex B (liftSub A p)) b a ha)
    Presheaf.sigmaIntro (B := reindex B (liftSub A p)) a c

theorem sigmaFilling_fills {Γ Δ : Context.{u}} {A : Family Γ} {B : Family (total A)}
    (F : Filling A) (hF : F.Lawful) (G : Filling B) (hG : G.Lawful)
    (p : total (interval Δ) ⟶ Γ) (φ : Cofibration Δ) (b : OpenBox (reindex (sigma A B) p) φ) :
    b.Fills ((sigmaFilling F hF G).fill p φ b) := by
  let first := OpenBox.sigmaFst (B := reindex B (liftSub A p)) b
  let a := F.fill p φ first
  have ha : first.Fills a := hF.fills p φ first
  let second := OpenBox.sigmaSnd (B := reindex B (liftSub A p)) b a ha
  exact OpenBox.sigmaIntro_fills (B := reindex B (liftSub A p)) b a ha
    (G.fill (pair p a) φ second) (hG.fills (pair p a) φ second)

set_option backward.isDefEq.respectTransparency false in
theorem sigmaFilling_uniform {Γ Δ Θ : Context.{u}} {A : Family Γ} {B : Family (total A)}
    (F : Filling A) (hF : F.Lawful) (G : Filling B) (hG : G.Lawful)
    (p : total (interval Δ) ⟶ Γ) (φ : Cofibration Δ) (b : OpenBox (reindex (sigma A B) p) φ)
    (σ : Θ ⟶ Δ) :
    (sigmaFilling F hF G).fill (liftSub (interval Δ) σ ≫ p) (φ.reindex σ) (b.reindex σ) =
      ((sigmaFilling F hF G).fill p φ b).reindex (liftSub (interval Δ) σ) := by
  let L := liftSub (interval Δ) σ
  let first := OpenBox.sigmaFst (B := reindex B (liftSub A p)) b
  let a := F.fill p φ first
  have ha : first.Fills a := hF.fills p φ first
  let k : {z : Term (reindex A (L ≫ p)) // (first.reindex σ).Fills z} →
      Term (reindex (sigma A B) (L ≫ p)) := fun z =>
    Presheaf.sigmaIntro (B := reindex B (liftSub A (L ≫ p))) z.val
      (G.fill (pair (L ≫ p) z.val) (φ.reindex σ)
        (OpenBox.sigmaSnd (B := reindex B (liftSub A (L ≫ p))) (b.reindex σ) z.val z.property))
  have hfirst : (⟨F.fill (L ≫ p) (φ.reindex σ) (first.reindex σ),
      hF.fills (L ≫ p) (φ.reindex σ) (first.reindex σ)⟩ :
      {z : Term (reindex A (L ≫ p)) // (first.reindex σ).Fills z}) =
      ⟨a.reindex L,ha.reindex σ⟩ := Subtype.ext (hF.uniform p φ first σ)
  calc
    _ = k ⟨a.reindex L,ha.reindex σ⟩ := congrArg k hfirst
    _ = _ := by
      dsimp only [k]
      rw [← OpenBox.sigmaSnd_reindex (B := reindex B (liftSub A p)) b a ha σ]
      exact congrArg (fun c => Presheaf.sigmaIntro (B := reindex B (liftSub A (L ≫ p)))
        (a.reindex L) c) (hG.uniform (pair p a) φ
          (OpenBox.sigmaSnd (B := reindex B (liftSub A p)) b a ha) σ)

theorem sigmaFilling_lawful {Γ : Context.{u}} {A : Family Γ} {B : Family (total A)}
    (F : Filling A) (hF : F.Lawful) (G : Filling B) (hG : G.Lawful) :
    (sigmaFilling F hF G).Lawful where
  fills := sigmaFilling_fills F hF G hG
  uniform := sigmaFilling_uniform F hF G hG

end SquareKit.Cubical.Presheaf
