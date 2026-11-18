import SquareKit.Internal.Cubical.SequentialFilling
import SquareKit.Internal.Cubical.Filling
import SquareKit.Internal.Cubical.PartialSums

/-! Fill a dependent pair by filling its first component, then its second
component along that actual first filler. -/
namespace SquareKit.Cubical.Presheaf
open CategoryTheory SquareKit.SequentialFilling
universe u

def sigmaFilling {Γ : Context.{u}} {A : Family Γ} {B : Family (total A)}
    (F : Filling A) (hF : F.Lawful) (G : Filling B) : Filling (sigma A B) where
  fill p φ b :=
    let a := F.fill p φ (OpenBox.sigmaFst (B := reindex B (liftSub A p)) b)
    let ha := (hF.fills p φ (OpenBox.sigmaFst (B := reindex B (liftSub A p)) b))
    let c := G.fill (pair p a) φ (OpenBox.sigmaSnd (B := reindex B (liftSub A p)) b a ha)
    Presheaf.sigmaIntro (B := reindex B (liftSub A p)) a c

/-- Native data for the shared two-stage selection proof. -/
def sigmaProblem {Γ Δ : Context.{u}} {A : Family Γ} {B : Family (total A)} (F : Filling A) (hF : F.Lawful) (G : Filling B)
    (p : total (interval Δ) ⟶ Γ) (φ : Cofibration Δ) (b : OpenBox (reindex (sigma A B) p) φ) : Problem where
  FirstBox := OpenBox (reindex A p) φ
  First := Term (reindex A p)
  firstBox := OpenBox.sigmaFst (B := reindex B (liftSub A p)) b
  firstFill := F.fill p φ
  FirstFills := OpenBox.Fills
  first_fills := hF.fills p φ
  SecondBox a := OpenBox (reindex B (pair p a)) φ
  Second a := Term (reindex B (pair p a))
  secondBox a ha := OpenBox.sigmaSnd (B := reindex B (liftSub A p)) b a ha
  secondFill a := G.fill (pair p a) φ
  Whole := Term (reindex (sigma A B) p)
  pair := Presheaf.sigmaIntro (B := reindex B (liftSub A p))

/-- The shared selection retains the native algorithm exactly. -/
theorem sigmaProblem_fill {Γ Δ : Context.{u}} {A : Family Γ} {B : Family (total A)} (F : Filling A) (hF : F.Lawful) (G : Filling B)
    (p : total (interval Δ) ⟶ Γ) (φ : Cofibration Δ) (b : OpenBox (reindex (sigma A B) p) φ) :
    (sigmaProblem F hF G p φ b).fill = (sigmaFilling F hF G).fill p φ b := rfl

set_option backward.isDefEq.respectTransparency false in
def sigmaSubstitution {Γ Δ Θ : Context.{u}} {A : Family Γ} {B : Family (total A)} (F : Filling A) (hF : F.Lawful) (G : Filling B) (hG : G.Lawful)
    (p : total (interval Δ) ⟶ Γ) (φ : Cofibration Δ) (b : OpenBox (reindex (sigma A B) p) φ) (σ : Θ ⟶ Δ) :
    Substitution (sigmaProblem F hF G p φ b)
      (sigmaProblem F hF G (liftSub (interval Δ) σ ≫ p) (φ.reindex σ) (b.reindex σ)) where
  firstBox b := b.reindex σ
  first a := a.reindex (liftSub (interval Δ) σ)
  firstBox_eq := rfl
  first_uniform b := hF.uniform p φ b σ
  first_fills _a ha := ha.reindex σ
  secondBox _a b := b.reindex σ
  second _a c := c.reindex (liftSub (interval Δ) σ)
  whole c := c.reindex (liftSub (interval Δ) σ)
  secondBox_eq a ha := (OpenBox.sigmaSnd_reindex (B := reindex B (liftSub A p)) b a ha σ).symm
  second_uniform a b := hG.uniform (pair p a) φ b σ
  pair_eq _ _ := rfl

theorem sigmaFilling_fills {Γ Δ : Context.{u}} {A : Family Γ} {B : Family (total A)}
    (F : Filling A) (hF : F.Lawful) (G : Filling B) (hG : G.Lawful)
    (p : total (interval Δ) ⟶ Γ) (φ : Cofibration Δ) (b : OpenBox (reindex (sigma A B) p) φ) :
    b.Fills ((sigmaFilling F hF G).fill p φ b) :=
  (sigmaProblem F hF G p φ b).fills
    (fun _ c t => c.Fills t) b.Fills
    (fun a c => hG.fills (pair p a) φ c)
    (fun a ha c hc => OpenBox.sigmaIntro_fills (B := reindex B (liftSub A p)) b a ha c hc)

set_option backward.isDefEq.respectTransparency false in
theorem sigmaFilling_uniform {Γ Δ Θ : Context.{u}} {A : Family Γ} {B : Family (total A)}
    (F : Filling A) (hF : F.Lawful) (G : Filling B) (hG : G.Lawful)
    (p : total (interval Δ) ⟶ Γ) (φ : Cofibration Δ) (b : OpenBox (reindex (sigma A B) p) φ)
    (σ : Θ ⟶ Δ) :
    (sigmaFilling F hF G).fill (liftSub (interval Δ) σ ≫ p) (φ.reindex σ) (b.reindex σ) =
      ((sigmaFilling F hF G).fill p φ b).reindex (liftSub (interval Δ) σ) :=
  (sigmaSubstitution F hF G hG p φ b σ).uniform

theorem sigmaFilling_lawful {Γ : Context.{u}} {A : Family Γ} {B : Family (total A)}
    (F : Filling A) (hF : F.Lawful) (G : Filling B) (hG : G.Lawful) :
    (sigmaFilling F hF G).Lawful where
  fills := sigmaFilling_fills F hF G hG
  uniform := sigmaFilling_uniform F hF G hG

end SquareKit.Cubical.Presheaf
