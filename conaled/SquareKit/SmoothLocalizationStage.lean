import SquareKit.SmoothLocalization
import SquareKit.SmoothStage

/-! Experimental finite-presentation stages and coordinate restrictions for smooth localizations. -/
noncomputable section
namespace SquareKit.SmoothAlgebra.Localization
open CategoryTheory

def stage {n k : ℕ} (f : Fin k → Free n) : SmoothStage.Stage :=
  .presented (n + k) k (relation f)

def stageBase {n k : ℕ} (f : Fin k → Free n) : SmoothStage.Stage.free n ⟶ stage f := base f

/-- The stage Hom equivalence is exactly the algebra's universal property. -/
def stageHomEquiv {n k : ℕ} (f : Fin k → Free n) (B : SmoothStage.Stage) :
    (stage f ⟶ B) ≃ {h : Hom (Free n) (SmoothStage.Carrier B) // ∀ j, IsUnit (h (f j))} := homEquiv f

def coordinateMap {n m : ℕ} (f : Free n) (g : Free m) (c : Fin n → Operation m)
    (hc : pullback c f = g) : stage (fun _ : Fin 1 => f) ⟶ stage (fun _ : Fin 1 => g) :=
  map f g (pullback c) hc

theorem coordinateMap_base {n m : ℕ} (f : Free n) (g : Free m) (c : Fin n → Operation m)
    (hc : pullback c f = g) :
    stageBase (fun _ : Fin 1 => f) ≫ coordinateMap f g c hc =
      (show SmoothStage.Stage.free n ⟶ .free m from pullback c) ≫ stageBase (fun _ : Fin 1 => g) :=
  map_base f g (pullback c) hc

end SquareKit.SmoothAlgebra.Localization
