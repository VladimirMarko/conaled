import SquareKit.Internal.Cubical.TelescopeFilling
import SquareKit.Internal.Cubical.NormalizedFillingSubstitution

/-! Substitution of a finite tail retains its chosen fillers and the
iterated product filler assembled from them. -/
namespace SquareKit.Cubical.Presheaf
open CategoryTheory
universe u

theorem Filling.convert_trans {Γ : Context.{u}} {A B C : Family Γ}
    (e : A = B) (d : B = C) (F : Filling A) :
    (F.convert e).convert d = F.convert (e.trans d) := by
  cases e
  cases d
  rfl

theorem normalizedPiFilling_convert {Γ : Context.{u}} {A : Family Γ} {B C : Family (total A)}
    (F : Filling A) (hF : F.Lawful) (G : Filling B) (e : B = C) :
    normalizedPiFilling F hF (G.convert e) =
      (normalizedPiFilling F hF G).convert (congrArg (normalizedPi A) e) := by
  cases e
  rfl

namespace Telescope

def Fillings.reindex {Γ : Context.{u}} {T : Telescope Γ} (fs : Fillings T) :
    {Δ : Context.{u}} → (σ : Δ ⟶ Γ) → Fillings (T.reindex σ) :=
  match fs with
  | .nil _ => fun _ => .nil _
  | .cons F fs => fun σ => .cons (F.reindex σ) (fs.reindex (liftSub _ σ))

theorem Fillings.Lawful.reindex {Γ Δ : Context.{u}} {T : Telescope Γ} {fs : Fillings T}
    (h : fs.Lawful) (σ : Δ ⟶ Γ) : (fs.reindex σ).Lawful := by
  induction fs generalizing Δ with
  | nil => trivial
  | cons F fs ih => exact ⟨h.1.reindex σ, ih h.2 _⟩

theorem Fillings.pi_reindex {Γ Δ : Context.{u}} {T : Telescope Γ} (fs : Fillings T)
    (hs : fs.Lawful) {C : Family T.context} (G : Filling C) (σ : Δ ⟶ Γ) :
    ((fs.pi hs G).reindex σ).convert (T.pi_reindex C σ) =
      (fs.reindex σ).pi (hs.reindex σ) (G.reindex (T.map σ)) := by
  induction fs generalizing Δ with
  | nil => rfl
  | @cons Γ A T F fs ih =>
    change ((normalizedPiFilling F hs.1 (fs.pi hs.2 G)).reindex σ).convert
      ((normalizedPi_reindex A (T.pi C) σ).trans
        (congrArg (normalizedPi (Presheaf.reindex A σ)) (T.pi_reindex C (liftSub A σ)))) = _
    rw [← Filling.convert_trans (normalizedPi_reindex A (T.pi C) σ)
      (congrArg (normalizedPi (Presheaf.reindex A σ)) (T.pi_reindex C (liftSub A σ)))]
    rw [normalizedPiFilling_reindex, ← normalizedPiFilling_convert _ _ _ (T.pi_reindex C (liftSub A σ))]
    exact congrArg (normalizedPiFilling (F.reindex σ) (hs.1.reindex σ)) (ih hs.2 G (liftSub A σ))

end Telescope
end SquareKit.Cubical.Presheaf
