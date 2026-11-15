import SquareKit.Internal.Cubical.Telescopes
import SquareKit.Internal.Cubical.FillingTransport
import SquareKit.Internal.Cubical.FunctionFilling

/-! Actual chosen fillers for finite dependent tails supply iterated product
filling. The capability is assembled from the already proved Pi constructor. -/
namespace SquareKit.Cubical.Presheaf
universe u
namespace Telescope

inductive Fillings : {Γ : Context.{u}} → Telescope Γ → Type (u+1) where
  | nil (Γ : Context.{u}) : Fillings (.nil Γ)
  | cons {Γ : Context.{u}} {A : Family Γ} {T : Telescope (total A)}
      (F : Filling A) (fs : Fillings T) : Fillings (.cons A T)

def Fillings.Lawful {Γ : Context.{u}} {T : Telescope Γ} : Fillings T → Prop
  | .nil _ => True
  | .cons F fs => F.Lawful ∧ fs.Lawful

noncomputable def Fillings.pi {Γ : Context.{u}} {T : Telescope Γ} (fs : Fillings T) :
    fs.Lawful → {C : Family T.context} → Filling C → Filling (T.pi C) :=
  match fs with
  | .nil _ => fun _ {_} G => G
  | .cons F fs => fun hs {_} G =>
    (piFilling F hs.1 (fs.pi hs.2 G)).transport (normalizedPiIso _ _)

theorem Fillings.pi_lawful {Γ : Context.{u}} {T : Telescope Γ} (fs : Fillings T)
    (hs : fs.Lawful) {C : Family T.context} (G : Filling C) (hG : G.Lawful) : (fs.pi hs G).Lawful := by
  induction fs with
  | nil => exact hG
  | cons F fs ih =>
    exact Filling.transport_lawful (normalizedPiIso _ _)
      (piFilling F hs.1 (fs.pi hs.2 G)) (piFilling_lawful F hs.1 (fs.pi hs.2 G) (ih hs.2 G hG))

end Telescope
end SquareKit.Cubical.Presheaf
