import Examples.CartesianClassifier
/-! Dependent Sigma boxes with a proper face, variable cap and composed substitutions. -/
set_option autoImplicit false
set_option warningAsError true
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
noncomputable section
namespace Examples.SharedSigmaFilling
open CategoryTheory SquareKit.Cubical.Cartesian
abbrev ctx := representable.{0} (⟨3⟩ : Cube)
def cap : Term (interval ctx) where
  val x := ⟨fun _ => x.val.down (0 : Fin 3)⟩
  property f := by
    apply ULift.ext
    funext i
    exact congrArg (fun k => k (0 : Fin 3)) (congrArg ULift.down f.map_val)
def face : Subcontext ctx := (Face.eq (.var (1 : Fin 3)) (.endpoint false)).cofibration.toSubcontext

theorem cap_ne_endpoint (b : Bool) : cap ≠ endpoint ctx b := by
  intro h
  have hh := congrArg (fun t => (t.val (representableGeneric ⟨3⟩)).down (0 : Fin 1)) h
  cases hh

theorem face_proper : ¬ face.holds (representableGeneric ⟨3⟩) := by
  intro h
  change Dim.var (1 : Fin 3) = Dim.endpoint false at h
  cases h

def zeroPoint : ctx.Elements := ctx.elementsMk (.op ⟨0⟩) ⟨fun _ => .endpoint false⟩
theorem face_inhabited : face.holds zeroPoint := rfl

def selected (b : Bool) (n : Fin (if b then 2 else 1)) :
    Term (sigma (ClassifierExamples.tags ctx) (ClassifierExamples.branch ctx)) where
  val _ := ⟨⟨b⟩,⟨n⟩⟩
  property _ := rfl

def box (b : Bool) (n : Fin (if b then 2 else 1)) :
    OpenBox (reindex (sigma (ClassifierExamples.tags ctx) (ClassifierExamples.branch ctx))
      (projection (interval ctx))) face cap where
  tube := PartialSection.ofTerm _ (Term.reindex (selected b n) (projection (interval ctx)))
  base := selected b n
  boundary _ _ := rfl

def swap01 : (⟨3⟩ : Cube) ⟶ ⟨3⟩ := fun i => .var (Equiv.swap (0 : Fin 3) 1 i)
def swap12 : (⟨3⟩ : Cube) ⟶ ⟨3⟩ := fun i => .var (Equiv.swap (1 : Fin 3) 2 i)
def σ : ctx ⟶ ctx := representableMap swap01
def τ : ctx ⟶ ctx := representableMap swap12

theorem sigma_ne_id : σ ≠ 𝟙 ctx := by
  intro h
  have hh := congrArg (fun f : ctx ⟶ ctx => (f.app (.op ⟨3⟩) ⟨𝟙 _⟩).down (0 : Fin 3)) h
  change Dim.var (1 : Fin 3) = Dim.var (0 : Fin 3) at hh
  have := Dim.var.inj hh
  contradiction

theorem tau_ne_id : τ ≠ 𝟙 ctx := by
  intro h
  have hh := congrArg (fun f : ctx ⟶ ctx => (f.app (.op ⟨3⟩) ⟨𝟙 _⟩).down (1 : Fin 3)) h
  change Dim.var (2 : Fin 3) = Dim.var (1 : Fin 3) at hh
  have := Dim.var.inj hh
  contradiction

theorem composite_ne_id : τ ≫ σ ≠ 𝟙 ctx := by
  intro h
  have hh := congrArg (fun f : ctx ⟶ ctx => (f.app (.op ⟨3⟩) ⟨𝟙 _⟩).down (0 : Fin 3)) h
  change Dim.var (2 : Fin 3) = Dim.var (0 : Fin 3) at hh
  have := Dim.var.inj hh
  contradiction
end Examples.SharedSigmaFilling

namespace Examples.SharedSigmaFilling
open CategoryTheory SquareKit.Cubical.Cartesian
abbrev filling := ClassifierExamples.sumFilling ctx
abbrev p := projection (interval ctx)
def filled (b : Bool) (n : Fin (if b then 2 else 1)) := filling.fill p face cap (box b n)
theorem cap_recovery (b : Bool) (n : Fin (if b then 2 else 1)) :
    Term.reindex (filled b n) (graph cap) = selected b n :=
  ((ClassifierExamples.sumFilling_lawful ctx).fills p face cap (box b n)).1
example : ((Term.reindex (filled true 1) (graph cap)).val zeroPoint).2.down.val = 1 := by
  rw [cap_recovery]
  rfl
example : ((Term.reindex (filled false 0) (graph cap)).val zeroPoint).2.down.val = 0 := by
  rw [cap_recovery]
  rfl

theorem first_substitution (b : Bool) (n : Fin (if b then 2 else 1)) :
    filling.fill (intervalSub σ ≫ p) (face.reindex σ) (Term.reindex cap σ) ((box b n).reindex σ) =
      Term.reindex (filled b n) (intervalSub σ) :=
  (ClassifierExamples.sumFilling_lawful ctx).uniform p face cap (box b n) σ

theorem two_substitutions (b : Bool) (n : Fin (if b then 2 else 1)) :
    filling.fill (intervalSub τ ≫ intervalSub σ ≫ p) ((face.reindex σ).reindex τ)
      (Term.reindex (Term.reindex cap σ) τ) (((box b n).reindex σ).reindex τ) =
        Term.reindex (Term.reindex (filled b n) (intervalSub σ)) (intervalSub τ) := by
  rw [(ClassifierExamples.sumFilling_lawful ctx).uniform, first_substitution]

theorem composite_substitution (b : Bool) (n : Fin (if b then 2 else 1)) :
    filling.fill (intervalSub (τ ≫ σ) ≫ p) (face.reindex (τ ≫ σ))
      (Term.reindex cap (τ ≫ σ)) ((box b n).reindex (τ ≫ σ)) =
        Term.reindex (Term.reindex (filled b n) (intervalSub σ)) (intervalSub τ) :=
  (ClassifierExamples.sumFilling_lawful ctx).uniform p face cap (box b n) (τ ≫ σ)
end Examples.SharedSigmaFilling
