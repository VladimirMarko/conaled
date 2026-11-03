import SquareKit.SheafBaseChange
import Examples.SheafImage

/-! Experimental finite base change for local existential images.
The chosen categorical pullback has sections E × Bool; at X it is empty.
-/
namespace Examples.SheafBaseChange
open CategoryTheory Opposite SquareKit.SheafImage
open Examples.SheafImage Examples.SheafImage.Diamond

/-- Every object receives an arrow from the overlap W. -/
def fromW : (a : Diamond) → (W ⟶ a)
  | W => .id W
  | U => .wu
  | V => .wv
  | X => .wx

def boolData : Diamondᵒᵖ ⥤ Type := (Functor.const _).obj Bool

/-- Compatibility on W forces all local Bool sections to be equal. -/
theorem bool_isSheaf : Presieve.IsSheaf topology boolData := by
  intro a S hS x hx
  have hw := hS W (fromW a) (by decide)
  refine ⟨(show Bool from @x W (fromW a) hw), ?_, ?_⟩
  · intro b f hf
    exact hx (𝟙 W) (fromW b) hw hf ((inferInstance : Subsingleton (Arrow W a)).elim _ _)
  · intro t ht
    exact ht (fromW a) hw

abbrev D : Sheaf topology Type :=
  ⟨boolData, (isSheaf_iff_isSheaf_of_type _ _).mpr bool_isSheaf⟩

def base : D ⟶ terminal := ⟨{ app _ := ↾fun _ => () }⟩

/-- The base change is nontrivial: it identifies two distinct sections at X. -/
theorem base_not_injective : ¬ Function.Injective (base.hom.app (op X)) := by
  intro h
  have : (false : Bool) = true := h rfl
  cases this

noncomputable abbrev P := Limits.pullback toTerminal base
noncomputable abbrev left : P ⟶ E := Limits.pullback.fst toTerminal base
noncomputable abbrev down : P ⟶ D := Limits.pullback.snd toTerminal base

theorem square : IsPullback left down toTerminal base := IsPullback.of_hasPullback _ _

/-- The chosen sheaf pullback has the independently expected product sections. -/
noncomputable def productSections (a : Diamondᵒᵖ) : P.obj.obj a ≃ (data.obj a × Bool) :=
  Equiv.ofBijective (fun p => (left.hom.app a p, down.hom.app a p)) (by
    constructor
    · intro p q h
      exact Limits.Types.ext_of_isPullback (sections_isPullback square a)
        (congrArg Prod.fst h) (congrArg Prod.snd h)
    · rintro ⟨e, b⟩
      obtain ⟨p, he, hb⟩ := Limits.Types.exists_of_isPullback (sections_isPullback square a)
        e b rfl
      exact ⟨p, Prod.ext he hb⟩)

theorem productSections_left (a : Diamondᵒᵖ) (p : P.obj.obj a) :
    (productSections a p).1 = left.hom.app a p := rfl

theorem productSections_down (a : Diamondᵒᵖ) (p : P.obj.obj a) :
    (productSections a p).2 = down.hom.app a p := rfl

theorem productSections_naturality {a b : Diamondᵒᵖ} (f : a ⟶ b) (p : P.obj.obj a) :
    productSections b (P.obj.map f p) =
      (data.map f (productSections a p).1, (productSections a p).2) := by
  apply Prod.ext
  · exact NatTrans.naturality_apply left.hom f p
  · exact NatTrans.naturality_apply down.hom f p

/-- The public substitution law computes the base-changed top image. -/
theorem baseChanged_top : localImage ⊤ down = ⊤ := by
  have h := beckChevalley (⊤ : Subfunctor E.obj) square
  have htop : (⊤ : Subfunctor E.obj).preimage left.hom = ⊤ := rfl
  rw [htop, Examples.SheafImage.localImage_top] at h
  exact h.symm

/-- Both Bool sections have local lifts over X. -/
theorem locally_at_X (b : Bool) : (localImage ⊤ down).obj (op X) b := by
  rw [baseChanged_top]
  trivial

/-- A global lift would give the forbidden E section through the first projection. -/
theorem no_pointwise_at_X (b : Bool) :
    ¬ ((⊤ : Subfunctor P.obj).image down.hom).obj (op X) b := by
  rintro ⟨p, _, _⟩
  exact no_pointwise_witness ⟨left.hom.app (op X) p, trivial, rfl⟩

example : (localImage ⊤ down).obj (op X) false ∧ (localImage ⊤ down).obj (op X) true :=
  ⟨locally_at_X false, locally_at_X true⟩

/-- Source selection is first pulled back along E → 1, then along the square. -/
theorem baseChanged_selective :
    localImage ((selective.preimage toTerminal.hom).preimage left.hom) down =
      selective.preimage base.hom := by
  have hs : localImage (selective.preimage toTerminal.hom) toTerminal = selective := by
    simpa using selective_image
  rw [← beckChevalley _ square, hs]

theorem selective_at_U (b : Bool) :
    (localImage ((selective.preimage toTerminal.hom).preimage left.hom) down).obj (op U) b := by
  rw [baseChanged_selective]
  exact Or.inr rfl

theorem selective_not_V (b : Bool) :
    ¬ (localImage ((selective.preimage toTerminal.hom).preimage left.hom) down).obj (op V) b := by
  rw [baseChanged_selective]
  change ¬ (V = W ∨ V = U)
  decide

theorem selective_not_X (b : Bool) :
    ¬ (localImage ((selective.preimage toTerminal.hom).preimage left.hom) down).obj (op X) b := by
  rw [baseChanged_selective]
  change ¬ (X = W ∨ X = U)
  decide

example (Q : Subfunctor E.obj) :
    Presieve.IsSheaf topology ((localImage Q toTerminal).preimage base.hom).toFunctor ∧
    Presieve.IsSheaf topology (localImage (Q.preimage left.hom) down).toFunctor :=
  beckChevalley_isSheaf Q left down toTerminal base

-- The opt-in sheaf application retains ordinary graph calls.
example (n : Nat) : ∃ m, m = n + 1 ∧ 2 * (n + 1) = 2 * m :=
  (SquareKit.Internal.Graph.inSet (fun x => x + 1) (fun x => 2 * x) n _).mpr rfl

end Examples.SheafBaseChange
