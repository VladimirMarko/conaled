import SquareKit.Internal.SheafContexts
import Examples.SheafBaseChange

/-! Experimental finite sheaf interpretation of regular contexts and terms. -/
namespace Examples.SheafContexts
open CategoryTheory Opposite SquareKit.Internal SquareKit.SheafImage
open Examples.SheafImage Examples.SheafImage.Diamond
open Examples.SheafBaseChange

inductive Kind where | e | b
  deriving DecidableEq
open Kind

inductive Op : Kind → Kind → Type where | neg : Op b b

def model : Presheaf.Model (J := Diamond) Op where
  carrier
    | e => data
    | b => boolData
  arrow
    | .neg => { app _ := ↾Bool.not }

theorem carriers_areSheaves (s : Kind) : Presieve.IsSheaf topology (model.carrier s) := by
  cases s
  · exact data_isSheaf
  · exact bool_isSheaf

abbrev ctx := SquareKit.Internal.SheafContexts.context model carriers_areSheaves
abbrev sub {Γ Δ : List Kind} (σ : Sub Op Γ Δ) :=
  SquareKit.Internal.SheafContexts.substitution model carriers_areSheaves σ
abbrev proj {s : Kind} {Γ : List Kind} :=
  SquareKit.Internal.SheafContexts.projection model carriers_areSheaves (s := s) (Γ := Γ)

def empty (j : Diamondᵒᵖ) : Env (model.fiber j) [] := fun {_} i => nomatch i

def emptyIso : ctx [] ≅ terminal where
  hom := ⟨{ app _ := ↾fun _ => () }⟩
  inv := ⟨{ app j := ↾fun _ => empty j
            naturality := by intro j k f; ext x s i; nomatch i }⟩
  hom_inv_id := by ext j ρ s i; nomatch i
  inv_hom_id := rfl

def singletonIso (s : Kind) : ctx [s] ≅ SquareKit.Internal.SheafContexts.sort model carriers_areSheaves s where
  hom := ⟨{ app _ := ↾fun ρ => ρ .zero }⟩
  inv := ⟨{ app j := ↾fun x => Env.extend x (empty j)
            naturality := by
              intro j k f; ext x t i
              cases i with
              | zero => rfl
              | succ i => nomatch i }⟩
  hom_inv_id := by
    ext j ρ t i
    cases i with
    | zero => rfl
    | succ i => nomatch i
  inv_hom_id := rfl

theorem empty_unique (j : Diamondᵒᵖ) (ρ : (ctx []).obj.obj j) : @ρ = @empty j :=
  model.empty_context j ρ (empty j)

theorem e_at_X_empty : IsEmpty ((ctx [e]).obj.obj (op X)) :=
  ⟨fun ρ => Empty.elim ((singletonIso e).hom.hom.app (op X) ρ)⟩

def boolEnv (j : Diamondᵒᵖ) (x : Bool) : (ctx [b]).obj.obj j := Env.extend x (empty j)

theorem boolEnv_distinct (j : Diamondᵒᵖ) : @boolEnv j false ≠ @boolEnv j true := by
  intro h
  have : (false : Bool) = true := congrArg (fun ρ => ρ .zero) h
  cases this

def forget : Sub Op [] [b] := fun {_} i => nomatch i

theorem projection_comparison : (proj (s := e) (Γ := [])) ≫ emptyIso.hom =
    (singletonIso e).hom ≫ toTerminal := rfl

theorem forget_comparison : sub forget ≫ emptyIso.hom = (singletonIso b).hom ≫ base := rfl

def headE : ctx [e,b] ⟶ E :=
  SquareKit.Internal.SheafContexts.term model carriers_areSheaves (.var .zero)

def tailBool : ctx [e,b] ⟶ D := proj ≫ (singletonIso b).hom

noncomputable def toProduct : ctx [e,b] ⟶ P :=
  Limits.pullback.lift headE tailBool (by ext j ρ; rfl)

theorem toProduct_left : toProduct ≫ left = headE := Limits.pullback.lift_fst _ _ _
theorem toProduct_down : toProduct ≫ down = tailBool := Limits.pullback.lift_snd _ _ _

/-- Explicit product sections agree with the earlier categorical sheaf pullback. -/
noncomputable def extendedIso : ctx [e,b] ≅ P where
  hom := toProduct
  inv := ⟨{
    app j := ↾fun p => Env.extend (left.hom.app j p) (boolEnv j (down.hom.app j p))
    naturality := by
      intro j k f; ext p s i
      cases i with
      | zero => exact NatTrans.naturality_apply left.hom f p
      | succ i =>
        cases i with
        | zero => exact NatTrans.naturality_apply down.hom f p
        | succ i => nomatch i }⟩
  hom_inv_id := by
    ext j ρ s i
    cases i with
    | zero => exact congrArg (fun (f : ctx [e,b] ⟶ E) => f.hom.app j ρ) toProduct_left
    | succ i =>
      cases i with
      | zero => exact congrArg (fun (f : ctx [e,b] ⟶ D) => f.hom.app j ρ) toProduct_down
      | succ i => nomatch i
  inv_hom_id := by
    apply square.hom_ext
    · rw [Category.assoc, toProduct_left]
      rfl
    · rw [Category.assoc, toProduct_down]
      rfl

theorem extended_left : extendedIso.hom ≫ left = headE := toProduct_left

theorem extended_down : extendedIso.hom ≫ down = proj ≫ (singletonIso b).hom :=
  toProduct_down

noncomputable def extendedSections (j : Diamondᵒᵖ) :
    (ctx [e,b]).obj.obj j ≃ data.obj j × Bool :=
  ((sheafToPresheaf topology Type ⋙ (evaluation _ Type).obj j).mapIso extendedIso).toEquiv.trans
    (productSections j)

theorem extendedSections_apply (j : Diamondᵒᵖ) (ρ : (ctx [e,b]).obj.obj j) :
    extendedSections j ρ = (ρ .zero, ρ (.succ .zero)) := by
  apply Prod.ext
  · exact congrArg (fun (f : ctx [e,b] ⟶ E) => f.hom.app j ρ) toProduct_left
  · exact congrArg (fun (f : ctx [e,b] ⟶ D) => f.hom.app j ρ) toProduct_down

theorem lift_comparison : sub (forget.lift (b := e)) ≫ (singletonIso e).hom =
    extendedIso.hom ≫ left := by
  rw [extended_left]
  rfl

/-- The empty substitution, extended by E, is the required context pullback. -/
theorem finite_square : IsPullback (sub (forget.lift (b := e))) proj proj (sub forget) :=
  SquareKit.Internal.SheafContexts.context_pullback model carriers_areSheaves forget e

/-- Transport E → 1 along the checked context isomorphisms. -/
theorem context_top : localImage ⊤ (proj (s := e) (Γ := [])) = ⊤ := by
  have hs : IsPullback (singletonIso e).hom proj toTerminal emptyIso.hom :=
    IsPullback.of_horiz_isIso ⟨projection_comparison.symm⟩
  have h := beckChevalley (⊤ : Subfunctor E.obj) hs
  have ht : (⊤ : Subfunctor E.obj).preimage (singletonIso e).hom.hom = ⊤ := rfl
  rw [ht, Examples.SheafImage.localImage_top] at h
  exact h.symm

/-- Contextual Beck–Chevalley proves local existence over every Bool environment. -/
theorem extended_top : localImage ⊤ (proj (s := e) (Γ := [b])) = ⊤ := by
  have h := SquareKit.Internal.SheafContexts.exists_substitution model carriers_areSheaves
    (⊤ : Subfunctor (model.context [e])) forget
  have ht : (⊤ : Subfunctor (model.context [e])).preimage (sub forget.lift).hom = ⊤ := rfl
  rw [ht, context_top] at h
  exact h.symm

theorem locally_at_X (x : Bool) :
    (localImage ⊤ (proj (s := e))).obj (op X) (boolEnv (op X) x) := by
  rw [extended_top]; trivial

theorem no_pointwise_at_X (x : Bool) :
    ¬ ((⊤ : Subfunctor (model.context [e,b])).image (proj (s := e)).hom).obj
      (op X) (boolEnv (op X) x) := by
  rintro ⟨ρ, _, _⟩
  exact no_pointwise_witness ⟨ρ .zero, trivial, rfl⟩

def selected : Subfunctor (model.context []) := selective.preimage emptyIso.hom.hom

theorem selected_image :
    localImage (selected.preimage (proj (s := e)).hom) proj = selected := by
  have hc := preimage_isSheaf selective emptyIso.hom selective_isSheaf
  have h := frobenius (⊤ : Subfunctor (model.context [e])) proj selected hc
  rw [top_inf_eq, context_top, top_inf_eq] at h
  exact h

theorem extended_selected :
    localImage ((selected.preimage (proj (s := e)).hom).preimage (sub forget.lift).hom) proj =
      selected.preimage (sub forget).hom := by
  rw [← SquareKit.Internal.SheafContexts.exists_substitution model carriers_areSheaves _ forget, selected_image]

theorem selected_at_U (x : Bool) :
    (localImage ((selected.preimage (proj (s := e)).hom).preimage (sub forget.lift).hom) proj).obj
      (op U) (boolEnv (op U) x) := by
  rw [extended_selected]; exact Or.inr rfl

theorem selected_not_V (x : Bool) :
    ¬ (localImage ((selected.preimage (proj (s := e)).hom).preimage (sub forget.lift).hom) proj).obj
      (op V) (boolEnv (op V) x) := by
  rw [extended_selected]; change ¬ (V = W ∨ V = U); decide

theorem selected_not_X (x : Bool) :
    ¬ (localImage ((selected.preimage (proj (s := e)).hom).preimage (sub forget.lift).hom) proj).obj
      (op X) (boolEnv (op X) x) := by
  rw [extended_selected]; change ¬ (X = W ∨ X = U); decide

def neg : Term Op [b] b := .app .neg (.var .zero)
def negate : Sub Op [b] [b] := fun {_} i => match i with
  | .zero => neg
  | .succ i => nomatch i

theorem neg_substitution :
    SquareKit.Internal.SheafContexts.term model carriers_areSheaves (neg.subst negate) =
      sub negate ≫ SquareKit.Internal.SheafContexts.term model carriers_areSheaves neg :=
  SquareKit.Internal.SheafContexts.term_substitution model carriers_areSheaves negate neg

theorem neg_value (x : Bool) :
    (SquareKit.Internal.SheafContexts.term model carriers_areSheaves neg).hom.app (op X) (boolEnv (op X) x) = !x := rfl

theorem twice_neg_value (x : Bool) :
    (SquareKit.Internal.SheafContexts.term model carriers_areSheaves (neg.subst negate)).hom.app (op X) (boolEnv (op X) x) = x := by
  rw [neg_substitution]
  change (!(!x)) = x
  cases x <;> rfl

-- Ordinary callers retain their existing graph interface.
example (n : Nat) : ∃ m, m = n + 1 ∧ 2 * (n + 1) = 2 * m :=
  (Graph.inSet (fun x => x + 1) (fun x => 2 * x) n _).mpr rfl

end Examples.SheafContexts
