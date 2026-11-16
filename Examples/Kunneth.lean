import SquareKit.KunnethPredicates
import Examples.MatesBaseChange
import Mathlib.CategoryTheory.Monoidal.Types.Basic

/-! Two independently observed predicate models, nonidentity transport, and
controls for missing projection-formula hypotheses and selected native maps. -/
namespace Examples.Kunneth
open CategoryTheory MonoidalCategory SquareKit.Kunneth
open scoped CategoryTheory.SemilatticeInf
open SquareKit.Kunneth.Predicates

abbrev Base := Bool
abbrev Space := Bool × Bool
def f : Space ⟶ Base := ↾Prod.fst
abbrev W := Limits.Types.PullbackObj f f
abbrev p : W ⟶ Space := (Limits.Types.pullbackCone f f).fst
abbrev q : W ⟶ Space := (Limits.Types.pullbackCone f f).snd
theorem square : IsPullback p q f f :=
  IsPullback.of_isLimit (Limits.Types.pullbackLimitCone f f).isLimit

theorem proper_f : Function.Surjective f := fun b => ⟨(b,false), rfl⟩
theorem f_not_injective : ¬ Function.Injective f := by
  intro h
  have e := h (a₁ := (false,false)) (a₂ := (false,true)) rfl
  cases e

/-- A varies both over the base and within a nontrivial fiber. -/
def A : Fiber Unit Space := {xi | xi.1.1 = true ∨ xi.1.2 = true}
def B : Fiber Unit Space := {xi | xi.1.1 = true ∨ xi.1.2 = false}

theorem A_varies : ((false,true),()) ∈ A ∧ ((false,false),()) ∉ A := by
  change (false = true ∨ true = true) ∧ ¬ (false = true ∨ false = true)
  decide

theorem push_A (s : Bool) : (s,()) ∈ (push Unit f).obj A ↔ s = true := by
  constructor
  · intro h
    have hh := h (s,false) rfl
    change s = true ∨ false = true at hh
    exact hh.resolve_right Bool.false_ne_true
  · intro h x hx
    exact Or.inl (hx.trans h)

theorem push_B (s : Bool) : (s,()) ∈ (push Unit f).obj B ↔ s = true := by
  constructor
  · intro h
    have hh := h (s,true) rfl
    change s = true ∨ true = false at hh
    exact hh.resolve_right (by intro e; cases e)
  · intro h x hx
    exact Or.inl (hx.trans h)

noncomputable def sourceIso := Indexed.kunnethIso (proper Unit) square proper_f proper_f A B

/-- The ordinary theorem connects the independently computed input observation
with the external product over the actual pullback. -/
theorem source_observation (s : Bool) :
    (s,()) ∈ (push Unit (p ≫ f)).obj ((pull Unit p).obj A ⊗ (pull Unit q).obj B) ↔
      s = true := by
  have forward := leOfHom sourceIso.hom
  have backward := leOfHom sourceIso.inv
  constructor
  · intro h
    exact (push_A s).mp (backward h).1
  · intro h
    exact forward ⟨(push_A s).mpr h, (push_B s).mpr h⟩

/-- The second model has two independent coefficient colors. -/
def A₂ : Fiber Bool Space := {xi | xi.2 = false ∨ xi.1.1 = true}
def B₂ : Fiber Bool Space := Set.univ
noncomputable def targetIso := Indexed.kunnethIso (proper Bool) square proper_f proper_f A₂ B₂

theorem target_observation (s c : Bool) :
    (s,c) ∈ (push Bool (p ≫ f)).obj ((pull Bool p).obj A₂ ⊗ (pull Bool q).obj B₂) ↔
      c = false ∨ s = true := by
  have forward := leOfHom targetIso.hom
  have backward := leOfHom targetIso.inv
  constructor
  · intro h
    exact (backward h).1 (s,false) rfl
  · intro h
    apply forward
    constructor
    · intro x hx
      exact h.elim Or.inl (fun hs => Or.inr (hx.trans hs))
    · intro x hx
      trivial

/-- This target coefficient object cannot come from duplicating one color. -/
theorem target_outside_image :
    ¬ ∃ T : Fiber Unit Space, (recolor (fun _ : Bool => ()) Space).obj T = A₂ := by
  rintro ⟨T, h⟩
  have hfalse : ((false,false),false) ∈ (recolor (fun _ : Bool => ()) Space).obj T := by
    rw [h]
    exact Or.inl rfl
  have htrue : ((false,false),true) ∈ (recolor (fun _ : Bool => ()) Space).obj T := hfalse
  rw [h] at htrue
  cases htrue with
  | inl h => cases h
  | inr h => cases h

/-- An empty fiber defeats PF even though the pullback and adjunction exist. -/
def emptyMap : Empty ⟶ Unit := ↾Empty.elim

theorem empty_projection_not_iso :
    ¬ IsIso (projection (adj Unit emptyMap) (Set.univ : Fiber Unit Empty)
      (∅ : Fiber Unit Unit)) := by
  intro h
  let := h
  have back := leOfHom (inv (projection (adj Unit emptyMap)
    (Set.univ : Fiber Unit Empty) (∅ : Fiber Unit Unit)))
  have hv : ((),()) ∈ (push Unit emptyMap).obj
      ((Set.univ : Fiber Unit Empty) ⊗ (pull Unit emptyMap).obj (∅ : Fiber Unit Unit)) := by
    intro x
    exact x.elim
  exact (back hv).2

/-- The source instance transports to the independently defined target map. -/
theorem transported_map :
    (inputIso (fun _ : Bool => ()) f f A B).inv ≫
      (recolor (fun _ : Bool => ()) Base).map sourceIso.hom ≫
        (indexedOutputIso (fun _ : Bool => ()) p q f A B).hom =
    (Indexed.kunnethIso (proper Bool) square proper_f proper_f
      ((recolor (fun _ : Bool => ()) Space).obj A)
      ((recolor (fun _ : Bool => ()) Space).obj B)).hom :=
  indexed_transport (fun _ : Bool => ()) square A B

/-- The inverse is transported too, with the endpoint conversions reversed. -/
theorem transported_inverse :
    (indexedOutputIso (fun _ : Bool => ()) p q f A B).inv ≫
      (recolor (fun _ : Bool => ()) Base).map sourceIso.inv ≫
        (inputIso (fun _ : Bool => ()) f f A B).hom =
    (Indexed.kunnethIso (proper Bool) square proper_f proper_f
      ((recolor (fun _ : Bool => ()) Space).obj A)
      ((recolor (fun _ : Bool => ()) Space).obj B)).inv :=
  inverse_transport _ _ _ _ _ transported_map

namespace SelectedMap
/-- A non-thin control: the square selects a Boolean tag. -/
def tag : Type ⥤ Type where
 obj T := T × Bool
 map h := ↾fun x => (h x.1, x.2)
def selected : (𝟭 (Type)) ⋙ 𝟭 (Type) ⟶ (𝟭 (Type)) ⋙ tag where
 app T := ↾fun x => (x,true)

/-- Both coefficients and the selected tag survive the canonical construction. -/
theorem map_value (a : Nat) (b : Bool) :
    (SquareKit.Kunneth.map (Adjunction.id (C := Type)) (Adjunction.id (C := Type))
      (Adjunction.id (C := Type)) selected Nat Bool) (a,b) = (a,(b,true)) := rfl

/-- With this square, BC fails to be invertible and so does the Künneth map. -/
theorem not_surjective : ¬ Function.Surjective
    (SquareKit.Kunneth.map (Adjunction.id (C := Type)) (Adjunction.id (C := Type))
      (Adjunction.id (C := Type)) selected Nat Bool) := by
  intro h
  obtain ⟨⟨a,b⟩, he⟩ := h ((0 : Nat),(false,false))
  rw [map_value] at he
  have bad := congrArg (fun x : Nat × (Bool × Bool) => x.2.2) he
  cases bad
end SelectedMap

section NativeRecovery
open CategoryTheory.Limits SquareKit
variable {C D : Type} [Category C] [Category D] [HasPullbacks C] [HasPullbacks D]
 (h : Internal.GeometricMorphism D C) {X Y : C} (s : X ⟶ Y) (V : Over Y)
/-- Existing native projection observations retain their original assumptions. -/
theorem native_first_projection :
    ((h.pullbackPost s).hom.app V).left ≫
      pullback.fst (h.inverseImage.map V.hom) (h.inverseImage.map s) =
    h.inverseImage.map (pullback.fst V.hom s) :=
  MixedBaseChange.comparison_fst h.inverseImage s V

theorem native_second_projection :
    ((h.pullbackPost s).hom.app V).left ≫
      pullback.snd (h.inverseImage.map V.hom) (h.inverseImage.map s) =
    h.inverseImage.map (pullback.snd V.hom s) :=
  MixedBaseChange.comparison_snd h.inverseImage s V
end NativeRecovery

/-- The same shared adjoint-square layer retains the actual selected dependent
function after two substitutions, without any PF or exceptional-operation law. -/
abbrev native_evaluation := Examples.MatesBaseChange.FiniteProducts.twice_evaluation

theorem native_selected_value (n : Nat) :
    (SquareKit.TypeTerminalProduct.evaluate Examples.MatesBaseChange.FiniteProducts.values
      Examples.TerminalProducts.Native.last n).val = n :=
  Examples.MatesBaseChange.FiniteProducts.selected_value n

end Examples.Kunneth
