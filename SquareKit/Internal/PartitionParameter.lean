import SquareKit.Internal.PartitionSection

/-! Transport of parameter subterminals along isomorphisms preserves both
predicate carriers and every predicate-preserving map. -/
noncomputable section
set_option autoImplicit false
namespace SquareKit.Internal.PartitionSection
open CategoryTheory CategoryTheory.Limits
universe v u
variable {C : Type u} [Category.{v} C] [HasTerminal C] [FinitaryExtensive C]
variable {U V : C} (u : U ⟶ ⊤_ C) (v : V ⟶ ⊤_ C) [Mono u] [Mono v]

/-- Parameter transport changes only the bound map. -/
def mapParameter (t : U ⟶ V) : Model u ⥤ Model v where
  obj M := {
    P := M.P, Q := M.Q, p := M.p, q := M.q
    bound := M.bound ≫ t
    bound_over := terminal.hom_ext _ _
    partition := M.partition }
  map f := ⟨f.left, f.right, f.left_over, f.right_over⟩
  map_id _ := Subsingleton.elim _ _
  map_comp _ _ := Subsingleton.elim _ _

/-- The isomorphism case of parameter transport. -/
def changeParameter (e : U ≅ V) : Model u ⥤ Model v := mapParameter u v e.hom

/-- Parameter isomorphisms yield model-category equivalences, retaining the predicates. -/
def parameterEquivalence (e : U ≅ V) : Model u ≌ Model v where
  functor := changeParameter u v e
  inverse := changeParameter v u e.symm
  unitIso := NatIso.ofComponents (fun M => {
    hom := ⟨𝟙 _, 𝟙 _, Category.id_comp _, Category.id_comp _⟩
    inv := ⟨𝟙 _, 𝟙 _, Category.id_comp _, Category.id_comp _⟩
    hom_inv_id := Subsingleton.elim _ _
    inv_hom_id := Subsingleton.elim _ _ }) (by intros; apply Subsingleton.elim)
  counitIso := NatIso.ofComponents (fun M => {
    hom := ⟨𝟙 _, 𝟙 _, Category.id_comp _, Category.id_comp _⟩
    inv := ⟨𝟙 _, 𝟙 _, Category.id_comp _, Category.id_comp _⟩
    hom_inv_id := Subsingleton.elim _ _
    inv_hom_id := Subsingleton.elim _ _ }) (by intros; apply Subsingleton.elim)

/-- Parameter transport preserves the meaning of a section under the coproduct map. -/
theorem mapParameter_section (t : U ⟶ V) (M : Model u) :
    ((mapParameter u v t).obj M).toSection = M.toSection ≫ coprod.map t (𝟙 (⊤_ C)) := by
  apply M.partition.hom_ext
  rintro ⟨j⟩
  cases j
  · change ((mapParameter u v t).obj M).p ≫ _ = _
    rw [Model.p_section]
    change (M.bound ≫ t) ≫ coprod.inl = M.p ≫ M.toSection ≫ coprod.map t (𝟙 _)
    rw [← Category.assoc M.p, Model.p_section]
    simp only [Category.assoc, coprod.inl_map]
  · change ((mapParameter u v t).obj M).q ≫ _ = _
    rw [Model.q_section]
    change M.q ≫ coprod.inr = M.q ≫ M.toSection ≫ coprod.map t (𝟙 _)
    rw [← Category.assoc M.q, Model.q_section, Category.assoc, coprod.inr_map, Category.id_comp]
/-- Isomorphic parameter transport has the same section formula. -/
theorem changeParameter_section (e : U ≅ V) (M : Model u) :
    ((changeParameter u v e).obj M).toSection = M.toSection ≫ coprod.map e.hom (𝟙 (⊤_ C)) :=
  mapParameter_section u v e.hom M
end SquareKit.Internal.PartitionSection

namespace SquareKit.Internal.PartitionSection
open CategoryTheory CategoryTheory.Limits
universe v u
variable {C : Type u} [Category.{v} C] [HasTerminal C] [FinitaryExtensive C]
variable {U V W : C} (u : U ⟶ ⊤_ C) (v : V ⟶ ⊤_ C) (w : W ⟶ ⊤_ C)
variable [Mono u] [Mono v] [Mono w]

/-- Identity parameter substitution keeps the carriers and predicate maps. -/
def parameterIdentityIso : mapParameter u u (𝟙 U) ≅ 𝟭 (Model u) :=
  NatIso.ofComponents (fun M => {
    hom := ⟨𝟙 _, 𝟙 _, terminal.hom_ext _ _, terminal.hom_ext _ _⟩
    inv := ⟨𝟙 _, 𝟙 _, terminal.hom_ext _ _, terminal.hom_ext _ _⟩
    hom_inv_id := Subsingleton.elim _ _
    inv_hom_id := Subsingleton.elim _ _ }) (by intros; apply Subsingleton.elim)

/-- Successive parameter substitutions compare with their actual composite. -/
def parameterCompIso (s : U ⟶ V) (t : V ⟶ W) :
    mapParameter u v s ⋙ mapParameter v w t ≅ mapParameter u w (s ≫ t) :=
  NatIso.ofComponents (fun M => {
    hom := ⟨𝟙 _, 𝟙 _, terminal.hom_ext _ _, terminal.hom_ext _ _⟩
    inv := ⟨𝟙 _, 𝟙 _, terminal.hom_ext _ _, terminal.hom_ext _ _⟩
    hom_inv_id := Subsingleton.elim _ _
    inv_hom_id := Subsingleton.elim _ _ }) (by intros; apply Subsingleton.elim)
end SquareKit.Internal.PartitionSection
