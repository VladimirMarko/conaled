import SquareKit.OracleModalityKripke
import SquareKit.SheafSections
import Mathlib.CategoryTheory.Category.Preorder

/-! The same persistent oracle propositions as actual subterminal sheaves.
This constructs ordinary section objects, not quotient-inductive oracle sheafification. -/

namespace OracleModality.Kripke

open CategoryTheory Opposite SquareKit.SheafRelation

variable {W : Type} [Preorder W]

abbrev Site (W : Type) := OrderDual W
abbrev AnswerSheaf (W : Type) [Preorder W] :=
  Sheaf (⊥ : GrothendieckTopology (Site W)) (Type 0)

/-- Answers at a stage are lifted proofs of the explicitly represented predicate. -/
def answerData (U : Truth W) : (Site W)ᵒᵖ ⥤ Type where
  obj X := PLift (X.unop ∈ U)
  map f := ↾fun h => ⟨U.lower (@leOfHom (Site W) _ _ _ f.unop) h.down⟩
  map_id _ := by ext x; exact Subsingleton.elim _ _
  map_comp _ _ := by ext x; exact Subsingleton.elim _ _

def answers (U : Truth W) : AnswerSheaf W :=
  ⟨answerData U, Presheaf.isSheaf_bot _⟩

instance answer_subsingleton (U : Truth W) (X : (Site W)ᵒᵖ) :
    Subsingleton ((answers U).obj.obj X) := inferInstanceAs (Subsingleton (PLift (X.unop ∈ U)))

private instance product_answer_subsingleton (U V : Truth W) (X : (Site W)ᵒᵖ) :
    Subsingleton ((product (answers U) (answers V)).obj.obj X) :=
  inferInstanceAs (Subsingleton (PLift (X.unop ∈ U) × PLift (X.unop ∈ V)))

/-- The answer object's support is exactly the given truth value. -/
theorem answer_support (U : Truth W) (w : W) :
    Nonempty ((answers U).obj.obj (op (show Site W from w))) ↔ w ∈ U :=
  ⟨fun ⟨h⟩ => h.down, fun h => ⟨⟨h⟩⟩⟩

def inclusion {U V : Truth W} (h : U ≤ V) : answers U ⟶ answers V :=
  ⟨{ app _ := ↾fun x => ⟨h x.down⟩
     naturality := by intros; ext x; exact Subsingleton.elim _ _ }⟩

/-- Full entailment representation for the selected persistent predicates. -/
theorem hom_iff (U V : Truth W) : Nonempty (answers U ⟶ answers V) ↔ U ≤ V := by
  constructor
  · rintro ⟨f⟩ w hw
    exact (f.hom.app (op (show Site W from w)) ⟨hw⟩).down
  · intro h
    exact ⟨inclusion h⟩

/-- The actual product answer object represents conjunction. -/
def productIso (U V : Truth W) : product (answers U) (answers V) ≅ answers (U ⊓ V) where
  hom := ⟨{ app _ := ↾fun h => ⟨h.1.down, h.2.down⟩
            naturality := by intros; ext x; exact Subsingleton.elim _ _ }⟩
  inv := ⟨{ app _ := ↾fun h => (⟨h.down.1⟩, ⟨h.down.2⟩)
            naturality := by intros; ext x; exact Subsingleton.elim _ _ }⟩
  hom_inv_id := by ext X x; exact Subsingleton.elim _ _
  inv_hom_id := by ext X x; exact Subsingleton.elim _ _

/-- Parameterized implication is represented by actual sheaf maps between these predicates. -/
theorem parameterized_implication (R U V : Truth W) :
    Nonempty (product (answers R) (answers U) ⟶ answers V) ↔ R ≤ U ⇨ V := by
  rw [le_himp_iff, ← hom_iff]
  constructor
  · rintro ⟨f⟩
    exact ⟨(productIso R U).inv ≫ f⟩
  · rintro ⟨f⟩
    exact ⟨(productIso R U).hom ≫ f⟩

/-- The display forgets an answer; its section must construct answers at every stage. -/
def display (U : Truth W) : answers U ⟶ answers ⊤ := inclusion le_top

private theorem top_hom_unique {A : AnswerSheaf W} (f g : A ⟶ answers ⊤) : f = g := by
  ext X x
  exact Subsingleton.elim _ _

theorem term_iff (U : Truth W) : Nonempty (SquareKit.Family.Term (display U)) ↔ U = ⊤ := by
  constructor
  · rintro ⟨t⟩
    exact top_le_iff.mp ((hom_iff ⊤ U).mp ⟨t.val⟩)
  · intro h
    subst U
    exact ⟨⟨𝟙 _, top_hom_unique _ _⟩⟩

/-- An actual global internal section exists exactly when the unmodalized predicate is valid. -/
theorem global_section_iff (U : Truth W) :
    Nonempty (SquareKit.SheafSections.unit ⟶ SquareKit.SheafSections.sections (display U)) ↔
      U = ⊤ := by
  rw [← term_iff]
  exact (SquareKit.SheafSections.globalEquiv (display U)).nonempty_congr

/-- The positive section uses the existing name/global-name construction. -/
noncomputable def topSection :
    SquareKit.SheafSections.unit ⟶ SquareKit.SheafSections.sections (display (⊤ : Truth W)) :=
  SquareKit.SheafSections.name _ ⟨𝟙 _, top_hom_unique _ _⟩

end OracleModality.Kripke
