import SquareKit.Internal.SheafAssociativity
import Examples.SheafFormula

/-! Ordinary local relation composition, with optional source associativity transport. -/
namespace Examples.SheafRelations
open CategoryTheory Opposite
open SquareKit.SheafRelation SquareKit.SheafImage
open Examples.SheafImage Examples.SheafImage.Diamond
open Examples.SheafBaseChange

/-- Top relations are closed on every product sheaf. -/
theorem top_closed (A B : Sheaf topology Type) :
    Presieve.IsSheaf topology (⊤ : Relation A B).toFunctor := by
  apply (Subfunctor.isSheaf_iff _ (product_isSheaf A B)).mpr
  intros; trivial

/-- All endpoint pairs can be joined locally through E, using the prior local-image proof. -/
theorem throughE (A B : Sheaf topology Type) : comp (⊤ : Relation A E) (⊤ : Relation E B) = ⊤ := by
  apply top_unique
  intro U p _
  apply (mem_comp _ _ p).mpr
  have h : (localImage ⊤ toTerminal).obj U () := by rw [localImage_top]; trivial
  apply topology.superset_covering _ h
  intro j f hf
  rcases hf with ⟨e, _, _⟩
  exact (witness_comp _ _ f p.1 p.2).mpr ⟨e, trivial, trivial⟩

/-- Bool supplies an actual intermediate section for every endpoint pair. -/
theorem throughBool (A B : Sheaf topology Type) : comp (⊤ : Relation A D) (⊤ : Relation D B) = ⊤ := by
  apply top_unique
  intro U p _
  exact (Subfunctor.le_sheafify _ _ _) ⟨(false,p), ⟨trivial,trivial⟩, rfl⟩

theorem top_associative :
    comp (comp (⊤ : Relation terminal E) (⊤ : Relation E D)) (⊤ : Relation D D) =
      comp (⊤ : Relation terminal E) (comp (⊤ : Relation E D) (⊤ : Relation D D)) :=
  SquareKit.Internal.SheafAssociativity.associative terminal E D D _ _ _
    (top_closed _ _) (top_closed _ _) (top_closed _ _)

theorem both_at_X (b : Bool) :
    (comp (comp (⊤ : Relation terminal E) (⊤ : Relation E D)) (⊤ : Relation D D)).obj (op X) ((),b) ∧
    (comp (⊤ : Relation terminal E) (comp (⊤ : Relation E D) (⊤ : Relation D D))).obj (op X) ((),b) := by
  have hl : (comp (comp (⊤ : Relation terminal E) (⊤ : Relation E D)) (⊤ : Relation D D)).obj
      (op X) ((),b) := by rw [throughE, throughBool]; trivial
  exact ⟨hl, top_associative ▸ hl⟩

theorem no_intermediate_pair_at_X : ¬ ∃ _e : E.obj.obj (op X), ∃ _b : D.obj.obj (op X), True := by
  rintro ⟨e, _, _⟩
  exact no_pointwise_witness ⟨e,trivial,rfl⟩

/-- This last relation requires equal Bool arguments as well as W/U support. -/
abbrev selectedLast : Relation D D := Examples.SheafFormula.selectedEq

theorem selectedLast_closed : Presieve.IsSheaf topology selectedLast.toFunctor :=
  Examples.SheafFormula.selectedEq_isSheaf

def support : Relation terminal D := selective.preimage (fst terminal D).hom

theorem support_closed : Presieve.IsSheaf topology support.toFunctor :=
  preimage_isSheaf selective (fst terminal D) selective_isSheaf

/-- The intermediate Bool must equal the endpoint Bool; all such endpoints are allowed on W/U. -/
theorem selected_composition : comp (⊤ : Relation terminal D) selectedLast = support := by
  apply le_antisymm
  · apply (adjunction _ _ support support_closed).mpr
    intro U p hp
    exact hp.2.2
  · intro U p hp
    exact (Subfunctor.le_sheafify _ _ _) ⟨(p.2,p), ⟨trivial, rfl, hp⟩, rfl⟩

theorem selected_associative :
    comp (comp (⊤ : Relation terminal E) (⊤ : Relation E D)) selectedLast =
      comp (⊤ : Relation terminal E) (comp (⊤ : Relation E D) selectedLast) :=
  SquareKit.Internal.SheafAssociativity.associative terminal E D D _ _ _
    (top_closed _ _) (top_closed _ _) selectedLast_closed

theorem selected_chain :
    comp (⊤ : Relation terminal E) (comp (⊤ : Relation E D) selectedLast) = support := by
  rw [← selected_associative, throughE, selected_composition]

theorem selected_at_U (b : Bool) :
    (comp (⊤ : Relation terminal E) (comp (⊤ : Relation E D) selectedLast)).obj (op U) ((),b) := by
  rw [selected_chain]; exact Or.inr rfl

theorem selected_not_V (b : Bool) :
    ¬ (comp (⊤ : Relation terminal E) (comp (⊤ : Relation E D) selectedLast)).obj (op V) ((),b) := by
  rw [selected_chain]; change ¬ (V = W ∨ V = U); decide

theorem selected_not_X (b : Bool) :
    ¬ (comp (⊤ : Relation terminal E) (comp (⊤ : Relation E D) selectedLast)).obj (op X) ((),b) := by
  rw [selected_chain]; change ¬ (X = W ∨ X = U); decide

example (n : Nat) : ∃ m, m = n + 1 ∧ 2 * (n + 1) = 2 * m :=
  (SquareKit.Internal.Graph.inSet (fun x => x + 1) (fun x => 2 * x) n _).mpr rfl

end Examples.SheafRelations
