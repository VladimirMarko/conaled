import SquareKit.FiniteHigherMappingBicategory
import SquareKit.FiniteHigherDescent

/-! Atomic completion, its actual unit, and descent for every covering sieve. -/

set_option autoImplicit false
set_option warningAsError true
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option backward.defeqAttrib.useBackward true

noncomputable section
namespace SquareKit.FiniteHigherCompletion
open CategoryTheory Bicategory SquareKit.HigherCategory SquareKit.PseudofunctorMapping
open SquareKit.PseudofunctorComposition SquareKit.ContractibleBicategory SquareKit.FiniteHigherMap
open scoped Pseudofunctor.StrongTrans
universe u v w u' v' w' u'' v'' w''
variable {X : Type u} [Bicategory.{v,w} X]
  {A : Type u'} [Bicategory.{v',w'} A] {B : Type u''} [Bicategory.{v'',w''} B]

theorem pair_fst (F : Pseudofunctor X A) (G : Pseudofunctor X B) :
    (pair F G).comp (Bicategory.Prod.fst A B).toPseudofunctor = F := by
  dsimp only [Pseudofunctor.comp]
  conv_rhs => rw [show F = {F with mapId := F.mapId, mapComp := F.mapComp} from rfl]
  congr 1
  · funext x
    apply Iso.ext
    simp [pair]
  · funext x y z f g
    apply Iso.ext
    simp [pair]

theorem pair_snd (F : Pseudofunctor X A) (G : Pseudofunctor X B) :
    (pair F G).comp (Bicategory.Prod.snd A B).toPseudofunctor = G := by
  dsimp only [Pseudofunctor.comp]
  conv_rhs => rw [show G = {G with mapId := G.mapId, mapComp := G.mapComp} from rfl]
  congr 1
  · funext x
    apply Iso.ext
    simp [pair]
  · funext x y z f g
    apply Iso.ext
    simp [pair]


def equalityEquivalence {Y : Type*} [Bicategory Y] {a b : Y} (h : a = b) :
    Bicategory.Equivalence a b := h ▸ Bicategory.Equivalence.id a

abbrev atomicDiagram (A B : Type) [Bicategory.{0,0} A] [Bicategory.{0,0} B] :
    FullDiagram.{0,0,0} where
  top := A × B
  left := A
  right := B
  empty := Terminal
  rL := (Bicategory.Prod.fst A B).toPseudofunctor
  rR := (Bicategory.Prod.snd A B).toPseudofunctor
  r0 := toTerminal
  sL := toTerminal
  sR := toTerminal
  cL := comparisonEquivalence _ _
  cR := comparisonEquivalence _ _

abbrev completion (F : FullDiagram.{0,0,0}) : FullDiagram.{0,0,0} :=
  atomicDiagram F.left F.right

def unitCore (F : FullDiagram.{0,0,0}) : MapCore F (completion F) where
  top := pair F.rL F.rR
  left := Pseudofunctor.id F.left
  right := Pseudofunctor.id F.right
  empty := toTerminal
  topLeft := equalityEquivalence ((comp_id F.rL).trans (pair_fst F.rL F.rR).symm)
  topRight := equalityEquivalence ((comp_id F.rR).trans (pair_snd F.rL F.rR).symm)
  topEmpty := comparisonEquivalence _ _
  leftEmpty := comparisonEquivalence _ _
  rightEmpty := comparisonEquivalence _ _

def unit (F : FullDiagram.{0,0,0}) : SquareKit.FiniteHigherMap.Map (F := F) (T := completion F) where
  toMapCore := unitCore F
  leftCoherence := modificationIso _ _
  rightCoherence := modificationIso _ _

end SquareKit.FiniteHigherCompletion
namespace SquareKit.AtomicBinaryDescent
open CategoryTheory Bicategory SquareKit.HigherCategory
open SquareKit.PseudofunctorMapping SquareKit.ContractibleBicategory SquareKit.FiniteHigherCompletion
open SquareKit.RestrictionDescent
open scoped Pseudofunctor.StrongTrans

theorem terminal_local (x y : Terminal) :
    ((toTerminal (C := Terminal)).toPrelaxFunctor.mapFunctor x y).IsEquivalence := by
  exact {
    faithful := { map_injective := by intro a b m n h; apply Subsingleton.elim }
    full := { map_surjective := by intro a b m; exact ⟨default, Subsingleton.elim _ _⟩ }
    essSurj := { mem_essImage := fun z => ⟨default, ⟨{
      hom := default
      inv := default
      hom_inv_id := Subsingleton.elim _ _
      inv_hom_id := Subsingleton.elim _ _ }⟩⟩ } }

theorem terminal_biequivalence : IsBiequivalence (toTerminal (C := Terminal)) := by
  refine ⟨?_, terminal_local⟩
  intro z
  refine ⟨z, ?_⟩
  have h : (toTerminal (C := Terminal)).obj z = z := Subsingleton.elim _ _
  rw [h]
  exact ⟨Bicategory.Equivalence.id z⟩

variable (A B : Type) [Bicategory.{0,0} A] [Bicategory.{0,0} B]
theorem atomic_pair : pair (atomicDiagram A B).rL (atomicDiagram A B).rR =
    Pseudofunctor.id (A × B) := rfl

end SquareKit.AtomicBinaryDescent
namespace SquareKit.FiniteHigherCompletionDescent
open CategoryTheory Bicategory SquareKit.HigherCategory
open SquareKit.FiniteHigherCompletion SquareKit.FiniteHigherDescent SquareKit.AtomicBinaryDescent

theorem completion_isStack (D : FullDiagram.{0,0,0}) :
    IsStack (completion D) := by
  apply (stack_criterion _).mpr
  refine ⟨terminal_biequivalence, ?_⟩
  rw [show SquareKit.PseudofunctorMapping.pair (completion D).rL (completion D).rR =
    Pseudofunctor.id (D.left × D.right) from rfl]
  exact SquareKit.Biequivalence.id

theorem completion_allCoveringSieves (D : FullDiagram.{0,0,0}) :
    IsStackOnAllCoveringSieves (completion D) :=
  (allCoveringSieves_iff _).mpr (completion_isStack D)

end SquareKit.FiniteHigherCompletionDescent

end
