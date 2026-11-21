import SquareKit.Internal.CoherentSheafOver
import Examples.SheafImage
import Mathlib.CategoryTheory.Sites.Types

/-! Proper-cover specialization of the coherent sheaf decoder. -/
noncomputable section
namespace Examples.CoherentSheafOver
open CategoryTheory Opposite SquareKit.CoherentSheafOver
open Examples.SheafImage

example : ((classification topology).functor.obj
    ((classification topology).inverse.obj E)) ≅ E :=
  (classification topology).counitIso.app E

example : Presheaf.IsSheaf topology
    ((decode topology).obj ((encode topology).obj E)).obj :=
  ((decode topology).obj ((encode topology).obj E)).property

namespace Contexts
open SquareKit.RepresentableClassification

abbrev Base := Discrete PUnit.{1}
abbrev Context := SquareKit.RepresentableClassification.Context.{0} Base
abbrev boolContext : Context := (Functor.const _).obj Bool
abbrev unitContext : Context := (Functor.const _).obj PUnit.{1}
abbrev J := representedTopology (C := Base)

def boolMap (f : Bool → Bool) : boolContext ⟶ boolContext where
  app _ := ↾f

def constantCover : Sieve boolContext where
  arrows {Δ} f := ∀ I (x y : Δ.obj I), f.app I x = f.app I y
  downward_closed hf g I x y := hf I (g.app I x) (g.app I y)

theorem proper_cover : constantCover ∈ J boolContext := by
  intro x I f g
  rfl

theorem identity_not_in_cover : ¬ constantCover (𝟙 boolContext) := by
  intro h
  have hh := h (op ⟨PUnit.unit⟩) true false
  exact Bool.noConfusion hh

def liftedCover : Sieve (Over.mk (𝟙 boolContext)) :=
  (Sieve.overEquiv _).symm constantCover

theorem liftedCover_covering : liftedCover ∈ J.over boolContext _ :=
  J.overEquiv_symm_mem_over _ _ proper_cover

theorem liftedCover_proper : liftedCover ≠ ⊤ := by
  intro h
  have hi : liftedCover (𝟙 _) := by rw [h]; trivial
  exact identity_not_in_cover hi

example : J.Subcanonical := inferInstance
example : (CostructuredArrow.toOver representables boolContext).IsCoverDense
    (J.over boolContext) := inferInstance

/-- The positive example uses the complete derived decoder on the actual
represented-context site, with all size obligations discharged. -/
abbrev classifier := codeDisplayClassification representables J boolContext

def boolDisplay : Over (contextSheaf boolContext J) :=
  Over.mk (show contextSheaf boolContext J ⟶ contextSheaf boolContext J from
    ⟨yoneda.map (boolMap id)⟩)

example : classifier.functor.obj (classifier.inverse.obj boolDisplay) ≅ boolDisplay :=
  classifier.counitIso.app boolDisplay

/-- A subterminal presheaf supported on a sieve. -/
def support (S : Sieve boolContext) : (Over boolContext)ᵒᵖ ⥤ Type where
  obj X := PLift (S X.unop.hom)
  map f := ↾fun h => ⟨by
    rw [← Over.w f.unop]
    exact S.downward_closed h.down f.unop.left⟩
  map_id _ := by ext; apply Subsingleton.elim
  map_comp _ _ := by ext; apply Subsingleton.elim

theorem support_empty_at_identity : IsEmpty
    ((support constantCover).obj (op (Over.mk (𝟙 boolContext)))) :=
  ⟨fun h => identity_not_in_cover h.down⟩

/-- Every old represented local view of the counterexample is terminal. -/
def support_local (x : boolContext.Elements) :
    (Over.map (represented x)).op ⋙ support constantCover ≅ (Functor.const _).obj PUnit.{1} :=
  NatIso.ofComponents (fun U =>
    { hom := ↾fun _ => PUnit.unit
      inv := ↾fun _ => ⟨constantCover.downward_closed (proper_cover x) U.unop.hom⟩
      hom_inv_id := by ext z; change (_ : PLift _) = z; apply Subsingleton.elim
      inv_hom_id := by ext; rfl }) (by intros; rfl)

example : Presheaf.IsSheaf (⊥ : GrothendieckTopology (Over boolContext))
    (support constantCover) := Presheaf.isSheaf_bot _

theorem bot_over : (⊥ : GrothendieckTopology Context).over boolContext = ⊥ := by
  ext U S
  change Sieve.overEquiv U S = ⊤ ↔ S = ⊤
  constructor
  · intro h
    apply (Sieve.overEquiv U).injective
    simpa using h
  · rintro rfl
    exact map_top _

example : (⊥ : GrothendieckTopology Context).Subcanonical := ⟨bot_le⟩

example : Presheaf.IsSheaf ((⊥ : GrothendieckTopology Context).over boolContext)
    (support constantCover) := by
  rw [bot_over]
  exact Presheaf.isSheaf_bot _

/-- Subcanonicity without represented coverage cannot recover the original object. -/
theorem support_not_terminal : ¬ Nonempty
    (support constantCover ≅ (Functor.const _).obj PUnit.{1}) := by
  rintro ⟨e⟩
  exact support_empty_at_identity.false
    ((e.app (op (Over.mk (𝟙 boolContext)))).inv PUnit.unit)

def supportedBotSheaf : Sheaf ((⊥ : GrothendieckTopology Context).over boolContext) Type :=
  ⟨support constantCover, by rw [bot_over]; exact Presheaf.isSheaf_bot _⟩

def terminalBotSheaf : Sheaf ((⊥ : GrothendieckTopology Context).over boolContext) Type :=
  ⟨(Functor.const _).obj PUnit.{1}, by rw [bot_over]; exact Presheaf.isSheaf_bot _⟩

def localBotIso (x : boolContext.Elements) :
    ((⊥ : GrothendieckTopology Context).overMapPullback Type (represented x)).obj
      supportedBotSheaf ≅
    ((⊥ : GrothendieckTopology Context).overMapPullback Type (represented x)).obj
      terminalBotSheaf :=
  ObjectProperty.isoMk _ (support_local x)

theorem original_sheaves_not_iso : ¬ Nonempty (supportedBotSheaf ≅ terminalBotSheaf) := by
  rintro ⟨e⟩
  exact support_not_terminal ⟨(sheafToPresheaf _ _).mapIso e⟩

def supportToTerminal : supportedBotSheaf ⟶ terminalBotSheaf :=
  ⟨{ app := fun _ => ↾fun _ => PUnit.unit }⟩

theorem local_support_map_iso (x : boolContext.Elements) :
    IsIso (((⊥ : GrothendieckTopology Context).overMapPullback Type (represented x)).map
      supportToTerminal) := by
  change IsIso (localBotIso x).hom
  infer_instance

theorem support_map_not_iso : ¬ IsIso supportToTerminal := by
  intro h
  exact original_sheaves_not_iso ⟨asIso supportToTerminal⟩

abbrev pairContext : Context := (Functor.const _).obj (Bool × Bool)

def pairProjection : pairContext ⟶ boolContext where
  app _ := ↾Prod.fst

def pairCollapse : pairContext ⟶ pairContext where
  app _ := ↾fun p => (p.1, false)

def pairPoint (p : Bool × Bool) : unitContext ⟶ pairContext where
  app _ := ↾fun _ => p

def pairDisplay : Over (contextSheaf boolContext J) :=
  Over.mk (show contextSheaf pairContext J ⟶ contextSheaf boolContext J from
    ⟨yoneda.map pairProjection⟩)

def collapse : pairDisplay ⟶ pairDisplay :=
  Over.homMk (show contextSheaf pairContext J ⟶ contextSheaf pairContext J from
    ⟨yoneda.map pairCollapse⟩) (by ext; rfl)

theorem collapse_not_iso : ¬ IsIso collapse := by
  intro h
  let : IsIso collapse.left := (Over.forget (contextSheaf boolContext J)).map_isIso collapse
  let a : contextSheaf unitContext J ⟶ contextSheaf pairContext J :=
    ⟨yoneda.map (pairPoint (true, true))⟩
  let b : contextSheaf unitContext J ⟶ contextSheaf pairContext J :=
    ⟨yoneda.map (pairPoint (true, false))⟩
  have hab : a ≫ collapse.left = b ≫ collapse.left := by ext; rfl
  have he := (cancel_mono collapse.left).1 hab
  have hh := congrArg
    (fun k : contextSheaf unitContext J ⟶ contextSheaf pairContext J =>
      (k.hom.app (op unitContext) (𝟙 unitContext)).app (op ⟨PUnit.unit⟩) PUnit.unit) he
  exact Bool.noConfusion (congrArg Prod.snd hh)

theorem code_collapse_not_iso : ¬ IsIso (classifier.inverse.map collapse) := by
  intro h
  exact collapse_not_iso (isIso_of_reflects_iso collapse classifier.inverse)

def negationSubstitution : LocalCode representables J boolContext ⥤
    LocalCode representables J boolContext := reindex representables J (boolMap Bool.not)

def doubleNegationComparison :
    negationSubstitution ⋙ negationSubstitution ≅
      reindex representables J (boolMap Bool.not ≫ boolMap Bool.not) :=
  reindexComp representables J (boolMap Bool.not) (boolMap Bool.not)

example : classifier.functor.map (classifier.inverse.map collapse) ≫
    (classifier.counitIso.app pairDisplay).hom =
      (classifier.counitIso.app pairDisplay).hom ≫ collapse :=
  classifier.counitIso.hom.naturality collapse

def diagonal : boolContext ⟶ pairContext where
  app _ := ↾fun b => (b, b)

theorem nonidentity_restriction :
    ((pairDisplay.left.obj.map (boolMap Bool.not).op diagonal).app
      (op ⟨PUnit.unit⟩)) false = (true, true) := rfl

set_option backward.defeqAttrib.useBackward true in
set_option backward.isDefEq.respectTransparency false in
set_option backward.isDefEq.respectTransparency.types false in
example (a : (classifier.functor.obj (classifier.inverse.obj pairDisplay)).left.obj.obj
    (op boolContext)) :
    (classifier.counitIso.app pairDisplay).hom.left.hom.app (op boolContext)
      ((classifier.functor.obj (classifier.inverse.obj pairDisplay)).left.obj.map
        (boolMap Bool.not).op a) =
      pairDisplay.left.obj.map (boolMap Bool.not).op
        ((classifier.counitIso.app pairDisplay).hom.left.hom.app (op boolContext) a) :=
  congrArg (fun k :
    (classifier.functor.obj (classifier.inverse.obj pairDisplay)).left.obj.obj (op boolContext) ⟶
      pairDisplay.left.obj.obj (op boolContext) => k a)
    ((classifier.counitIso.app pairDisplay).hom.left.hom.naturality (boolMap Bool.not).op)

end Contexts

end Examples.CoherentSheafOver
