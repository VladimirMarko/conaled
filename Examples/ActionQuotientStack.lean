import SquareKit.SheafActionQuotientStack
import Examples.TorsorStack

/-! Genuine targets, nontrivial torsors, retained stabilizers and descent controls. -/
noncomputable section
set_option autoImplicit false
set_option warningAsError true
namespace Examples.ActionQuotientStack
open CategoryTheory Opposite SquareKit SheafActionQuotient
open SmoothTorsors Orbifolds.QuarterTurn

/-- The target is the actual total sheaf of the clutching torsor. -/
def targetAction : Action group (SmoothClutching.total C4 quarterTurn) where
  act := SmoothClutching.sectionAction C4 quarterTurn
  one_act := SmoothClutching.sectionAction_one C4 quarterTurn
  mul_act := SmoothClutching.sectionAction_mul C4 quarterTurn
  natural := SmoothClutching.sectionAction_natural C4 quarterTurn

/-- The equivariant target map remembers the actual section, not an orbit label. -/
def genuine : Object targetAction SmoothClutching.base where
  torsor := nontrivialTorsor
  value _ p := p.val
  natural _ _ := rfl
  equivariant _ _ _ := rfl

theorem genuine_totalMap :
    genuine.totalMap = (SplitSheaf.displayIso (SmoothClutching.projection C4 quarterTurn)).hom := rfl

abbrev cover := TorsorStack.cover
abbrev localDatum := ((Stack.pseudofunctor targetAction).toDescentData
  (SheafTorsor.Stack.singleton cover)).obj genuine

example : (Stack.pseudofunctor targetAction).IsStack
    (SheafCover.topology (J := SmoothOpenSite.topology)) := inferInstance

example : ((Stack.pseudofunctor targetAction).toDescentData
    (fun f : TorsorStack.coverSieve.arrows.category => f.obj.hom)).IsEquivalence :=
  (Stack.pseudofunctor targetAction).isEquivalence_toDescentData _ (by
    simpa only [Sieve.ofArrows_category] using TorsorStack.cover_mem)

def recovery : Arrow (Stack.glue localDatum) genuine :=
  Descent.canonicalRecovery cover genuine

theorem glued_not_trivializable :
    ¬ Nonempty (SheafTorsor.Arrow (SheafTorsor.trivial group SmoothClutching.base)
      (Stack.glue localDatum).torsor) := by
  rintro ⟨h⟩
  exact nontrivialTorsor_not_trivializable ⟨h.comp recovery.torsorArrow⟩

theorem recovery_target (x : SmoothClutching.base.obj.Elements)
    (p : (Stack.glue localDatum).torsor.family.family.obj x) :
    (recovery.torsorArrow.iso.hom.app x p).val = (Stack.glue localDatum).value x p :=
  recovery.preserves x p

example : ((Stack.pseudofunctor targetAction).toDescentData
    (SheafTorsor.Stack.singleton cover)).obj (Stack.glue localDatum) ≅ localDatum :=
  Stack.localComparison localDatum

instance pulledCover_isLocallySurjective :
    Presheaf.IsLocallySurjective SmoothOpenSite.topology
      (SplitSheaf.p (SplitSheaf.tySub cover (SplitSheaf.p cover))).hom :=
  SheafCover.baseChangeCover_isLocallySurjective (A := cover) (SplitSheaf.p cover)

example : Arrow (reindex (Stack.glue localDatum) (SplitSheaf.p cover))
    ((Stack.datum localDatum).baseChange (SplitSheaf.p cover)).object :=
  Stack.baseChangeComparison localDatum (SplitSheaf.p cover)

/-- Every C4 element fixes the target of this non-effective action. -/
def ineffective : Action group point where
  act _ _ x := x
  one_act _ _ := rfl
  mul_act _ _ _ _ := rfl
  natural _ _ _ := rfl

abbrev regular : Object ineffective point := chart ineffective (𝟙 point)
def stabilizer (g : C4) : regular ⟶ regular where
  torsorArrow := loop g
  preserves _ _ := rfl

theorem stabilizers_distinct : stabilizer quarterTurn ≠ stabilizer 1 :=
  fun h => nonidentity_loop (congrArg Arrow.torsorArrow h)

abbrev regularCover := regular.torsor.family
instance regularCover_isLocallySurjective :
    Presheaf.IsLocallySurjective SmoothOpenSite.topology (SplitSheaf.p regularCover).hom :=
  regular.torsor.isLocallySurjective

abbrev regularData := ((Stack.pseudofunctor ineffective).toDescentData
  (SheafTorsor.Stack.singleton regularCover)).obj regular

/-- Both arrows survive the Mathlib bridge and constructive gluing. -/
theorem descended_stabilizers_distinct :
    Stack.glueFunctor.map (Stack.homEquiv (A := regularCover) regular regular
      (stabilizer quarterTurn)) ≠
    Stack.glueFunctor.map (Stack.homEquiv (A := regularCover) regular regular
      (stabilizer 1)) := by
  intro h
  apply stabilizers_distinct
  apply (Stack.homEquiv (A := regularCover) regular regular).injective
  apply (Stack.datumMapEquiv regularData regularData).injective
  exact (Descent.arrowEquiv (Stack.datum regularData) (Stack.datum regularData)).injective h

/-- Removing coverage loses actual stabilizers, before object recovery is considered. -/
theorem empty_descent_not_faithful :
    ¬ ((Stack.pseudofunctor ineffective).toDescentData TorsorStack.emptyFamily).Faithful := by
  intro h
  have he : ((Stack.pseudofunctor ineffective).toDescentData TorsorStack.emptyFamily).map
      (stabilizer quarterTurn) =
      ((Stack.pseudofunctor ineffective).toDescentData TorsorStack.emptyFamily).map (stabilizer 1) := by
    apply Pseudofunctor.DescentData.hom_ext
    intro i
    exact i.elim
  exact stabilizers_distinct
    (((Stack.pseudofunctor ineffective).toDescentData TorsorStack.emptyFamily).map_injective he)

/-- A target on which the group acts by actual multiplication. -/
def regularAction : Action group (SheafTorsor.groupSheaf group) where
  act U g m := g * (show group.obj.obj U from m)
  one_act U m := one_mul (show group.obj.obj U from m)
  mul_act U g h m := mul_assoc g h (show group.obj.obj U from m)
  natural {U _} f g m := (group.obj.map f).hom.map_mul g (show group.obj.obj U from m)

/-- The cover's group coordinate is a varying target value. -/
def coverLabel : SplitSheaf.extension regularCover ⟶ SheafTorsor.groupSheaf group := ⟨{
  app _ := ↾fun p => p.2
  naturality _ _ _ := rfl }⟩

abbrev incompatibleLocal := chart regularAction coverLabel
abbrev identityTransport := SheafTorsor.Descent.canonicalDatum regularCover regular.torsor

/-- Equivariant local target maps alone are insufficient: the identity torsor
cocycle does not preserve this varying target map on the overlap. -/
theorem target_compatibility_fails :
    ¬ (∀ (x : point.obj.Elements) (b c : regularCover.family.obj x)
      (p : incompatibleLocal.torsor.family.family.obj
        (SheafTorsor.Descent.point regularCover x b)),
      incompatibleLocal.value (SheafTorsor.Descent.point regularCover x c)
        (identityTransport.transport x b c p) =
      incompatibleLocal.value (SheafTorsor.Descent.point regularCover x b) p) := by
  intro h
  let U := op (op (SmoothPresentationSite.free 0))
  let x := point.obj.elementsMk U (𝟙 (op (SmoothPresentationSite.free 0)))
  let q : group.obj.obj U := (SmoothOpenSite.constantSection point quarterTurn).hom.app U x.val
  have he := h x (1 : group.obj.obj U) q (1 : group.obj.obj U)
  change 1 * q = 1 * (1 : group.obj.obj U) at he
  rw [one_mul, one_mul] at he
  apply quarterTurn_ne_one
  exact SmoothOpenSite.constantLabel_injective C4 (SmoothPresentationSite.free 0) (𝟙 _)
    (he.trans (map_one _).symm)

end Examples.ActionQuotientStack
