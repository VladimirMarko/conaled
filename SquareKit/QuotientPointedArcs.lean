import SquareKit.SheafActionQuotient
import Mathlib.CategoryTheory.Comma.Basic
import Mathlib.CategoryTheory.Equivalence

/-! The homotopy pullback of a quotient chart along a restriction functor.
Its boundary is an actual quotient isomorphism, not equality of orbit classes. -/
noncomputable section
namespace SquareKit.QuotientPointedArcs
open CategoryTheory Opposite SheafActionQuotient
universe u v w
variable {C : Type u} [Category.{v} C] {J : GrothendieckTopology C}
variable {G : Sheaf J GrpCat.{w}} {M : Sheaf J (Type w)}
variable (a : Action G M) {X Y : Sheaf J (Type w)} (f : X ⟶ Y)

/-- Since the target is a groupoid, each comma boundary is an isomorphism.
The comma morphism equation is the coherent boundary square. -/
abbrev Pullback := Comma (chartFunctor a X) (restriction (a := a) f)

instance : Groupoid (Pullback a f) := Groupoid.ofIsIso (fun h => by
  let hi := Comma.isoMk (asIso h.left) (asIso h.right) h.w
  have he : hi.hom = h := by ext <;> rfl
  rw [← he]
  exact hi.isIso_hom)

/-- Restrict a lifted arc and retain its identity boundary isomorphism. -/
def comparison : Discrete (Y ⟶ M) ⥤ Pullback a f :=
  Discrete.functor fun h => {
    left := ⟨f ≫ h⟩
    right := chart a h
    hom := 𝟙 _ }

theorem chartFunctor_map_torsor {Z : Sheaf J (Type w)}
    {m n : Discrete (Z ⟶ M)} (h : m ⟶ n) :
    ((chartFunctor a Z).map h).torsorArrow = SheafTorsor.Arrow.ident (SheafTorsor.trivial G Z) := by
  cases m
  cases n
  cases Discrete.eq_of_hom h
  rfl

/-- Restriction being fully faithful on torsors controls every quotient arrow
with a fixed boundary. It does not require the quotient objects to be charts. -/
theorem comparison_arrow_underlying
    [CategoryTheory.Functor.Faithful (SheafTorsor.restriction (G := G) f)]
    {m n : Discrete (Y ⟶ M)} (h : (comparison a f).obj m ⟶ (comparison a f).obj n) :
    h.right.torsorArrow = SheafTorsor.Arrow.ident (SheafTorsor.trivial G Y) := by
  apply (SheafTorsor.restriction f).map_injective
  have hw := congrArg Arrow.torsorArrow h.w
  change SheafTorsor.Arrow.comp ((chartFunctor a X).map h.left).torsorArrow
      (SheafTorsor.Arrow.ident _) =
    SheafTorsor.Arrow.comp (SheafTorsor.Arrow.ident _) (h.right.torsorArrow.reindex f) at hw
  rw [chartFunctor_map_torsor] at hw
  exact hw.symm

theorem comparison_arrow_eq
    [CategoryTheory.Functor.Faithful (SheafTorsor.restriction (G := G) f)]
    {m n : Discrete (Y ⟶ M)} (h : (comparison a f).obj m ⟶ (comparison a f).obj n) : m = n := by
  apply Discrete.ext
  ext U y
  have hp := h.right.preserves (Y.obj.elementsMk U y) (1 : G.obj.obj U)
  rw [comparison_arrow_underlying a f h] at hp
  exact ((a.one_act U (n.as.hom.app U y)).symm.trans hp).trans (a.one_act U (m.as.hom.app U y)) |>.symm

instance comparison_faithful : (comparison a f).Faithful where
  map_injective _ := Subsingleton.elim _ _

instance comparison_full [CategoryTheory.Functor.Faithful (SheafTorsor.restriction (G := G) f)] :
    (comparison a f).Full where
  map_surjective {m n} h := by
    have he := comparison_arrow_eq a f h
    subst n
    refine ⟨𝟙 m, ?_⟩
    rw [CategoryTheory.Functor.map_id]
    apply CommaMorphism.ext
    · apply Subsingleton.elim
    · apply SheafActionQuotient.Arrow.ext
      exact (comparison_arrow_underlying a f h).symm

section Lifting
variable [CategoryTheory.Functor.Full (SheafTorsor.restriction (G := G) f)]

/-- The boundary trivialization lifts through the proved full torsor restriction. -/
def liftTrivialization (P : Pullback a f) :
    SheafTorsor.Arrow (SheafTorsor.trivial G Y) P.right.torsor :=
  (SheafTorsor.restriction f).preimage P.hom.torsorArrow

theorem liftTrivialization_boundary (P : Pullback a f) :
    (liftTrivialization a f P).reindex f = P.hom.torsorArrow :=
  (SheafTorsor.restriction f).map_preimage (X := SheafTorsor.trivial G Y)
    (Y := P.right.torsor) P.hom.torsorArrow

/-- A lifted actual section determines the smooth arc. -/
def liftArc (P : Pullback a f) : Y ⟶ M :=
  P.right.sectionMap (SheafTorsor.sectionOfArrow (liftTrivialization a f P))

theorem liftArc_boundary (P : Pullback a f) : f ≫ liftArc a f P = P.left.as := by
  ext U x
  have he := congrArg (fun e => e.iso.hom.app (X.obj.elementsMk U x) (1 : G.obj.obj U))
    (liftTrivialization_boundary a f P)
  have hp := P.hom.preserves (X.obj.elementsMk U x) (1 : G.obj.obj U)
  change P.right.value (Y.obj.elementsMk U (f.hom.app U x))
    ((liftTrivialization a f P).iso.hom.app (Y.obj.elementsMk U (f.hom.app U x)) (1 : G.obj.obj U)) = _
  exact (congrArg (P.right.value (Y.obj.elementsMk U (f.hom.app U x))) he).trans
    (hp.trans (a.one_act U (P.left.as.hom.app U x)))

/-- The comparison's boundary square includes the chosen torsor isomorphism,
so essential surjectivity retains the complete pointed datum. -/
def comparisonIso (P : Pullback a f) : (comparison a f).obj ⟨liftArc a f P⟩ ≅ P :=
  Comma.isoMk (eqToIso (Discrete.ext (liftArc_boundary a f P)))
    (SheafActionQuotient.Arrow.toIso
      (P.right.chartOfTrivialization (liftTrivialization a f P))) (by
      apply SheafActionQuotient.Arrow.ext
      change SheafTorsor.Arrow.comp
        ((chartFunctor a X).map _).torsorArrow P.hom.torsorArrow =
          SheafTorsor.Arrow.comp (SheafTorsor.Arrow.ident _)
            ((liftTrivialization a f P).reindex f)
      rw [chartFunctor_map_torsor, liftTrivialization_boundary]
      rfl)

instance comparison_essSurj : (comparison a f).EssSurj where
  mem_essImage P := ⟨⟨liftArc a f P⟩, ⟨comparisonIso a f P⟩⟩

end Lifting

/-- The quotient chart square is a homotopy pullback whenever torsor
restriction is fully faithful. All arrows and the boundary iso are retained. -/
def equivalence [CategoryTheory.Functor.Full (SheafTorsor.restriction (G := G) f)]
    [CategoryTheory.Functor.Faithful (SheafTorsor.restriction (G := G) f)] :
    Discrete (Y ⟶ M) ≌ Pullback a f := by
  letI : (comparison a f).IsEquivalence := {}
  exact (comparison a f).asEquivalence

end SquareKit.QuotientPointedArcs
