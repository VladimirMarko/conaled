import SquareKit.StructureIdentity.Descriptions

/-! Typed expressions and propositional laws whose invariance is derived from
their syntax. Contexts may contain functions and relations as well as carriers. -/
set_option autoImplicit false
set_option warningAsError true
namespace SquareKit.StructureIdentity
open Description

inductive Expression (D : Description.{0}) : Description → Description → Type 1
  | data {C} : Expression D C D
  | var {C} : Expression D C C
  | fixed {C} {A : Type} (a : A) : Expression D C (.fixed A)
  | pair {C E F} : Expression D C E → Expression D C F → Expression D C (.product E F)
  | first {C E F} : Expression D C (.product E F) → Expression D C E
  | second {C E F} : Expression D C (.product E F) → Expression D C F
  | apply {C E F} : Expression D C (.function E F) → Expression D C E → Expression D C F

namespace Expression
def eval {D C E : Description} {X : Type} (s : D.Data X) (c : C.Data X) :
    Expression D C E → E.Data X
  | .data => s
  | .var => c
  | .fixed a => a
  | .pair a b => (a.eval s c, b.eval s c)
  | .first a => (a.eval s c).1
  | .second a => (a.eval s c).2
  | .apply f a => f.eval s c (a.eval s c)

theorem preserves {D C E : Description} {X Y : Type} (e : X ≃ Y)
    {s : D.Data X} {t : D.Data Y} {c : C.Data X} {d : C.Data Y}
    (hs : D.Preserves e s t) (hc : C.Preserves e c d) (a : Expression D C E) :
    E.Preserves e (a.eval s c) (a.eval t d) := by
  induction a with
  | data => exact hs
  | var => exact hc
  | fixed a => rfl
  | pair a b ha hb => exact ⟨ha, hb⟩
  | first a ha => exact ha.1
  | second a ha => exact ha.2
  | apply f a hf ha => exact hf _ _ ha
end Expression

inductive Formula (D : Description.{0}) : Description → Type 1
  | truth {C} : Formula D C
  | equal {C E} : Expression D C E → Expression D C E → Formula D C
  | holds {C} : Expression D C (.fixed Prop) → Formula D C
  | and {C} : Formula D C → Formula D C → Formula D C
  | implies {C} : Formula D C → Formula D C → Formula D C
  | all {C} (E : Description) : Formula D (.product C E) → Formula D C

namespace Formula
def Eval {D C : Description} {X : Type} (s : D.Data X) (c : C.Data X) :
    Formula D C → Prop
  | .truth => True
  | .equal a b => a.eval s c = b.eval s c
  | .holds a => a.eval s c
  | .and p q => p.Eval s c ∧ q.Eval s c
  | .implies p q => p.Eval s c → q.Eval s c
  | .all E p => ∀ x : E.Data X, @Eval D (.product C E) X s (c, x) p

theorem invariant {D C : Description} {X Y : Type} (e : X ≃ Y)
    {s : D.Data X} {t : D.Data Y} (hs : D.Preserves e s t)
    (p : Formula D C) {c : C.Data X} {d : C.Data Y} (hc : C.Preserves e c d) :
    p.Eval s c ↔ p.Eval t d := by
  induction p with
  | truth => exact Iff.rfl
  | @equal C E a b =>
    have ha := (E.preserves_iff _ _ _).mp (a.preserves e hs hc)
    have hb := (E.preserves_iff _ _ _).mp (b.preserves e hs hc)
    change a.eval s c = b.eval s c ↔ a.eval t d = b.eval t d
    constructor
    · intro h
      exact ha.symm.trans ((congrArg (E.transport e) h).trans hb)
    · intro h
      exact (E.transport e).injective (ha.trans (h.trans hb.symm))
  | holds a =>
    exact Iff.of_eq (a.preserves e hs hc)
  | and p q hp hq => exact and_congr (hp hc) (hq hc)
  | implies p q hp hq => exact imp_congr (hp hc) (hq hc)
  | all E p hp =>
    constructor
    · intro h y
      exact (hp ⟨hc, (E.preserves_iff _ _ _).mpr ((E.transport e).apply_symm_apply y)⟩).mp
        (h ((E.transport e).symm y))
    · intro h x
      exact (hp ⟨hc, (E.preserves_iff _ _ _).mpr rfl⟩).mpr (h (E.transport e x))
end Formula

namespace Formula
/-- A dependent client: values of a context satisfying a formula in a structure. -/
def Solutions {D C : Description} (p : Formula D C) {X : Type} (s : D.Data X) :=
  {c : C.Data X // p.Eval s c}

def solutionEquiv {D C : Description} (p : Formula D C) {X Y : Type}
    (e : X ≃ Y) {s : D.Data X} {t : D.Data Y} (hs : D.Preserves e s t) :
    p.Solutions s ≃ p.Solutions t where
  toFun c := ⟨C.transport e c.val,
    (p.invariant e hs ((C.preserves_iff _ _ _).mpr rfl)).mp c.property⟩
  invFun d := ⟨(C.transport e).symm d.val,
    (p.invariant e hs ((C.preserves_iff _ _ _).mpr ((C.transport e).apply_symm_apply _))).mpr d.property⟩
  left_inv c := Subtype.ext ((C.transport e).symm_apply_apply c.val)
  right_inv d := Subtype.ext ((C.transport e).apply_symm_apply d.val)
end Formula

structure Specification where
  description : Description.{0}
  law : Formula description (.fixed Unit)

namespace Specification
def Model (T : Specification) (X : Type) := {s : T.description.Data X // T.law.Eval (C := .fixed Unit) s ()}

def transport (T : Specification) {X Y : Type} (e : X ≃ Y) : T.Model X ≃ T.Model Y where
  toFun s := ⟨T.description.transport e s.val,
    (T.law.invariant e ((T.description.preserves_iff _ _ _).mpr rfl) rfl).mp s.property⟩
  invFun t := ⟨(T.description.transport e).symm t.val, by
    apply (T.law.invariant e
      ((T.description.preserves_iff _ _ _).mpr ((T.description.transport e).apply_symm_apply _)) rfl).mpr
    exact t.property⟩
  left_inv s := Subtype.ext ((T.description.transport e).symm_apply_apply s.val)
  right_inv t := Subtype.ext ((T.description.transport e).apply_symm_apply t.val)

def Preserves (T : Specification) {X Y : Type} (e : X ≃ Y)
    (s : T.Model X) (t : T.Model Y) : Prop := T.description.Preserves e s.val t.val

theorem preserves_iff (T : Specification) {X Y : Type} (e : X ≃ Y)
    (s : T.Model X) (t : T.Model Y) :
    T.Preserves e s t ↔ T.transport e s = t := by
  constructor
  · intro h
    exact Subtype.ext ((T.description.preserves_iff _ _ _).mp h)
  · intro h
    exact (T.description.preserves_iff _ _ _).mpr (congrArg Subtype.val h)

@[simp] theorem transport_refl (T : Specification) {X : Type} (s : T.Model X) :
    T.transport (Equiv.refl X) s = s := by
  apply Subtype.ext
  exact congrArg (fun k => k s.val) T.description.transport_refl

@[simp] theorem transport_trans (T : Specification) {X Y Z : Type}
    (e : X ≃ Y) (f : Y ≃ Z) (s : T.Model X) :
    T.transport (e.trans f) s = T.transport f (T.transport e s) := by
  apply Subtype.ext
  exact congrArg (fun k => k s.val) (T.description.transport_trans e f)

end Specification
end SquareKit.StructureIdentity
