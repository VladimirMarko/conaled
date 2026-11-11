import Mathlib.Logic.Function.Basic
import Mathlib.Logic.Equiv.Defs

/-! Selected diagonal constructions and their interpretation laws. -/

namespace SquareKit.DiagonalConstruction

universe u v u' v' u'' v''

variable {A : Type u} {Y : Type v}

def diagonal (e : A → A → Y) (h : Y → Y) (a : A) : Y := h (e a a)

/-- A selected code, rather than just existence of a fixed point. -/
structure Selected (e : A → A → Y) (h : Y → Y) where
  code : A
  represents : ∀ a, e code a = diagonal e h a

namespace Selected
variable {e : A → A → Y} {h : Y → Y}
def witness (s : Selected e h) : Y := e s.code s.code

theorem fixed (s : Selected e h) : h s.witness = s.witness :=
  (s.represents s.code).symm

noncomputable def ofSurjective (e : A → A → Y) (he : Function.Surjective e)
    (h : Y → Y) : Selected e h where
  code := Classical.choose (he (diagonal e h))
  represents a := congrFun (Classical.choose_spec (he (diagonal e h))) a
end Selected

/-- The existing Mathlib baseline, without a selected code in its conclusion. -/
theorem baseline (e : A → A → Y) (he : Function.Surjective e) (h : Y → Y) :
    ∃ y, h y = y := Function.exists_fixed_point_of_surjective e he h

/-- Local interpretation laws do not include coverage of target codes. -/
structure Map {B : Type u'} {Z : Type v'}
    (e : A → A → Y) (h : Y → Y) (e' : B → B → Z) (h' : Z → Z) where
  code : A → B
  value : Y → Z
  evaluation : ∀ a b, value (e a b) = e' (code a) (code b)
  step : ∀ y, value (h y) = h' (value y)

namespace Map
variable {B : Type u'} {Z : Type v'} {C : Type u''} {W : Type v''}
variable {e : A → A → Y} {h : Y → Y} {e' : B → B → Z} {h' : Z → Z}
variable {e'' : C → C → W} {h'' : W → W}

def id (e : A → A → Y) (h : Y → Y) : Map e h e h where
  code := _root_.id
  value := _root_.id
  evaluation _ _ := rfl
  step _ := rfl

def comp (g : Map e' h' e'' h'') (f : Map e h e' h') : Map e h e'' h'' where
  code := g.code ∘ f.code
  value := g.value ∘ f.value
  evaluation a b := by rw [Function.comp_apply, f.evaluation, g.evaluation]; rfl
  step y := by rw [Function.comp_apply, f.step, g.step]; rfl

theorem diagonal_preserved (f : Map e h e' h') (a : A) :
    f.value (diagonal e h a) = diagonal e' h' (f.code a) := by
  unfold diagonal
  rw [f.step, f.evaluation]

def selected (f : Map e h e' h') (cover : Function.Surjective f.code)
    (s : Selected e h) : Selected e' h' where
  code := f.code s.code
  represents b := by
    obtain ⟨a, rfl⟩ := cover b
    rw [← f.evaluation, s.represents, f.diagonal_preserved]

theorem witness_preserved (f : Map e h e' h') (cover : Function.Surjective f.code)
    (s : Selected e h) : (f.selected cover s).witness = f.value s.witness :=
  (f.evaluation s.code s.code).symm

@[ext] theorem ext (f g : Map e h e' h') (hc : f.code = g.code)
    (hv : f.value = g.value) : f = g := by cases f; cases g; cases hc; cases hv; rfl

theorem id_comp (f : Map e h e' h') : (id e' h').comp f = f := rfl
theorem comp_id (f : Map e h e' h') : f.comp (id e h) = f := rfl
theorem comp_assoc {D : Type*} {V : Type*} {e''' : D → D → V} {h''' : V → V}
    (k : Map e'' h'' e''' h''') (g : Map e' h' e'' h'') (f : Map e h e' h') :
    (k.comp g).comp f = k.comp (g.comp f) := rfl
end Map

/-- Change of both code and value presentation by independent equivalences. -/
def recode {B : Type u'} {Z : Type v'} (a : A ≃ B) (y : Y ≃ Z)
    (e : A → A → Y) : B → B → Z := fun b c => y (e (a.symm b) (a.symm c))

def restep {Z : Type v'} (y : Y ≃ Z) (h : Y → Y) : Z → Z :=
  fun z => y (h (y.symm z))

def presentationMap {B : Type u'} {Z : Type v'} (a : A ≃ B) (y : Y ≃ Z)
    (e : A → A → Y) (h : Y → Y) : Map e h (recode a y e) (restep y h) where
  code := a
  value := y
  evaluation _ _ := by simp [recode]
  step _ := by simp [restep]

theorem recode_recover {B : Type u'} {Z : Type v'} (a : A ≃ B) (y : Y ≃ Z)
    (e : A → A → Y) : recode a.symm y.symm (recode a y e) = e := by
  funext x z
  simp [recode]

theorem restep_recover {Z : Type v'} (y : Y ≃ Z) (h : Y → Y) :
    restep y.symm (restep y h) = h := by
  funext x
  simp [restep]

theorem recover_code {B : Type u'} {Z : Type v'} (a : A ≃ B) (y : Y ≃ Z)
    {e : A → A → Y} {h : Y → Y} (s : Selected e h) :
    a.symm (((presentationMap a y e h).selected a.surjective s).code) = s.code :=
  a.symm_apply_apply s.code

theorem recover_witness {B : Type u'} {Z : Type v'} (a : A ≃ B) (y : Y ≃ Z)
    {e : A → A → Y} {h : Y → Y} (s : Selected e h) :
    y.symm (((presentationMap a y e h).selected a.surjective s).witness) = s.witness := by
  exact (congrArg y.symm
    ((presentationMap a y e h).witness_preserved a.surjective s)).trans
    (y.symm_apply_apply s.witness)

theorem no_negation_representation (e : A → A → Bool) (s : Selected e Bool.not) : False := by
  have hf := s.fixed
  cases hw : s.witness <;> simp [hw] at hf

theorem no_boolean_surjection (e : A → A → Bool) : ¬ Function.Surjective e := by
  intro he
  exact no_negation_representation e (Selected.ofSurjective e he Bool.not)

end SquareKit.DiagonalConstruction
