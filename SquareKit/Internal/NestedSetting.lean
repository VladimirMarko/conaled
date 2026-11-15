import SquareKit.Internal.FiniteClassifierComparison
import SquareKit.Internal.MixedSetting
import SquareKit.FamilyCoherence
import Mathlib.CategoryTheory.Limits.Types.Pullbacks
import Mathlib.CategoryTheory.Comma.Over.Pullback

/-! Two successive internal finite presentations. The second parameter may
use the first generic model. Split families are compared with equality-bearing
pullbacks; the constructed total spaces also determine actual slice settings.
Native equality is used throughout. This is an extensional specialization. -/

namespace SquareKit.Internal.NestedSetting
open FiniteSetting
open CategoryTheory Limits
universe u
variable {X Y Z W : Type u}

/-- The finite classifier setting, in its flattened slice representation. -/
abbrev Setting {X : Type u} (P : Presentation X) := Over (Total P)

/-- The slice at the internally constructed object agrees with its flattening. -/
def settingEquivalence (P : Presentation X) : Over (formedDisplay P) ≌ Setting P :=
  Over.iteratedSliceEquiv (formedDisplay P)

/-- The second presentation lives in the context of the first generic model. -/
abbrev Nested (P : Presentation X) (Q : Presentation (Total P)) := Total Q

def base (P : Presentation X) (Q : Presentation (Total P)) (a : Nested P Q) : X := a.1.1

def reindex (P : Presentation X) (Q : Presentation (Total P)) (σ : Y → X) :
    Presentation (Total (P.subst σ)) := Q.subst (totalMap P σ)

def map (P : Presentation X) (Q : Presentation (Total P)) (σ : Y → X) :
    Nested (P.subst σ) (reindex P Q σ) → Nested P Q :=
  totalMap Q (totalMap P σ)

@[simp] theorem reindex_id (P : Presentation X) (Q : Presentation (Total P)) :
    reindex P Q id = Q := rfl

@[simp] theorem reindex_comp (P : Presentation X) (Q : Presentation (Total P))
    (σ : Y → X) (τ : Z → Y) :
    reindex (P.subst σ) (reindex P Q σ) τ = reindex P Q (σ ∘ τ) := rfl

@[simp] theorem map_id (P : Presentation X) (Q : Presentation (Total P)) :
    map P Q id = id := rfl

@[simp] theorem map_comp (P : Presentation X) (Q : Presentation (Total P))
    (σ : Y → X) (τ : Z → Y) :
    map P Q σ ∘ map (P.subst σ) (reindex P Q σ) τ = map P Q (σ ∘ τ) := rfl

/-- Construct first, then pull back the whole nested context along the base map. -/
structure Pullback (P : Presentation X) (Q : Presentation (Total P)) (σ : Y → X) where
  point : Y
  original : Nested P Q
  over : base P Q original = σ point

@[ext] theorem Pullback.ext {P : Presentation X} {Q : Presentation (Total P)}
    {σ : Y → X} {a b : Pullback P Q σ} (hp : a.point = b.point)
    (ho : a.original = b.original) : a = b := by
  cases a; cases b; cases hp; cases ho; rfl

/-- This comparison transports both dependent components, not merely their tags. -/
def comparison (P : Presentation X) (Q : Presentation (Total P)) (σ : Y → X) :
    Pullback P Q σ ≃ Nested (P.subst σ) (reindex P Q σ) where
  toFun a := by
    rcases a with ⟨y, ⟨⟨x, a⟩, b⟩, h⟩
    change x = σ y at h
    subst x
    exact ⟨⟨y, a⟩, b⟩
  invFun a := ⟨a.1.1, map P Q σ a, rfl⟩
  left_inv := by rintro ⟨y, ⟨⟨x, a⟩, b⟩, h⟩; change x = σ y at h; subst x; rfl
  right_inv := by rintro ⟨⟨y, a⟩, b⟩; rfl

@[simp] theorem comparison_base (P : Presentation X) (Q : Presentation (Total P))
    (σ : Y → X) (a : Pullback P Q σ) :
    base (P.subst σ) (reindex P Q σ) (comparison P Q σ a) = a.point := by
  rcases a with ⟨y, ⟨⟨x, a⟩, b⟩, h⟩; change x = σ y at h; subst x; rfl

@[simp] theorem comparison_original (P : Presentation X) (Q : Presentation (Total P))
    (σ : Y → X) (a : Pullback P Q σ) :
    map P Q σ (comparison P Q σ a) = a.original := by
  rcases a with ⟨y, ⟨⟨x, a⟩, b⟩, h⟩; change x = σ y at h; subst x; rfl

/-- Identity comparison keeps the whole selected dependent object. -/
theorem comparison_id (P : Presentation X) (Q : Presentation (Total P))
    (a : Pullback P Q id) : comparison P Q id a = a.original :=
  comparison_original P Q id a

/-- Rebase both dependent components and compose the base equation. -/
def rebase (P : Presentation X) (Q : Presentation (Total P))
    (σ : Y → X) (τ : Z → Y)
    (a : Pullback (P.subst σ) (reindex P Q σ) τ) : Pullback P Q (σ ∘ τ) :=
  ⟨a.point, map P Q σ a.original, congrArg σ a.over⟩

/-- The comparison is coherent for two successive base substitutions. -/
theorem comparison_comp (P : Presentation X) (Q : Presentation (Total P))
    (σ : Y → X) (τ : Z → Y)
    (a : Pullback (P.subst σ) (reindex P Q σ) τ) :
    comparison P Q (σ ∘ τ) (rebase P Q σ τ a) =
      comparison (P.subst σ) (reindex P Q σ) τ a := by
  rcases a with ⟨z, ⟨⟨y, a⟩, b⟩, h⟩; change y = τ z at h; subst y; rfl

theorem rebase_id (P : Presentation X) (Q : Presentation (Total P))
    (σ : Y → X) (a : Pullback P Q σ) : rebase P Q id σ a = a := by
  cases a; rfl

theorem rebase_comp (P : Presentation X) (Q : Presentation (Total P))
    (σ : Y → X) (τ : Z → Y) (υ : W → Z)
    (a : Pullback ((P.subst σ).subst τ) (reindex (P.subst σ) (reindex P Q σ) τ) υ) :
    rebase P Q σ (τ ∘ υ) (rebase (P.subst σ) (reindex P Q σ) τ υ a) =
      rebase P Q (σ ∘ τ) υ a := by cases a; rfl

/-- The constructed nested total is an actual categorical pullback, not only
an agreement of its Boolean observations. -/
theorem formed_isPullback (P : Presentation X) (Q : Presentation (Total P))
    (σ : Y → X) :
    IsPullback (↾(map P Q σ)) (↾(base (P.subst σ) (reindex P Q σ)))
      (↾(base P Q)) (↾σ) := by
  apply (Types.isPullback_iff _ _ _ _).mpr
  refine ⟨rfl, ?_, ?_⟩
  · intro a b h
    apply (comparison P Q σ).symm.injective
    exact Pullback.ext h.2 h.1
  · intro a y h
    refine ⟨comparison P Q σ ⟨y,a,h⟩, ?_, ?_⟩
    · exact comparison_original P Q σ _
    · exact comparison_base P Q σ _

/-- The second slice, formed within the first setting, flattens to Set/Total(Q). -/
def secondSettingEquivalence (P : Presentation X) (Q : Presentation (Total P)) :
    Over (formedDisplay Q) ≌ Setting Q := settingEquivalence Q

/-- The display and pullback representations induce equivalent actual settings. -/
noncomputable def comparisonSettings (P : Presentation X)
    (Q : Presentation (Total P)) (σ : Y → X) :
    Over (Pullback P Q σ) ≌ Setting (reindex P Q σ) :=
  Over.mapIso (comparison P Q σ).toIso

/-- Actual inverse image between the constructed slice settings. -/
noncomputable def settingSub (P : Presentation X) (Q : Presentation (Total P))
    (σ : Y → X) : Setting Q ⥤ Setting (reindex P Q σ) :=
  Over.pullback (↾(map P Q σ))

noncomputable def settingSubIdentity (P : Presentation X) (Q : Presentation (Total P)) :
    settingSub P Q id ≅ 𝟭 (Setting Q) := Over.pullbackId

noncomputable def settingSubComposition (P : Presentation X) (Q : Presentation (Total P))
    (σ : Y → X) (τ : Z → Y) :
    settingSub P Q (σ ∘ τ) ≅
      settingSub P Q σ ⋙ settingSub (P.subst σ) (reindex P Q σ) τ :=
  Over.pullbackComp (↾(map (P.subst σ) (reindex P Q σ) τ)) (↾(map P Q σ))

/-- Arbitrary slice sections, not only the displayed pair, obey the existing
canonical composition comparison. Its type is the iterated pullback family. -/
theorem setting_term_twice (P : Presentation X) (Q : Presentation (Total P))
    {A : Type u} (p : A ⟶ Nested P Q) (t : SquareKit.Family.Term p)
    (σ : Y → X) (τ : Z → Y) :
    (SquareKit.Family.termSub (SquareKit.Family.reindex p (↾(map P Q σ)))
      (↾(map (P.subst σ) (reindex P Q σ) τ))
      (SquareKit.Family.termSub p (↾(map P Q σ)) t)).val ≫
        (SquareKit.Family.compositionIso p (↾(map P Q σ))
          (↾(map (P.subst σ) (reindex P Q σ) τ))).hom =
      (SquareKit.Family.termSub p (↾(map P Q (σ ∘ τ))) t).val :=
  SquareKit.Family.termSub_composition p (↾(map P Q σ))
    (↾(map (P.subst σ) (reindex P Q σ) τ)) t

/-- Arbitrary dependent types may be used in the constructed nested setting. -/
abbrev Ty (P : Presentation X) (Q : Presentation (Total P)) := Nested P Q → Type u

def typeSub {P : Presentation X} {Q : Presentation (Total P)} (A : Ty P Q)
    (σ : Y → X) : Ty (P.subst σ) (reindex P Q σ) := A ∘ map P Q σ

def termSub {P : Presentation X} {Q : Presentation (Total P)} {A : Ty P Q}
    (t : (a : Nested P Q) → A a) (σ : Y → X) :
    (a : Nested (P.subst σ) (reindex P Q σ)) → typeSub A σ a := fun a => t (map P Q σ a)

@[simp] theorem typeSub_id {P : Presentation X} {Q : Presentation (Total P)}
    (A : Ty P Q) : typeSub A id = A := rfl

@[simp] theorem typeSub_comp {P : Presentation X} {Q : Presentation (Total P)}
    (A : Ty P Q) (σ : Y → X) (τ : Z → Y) :
    typeSub (typeSub A σ) τ = typeSub A (σ ∘ τ) := rfl

@[simp] theorem termSub_id {P : Presentation X} {Q : Presentation (Total P)}
    {A : Ty P Q} (t : (a : Nested P Q) → A a) : termSub t id = t := rfl

@[simp] theorem termSub_comp {P : Presentation X} {Q : Presentation (Total P)}
    {A : Ty P Q} (t : (a : Nested P Q) → A a) (σ : Y → X) (τ : Z → Y) :
    termSub (termSub t σ) τ = termSub t (σ ∘ τ) := rfl

theorem type_comparison {P : Presentation X} {Q : Presentation (Total P)}
    (A : Ty P Q) (σ : Y → X) (a : Pullback P Q σ) :
    typeSub A σ (comparison P Q σ a) = A a.original :=
  congrArg A (comparison_original P Q σ a)

/-- The same type comparison transports the term, rather than comparing it in
an unrelated fiber or retaining only inhabitation. -/
theorem term_comparison {P : Presentation X} {Q : Presentation (Total P)}
    {A : Ty P Q} (t : (a : Nested P Q) → A a) (σ : Y → X) (a : Pullback P Q σ) :
    cast (type_comparison A σ a) (termSub t σ (comparison P Q σ a)) = t a.original := by
  rcases a with ⟨y, ⟨⟨x,a⟩,b⟩,h⟩; change x = σ y at h; subst x; rfl

/-- The whole dependent selected value agrees after two substitutions. -/
theorem dependent_comparison_comp {P : Presentation X} {Q : Presentation (Total P)}
    {A : Ty P Q} (t : (a : Nested P Q) → A a) (σ : Y → X) (τ : Z → Y)
    (a : Pullback (P.subst σ) (reindex P Q σ) τ) :
    (⟨map P Q (σ ∘ τ) (comparison P Q (σ ∘ τ) (rebase P Q σ τ a)),
      termSub (termSub t σ) τ (comparison P Q (σ ∘ τ) (rebase P Q σ τ a))⟩ :
        (z : Nested P Q) × A z) =
      ⟨map P Q σ a.original, t (map P Q σ a.original)⟩ :=
  congrArg (fun z => (⟨z,t z⟩ : (z : Nested P Q) × A z))
    (comparison_original P Q (σ ∘ τ) (rebase P Q σ τ a))

/-- A selected first section and a dependent second section. -/
abbrev Argument (P : Presentation X) (Q : Presentation (Total P)) :=
  (a : Section P) × Section (Q.subst a.graph)

/-- The two selected sections determine their classifying map. -/
def classify {P : Presentation X} {Q : Presentation (Total P)} (s : Argument P Q) :
    X → Nested P Q := fun x => ⟨⟨x, s.1 x⟩, s.2 x⟩

@[simp] theorem classify_base {P : Presentation X} {Q : Presentation (Total P)}
    (s : Argument P Q) : base P Q ∘ classify s = id := rfl

/-- Normalize a whole dependent pair along its base equation. -/
def normalize {P : Presentation X} {Q : Presentation (Total P)}
    (z : Nested P Q) {x : X} (h : base P Q z = x) :
    (a : Fiber P x) × Fiber Q ⟨x,a⟩ := by
  rcases z with ⟨⟨y,a⟩,b⟩
  change y = x at h
  subst y
  exact ⟨a,b⟩

theorem normalize_eta {P : Presentation X} {Q : Presentation (Total P)}
    (z : Nested P Q) {x : X} (h : base P Q z = x) :
    (⟨⟨x,(normalize z h).1⟩,(normalize z h).2⟩ : Nested P Q) = z := by
  rcases z with ⟨⟨y,a⟩,b⟩
  change y = x at h
  subst y
  rfl

/-- Every map over the base recovers both dependent selections. -/
def recover {P : Presentation X} {Q : Presentation (Total P)}
    (f : X → Nested P Q) (h : base P Q ∘ f = id) : Argument P Q :=
  ⟨fun x => (normalize (f x) (congrFun h x)).1,
    fun x => (normalize (f x) (congrFun h x)).2⟩

@[simp] theorem recover_classify {P : Presentation X} {Q : Presentation (Total P)}
    (s : Argument P Q) : recover (classify s) (classify_base s) = s := by cases s; rfl

@[simp] theorem classify_recover {P : Presentation X} {Q : Presentation (Total P)}
    (f : X → Nested P Q) (h : base P Q ∘ f = id) : classify (recover f h) = f := by
  funext x
  exact normalize_eta (f x) (congrFun h x)

/-- Universal section interpretation of the nested construction. -/
def argumentEquiv (P : Presentation X) (Q : Presentation (Total P)) :
    Argument P Q ≃ {f : X → Nested P Q // base P Q ∘ f = id} where
  toFun s := ⟨classify s, classify_base s⟩
  invFun f := recover f.val f.property
  left_inv := recover_classify
  right_inv f := Subtype.ext (classify_recover f.val f.property)

/-- Reconstruct a classifying map in the substituted context from an arbitrary
map to the original nested total whose base is the substitution. -/
def liftClassifying {P : Presentation X} {Q : Presentation (Total P)}
    (σ : Y → X) (f : Y → Nested P Q) (h : base P Q ∘ f = σ) :
    Y → Nested (P.subst σ) (reindex P Q σ) :=
  fun y => comparison P Q σ ⟨y,f y,congrFun h y⟩

theorem liftClassifying_base {P : Presentation X} {Q : Presentation (Total P)}
    (σ : Y → X) (f : Y → Nested P Q) (h : base P Q ∘ f = σ) :
    base (P.subst σ) (reindex P Q σ) ∘ liftClassifying σ f h = id := by
  funext y
  exact comparison_base P Q σ _

/-- Universal interpretation over every base substitution. Both sections and
their dependence are recovered, so this is stronger than a map on observations. -/
def argumentOverEquiv (P : Presentation X) (Q : Presentation (Total P)) (σ : Y → X) :
    Argument (P.subst σ) (reindex P Q σ) ≃
      {f : Y → Nested P Q // base P Q ∘ f = σ} where
  toFun s := ⟨map P Q σ ∘ classify s,rfl⟩
  invFun f := recover (liftClassifying σ f.val f.property)
    (liftClassifying_base σ f.val f.property)
  left_inv s := by
    apply (argumentEquiv (P.subst σ) (reindex P Q σ)).injective
    apply Subtype.ext
    change classify (recover _ _) = classify s
    rw [classify_recover]
    funext y
    exact (comparison P Q σ).apply_symm_apply (classify s y)
  right_inv f := by
    apply Subtype.ext
    change map P Q σ ∘ classify (recover _ _) = f.val
    rw [classify_recover]
    funext y
    exact comparison_original P Q σ _

/-- Both models are interpreted from the existing geometric scheme, in order. -/
noncomputable def argumentOfModels {P : Presentation X} {Q : Presentation (Total P)}
    (M : Model P) (N : Model (Q.subst M.toSection.graph)) : Argument P Q :=
  ⟨M.toSection, N.toSection⟩

theorem first_model_recovery {P : Presentation X} {Q : Presentation (Total P)}
    (M : Model P) (N : Model (Q.subst M.toSection.graph)) :
    (argumentOfModels M N).1.toModel = M := Model.toSection_toModel M

theorem second_model_recovery {P : Presentation X} {Q : Presentation (Total P)}
    (M : Model P) (N : Model (Q.subst M.toSection.graph)) :
    (argumentOfModels M N).2.toModel = N := Model.toSection_toModel N

/-- Reindexing the first generic model along the nested classifying map
recovers the author's first interpretation. -/
theorem first_generic_recovery {P : Presentation X} {Q : Presentation (Total P)}
    (s : Argument P Q) :
    (genericModel P).subst (fun x => (classify s x).1) = s.1.toModel := rfl

/-- The second generic model recovers the second interpretation over the
selected first model, preserving the dependency. -/
theorem second_generic_recovery {P : Presentation X} {Q : Presentation (Total P)}
    (s : Argument P Q) : (genericModel Q).subst (classify s) = s.2.toModel := rfl

/-- Reindex the argument using the lifted first section; no second comparison
law is an added field. -/
def argumentSub {P : Presentation X} {Q : Presentation (Total P)}
    (s : Argument P Q) (σ : Y → X) : Argument (P.subst σ) (reindex P Q σ) :=
  ⟨s.1.subst σ, s.2.subst σ⟩

@[simp] theorem argumentSub_id {P : Presentation X} {Q : Presentation (Total P)}
    (s : Argument P Q) : argumentSub s id = s := rfl

@[simp] theorem argumentSub_comp {P : Presentation X} {Q : Presentation (Total P)}
    (s : Argument P Q) (σ : Y → X) (τ : Z → Y) :
    argumentSub (argumentSub s σ) τ = argumentSub s (σ ∘ τ) := rfl

theorem classify_sub {P : Presentation X} {Q : Presentation (Total P)}
    (s : Argument P Q) (σ : Y → X) :
    map P Q σ ∘ classify (argumentSub s σ) = classify s ∘ σ := rfl

/-- The comparison reconstructs both selected components, including the
second value's type over the selected first one. -/
theorem selected_comparison {P : Presentation X} {Q : Presentation (Total P)}
    (s : Argument P Q) (σ : Y → X) (y : Y) :
    comparison P Q σ ⟨y, classify s (σ y), rfl⟩ =
      classify (argumentSub s σ) y := rfl

end SquareKit.Internal.NestedSetting
