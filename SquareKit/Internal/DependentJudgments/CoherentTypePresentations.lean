import SquareKit.Internal.DependentJudgments.NativeTypeModel
import Mathlib.Logic.Equiv.Fin.Basic

/-! Concrete presentation changes of dependent Type families. Fiber equivalences
may relate unequal types. Native identity and J remain lower-truncated. -/
namespace SquareKit.Internal.DependentJudgments.CoherentTypePresentations
open PathTransport.Typed StructuralModel
set_option backward.isDefEq.respectTransparency false
universe u

abbrev FamilyComparison {Γ Δ : Type u} (e : Γ ≃ Δ) (A : Γ → Type u) (B : Δ → Type u) :=
  (γ : Γ) → A γ ≃ B (e γ)

namespace FamilyComparison
variable {Γ Δ Θ : Type u} {e : Γ ≃ Δ} {A : Γ → Type u} {B : Δ → Type u}

def term (f : FamilyComparison e A B) : ((γ : Γ) → A γ) ≃ ((δ : Δ) → B δ) :=
  Equiv.piCongr e f

@[simp] theorem term_apply (f : FamilyComparison e A B) (t : (γ : Γ) → A γ) (γ : Γ) :
    f.term t (e γ) = f γ (t γ) := Equiv.piCongr_apply_apply e f t γ

def total (f : FamilyComparison e A B) : Sigma A ≃ Sigma B := Equiv.sigmaCongr e f

@[simp] theorem total_apply (f : FamilyComparison e A B) (γ : Γ) (a : A γ) :
    f.total ⟨γ, a⟩ = ⟨e γ, f γ a⟩ := rfl

def identity (A : Γ → Type u) : FamilyComparison (Equiv.refl Γ) A A := fun γ => Equiv.refl (A γ)

def compose {g : Δ ≃ Θ} {C : Θ → Type u}
    (f : FamilyComparison e A B) (h : FamilyComparison g B C) :
    FamilyComparison (e.trans g) A C := fun γ => (f γ).trans (h (e γ))

theorem term_identity (t : (γ : Γ) → A γ) : (identity A).term t = t := by
  funext γ
  exact term_apply (identity A) t γ

theorem term_compose {g : Δ ≃ Θ} {C : Θ → Type u}
    (f : FamilyComparison e A B) (h : FamilyComparison g B C) (t : (γ : Γ) → A γ) :
    (f.compose h).term t = h.term (f.term t) := by
  funext θ
  obtain ⟨γ, rfl⟩ := (e.trans g).surjective θ
  rw [term_apply]
  change h (e γ) (f γ (t γ)) = h.term (f.term t) (g (e γ))
  rw [term_apply, term_apply]

theorem total_compose {g : Δ ≃ Θ} {C : Θ → Type u}
    (f : FamilyComparison e A B) (h : FamilyComparison g B C) :
    (f.compose h).total = f.total.trans h.total := by
  apply Equiv.ext
  intro z
  rfl

/-- Native identity is mapped by congruence of the fiber equivalence. -/
def identityFamily (f : FamilyComparison e A B) (x y : (γ : Γ) → A γ) :
    FamilyComparison e (fun γ => ULift.{u} (PLift (x γ = y γ)))
      (fun δ => ULift.{u} (PLift (f.term x δ = f.term y δ))) := fun γ => {
  toFun p := ⟨⟨(f.term_apply x γ).trans (congrArg (f γ) p.down.down) |>.trans
    (f.term_apply y γ).symm⟩⟩
  invFun p := ⟨⟨(f γ).injective ((f.term_apply x γ).symm.trans p.down.down |>.trans
    (f.term_apply y γ))⟩⟩
  left_inv _ := Subsingleton.elim _ _
  right_inv _ := Subsingleton.elim _ _
}

theorem identityFamily_refl (f : FamilyComparison e A B) (x : (γ : Γ) → A γ) (γ : Γ) :
    f.identityFamily x x γ ⟨⟨rfl⟩⟩ = ⟨⟨rfl⟩⟩ := Subsingleton.elim _ _

end FamilyComparison

section TelescopeDefinition
variable (Base : Type u) (Fiber : Base → Type u)
local notation "M" => NativeType.structuralModel Base Fiber

/-- Each new binder may have a different equivalent fiber presentation. -/
inductive TelescopeComparison : {Γ Δ : (M).Context} → (Γ ≃ Δ) → {n : Nat} →
    Telescope M Γ n → Telescope M Δ n → Type (u+1) where
  | nil {Γ Δ} (e : Γ ≃ Δ) : TelescopeComparison e .nil .nil
  | cons {Γ Δ} {e : Γ ≃ Δ} {n} {A : (M).Family Γ} {B : (M).Family Δ}
      {T : Telescope M ((M).extend Γ A) n} {U : Telescope M ((M).extend Δ B) n}
      (f : FamilyComparison e A B) (tail : TelescopeComparison f.total T U) :
      TelescopeComparison e (.cons A T) (.cons B U)

end TelescopeDefinition

namespace TelescopeComparison
variable {Base : Type u} {Fiber : Base → Type u}
local notation "M" => NativeType.structuralModel Base Fiber

def total {Γ Δ : (M).Context} {e : Γ ≃ Δ} {n}
    {T : Telescope M Γ n} {U : Telescope M Δ n}
    (c : TelescopeComparison Base Fiber e T U) : T.total ≃ U.total :=
  match c with
  | .nil e => e
  | .cons _ tail => tail.total

theorem projection {Γ Δ : (M).Context} {e : Γ ≃ Δ} {n}
    {T : Telescope M Γ n} {U : Telescope M Δ n}
    (c : TelescopeComparison Base Fiber e T U) (z : T.total) :
    U.projection.down (c.total z) = e (T.projection.down z) := by
  induction c with
  | nil => rfl
  | cons f tail ih => exact congrArg Sigma.fst (ih z)


def identity {Γ : (M).Context} {n} (T : Telescope M Γ n) :
    TelescopeComparison Base Fiber (Equiv.refl Γ) T T :=
  match T with
  | .nil => .nil _
  | .cons A T => .cons (FamilyComparison.identity A) (identity T)

theorem identity_total {Γ : (M).Context} {n} (T : Telescope M Γ n) :
    (identity T).total = Equiv.refl T.total := by
  induction T with
  | nil => rfl
  | cons A T ih => exact ih

def compose {Γ Δ Θ : (M).Context} {e : Γ ≃ Δ} {g : Δ ≃ Θ} {n}
    {T : Telescope M Γ n} {U : Telescope M Δ n} {V : Telescope M Θ n}
    (c : TelescopeComparison Base Fiber e T U) (d : TelescopeComparison Base Fiber g U V) :
    TelescopeComparison Base Fiber (e.trans g) T V := by
  cases c with
  | nil e => cases d with | nil g => exact .nil (e.trans g)
  | cons f tail =>
    cases d with
    | cons h tail' =>
      refine .cons (f.compose h) ?_
      rw [FamilyComparison.total_compose]
      exact compose tail tail'
termination_by n


theorem total_cast {Γ Δ : (M).Context} {e e' : Γ ≃ Δ} {n}
    {T : Telescope M Γ n} {U : Telescope M Δ n}
    (h : e = e') (c : TelescopeComparison Base Fiber e T U) :
    (cast (congrArg (fun k => TelescopeComparison Base Fiber k T U) h) c).total = c.total := by
  cases h; rfl

theorem compose_total {Γ Δ Θ : (M).Context} {e : Γ ≃ Δ} {g : Δ ≃ Θ} {n}
    {T : Telescope M Γ n} {U : Telescope M Δ n} {V : Telescope M Θ n}
    (c : TelescopeComparison Base Fiber e T U) (d : TelescopeComparison Base Fiber g U V) :
    (compose c d).total = c.total.trans d.total := by
  induction c generalizing Θ with
  | nil e => cases d with | nil g => rw [compose]; rfl
  | cons f tail ih =>
    cases d with
    | cons h tail' =>
      rw [compose]
      dsimp only [total]
      exact (total_cast (FamilyComparison.total_compose f h).symm (compose tail tail')).trans (ih tail')

end TelescopeComparison

namespace FamilyComparison
variable {Base : Type u} {Fiber : Base → Type u} {Γ Δ : Type u} {e : Γ ≃ Δ}
variable {A : Γ → Type u} {B : Δ → Type u}
local notation "M" => NativeType.structuralModel Base Fiber

def path (f : FamilyComparison e A B) (x : (γ : Γ) → A γ) :
    (M).pathContext A ⟨x⟩ ≃ (M).pathContext B ⟨f.term x⟩ :=
  Equiv.sigmaCongr f.total (fun z => {
    toFun p := ⟨⟨(f.term_apply x z.1).trans (congrArg (f z.1) p.down.down)⟩⟩
    invFun p := ⟨⟨(f z.1).injective ((f.term_apply x z.1).symm.trans p.down.down)⟩⟩
    left_inv := by rintro ⟨⟨p⟩⟩; rfl
    right_inv := by rintro ⟨⟨p⟩⟩; rfl })

theorem path_root (f : FamilyComparison e A B) (x : (γ : Γ) → A γ) (γ : Γ) :
    f.path x (((M).rootSub A ⟨x⟩).down γ) =
      ((M).rootSub B ⟨f.term x⟩).down (e γ) := by
  apply (NativeType.rootEquiv Base Fiber B ⟨f.term x⟩).symm.injective
  rfl

end FamilyComparison


section Extension
variable {R S X Y : Type u} (r : R ≃ X) (s : S ≃ Y) (e : X ≃ Y)

/-- The reflexive branch context is determined by the compared total contexts. -/
def rootComparison : R ≃ S := (r.trans e).trans s.symm

theorem rootComparison_square (z : R) : s (rootComparison r s e z) = e (r z) :=
  s.apply_symm_apply _

variable {C : X → Type u} {D : Y → Type u} (m : FamilyComparison e C D)

def branchFamily : FamilyComparison (rootComparison r s e) (C ∘ r) (D ∘ s) :=
  fun z => (m (r z)).trans (Equiv.cast (congrArg D (rootComparison_square r s e z).symm))

def branchTerm (d : (z : R) → C (r z)) : (z : S) → D (s z) :=
  (branchFamily r s e m).term d

/-- Naturality of extension is proved from the inverse equations of the root
maps. The transformed branch is constructed from the old branch and motive. -/
theorem extension_map (d : (z : R) → C (r z)) :
    m.term (Equiv.piCongrLeft C r d) =
      Equiv.piCongrLeft D s (branchTerm r s e m d) := by
  funext y
  obtain ⟨z, rfl⟩ := (r.trans e).surjective y
  apply eq_of_heq
  have hl : m.term (Equiv.piCongrLeft C r d) (e (r z)) = m (r z) (d z) := by
    rw [FamilyComparison.term_apply, Equiv.piCongrLeft_apply_apply]
  apply (heq_of_eq hl).trans
  apply HEq.symm
  apply (congr_arg_heq (fun y => Equiv.piCongrLeft D s (branchTerm r s e m d) y)
    (rootComparison_square r s e z).symm).trans
  apply (heq_of_eq (Equiv.piCongrLeft_apply_apply D s _ (rootComparison r s e z))).trans
  apply (heq_of_eq (FamilyComparison.term_apply (branchFamily r s e m) d z)).trans
  exact cast_heq _ _

end Extension

section ContextualJ
variable {Base : Type u} {Fiber : Base → Type u}
local notation "M" => NativeType.structuralModel Base Fiber
variable {Γ Δ : Type u} {e : Γ ≃ Δ} {A : Γ → Type u} {B : Δ → Type u}
variable (f : FamilyComparison e A B) (x : (γ : Γ) → A γ) {n : Nat}
variable {T : Telescope (NativeType.structuralModel Base Fiber)
  ((NativeType.structuralModel Base Fiber).pathContext A ⟨x⟩) n}
variable {U : Telescope (NativeType.structuralModel Base Fiber)
  ((NativeType.structuralModel Base Fiber).pathContext B ⟨f.term x⟩) n}
variable (c : TelescopeComparison Base Fiber (f.path x) T U)
variable {C : T.total → Type u} {D : U.total → Type u}
variable (m : FamilyComparison c.total C D)

def jBranchComparison :
    (Telescope.pullback M T ((M).rootSub A ⟨x⟩)).total ≃
      (Telescope.pullback M U ((M).rootSub B ⟨f.term x⟩)).total :=
  rootComparison (NativeType.rootTailEquiv Base Fiber A ⟨x⟩ T)
    (NativeType.rootTailEquiv Base Fiber B ⟨f.term x⟩ U) c.total

theorem jBranchComparison_square
    (z : (Telescope.pullback M T ((M).rootSub A ⟨x⟩)).total) :
    ((M).rootTail B ⟨f.term x⟩ U).down (jBranchComparison f x c z) =
      c.total (((M).rootTail A ⟨x⟩ T).down z) :=
  rootComparison_square (NativeType.rootTailEquiv Base Fiber A ⟨x⟩ T)
    (NativeType.rootTailEquiv Base Fiber B ⟨f.term x⟩ U) c.total z

def jBranch (d : (M).Section (Telescope.pullback M T ((M).rootSub A ⟨x⟩)).total
    ((M).subTy C ((M).rootTail A ⟨x⟩ T))) :
    (M).Section (Telescope.pullback M U ((M).rootSub B ⟨f.term x⟩)).total
      ((M).subTy D ((M).rootTail B ⟨f.term x⟩ U)) :=
  ⟨branchTerm (NativeType.rootTailEquiv Base Fiber A ⟨x⟩ T)
    (NativeType.rootTailEquiv Base Fiber B ⟨f.term x⟩ U) c.total m d.down⟩

/-- Native contextual J respects unequal fiber presentations throughout every
finite telescope, motive and branch. The only input is their fiber equivalences. -/
theorem contextualJ_compare
    (d : (M).Section (Telescope.pullback M T ((M).rootSub A ⟨x⟩)).total
      ((M).subTy C ((M).rootTail A ⟨x⟩ T))) :
    m.term (NativeType.contextualJ Base Fiber A ⟨x⟩ T C d).down =
      (NativeType.contextualJ Base Fiber B ⟨f.term x⟩ U D (jBranch f x c m d)).down :=
  extension_map (NativeType.rootTailEquiv Base Fiber A ⟨x⟩ T)
    (NativeType.rootTailEquiv Base Fiber B ⟨f.term x⟩ U) c.total m d.down

end ContextualJ


namespace FiniteOption
abbrev Base := Nat × Bool
def flip : Base ≃ Base where
  toFun p := (p.1, !p.2)
  invFun p := (p.1, !p.2)
  left_inv p := by cases p; simp
  right_inv p := by cases p; simp

def direct (p : Base) : Type := Fin (p.1 + 1)
def coded (p : Base) : Type := Option (Fin p.1)
def comparison : FamilyComparison flip direct coded := fun p => finSuccEquiv p.1
def zero : (p : Base) → direct p := fun p => (0 : Fin (p.1 + 1))

theorem flip_changes_context : flip (3, false) = (3, true) := rfl

theorem zero_is_none (p : Base) : comparison.term zero (flip p) = none := by
  rw [FamilyComparison.term_apply]
  exact finSuccEquiv_zero

theorem successor_is_some (p : Base) (i : Fin p.1) : comparison p i.succ = some i :=
  finSuccEquiv_succ i

local notation "M₀" => NativeType.structuralModel Nat (fun n => Fin (n+1))
abbrev SourcePath := (M₀).pathContext direct ⟨zero⟩
abbrev TargetPath := (M₀).pathContext coded ⟨comparison.term zero⟩
def path : SourcePath ≃ TargetPath := comparison.path zero

def firstSource (p : SourcePath) : Type := Fin (p.1.1.1 + 1)
def firstTarget (p : TargetPath) : Type := Option (Fin p.1.1.1)
def firstComparison : FamilyComparison path firstSource firstTarget := fun p => finSuccEquiv p.1.1.1

def secondSource (p : Sigma firstSource) : Type := Fin (p.2.val + 1)
def secondTarget (p : Sigma firstTarget) : Type :=
  Option (Fin ((finSuccEquiv p.1.1.1.1).symm p.2).val)

def secondComparison : FamilyComparison firstComparison.total secondSource secondTarget := by
  intro p
  change Fin (p.2.val + 1) ≃ Option (Fin ((finSuccEquiv p.1.1.1.1).symm
    (finSuccEquiv p.1.1.1.1 p.2)).val)
  simpa only [Equiv.symm_apply_apply] using finSuccEquiv p.2.val

def sourceTail : Telescope M₀ SourcePath 2 := .cons firstSource (.cons secondSource .nil)
def targetTail : Telescope M₀ TargetPath 2 := .cons firstTarget (.cons secondTarget .nil)
def tails : TelescopeComparison Nat (fun n => Fin (n+1)) path sourceTail targetTail :=
  .cons firstComparison (.cons secondComparison (.nil secondComparison.total))

def sourceMotive (z : sourceTail.total) : Type := Fin (z.1.1.1.1.1 + 1)
def targetMotive (z : targetTail.total) : Type := Option (Fin z.1.1.1.1.1)
def motives : FamilyComparison tails.total sourceMotive targetMotive :=
  fun z => finSuccEquiv z.1.1.1.1.1

def sourceBranch : (M₀).Section
    (Telescope.pullback M₀ sourceTail ((M₀).rootSub direct ⟨zero⟩)).total
    ((M₀).subTy sourceMotive ((M₀).rootTail direct ⟨zero⟩ sourceTail)) :=
  ⟨fun z => z.1.2⟩

def targetBranch := jBranch comparison zero tails motives sourceBranch

def sourceResult := NativeType.contextualJ Nat (fun n => Fin (n+1)) direct ⟨zero⟩
  sourceTail sourceMotive sourceBranch

def targetResult := NativeType.contextualJ Nat (fun n => Fin (n+1)) coded
  ⟨comparison.term zero⟩ targetTail targetMotive targetBranch

/-- Two dependent binders and the result family all change representation. -/
theorem j_preserves_selected : motives.term sourceResult.down = targetResult.down :=
  contextualJ_compare comparison zero tails motives sourceBranch

def sampleBranch : (Telescope.pullback M₀ sourceTail ((M₀).rootSub direct ⟨zero⟩)).total :=
  ⟨⟨(3, false), (⟨2, by decide⟩ : Fin 4)⟩, (⟨1, by decide⟩ : Fin 3)⟩

def sampleSource : sourceTail.total := ((M₀).rootTail direct ⟨zero⟩ sourceTail).down sampleBranch

theorem source_selected_two : (sourceResult.down sampleSource).val = 2 := by
  have h := NativeType.contextualJ_beta Nat (fun n => Fin (n+1)) direct ⟨zero⟩
    sourceTail sourceMotive sourceBranch
  exact congrArg (fun t => (t.down sampleBranch).val) (eq_of_heq h)

theorem target_selected_some_one : targetResult.down (tails.total sampleSource) = some ⟨1, by decide⟩ := by
  rw [← j_preserves_selected, FamilyComparison.term_apply]
  have h : sourceResult.down sampleSource = (⟨2, by decide⟩ : Fin 4) :=
    Fin.ext source_selected_two
  rw [h]
  rfl

end FiniteOption

end SquareKit.Internal.DependentJudgments.CoherentTypePresentations
