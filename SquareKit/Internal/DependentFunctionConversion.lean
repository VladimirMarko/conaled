import SquareKit.Internal.DependentFunctionNormalizationSubstitution

/-! Canonical equality characterizes the existing generated equality relation. -/
namespace SquareKit.Internal.DependentFunctions

mutual
  theorem DepEq.normal_eq : {n : Nat} → {Γ : Ctx n} → {t u : Dep Γ} →
      DepEq t u → t.normal = u.normal
    | _, _, _, _, .refl _ => rfl
    | _, _, _, _, .symm h => (DepEq.normal_eq h).symm
    | _, _, _, _, .trans h k => (DepEq.normal_eq h).trans (DepEq.normal_eq k)
    | _, _, _, _, .app h a => congrArg (fun f => f.plug a) (FuncEq.normal_eq h)
    | _, _, _, _, .beta t a => by
      change t.normal.plug a = ((Sub.plug _ a).depSub t).normal
      rw [← Normal.plug_ofRen, Sub.depSub_ofRen, Dep.normal_map]
      rfl
    | _, _, _, _, .sub σ _ h => by
      simp only [Dep.normal_sub, DepEq.normal_eq h]
  theorem FuncEq.normal_eq : {n : Nat} → {Γ : Ctx n} → {f g : Func Γ} →
      FuncEq f g → f.normal = g.normal
    | _, _, _, _, .refl _ => rfl
    | _, _, _, _, .symm h => (FuncEq.normal_eq h).symm
    | _, _, _, _, .trans h k => (FuncEq.normal_eq h).trans (FuncEq.normal_eq k)
    | _, _, _, _, .lam h => DepEq.normal_eq h
    | _, _, _, _, .eta f => by
      change ((Ren.weaken _).funcMap f).normal.plug (.var 0) = f.normal
      rw [Func.normal_map, Normal.Dep.eta_plug]
    | _, _, _, _, .sub σ _ h => by
      simp only [Func.normal_sub, FuncEq.normal_eq h]
end

theorem Dep.convertible_iff {n} {Γ : Ctx n} (t u : Dep Γ) :
    DepEq t u ↔ t.normal = u.normal := by
  constructor
  · exact DepEq.normal_eq
  · intro h
    exact .trans t.normal_sound (by rw [h]; exact .symm u.normal_sound)

theorem Func.convertible_iff {n} {Γ : Ctx n} (f g : Func Γ) :
    FuncEq f g ↔ f.normal = g.normal := by
  constructor
  · exact FuncEq.normal_eq
  · intro h
    exact .trans f.normal_sound (by rw [h]; exact .symm g.normal_sound)

-- Structural comparison retains variable paths and literal base-index syntax.
deriving instance DecidableEq for DVar
deriving instance DecidableEq for FVar
deriving instance DecidableEq for Normal.Dep

def Dep.decideEq {n} {Γ : Ctx n} (t u : Dep Γ) : Decidable (DepEq t u) :=
  if h : t.normal = u.normal then isTrue ((t.convertible_iff u).mpr h)
  else isFalse (fun k => h ((t.convertible_iff u).mp k))

def Func.decideEq {n} {Γ : Ctx n} (f g : Func Γ) : Decidable (FuncEq f g) :=
  if h : f.normal = g.normal then isTrue ((f.convertible_iff g).mpr h)
  else isFalse (fun k => h ((f.convertible_iff g).mp k))

inductive ConversionFailure where
  | leftIndex | rightIndex | notConvertible
  deriving DecidableEq, Repr

/-- Optional author service. The expected index is explicit; no index equation
or source elaboration is inferred. Successful output is the existing proof. -/
def Dep.check {n} {Γ : Ctx n} (expected : DependentStructural.Base n) (t u : Dep Γ) :
    Except ConversionFailure (PLift (DepEq t u)) :=
  if t.type ≠ expected then .error .leftIndex
  else if u.type ≠ expected then .error .rightIndex
  else match t.decideEq u with
    | .isTrue h => .ok ⟨h⟩
    | .isFalse _ => .error .notConvertible

def Func.check {n} {Γ : Ctx n} (expected : DependentStructural.Base (n+1))
    (f g : Func Γ) : Except ConversionFailure (PLift (FuncEq f g)) :=
  if f.type ≠ expected then .error .leftIndex
  else if g.type ≠ expected then .error .rightIndex
  else match f.decideEq g with
    | .isTrue h => .ok ⟨h⟩
    | .isFalse _ => .error .notConvertible

theorem Dep.check_success {n} {Γ : Ctx n} (b : DependentStructural.Base n) (t u : Dep Γ) :
    (∃ h, t.check b u = .ok h) ↔ t.type = b ∧ u.type = b ∧ DepEq t u := by
  unfold Dep.check
  split
  · simp_all
  · split
    · simp_all
    · cases t.decideEq u with
      | isTrue h => simp_all; exact ⟨⟨h⟩, trivial⟩
      | isFalse h => simp_all

theorem Func.check_success {n} {Γ : Ctx n} (b : DependentStructural.Base (n+1)) (f g : Func Γ) :
    (∃ h, f.check b g = .ok h) ↔ f.type = b ∧ g.type = b ∧ FuncEq f g := by
  unfold Func.check
  split
  · simp_all
  · split
    · simp_all
    · cases f.decideEq g with
      | isTrue h => simp_all; exact ⟨⟨h⟩, trivial⟩
      | isFalse h => simp_all

end SquareKit.Internal.DependentFunctions
