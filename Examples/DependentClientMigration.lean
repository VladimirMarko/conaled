import SquareKit.Internal.DependentJudgments.DerivedPathSemantics
import Examples.DependentCongruence
import SquareKit.Internal.DependentJudgments.NativeTypeModel

/-! A guarded replacement for the retained dependent pairing conversion. -/
namespace Examples.DependentClientMigration
open SquareKit.Internal.DependentJudgments.Contextual
open SquareKit.GuardedTheory
set_option backward.isDefEq.respectTransparency false
noncomputable section
variable {V : Type} {Ω : List (Judgment V)} {Γ A x : Expression V}

abbrev constantFamily (Γ A : Expression V) := subTy A (weaken Γ A)
abbrev computed (Γ A x : Expression V) :=
  transport Γ A (constantFamily Γ A) x x (reflexivity A x) x
abbrev firstPair (Γ A t : Expression V) := pair A (identitySub Γ) t
abbrev secondFamily (Γ A : Expression V) :=
  identity (subTy A (weaken Γ A)) (generic Γ A) (generic Γ A)
abbrev secondTerm (Γ A : Expression V) :=
  reflexivity (subTy A (weaken Γ A)) (generic Γ A)
abbrev doublePair (Γ A t : Expression V) :=
  pair (secondFamily Γ A) (firstPair Γ A t)
    (subTm (secondTerm Γ A) (firstPair Γ A t))

def computed_typed (hx : Tm (Ω := Ω) Γ A x) : Tm (Ω := Ω) Γ A (computed Γ A x) :=
  (hx.transport (hx.family.substitute hx.family.weaken) hx hx.reflexivity
    (hx.convert (hx.family.weakenSection hx).symmetric)).convert (hx.family.weakenSection hx)

def computed_beta (hx : Tm (Ω := Ω) Γ A x) : Equal (Ω := Ω) (computed Γ A x) x :=
  hx.transportRefl (hx.family.substitute hx.family.weaken)
    (hx.convert (hx.family.weakenSection hx).symmetric)

def firstPair_typed (ht : Tm (Ω := Ω) Γ A t) :
    Sub (Ω := Ω) Γ (extend Γ A) (firstPair Γ A t) :=
  ht.section

def doublePair_typed (ht : Tm (Ω := Ω) Γ A t) :
    Sub (Ω := Ω) Γ (extend (extend Γ A) (secondFamily Γ A)) (doublePair Γ A t) :=
  Sub.pair (ht.family.generic.identity ht.family.generic) (firstPair_typed ht)
    (ht.family.generic.reflexivity.substitute (firstPair_typed ht))

/-- Both the first component and the dependent second component change. -/
def replacement (hx : Tm (Ω := Ω) Γ A x) :
    Equal (Ω := Ω) (doublePair Γ A (computed Γ A x)) (doublePair Γ A x) := by
  have h := Equal.pair (.reflexive A) (.reflexive (identitySub Γ)) (computed_beta hx)
  exact Equal.pair (.reflexive (secondFamily Γ A)) h
    (Equal.subTm (.reflexive (secondTerm Γ A)) h)

namespace Source
abbrev g : Expression (Fin 3) := .var 0
abbrev a : Expression (Fin 3) := .var 1
abbrev pointExpr : Expression (Fin 3) := .var 2
def assumptions : List (Judgment (Fin 3)) := [term g a pointExpr]
def point : Tm (Ω := assumptions) g a pointExpr := .hypothesis (by simp [assumptions])
def left : Expression (Fin 3) := doublePair g a (computed g a pointExpr)
def right : Expression (Fin 3) := doublePair g a pointExpr
def left_typed := doublePair_typed (computed_typed point)
def right_typed := doublePair_typed point
def equality : Equal (Ω := assumptions) left right := replacement point

theorem first_recipes_distinct : computed g a pointExpr ≠ pointExpr := by
  intro h
  cases h

/-- The source congruence retains the whole dependent substitution. -/
def reindex (σ : Expression (Fin 3)) :
    Equal (Ω := assumptions) (comp left σ) (comp right σ) :=
  Equal.comp equality (.reflexive σ)
end Source

namespace Semantics
open SquareKit.Internal.DependentJudgments SquareKit.Internal.PathTransport.Typed
open DerivedSemantics
universe u
variable (M : Model.{u})

def selected (G : M.Context) (F : M.Family G) (v : M.Section G F) :=
  M.pairSub (M.identity (M.subTy F (M.weaken G F)) (M.genericVariable G F) (M.genericVariable G F))
    (M.toStructuralModel.sectionSub F v)
    (M.subTm (M.reflexivity (M.subTy F (M.weaken G F)) (M.genericVariable G F))
      (M.toStructuralModel.sectionSub F v))

variable (ρ : V → Value M.toStructuralModel) (g a t : SquareKit.Internal.DependentJudgments.Contextual.Expression V)
  (G : M.Context) (F : M.Family G) (v : M.Section G F)
  (hg : g.eval (algebra M) ρ = .context G)
  (ha : a.eval (algebra M) ρ = .family G F)
  (ht : t.eval (algebra M) ρ = .term G F v)

include hg ha ht in
theorem doublePair_eval : (doublePair g a t).eval (algebra M) ρ =
    .substitution G (M.extend (M.extend G F)
      (M.identity (M.subTy F (M.weaken G F)) (M.genericVariable G F) (M.genericVariable G F)))
      (selected M G F v) := by
  have hs := sectionSub_eval M ρ g a t G F v hg ha ht
  have hw : (weaken g a).eval (algebra M) ρ = .substitution (M.extend G F) G (M.weaken G F) := by
    change SquareKit.Internal.DependentJudgments.operation M.toStructuralModel .weaken
      ![g.eval (algebra M) ρ, a.eval (algebra M) ρ] = _
    rw [hg, ha]
    simp [SquareKit.Internal.DependentJudgments.operation]
  have hv : (generic g a).eval (algebra M) ρ =
      .term (M.extend G F) (M.subTy F (M.weaken G F)) (M.genericVariable G F) := by
    change SquareKit.Internal.DependentJudgments.operation M.toStructuralModel .generic
      ![g.eval (algebra M) ρ, a.eval (algebra M) ρ] = _
    rw [hg, ha]
    simp [SquareKit.Internal.DependentJudgments.operation]
  have hf := subTy_eval M ρ a (weaken g a) G (M.extend G F) F (M.weaken G F) ha hw
  have hb := identity_eval M ρ _ _ _ _ _ _ _ hf hv hv
  have hr := reflexivity_eval M ρ _ _ _ _ _ hf hv
  have he := subTm_eval M ρ _ _ _ _ _ _ _ hr hs
  exact pair_eval M ρ _ _ _ _ _ _ _ _ hb hs he


namespace Original
open SquareKit.Internal.PathTransport.Typed.Authoring
abbrev contextCode := extendCode emptyCode (baseCode emptyCode)
abbrev familyCode : TyCode contextCode := baseCode contextCode
abbrev point : TmCode contextCode familyCode := fun M => interpretTm M CongruenceCaller.point

theorem first_right_selected : interpretSub M CongruenceCaller.pairedRight =
    M.toStructuralModel.sectionSub (familyCode M) (point M) := by
  rw [interpretSub_agrees]
  change M.pairSub _ _ _ = M.pairSub _ _ _
  apply congrArg (M.pairSub (familyCode M) (M.idSub (contextCode M)))
  apply eq_of_heq
  apply (castCode_eval _ _ M).trans
  apply HEq.trans ?_ (cast_heq _ _).symm
  dsimp [point]
  rw [interpretTm_agrees]
  repeat first
    | exact HEq.rfl
    | apply (castCode_eval _ _ M).trans
    | apply (M.subTm_id _).trans

theorem right_selected : interpretSub M CongruenceCaller.dependentPairedRight =
    selected M (contextCode M) (familyCode M) (point M) := by
  have h := first_right_selected M
  rw [interpretSub_agrees] at h ⊢
  change M.pairSub _ _ (M.subTm _ _) = M.pairSub _ _ (M.subTm _ _)
  rw [h]
  rfl


private theorem castCode_cancel {γ : CtxCode} {a b : TyCode γ}
    (h : a = b) (v : TmCode γ a) : castCode h.symm (castCode h v) = v := by
  cases h
  rfl

/-- This is the guarantee of the exact retained inventory client. -/
theorem original_guarantee : interpretSub M CongruenceCaller.dependentPairedLeft =
    interpretSub M CongruenceCaller.dependentPairedRight := by
  rw [interpretSub_agrees, interpretSub_agrees]
  have h := subSound Examples.DependentCongruence.DependentArguments.dependentPair
  simp only [castCode_cancel] at h
  exact congrFun h M

theorem left_selected : interpretSub M CongruenceCaller.dependentPairedLeft =
    selected M (contextCode M) (familyCode M) (point M) := by
  rw [original_guarantee, right_selected]

end Original
def environment (G : M.Context) (F : M.Family G) (v : M.Section G F) :
    Fin 3 → Value M.toStructuralModel := ![.context G, .family G F, .term G F v]

theorem environment_satisfied (G : M.Context) (F : M.Family G) (v : M.Section G F) :
    ∀ p ∈ Source.assumptions, p.eval (algebra M) (environment M G F v) := by
  intro p hp
  have h := List.mem_singleton.mp hp
  subst p
  exact ⟨G, F, v, rfl, rfl, rfl⟩

theorem replacement_eval (G : M.Context) (F : M.Family G) (v : M.Section G F) :
    Source.left.eval (algebra M) (environment M G F v) =
      Source.right.eval (algebra M) (environment M G F v) :=
  Source.equality.sound (model M) _ (environment_satisfied M G F v)

theorem right_recovers : Source.right.eval (algebra M)
    (environment M (Original.contextCode M) (Original.familyCode M) (Original.point M)) =
    .substitution (Original.contextCode M)
      (M.extend (M.extend (Original.contextCode M) (Original.familyCode M))
        (M.identity (M.subTy (Original.familyCode M)
          (M.weaken (Original.contextCode M) (Original.familyCode M)))
          (M.genericVariable (Original.contextCode M) (Original.familyCode M))
          (M.genericVariable (Original.contextCode M) (Original.familyCode M))))
      (interpretSub M Authoring.CongruenceCaller.dependentPairedRight) := by
  rw [Original.right_selected]
  exact doublePair_eval M _ Source.g Source.a Source.pointExpr _ _ _ rfl rfl rfl

theorem left_recovers : Source.left.eval (algebra M)
    (environment M (Original.contextCode M) (Original.familyCode M) (Original.point M)) =
    .substitution (Original.contextCode M)
      (M.extend (M.extend (Original.contextCode M) (Original.familyCode M))
        (M.identity (M.subTy (Original.familyCode M)
          (M.weaken (Original.contextCode M) (Original.familyCode M)))
          (M.genericVariable (Original.contextCode M) (Original.familyCode M))
          (M.genericVariable (Original.contextCode M) (Original.familyCode M))))
      (interpretSub M Authoring.CongruenceCaller.dependentPairedLeft) := by
  rw [replacement_eval, Original.original_guarantee]
  exact right_recovers M

abbrev target := M.extend (M.extend (Original.contextCode M) (Original.familyCode M))
  (M.identity (M.subTy (Original.familyCode M)
    (M.weaken (Original.contextCode M) (Original.familyCode M)))
    (M.genericVariable (Original.contextCode M) (Original.familyCode M))
    (M.genericVariable (Original.contextCode M) (Original.familyCode M)))

def recovered : Option (M.Substitution (Original.contextCode M) (target M)) :=
  (Source.left.eval (algebra M)
    (environment M (Original.contextCode M) (Original.familyCode M) (Original.point M))).substitutionAt
      (Original.contextCode M) (target M)

theorem recovered_eq : recovered M =
    some (interpretSub M Authoring.CongruenceCaller.dependentPairedLeft) := by
  unfold recovered
  rw [left_recovers, Value.substitutionAt_substitution]

/-- Exact selected arrows, including the dependent second component, survive
arbitrary object-context substitutions. -/
theorem recovered_twice {D E : M.Context}
    (σ : M.Substitution D (Original.contextCode M)) (τ : M.Substitution E D) :
    (recovered M).map (fun f => M.compSub (M.compSub f σ) τ) =
      some (M.compSub (M.compSub (interpretSub M Authoring.CongruenceCaller.dependentPairedLeft) σ) τ) := by
  rw [recovered_eq]
  rfl

end Semantics
namespace Discriminator
open Semantics SquareKit.Internal.PathTransport.Typed
abbrev M := SquareKit.Internal.DependentJudgments.NativeType.model Nat (fun n => Fin (n + 1))

def input (n : Nat) : Original.contextCode M := ⟨PUnit.unit, n⟩

theorem point_value : Original.point M = ⟨fun g => (show Nat from g.2)⟩ := by
  unfold Original.point
  rw [interpretTm_agrees]
  apply eq_of_heq
  exact castCode_eval _ _ M

theorem selected_point (n : Nat) :
    (recovered M).map (fun f => (f.down (input n)).1.2) = some n := by
  rw [recovered_eq, Original.left_selected, point_value]
  rfl

/-- Replacing the selected point by zero would lose data even though the
context and the shape of its dependent identity fiber are unchanged. -/
theorem rejects_erased_point :
    (recovered M).map (fun f => (f.down (input 2)).1.2) ≠ some 0 := by
  rw [selected_point]
  decide

def successor : M.Substitution (Original.contextCode M) (Original.contextCode M) :=
  ⟨fun g => input ((show Nat from g.2) + 1)⟩
def doubling : M.Substitution (Original.contextCode M) (Original.contextCode M) :=
  ⟨fun g => input (2 * (show Nat from g.2))⟩

theorem selected_after_two_substitutions :
    ((recovered M).map (fun f => M.compSub (M.compSub f successor) doubling)).map
      (fun f => (f.down (input 3)).1.2) = some 7 := by
  rw [recovered_twice, Original.left_selected, point_value]
  rfl

end Discriminator

end
end Examples.DependentClientMigration
