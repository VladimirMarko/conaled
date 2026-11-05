import SquareKit.Internal.DependentJudgments.FrozenMemo
import SquareKit.Internal.DependentJudgments.MemoNormalization
import SquareKit.Internal.DependentJudgments.DerivedGroupoidSemantics
import Mathlib.CategoryTheory.SingleObj

/-! The generated memo in the integer translation action. Ordinary groupoid
identity has discrete second identities; this example does not discharge the
separate higher-model gate. -/
noncomputable section
namespace Examples.GuardedGroupoidMemo
open CategoryTheory SquareKit.GuardedTheory
open SquareKit.Internal.DependentJudgments
open SquareKit.Internal.DependentJudgments.Contextual
open SquareKit.Internal.DependentJudgments.Contextual.DerivedSemantics
open SquareKit.Internal.PathTransport.GroupoidModel
open SquareKit.Internal.DependentJudgments.Contextual.Memo
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward false

abbrev Integers := SingleObj (Multiplicative Int)
def integerPoint : Integers := SingleObj.star _
def translation : Integers ⥤ Type where
  obj _ := Int
  map p := ↾fun b => Multiplicative.toAdd p + b
  map_id _ := by ext b; exact zero_add b
  map_comp p q := by ext b; exact add_assoc _ _ _

abbrev alpha : Contextual.Expression (Fin 2) := .var 0
abbrev beta : Contextual.Expression (Fin 2) := .var 1
abbrev premises : List (Contextual.Judgment (Fin 2)) :=
  [family Contextual.empty alpha, family (Contextual.extend Contextual.empty alpha) beta]
def signature : Frozen.Signature premises where
  Γ := Contextual.empty
  A := alpha
  B := beta
  hA := .hypothesis (by simp [premises])
  hB := .hypothesis (by simp [premises])

section Evaluation
universe u
variable (M : SquareKit.Internal.PathTransport.Typed.Model.{u}) {V : Type}
variable (ρ : V → Value M.toStructuralModel)

theorem extend_eval (g a : Contextual.Expression V) (Γ : M.Context) (A : M.Family Γ)
    (hg : g.eval (Contextual.algebra M) ρ = .context Γ)
    (ha : a.eval (Contextual.algebra M) ρ = .family Γ A) :
    (Contextual.extend g a).eval (Contextual.algebra M) ρ = .context (M.extend Γ A) := by
  change SquareKit.Internal.DependentJudgments.operation M.toStructuralModel .extend
    ![g.eval (Contextual.algebra M) ρ, a.eval (Contextual.algebra M) ρ] = _
  rw [hg, ha]
  simp [SquareKit.Internal.DependentJudgments.operation]

theorem weaken_eval (g a : Contextual.Expression V) (Γ : M.Context) (A : M.Family Γ)
    (hg : g.eval (Contextual.algebra M) ρ = .context Γ)
    (ha : a.eval (Contextual.algebra M) ρ = .family Γ A) :
    (Contextual.weaken g a).eval (Contextual.algebra M) ρ =
      .substitution (M.extend Γ A) Γ (M.weaken Γ A) := by
  change SquareKit.Internal.DependentJudgments.operation M.toStructuralModel .weaken
    ![g.eval (Contextual.algebra M) ρ, a.eval (Contextual.algebra M) ρ] = _
  rw [hg, ha]
  simp [SquareKit.Internal.DependentJudgments.operation]

theorem generic_eval (g a : Contextual.Expression V) (Γ : M.Context) (A : M.Family Γ)
    (hg : g.eval (Contextual.algebra M) ρ = .context Γ)
    (ha : a.eval (Contextual.algebra M) ρ = .family Γ A) :
    (Contextual.generic g a).eval (Contextual.algebra M) ρ =
      .term (M.extend Γ A) (M.subTy A (M.weaken Γ A)) (M.genericVariable Γ A) := by
  change SquareKit.Internal.DependentJudgments.operation M.toStructuralModel .generic
    ![g.eval (Contextual.algebra M) ρ, a.eval (Contextual.algebra M) ρ] = _
  rw [hg, ha]
  simp [SquareKit.Internal.DependentJudgments.operation]

theorem comp_eval (s t : Contextual.Expression V) (Γ Δ Θ : M.Context)
    (σ : M.Substitution Δ Γ) (τ : M.Substitution Θ Δ)
    (hs : s.eval (Contextual.algebra M) ρ = .substitution Δ Γ σ)
    (ht : t.eval (Contextual.algebra M) ρ = .substitution Θ Δ τ) :
    (Contextual.comp s t).eval (Contextual.algebra M) ρ =
      .substitution Θ Γ (M.compSub σ τ) := by
  change SquareKit.Internal.DependentJudgments.operation M.toStructuralModel .comp
    ![s.eval (Contextual.algebra M) ρ, t.eval (Contextual.algebra M) ρ] = _
  rw [hs, ht]
  simp [SquareKit.Internal.DependentJudgments.operation]

theorem lift_eval (d a s : Contextual.Expression V) (Γ Δ : M.Context)
    (A : M.Family Γ) (σ : M.Substitution Δ Γ)
    (hd : d.eval (Contextual.algebra M) ρ = .context Δ)
    (ha : a.eval (Contextual.algebra M) ρ = .family Γ A)
    (hs : s.eval (Contextual.algebra M) ρ = .substitution Δ Γ σ) :
    (Contextual.lift d a s).eval (Contextual.algebra M) ρ =
      .substitution (M.extend Δ (M.subTy A σ)) (M.extend Γ A)
        (M.pairSub A (M.compSub σ (M.weaken Δ (M.subTy A σ)))
          (cast (congrArg (M.Section _) (M.subTy_comp A σ (M.weaken Δ (M.subTy A σ))))
            (M.genericVariable Δ (M.subTy A σ)))) := by
  have hA := subTy_eval M ρ a s Γ Δ A σ ha hs
  have hw := weaken_eval M ρ d (Contextual.subTy a s) Δ (M.subTy A σ) hd hA
  have hc := comp_eval M ρ s (Contextual.weaken d (Contextual.subTy a s)) Γ Δ _ σ _ hs hw
  have ht := generic_eval M ρ d (Contextual.subTy a s) Δ (M.subTy A σ) hd hA
  have et := Value.term_eq (M.subTy_comp A σ (M.weaken Δ (M.subTy A σ)))
    (cast_heq (congrArg (M.Section _) (M.subTy_comp A σ (M.weaken Δ (M.subTy A σ))))
      (M.genericVariable Δ (M.subTy A σ))).symm
  exact pair_eval M ρ a _ _ Γ _ A _ _ ha hc (ht.trans et)

variable {Ω : List (Contextual.Judgment V)}

/-- Semantic interpretation of a displayed tail, one source family at a time. -/
inductive DisplayRealization : {g : Contextual.Expression V} → Frozen.Display Ω g → M.Context → Type u where
  | nil {g} (hg : Ctx (Ω := Ω) g) (G : M.Context) : DisplayRealization (.nil hg) G
  | cons {g a} (ha : Ty (Ω := Ω) g a) (tail : Frozen.Display Ω (Contextual.extend g a))
      (G : M.Context) (A : M.Family G)
      (ha_eval : a.eval (Contextual.algebra M) ρ = .family G A)
      (rest : DisplayRealization tail (M.extend G A)) : DisplayRealization (.cons ha tail) G

namespace DisplayRealization
variable {M ρ}
def total {g G} {D : Frozen.Display Ω g} : DisplayRealization M ρ D G → M.Context
  | .nil _ G => G
  | .cons _ _ _ _ _ rest => rest.total

theorem total_eval {g G} {D : Frozen.Display Ω g} (R : DisplayRealization M ρ D G)
    (hg : g.eval (Contextual.algebra M) ρ = .context G) :
    D.total.eval (Contextual.algebra M) ρ = .context R.total := by
  induction R with
  | nil => exact hg
  | cons ha tail G A hA rest ih =>
      exact ih (extend_eval M ρ _ _ G A hg hA)

structure Pullback {g G} {D : Frozen.Display Ω g} (R : DisplayRealization M ρ D G)
    {d s} (hd : Ctx (Ω := Ω) d) (hs : Sub (Ω := Ω) d g s) (H : M.Context) where
  display : DisplayRealization M ρ (D.pullback hd hs) H
  map : M.Substitution display.total R.total
  map_eval : (D.square hs).eval (Contextual.algebra M) ρ = .substitution display.total R.total map

def pullback {g G} {D : Frozen.Display Ω g} (R : DisplayRealization M ρ D G)
    {d s} (hd : Ctx (Ω := Ω) d) (hs : Sub (Ω := Ω) d g s) (H : M.Context)
    (σ : M.Substitution H G) (hd_eval : d.eval (Contextual.algebra M) ρ = .context H)
    (hs_eval : s.eval (Contextual.algebra M) ρ = .substitution H G σ) : R.Pullback hd hs H :=
  match R with
  | .nil hg G => ⟨.nil hd H, σ, hs_eval⟩
  | .cons ha tail G A hA rest =>
      let hAs := subTy_eval M ρ _ _ G H A σ hA hs_eval
      let hL := lift_eval M ρ _ _ _ G H A σ hd_eval hA hs_eval
      let L := M.pairSub A (M.compSub σ (M.weaken H (M.subTy A σ)))
        (cast (congrArg (M.Section _) (M.subTy_comp A σ (M.weaken H (M.subTy A σ))))
          (M.genericVariable H (M.subTy A σ)))
      let next := rest.pullback (ha.substitute hs).extend (hs.lift ha)
        (M.extend H (M.subTy A σ)) L
        (extend_eval M ρ _ _ H (M.subTy A σ) hd_eval hAs) hL
      ⟨.cons (ha.substitute hs) (tail.pullback (ha.substitute hs).extend (hs.lift ha))
        H (M.subTy A σ) hAs next.display, next.map, next.map_eval⟩
end DisplayRealization

def termFamily : Value M.toStructuralModel → Value M.toStructuralModel
  | .term Γ A _ => .family Γ A
  | _ => .invalid

theorem family_of_eval {g a t : Contextual.Expression V} (ht : Tm (Ω := Ω) g a t)
    (hΩ : ∀ j ∈ Ω, j.eval (Contextual.algebra M) ρ)
    (G : M.Context) (A : M.Family G) (v : M.Section G A)
    (he : t.eval (Contextual.algebra M) ρ = .term G A v) :
    a.eval (Contextual.algebra M) ρ = .family G A := by
  rcases Contextual.interpret ht M ρ hΩ with ⟨G', A', v', _, hA, hv⟩
  change a.eval (Contextual.algebra M) ρ = .family G' A' at hA
  change t.eval (Contextual.algebra M) ρ = .term G' A' v' at hv
  exact hA.trans (congrArg (termFamily M) (hv.symm.trans he))
end Evaluation

section Realization
universe u
variable (C : Type u) [CategoryTheory.Groupoid.{u} C] (B : C ⥤ Type u)
local notation "M" => Instance.fullModel C B
variable {V : Type} {Ω : List (Contextual.Judgment V)}
variable (ρ : V → Value (Instance.structuralModel C B))

theorem transport_action {G : Grpd.{u,u}} (x y : Section (constant (Γ := G) C))
    (p : Section (identityFamily (constant C) x y))
    (b : ULift.{u+1} (Section (primitiveFiber B x))) (g : G) :
    ((transportValue M (constant C) (DerivedSemantics.Groupoid.genericFiber C B G)
      ⟨x⟩ ⟨y⟩ ⟨p⟩ b).down.obj g).as = B.map (p.obj g).as (b.down.obj g).as := by
  rcases b with ⟨b⟩
  exact DerivedSemantics.Groupoid.transportValue_action C B x y p b g

/-- Evaluation data for the actual generated binders, retaining the primitive
family at the generic base point. No memo output equation is assumed. -/
structure PointsRealization (F : Frozen.Points Ω) where
  context : Grpd.{u,u}
  x : Section (constant (Γ := context) C)
  y : Section (constant (Γ := context) C)
  z : Section (constant (Γ := context) C)
  context_eval : F.Γ.eval (Contextual.algebra M) ρ = .context context
  family_eval : F.A.eval (Contextual.algebra M) ρ = .family context (constant C)
  fiber_eval : F.B.eval (Contextual.algebra M) ρ =
    .family ((M).extend context (constant C)) (DerivedSemantics.Groupoid.genericFiber C B context)
  x_eval : F.x.eval (Contextual.algebra M) ρ = .term context (constant C) ⟨x⟩
  y_eval : F.y.eval (Contextual.algebra M) ρ = .term context (constant C) ⟨y⟩
  z_eval : F.z.eval (Contextual.algebra M) ρ = .term context (constant C) ⟨z⟩

namespace PointsRealization
variable {C B ρ} {F : Frozen.Points Ω} (R : PointsRealization C B ρ F)

def reindex {Δ σ : Contextual.Expression V} (hσ : Sub (Ω := Ω) Δ F.Γ σ)
    (H : Grpd.{u,u}) (s : H ⥤ R.context)
    (hΔ : Δ.eval (Contextual.algebra M) ρ = .context H)
    (hs : σ.eval (Contextual.algebra M) ρ = .substitution H R.context ⟨s⟩) :
    PointsRealization C B ρ (F.reindex hσ) where
  context := H
  x := R.x.reindex s
  y := R.y.reindex s
  z := R.z.reindex s
  context_eval := hΔ
  family_eval := subTy_eval M ρ F.A σ R.context H (constant C) ⟨s⟩ R.family_eval hs
  fiber_eval := by
    have hl := lift_eval M ρ Δ F.A σ R.context H (constant C) ⟨s⟩ hΔ R.family_eval hs
    exact subTy_eval M ρ F.B (Contextual.lift Δ F.A σ) _ _
      (DerivedSemantics.Groupoid.genericFiber C B R.context) _ R.fiber_eval hl
  x_eval := subTm_eval M ρ F.x σ R.context H (constant C) ⟨R.x⟩ ⟨s⟩ R.x_eval hs
  y_eval := subTm_eval M ρ F.y σ R.context H (constant C) ⟨R.y⟩ ⟨s⟩ R.y_eval hs
  z_eval := subTm_eval M ρ F.z σ R.context H (constant C) ⟨R.z⟩ ⟨s⟩ R.z_eval hs

def addY : PointsRealization C B ρ F.addY :=
  { R.reindex F.hx.family.weaken ((M).extend R.context (constant C))
      (SquareKit.Internal.PathTransport.GroupoidModel.weaken (constant C))
      (extend_eval M ρ F.Γ F.A R.context (constant C) R.context_eval R.family_eval)
      (weaken_eval M ρ F.Γ F.A R.context (constant C) R.context_eval R.family_eval) with
    y := «variable» (constant C)
    y_eval := generic_eval M ρ F.Γ F.A R.context (constant C) R.context_eval R.family_eval }

def addZ : PointsRealization C B ρ F.addZ :=
  { R.reindex F.hx.family.weaken ((M).extend R.context (constant C))
      (SquareKit.Internal.PathTransport.GroupoidModel.weaken (constant C))
      (extend_eval M ρ F.Γ F.A R.context (constant C) R.context_eval R.family_eval)
      (weaken_eval M ρ F.Γ F.A R.context (constant C) R.context_eval R.family_eval) with
    z := «variable» (constant C)
    z_eval := generic_eval M ρ F.Γ F.A R.context (constant C) R.context_eval R.family_eval }
end PointsRealization

structure OnePathRealization (F : Frozen.OnePath Ω) extends PointsRealization C B ρ F.toPoints where
  p : Section (identityFamily (constant C) x y)
  p_eval : F.p.eval (Contextual.algebra M) ρ = .term context (identityFamily (constant C) x y) ⟨p⟩

namespace OnePathRealization
variable {C B ρ} {F : Frozen.OnePath Ω} (R : OnePathRealization C B ρ F)
def reindex {Δ σ : Contextual.Expression V} (hσ : Sub (Ω := Ω) Δ F.Γ σ)
    (H : Grpd.{u,u}) (s : H ⥤ R.context)
    (hΔ : Δ.eval (Contextual.algebra M) ρ = .context H)
    (hs : σ.eval (Contextual.algebra M) ρ = .substitution H R.context ⟨s⟩) :
    OnePathRealization C B ρ (F.reindex hσ) where
  toPointsRealization := R.toPointsRealization.reindex hσ H s hΔ hs
  p := R.p.reindex s
  p_eval := subTm_eval M ρ F.p σ R.context H _ ⟨R.p⟩ ⟨s⟩ R.p_eval hs
end OnePathRealization

def PointsRealization.addP {F : Frozen.Points Ω} (R : PointsRealization C B ρ F) :
    OnePathRealization C B ρ F.addP := by
  let A := identityFamily (constant C) R.x R.y
  have hA := identity_eval M ρ F.A F.x F.y R.context (constant C) ⟨R.x⟩ ⟨R.y⟩
    R.family_eval R.x_eval R.y_eval
  exact {
    toPointsRealization := R.reindex F.hPath.weaken ((M).extend R.context A)
      (SquareKit.Internal.PathTransport.GroupoidModel.weaken A)
      (extend_eval M ρ F.Γ F.pathType R.context A R.context_eval hA)
      (weaken_eval M ρ F.Γ F.pathType R.context A R.context_eval hA)
    p := «variable» A
    p_eval := generic_eval M ρ F.Γ F.pathType R.context A R.context_eval hA }

structure ParallelRealization (F : Frozen.Parallel Ω) extends OnePathRealization C B ρ F.toOnePath where
  p' : Section (identityFamily (constant C) x y)
  p'_eval : F.p'.eval (Contextual.algebra M) ρ = .term context (identityFamily (constant C) x y) ⟨p'⟩

namespace ParallelRealization
variable {C B ρ} {F : Frozen.Parallel Ω} (R : ParallelRealization C B ρ F)
def reindex {Δ σ : Contextual.Expression V} (hσ : Sub (Ω := Ω) Δ F.Γ σ)
    (H : Grpd.{u,u}) (s : H ⥤ R.context)
    (hΔ : Δ.eval (Contextual.algebra M) ρ = .context H)
    (hs : σ.eval (Contextual.algebra M) ρ = .substitution H R.context ⟨s⟩) :
    ParallelRealization C B ρ (F.reindex hσ) where
  toOnePathRealization := R.toOnePathRealization.reindex hσ H s hΔ hs
  p' := R.p'.reindex s
  p'_eval := subTm_eval M ρ F.p' σ R.context H _ ⟨R.p'⟩ ⟨s⟩ R.p'_eval hs
end ParallelRealization

def OnePathRealization.addParallel {F : Frozen.OnePath Ω} (R : OnePathRealization C B ρ F) :
    ParallelRealization C B ρ F.addParallel := by
  let A := identityFamily (constant C) R.x R.y
  have hA := identity_eval M ρ F.A F.x F.y R.context (constant C) ⟨R.x⟩ ⟨R.y⟩
    R.family_eval R.x_eval R.y_eval
  exact {
    toOnePathRealization := R.reindex F.toPoints.hPath.weaken ((M).extend R.context A)
      (SquareKit.Internal.PathTransport.GroupoidModel.weaken A)
      (extend_eval M ρ F.Γ F.toPoints.pathType R.context A R.context_eval hA)
      (weaken_eval M ρ F.Γ F.toPoints.pathType R.context A R.context_eval hA)
    p' := «variable» A
    p'_eval := generic_eval M ρ F.Γ F.toPoints.pathType R.context A R.context_eval hA }

structure HomotopyRealization (F : Frozen.Homotopy Ω) extends ParallelRealization C B ρ F.toParallel where
  h : Section (identityFamily (identityFamily (constant C) x y) p p')
  h_eval : F.h.eval (Contextual.algebra M) ρ =
    .term context (identityFamily (identityFamily (constant C) x y) p p') ⟨h⟩

namespace HomotopyRealization
variable {C B ρ} {F : Frozen.Homotopy Ω} (R : HomotopyRealization C B ρ F)
def reindex {Δ σ : Contextual.Expression V} (hσ : Sub (Ω := Ω) Δ F.Γ σ)
    (H : Grpd.{u,u}) (s : H ⥤ R.context)
    (hΔ : Δ.eval (Contextual.algebra M) ρ = .context H)
    (hs : σ.eval (Contextual.algebra M) ρ = .substitution H R.context ⟨s⟩) :
    HomotopyRealization C B ρ (F.reindex hσ) where
  toParallelRealization := R.toParallelRealization.reindex hσ H s hΔ hs
  h := R.h.reindex s
  h_eval := subTm_eval M ρ F.h σ R.context H _ ⟨R.h⟩ ⟨s⟩ R.h_eval hs
end HomotopyRealization

def ParallelRealization.addH {F : Frozen.Parallel Ω} (R : ParallelRealization C B ρ F) :
    HomotopyRealization C B ρ F.addH := by
  let A := identityFamily (constant C) R.x R.y
  let H := identityFamily A R.p R.p'
  have hA := identity_eval M ρ F.A F.x F.y R.context (constant C) ⟨R.x⟩ ⟨R.y⟩
    R.family_eval R.x_eval R.y_eval
  have hH := identity_eval M ρ F.toPoints.pathType F.p F.p' R.context A ⟨R.p⟩ ⟨R.p'⟩ hA R.p_eval R.p'_eval
  exact {
    toParallelRealization := R.reindex F.hIdentity.weaken ((M).extend R.context H)
      (SquareKit.Internal.PathTransport.GroupoidModel.weaken H)
      (extend_eval M ρ F.Γ _ R.context H R.context_eval hH)
      (weaken_eval M ρ F.Γ _ R.context H R.context_eval hH)
    h := «variable» H
    h_eval := generic_eval M ρ F.Γ _ R.context H R.context_eval hH }

structure WithQRealization (F : Frozen.WithQ Ω) extends HomotopyRealization C B ρ F.toHomotopy where
  q : Section (identityFamily (constant C) y z)
  q_eval : F.q.eval (Contextual.algebra M) ρ = .term context (identityFamily (constant C) y z) ⟨q⟩

namespace WithQRealization
variable {C B ρ} {F : Frozen.WithQ Ω} (R : WithQRealization C B ρ F)
def reindex {Δ σ : Contextual.Expression V} (hσ : Sub (Ω := Ω) Δ F.Γ σ)
    (H : Grpd.{u,u}) (s : H ⥤ R.context)
    (hΔ : Δ.eval (Contextual.algebra M) ρ = .context H)
    (hs : σ.eval (Contextual.algebra M) ρ = .substitution H R.context ⟨s⟩) :
    WithQRealization C B ρ (F.reindex hσ) where
  toHomotopyRealization := R.toHomotopyRealization.reindex hσ H s hΔ hs
  q := R.q.reindex s
  q_eval := subTm_eval M ρ F.q σ R.context H _ ⟨R.q⟩ ⟨s⟩ R.q_eval hs
end WithQRealization

def HomotopyRealization.addQ {F : Frozen.Homotopy Ω} (R : HomotopyRealization C B ρ F) :
    WithQRealization C B ρ F.addQ := by
  let A := identityFamily (constant C) R.y R.z
  have hA := identity_eval M ρ F.A F.y F.z R.context (constant C) ⟨R.y⟩ ⟨R.z⟩
    R.family_eval R.y_eval R.z_eval
  exact {
    toHomotopyRealization := R.reindex F.hQ.weaken ((M).extend R.context A)
      (SquareKit.Internal.PathTransport.GroupoidModel.weaken A)
      (extend_eval M ρ F.Γ _ R.context A R.context_eval hA)
      (weaken_eval M ρ F.Γ _ R.context A R.context_eval hA)
    q := «variable» A
    q_eval := generic_eval M ρ F.Γ _ R.context A R.context_eval hA }

structure InputRealization (F : Frozen.Input Ω) extends WithQRealization C B ρ F.toWithQ where
  element : Section (primitiveFiber B x)
  element_eval : F.u.eval (Contextual.algebra M) ρ = .term context (primitiveFiber B x) ⟨element⟩

def WithQRealization.addU {F : Frozen.WithQ Ω} (R : WithQRealization C B ρ F) :
    InputRealization C B ρ F.addU := by
  let A := primitiveFiber B R.x
  have hs := sectionSub_eval M ρ F.Γ F.A F.x R.context (constant C) ⟨R.x⟩
    R.context_eval R.family_eval R.x_eval
  have hA := subTy_eval M ρ F.B _ _ R.context (DerivedSemantics.Groupoid.genericFiber C B R.context)
    _ R.fiber_eval hs
  exact {
    toWithQRealization := R.reindex F.hU.weaken ((M).extend R.context A)
      (SquareKit.Internal.PathTransport.GroupoidModel.weaken A)
      (extend_eval M ρ F.Γ _ R.context A R.context_eval hA)
      (weaken_eval M ρ F.Γ _ R.context A R.context_eval hA)
    element := «variable» A
    element_eval := generic_eval M ρ F.Γ _ R.context A R.context_eval hA }


namespace InputRealization
variable {C B ρ} {F : Frozen.Input Ω} (R : InputRealization C B ρ F)
def reindex {Δ σ : Contextual.Expression V} (hσ : Sub (Ω := Ω) Δ F.Γ σ)
    (H : Grpd.{u,u}) (s : H ⥤ R.context)
    (hΔ : Δ.eval (Contextual.algebra M) ρ = .context H)
    (hs : σ.eval (Contextual.algebra M) ρ = .substitution H R.context ⟨s⟩) :
    InputRealization C B ρ (F.reindex hσ) where
  toWithQRealization := R.toWithQRealization.reindex hσ H s hΔ hs
  element := R.element.reindex s
  element_eval := subTm_eval M ρ F.u σ R.context H _ ⟨R.element⟩ ⟨s⟩ R.element_eval hs

variable (hΩ : ∀ a ∈ Ω, a.eval (Contextual.algebra (Instance.fullModel C B)) ρ)

def selectedValue : Section (primitiveFiber B R.z) :=
  (transportValue M (constant C) (DerivedSemantics.Groupoid.genericFiber C B R.context)
    ⟨R.y⟩ ⟨R.z⟩ ⟨R.q⟩
    (transportValue M (constant C) (DerivedSemantics.Groupoid.genericFiber C B R.context)
      ⟨R.x⟩ ⟨R.y⟩ ⟨R.p⟩ ⟨R.element⟩)).down

include hΩ in
theorem value_eval : (F.parameters.value F.p).eval (Contextual.algebra M) ρ =
    .term R.context (primitiveFiber B R.z) ⟨R.selectedValue⟩ := by
  have e := Contextual.interpret (F.parameters.value_atPath F.hp) M ρ hΩ
  change (F.parameters.value F.p).eval (Contextual.algebra M) ρ = _ at e
  rw [e]
  have hp := transport_eval M ρ F.Γ F.A F.B F.x F.y F.p F.u R.context (constant C)
    (DerivedSemantics.Groupoid.genericFiber C B R.context) ⟨R.x⟩ ⟨R.y⟩ ⟨R.p⟩ ⟨R.element⟩
    R.context_eval R.family_eval R.fiber_eval R.x_eval R.y_eval R.p_eval R.element_eval
  exact transport_eval M ρ F.Γ F.A F.B F.y F.z F.q _ R.context (constant C)
    (DerivedSemantics.Groupoid.genericFiber C B R.context) ⟨R.y⟩ ⟨R.z⟩ ⟨R.q⟩ _
    R.context_eval R.family_eval R.fiber_eval R.y_eval R.z_eval R.q_eval hp

include hΩ in
/-- The observation is of the generated section selected in its first path. -/
theorem value_action (g : R.context) :
    Option.map (fun (t : (Instance.structuralModel C B).Section R.context (primitiveFiber B R.z)) => (t.down.obj g).as)
      (@Value.termAt (Instance.structuralModel C B) R.context (primitiveFiber B R.z)
        ((F.parameters.package F.hp).selectedValue.eval (Contextual.algebra M) ρ)) =
      some (B.map (R.q.obj g).as (B.map (R.p.obj g).as (R.element.obj g).as)) := by
  change Option.map _ (((F.parameters.value F.p).eval (Contextual.algebra M) ρ).termAt _ _) = _
  rw [R.value_eval hΩ]
  simp only [Value.termAt_term, Option.map_some]
  unfold selectedValue
  have e₁ := DerivedSemantics.Groupoid.transportValue_action C B R.x R.y R.p R.element g
  have e₂ := transport_action C B R.y R.z R.q
    (transportValue M (constant C) (DerivedSemantics.Groupoid.genericFiber C B R.context)
      ⟨R.x⟩ ⟨R.y⟩ ⟨R.p⟩ ⟨R.element⟩) g
  exact congrArg some (e₂.trans (congrArg (fun b => B.map (R.q.obj g).as b) e₁))

def selectedComposite : Section (primitiveFiber B R.z) :=
  (transportValue M (constant C) (DerivedSemantics.Groupoid.genericFiber C B R.context)
    ⟨R.x⟩ ⟨R.z⟩ (concatValue M (constant C) ⟨R.x⟩ ⟨R.y⟩ ⟨R.z⟩ ⟨R.p⟩ ⟨R.q⟩) ⟨R.element⟩).down

def selectedCertificate :=
  etaValue M (Γ := R.context) (constant C) (DerivedSemantics.Groupoid.genericFiber C B R.context)
    ⟨R.x⟩ ⟨R.y⟩ ⟨R.z⟩ ⟨R.p⟩ ⟨R.q⟩ ⟨R.element⟩

include hΩ in
theorem certificate_eval : (F.parameters.certificate F.p).eval (Contextual.algebra M) ρ =
    .term R.context _ R.selectedCertificate := by
  have e := Contextual.interpret (F.parameters.certificate_atPath F.hp) M ρ hΩ
  change (F.parameters.certificate F.p).eval (Contextual.algebra M) ρ = _ at e
  rw [e]
  exact eta_eval M ρ F.Γ F.A F.B F.x F.y F.z F.p F.q F.u R.context (constant C)
    (DerivedSemantics.Groupoid.genericFiber C B R.context) ⟨R.x⟩ ⟨R.y⟩ ⟨R.z⟩ ⟨R.p⟩ ⟨R.q⟩ ⟨R.element⟩
    R.context_eval R.family_eval R.fiber_eval R.x_eval R.y_eval R.z_eval R.p_eval R.q_eval R.element_eval

def varying : InputRealization C B ρ
    (F.reindex F.parameters.pathType_typed.weaken) := by
  let A := identityFamily (constant C) R.x R.y
  have hA := identity_eval M ρ F.A F.x F.y R.context (constant C) ⟨R.x⟩ ⟨R.y⟩
    R.family_eval R.x_eval R.y_eval
  exact R.reindex F.parameters.pathType_typed.weaken ((M).extend R.context A)
    (SquareKit.Internal.PathTransport.GroupoidModel.weaken A)
    (extend_eval M ρ F.Γ F.parameters.pathType R.context A R.context_eval hA)
    (weaken_eval M ρ F.Γ F.parameters.pathType R.context A R.context_eval hA)

def varyingPath : Section (identityFamily (constant C) R.varying.x R.varying.y) :=
  «variable» (identityFamily (constant C) R.x R.y)

def varyingValue := transportValue M (Γ := R.varying.context) (constant C)
  (DerivedSemantics.Groupoid.genericFiber C B R.varying.context)
  ⟨R.varying.y⟩ ⟨R.varying.z⟩ ⟨R.varying.q⟩
  (transportValue M (constant C) (DerivedSemantics.Groupoid.genericFiber C B R.varying.context)
    ⟨R.varying.x⟩ ⟨R.varying.y⟩ ⟨R.varyingPath⟩ ⟨R.varying.element⟩)

def varyingComposite := transportValue M (Γ := R.varying.context) (constant C)
  (DerivedSemantics.Groupoid.genericFiber C B R.varying.context)
  ⟨R.varying.x⟩ ⟨R.varying.z⟩
  (concatValue M (constant C) ⟨R.varying.x⟩ ⟨R.varying.y⟩ ⟨R.varying.z⟩
    ⟨R.varyingPath⟩ ⟨R.varying.q⟩) ⟨R.varying.element⟩

def certificateFamily : (M).Family R.varying.context :=
  (M).identity (primitiveFiber B R.varying.z) R.varyingValue R.varyingComposite

def certificateSection := etaValue M (Γ := R.varying.context) (constant C)
  (DerivedSemantics.Groupoid.genericFiber C B R.varying.context)
  ⟨R.varying.x⟩ ⟨R.varying.y⟩ ⟨R.varying.z⟩ ⟨R.varyingPath⟩ ⟨R.varying.q⟩ ⟨R.varying.element⟩

theorem certificateSection_eval : F.parameters.certificateSection.eval (Contextual.algebra M) ρ =
    .term R.varying.context R.certificateFamily R.certificateSection := by
  have hA := identity_eval M ρ F.A F.x F.y R.context (constant C) ⟨R.x⟩ ⟨R.y⟩
    R.family_eval R.x_eval R.y_eval
  have hp := generic_eval M ρ F.Γ F.parameters.pathType R.context
    (identityFamily (constant C) R.x R.y) R.context_eval hA
  exact eta_eval M ρ F.parameters.varying.Γ F.parameters.varying.A F.parameters.varying.B
    F.parameters.varying.x F.parameters.varying.y F.parameters.varying.z
    F.parameters.variablePath F.parameters.varying.q F.parameters.varying.u
    R.varying.context (constant C) (DerivedSemantics.Groupoid.genericFiber C B R.varying.context)
    ⟨R.varying.x⟩ ⟨R.varying.y⟩ ⟨R.varying.z⟩ ⟨R.varyingPath⟩ ⟨R.varying.q⟩ ⟨R.varying.element⟩
    R.varying.context_eval R.varying.family_eval R.varying.fiber_eval
    R.varying.x_eval R.varying.y_eval R.varying.z_eval hp R.varying.q_eval R.varying.element_eval

include hΩ in
theorem certificateFamily_eval : F.parameters.certificateFamily.eval (Contextual.algebra M) ρ =
    .family R.varying.context R.certificateFamily :=
  family_of_eval M ρ F.parameters.certificateSection_typed hΩ _ _ _ R.certificateSection_eval

def atPath := (M).toStructuralModel.sectionSub (identityFamily (constant C) R.x R.y) ⟨R.p⟩
def atParallelPath := (M).toStructuralModel.sectionSub (identityFamily (constant C) R.x R.y) ⟨R.p'⟩
def certificateAtPath := (M).subTm R.certificateSection R.atPath
def certificateAtParallelPath := (M).subTm R.certificateSection R.atParallelPath

def transportedCertificate := transportValue M (Γ := R.context)
  (identityFamily (constant C) R.x R.y) R.certificateFamily
  ⟨R.p⟩ ⟨R.p'⟩ ⟨R.h⟩ R.certificateAtPath

def dependentActionFamily := (M).identity ((M).subTy R.certificateFamily R.atParallelPath)
  R.transportedCertificate R.certificateAtParallelPath

theorem certificateAtPath_eval : (F.parameters.certificate F.p).eval (Contextual.algebra M) ρ =
    .term R.context ((M).subTy R.certificateFamily R.atPath) R.certificateAtPath := by
  have hA := identity_eval M ρ F.A F.x F.y R.context (constant C) ⟨R.x⟩ ⟨R.y⟩
    R.family_eval R.x_eval R.y_eval
  have hs := sectionSub_eval M ρ F.Γ F.parameters.pathType F.p R.context
    (identityFamily (constant C) R.x R.y) ⟨R.p⟩ R.context_eval hA R.p_eval
  exact subTm_eval M ρ F.parameters.certificateSection (F.parameters.atPath F.p) _ _
    R.certificateFamily R.certificateSection R.atPath R.certificateSection_eval hs

include hΩ in
theorem transportedCertificate_eval : (F.parameters.transportedCertificate F.p F.p' F.h).eval
    (Contextual.algebra M) ρ =
    .term R.context ((M).subTy R.certificateFamily R.atParallelPath) R.transportedCertificate := by
  have hA := identity_eval M ρ F.A F.x F.y R.context (constant C) ⟨R.x⟩ ⟨R.y⟩
    R.family_eval R.x_eval R.y_eval
  exact transport_eval M ρ F.Γ F.parameters.pathType F.parameters.certificateFamily F.p F.p' F.h
    (F.parameters.certificate F.p) R.context (identityFamily (constant C) R.x R.y) R.certificateFamily
    ⟨R.p⟩ ⟨R.p'⟩ ⟨R.h⟩ R.certificateAtPath R.context_eval hA
    (R.certificateFamily_eval hΩ) R.p_eval R.p'_eval R.h_eval R.certificateAtPath_eval

/-- The dependent action's domain is transport in the certificate family.
It is not replaced with the untransported certificate at the first path. -/
def dependentAction := apdValue M (Γ := R.context)
  (identityFamily (constant C) R.x R.y) R.certificateFamily
  ⟨R.p⟩ ⟨R.p'⟩ ⟨R.h⟩ R.certificateSection

include hΩ in
theorem dependentAction_eval : (F.parameters.dependentAction F.p F.p' F.h).eval (Contextual.algebra M) ρ =
    .term R.context R.dependentActionFamily R.dependentAction := by
  have hA := identity_eval M ρ F.A F.x F.y R.context (constant C) ⟨R.x⟩ ⟨R.y⟩
    R.family_eval R.x_eval R.y_eval
  exact apd_eval M ρ F.Γ F.parameters.pathType F.parameters.certificateFamily
    F.p F.p' F.h F.parameters.certificateSection R.context
    (identityFamily (constant C) R.x R.y) R.certificateFamily ⟨R.p⟩ ⟨R.p'⟩ ⟨R.h⟩
    R.certificateSection R.context_eval hA (R.certificateFamily_eval hΩ)
    R.p_eval R.p'_eval R.h_eval R.certificateSection_eval

include hΩ in
/-- The parsed source type agrees with the semantic type, with the transported
certificate as its first endpoint. -/
theorem dependentActionFamily_eval :
    (Contextual.identity (F.parameters.certificateType F.p')
      (F.parameters.transportedCertificate F.p F.p' F.h) (F.parameters.certificate F.p')).eval
      (Contextual.algebra M) ρ = .family R.context R.dependentActionFamily :=
  family_of_eval M ρ (F.parameters.dependentAction_typed F.hp F.hp' F.hh) hΩ
    R.context R.dependentActionFamily R.dependentAction (R.dependentAction_eval hΩ)

end InputRealization

def pointRealization (S : Frozen.Signature Ω) (G : Grpd.{u,u})
    (hΓ : S.Γ.eval (Contextual.algebra M) ρ = .context G)
    (hA : S.A.eval (Contextual.algebra M) ρ = .family G (constant C))
    (hB : S.B.eval (Contextual.algebra M) ρ = .family ((M).extend G (constant C))
      (DerivedSemantics.Groupoid.genericFiber C B G)) : PointsRealization C B ρ S.point := by
  have he := extend_eval M ρ S.Γ S.A G (constant C) hΓ hA
  have hw := weaken_eval M ρ S.Γ S.A G (constant C) hΓ hA
  have hv := generic_eval M ρ S.Γ S.A G (constant C) hΓ hA
  exact {
    context := (M).extend G (constant C)
    x := «variable» (constant C)
    y := «variable» (constant C)
    z := «variable» (constant C)
    context_eval := he
    family_eval := subTy_eval M ρ S.A _ G _ (constant C) _ hA hw
    fiber_eval := subTy_eval M ρ S.B _ _ _ _ _ hB (lift_eval M ρ _ S.A _ G _ (constant C) _ he hA hw)
    x_eval := hv
    y_eval := hv
    z_eval := hv }

end Realization


local notation "IM" => Instance.fullModel Integers translation
local notation "IS" => Instance.structuralModel Integers translation

def environment : Fin 2 → Value IS :=
  ![.family (IS).empty (constant Integers),
    .family ((IS).extend (IS).empty (constant Integers))
      (DerivedSemantics.Groupoid.genericFiber Integers translation (IS).empty)]

theorem empty_eval : Contextual.empty.eval (Contextual.algebra IM) environment = .context (IS).empty := rfl

theorem inputs : ∀ a ∈ premises, a.eval (Contextual.algebra IM) environment := by
  intro a ha
  simp only [premises, List.mem_cons, List.not_mem_nil, or_false] at ha
  rcases ha with rfl | rfl
  · exact ⟨(IS).empty, constant Integers, rfl, rfl⟩
  · exact ⟨(IS).extend (IS).empty (constant Integers),
      DerivedSemantics.Groupoid.genericFiber Integers translation (IS).empty,
      extend_eval IM environment Contextual.empty alpha (IS).empty (constant Integers) rfl rfl, rfl⟩

def pointData := pointRealization Integers translation environment signature (IS).empty rfl rfl rfl
def xyData := pointData.addY
def xyzData := xyData.addZ
def pData := xyzData.addP
def parallelData := pData.addParallel
def hData := parallelData.addH
def qData := hData.addQ
def realization : InputRealization Integers translation environment signature.input := qData.addU

/-- A point of the full generated context, including parallel first paths and
an actual second-identity witness. Here that witness is necessarily discrete. -/
def assignment (p q b : Int) : realization.context :=
  ⟨⟨⟨⟨⟨⟨⟨⟨Discrete.mk PUnit.unit, integerPoint⟩, integerPoint⟩, integerPoint⟩,
    Discrete.mk (Multiplicative.ofAdd p)⟩, Discrete.mk (Multiplicative.ofAdd p)⟩,
    Discrete.mk (𝟙 _)⟩, Discrete.mk (Multiplicative.ofAdd q)⟩, Discrete.mk b⟩

theorem first_loop_is_not_reflexivity :
    (realization.p.obj (assignment 1 2 0)).as ≠ 𝟙 integerPoint := by
  change Multiplicative.ofAdd (1 : Int) ≠ Multiplicative.ofAdd (0 : Int)
  decide

theorem replacement_is_reflexivity :
    (realization.p.obj (assignment 0 2 0)).as = 𝟙 integerPoint := rfl

/-- The concrete second identity is reflexivity, as required by this ordinary
groupoid instance. No nontrivial second identity is asserted. -/
theorem second_identity_is_reflexivity (p q b : Int) :
    (realization.h.obj (assignment p q b)).as = 𝟙 (realization.p.obj (assignment p q b)) := rfl

theorem generated_value (p q b : Int) :
    Option.map (fun (t : (IS).Section realization.context (primitiveFiber translation realization.z)) => (t.down.obj (assignment p q b)).as)
      (@Value.termAt IS realization.context (primitiveFiber translation realization.z)
        ((signature.input.parameters.package signature.input.hp).selectedValue.eval (Contextual.algebra IM) environment)) = some (q + (p + b)) :=
  realization.value_action inputs (assignment p q b)

example : Option.map (fun (t : (IS).Section realization.context (primitiveFiber translation realization.z)) => (t.down.obj (assignment 1 2 0)).as)
    (@Value.termAt IS realization.context (primitiveFiber translation realization.z)
      ((signature.input.parameters.package signature.input.hp).selectedValue.eval (Contextual.algebra IM) environment)) = some (3 : Int) := generated_value 1 2 0

/-- Replacing the first loop by reflexivity changes the generated value. -/
example : Option.map (fun (t : (IS).Section realization.context (primitiveFiber translation realization.z)) => (t.down.obj (assignment 0 2 0)).as)
    (@Value.termAt IS realization.context (primitiveFiber translation realization.z)
      ((signature.input.parameters.package signature.input.hp).selectedValue.eval (Contextual.algebra IM) environment)) = some (2 : Int) := generated_value 0 2 0


def tailUData : DisplayRealization IM environment signature.tailU qData.context := by
  have hs := sectionSub_eval IM environment signature.withQ.Γ signature.withQ.A signature.withQ.x
    qData.context (constant Integers) ⟨qData.x⟩ qData.context_eval qData.family_eval qData.x_eval
  have hA := subTy_eval IM environment signature.withQ.B _ _ qData.context
    (DerivedSemantics.Groupoid.genericFiber Integers translation qData.context) _ qData.fiber_eval hs
  exact .cons (M := IM) (ρ := environment) signature.withQ.hU (.nil signature.withQ.hU.extend) qData.context (primitiveFiber translation qData.x) hA
    (.nil (M := IM) (ρ := environment) signature.withQ.hU.extend realization.context)

def tailQData : DisplayRealization IM environment signature.tailQ hData.context :=
  .cons (M := IM) (ρ := environment) signature.withH.hQ signature.tailU hData.context (identityFamily (constant Integers) hData.y hData.z)
    (identity_eval IM environment signature.withH.A signature.withH.y signature.withH.z hData.context
      (constant Integers) ⟨hData.y⟩ ⟨hData.z⟩ hData.family_eval hData.y_eval hData.z_eval) tailUData

def tailHData : DisplayRealization IM environment signature.tailH parallelData.context :=
  .cons (M := IM) (ρ := environment) signature.withParallel.hIdentity signature.tailQ parallelData.context
    (identityFamily (identityFamily (constant Integers) parallelData.x parallelData.y) parallelData.p parallelData.p')
    (identity_eval IM environment signature.withParallel.toPoints.pathType signature.withParallel.p signature.withParallel.p'
      parallelData.context _ ⟨parallelData.p⟩ ⟨parallelData.p'⟩
      (identity_eval IM environment signature.withParallel.A signature.withParallel.x signature.withParallel.y
        parallelData.context (constant Integers) ⟨parallelData.x⟩ ⟨parallelData.y⟩
        parallelData.family_eval parallelData.x_eval parallelData.y_eval) parallelData.p_eval parallelData.p'_eval) tailQData

def tailParallelData : DisplayRealization IM environment signature.tailParallel pData.context :=
  .cons (M := IM) (ρ := environment) signature.withP.toPoints.hPath signature.tailH pData.context (identityFamily (constant Integers) pData.x pData.y)
    (identity_eval IM environment signature.withP.A signature.withP.x signature.withP.y pData.context
      (constant Integers) ⟨pData.x⟩ ⟨pData.y⟩ pData.family_eval pData.x_eval pData.y_eval) tailHData

def tailPData : DisplayRealization IM environment signature.tailP xyzData.context :=
  .cons (M := IM) (ρ := environment) signature.xyz.hPath signature.tailParallel xyzData.context (identityFamily (constant Integers) xyzData.x xyzData.y)
    (identity_eval IM environment signature.xyz.A signature.xyz.x signature.xyz.y xyzData.context
      (constant Integers) ⟨xyzData.x⟩ ⟨xyzData.y⟩ xyzData.family_eval xyzData.x_eval xyzData.y_eval) tailParallelData

def tailZData : DisplayRealization IM environment signature.tailZ xyData.context :=
  .cons (M := IM) (ρ := environment) signature.xy.hx.family signature.tailP xyData.context (constant Integers) xyData.family_eval tailPData

def duplicate : pointData.context ⥤ xyData.context :=
  SquareKit.Internal.PathTransport.GroupoidModel.pair (constant Integers) (𝟭 pointData.context) pointData.x

theorem duplicate_eval : signature.duplicate.eval (Contextual.algebra IM) environment =
    .substitution pointData.context xyData.context ⟨duplicate⟩ :=
  sectionSub_eval IM environment signature.point.Γ signature.point.A signature.point.x pointData.context
    (constant Integers) ⟨pointData.x⟩ pointData.context_eval pointData.family_eval pointData.x_eval

def sigmaData := tailZData.pullback signature.point.hx.family.context signature.duplicate_typed
  pointData.context ⟨duplicate⟩ pointData.context_eval duplicate_eval

def deltaRealization : InputRealization Integers translation environment signature.deltaInput :=
  realization.reindex signature.sigma_typed sigmaData.display.total sigmaData.map.down
    (sigmaData.display.total_eval pointData.context_eval) sigmaData.map_eval

def deltaAssignment (p q b : Int) : deltaRealization.context :=
  ⟨⟨⟨⟨⟨⟨⟨Discrete.mk PUnit.unit, integerPoint⟩, integerPoint⟩,
    Discrete.mk (Multiplicative.ofAdd p)⟩, Discrete.mk (Multiplicative.ofAdd p)⟩,
    Discrete.mk (𝟙 _)⟩, Discrete.mk (Multiplicative.ofAdd q)⟩, Discrete.mk b⟩

theorem sigma_assignment (p q b : Int) : sigmaData.map.down.obj (deltaAssignment p q b) = assignment p q b := rfl

def duplicateLift : Extend (constant (Γ := pointData.context) Integers) ⥤ xyzData.context :=
  SquareKit.Internal.PathTransport.GroupoidModel.pair (constant Integers)
    (SquareKit.Internal.PathTransport.GroupoidModel.weaken (constant Integers) ⋙ duplicate)
    («variable» (constant Integers))

def afterZData := tailPData.pullback
  (signature.xy.hx.family.substitute signature.duplicate_typed).extend
  (signature.duplicate_typed.lift signature.xy.hx.family)
  ((IS).extend pointData.context (constant Integers)) ⟨duplicateLift⟩
  (extend_eval IM environment signature.point.Γ signature.deltaZType pointData.context (constant Integers)
    pointData.context_eval (subTy_eval IM environment signature.xy.A signature.duplicate
      xyData.context pointData.context (constant Integers) ⟨duplicate⟩ xyData.family_eval duplicate_eval))
  (lift_eval IM environment signature.point.Γ signature.xy.A signature.duplicate xyData.context pointData.context
    (constant Integers) ⟨duplicate⟩ pointData.context_eval xyData.family_eval duplicate_eval)

def tauData := afterZData.display.pullback signature.point.hx.family.context signature.deltaX_as_z.section
  pointData.context ⟨duplicate⟩ pointData.context_eval
  (sectionSub_eval IM environment signature.point.Γ signature.deltaZType signature.point.x pointData.context
    (constant Integers) ⟨pointData.x⟩ pointData.context_eval
    (subTy_eval IM environment signature.xy.A signature.duplicate xyData.context pointData.context
      (constant Integers) ⟨duplicate⟩ xyData.family_eval duplicate_eval) pointData.x_eval)

def thetaRealization : InputRealization Integers translation environment signature.thetaInput :=
  deltaRealization.reindex signature.tau_typed tauData.display.total tauData.map.down
    (tauData.display.total_eval pointData.context_eval) tauData.map_eval

def thetaAssignment (p q b : Int) : thetaRealization.context :=
  ⟨⟨⟨⟨⟨⟨Discrete.mk PUnit.unit, integerPoint⟩,
    Discrete.mk (Multiplicative.ofAdd p)⟩, Discrete.mk (Multiplicative.ofAdd p)⟩,
    Discrete.mk (𝟙 _)⟩, Discrete.mk (Multiplicative.ofAdd q)⟩, Discrete.mk b⟩

theorem tau_assignment (p q b : Int) : tauData.map.down.obj (thetaAssignment p q b) = deltaAssignment p q b := rfl

/-- The same selected source package is pulled along both actual frozen maps. -/
theorem value_twice_eval :
    (Contextual.subTm (Contextual.subTm (signature.input.parameters.value signature.input.p) signature.sigma)
      signature.tau).eval (Contextual.algebra IM) environment =
    .term thetaRealization.context (primitiveFiber translation thetaRealization.z)
      ((IS).subTm ((IS).subTm ⟨realization.selectedValue⟩ sigmaData.map) tauData.map) := by
  have eσ := subTm_eval IM environment _ signature.sigma realization.context deltaRealization.context
    (primitiveFiber translation realization.z) ⟨realization.selectedValue⟩ sigmaData.map
    (realization.value_eval inputs) sigmaData.map_eval
  exact subTm_eval IM environment _ signature.tau deltaRealization.context thetaRealization.context
    _ _ tauData.map eσ tauData.map_eval

theorem generated_value_twice (p q b : Int) :
    Option.map (fun (t : (IS).Section thetaRealization.context (primitiveFiber translation thetaRealization.z)) =>
      (t.down.obj (thetaAssignment p q b)).as)
      (@Value.termAt IS thetaRealization.context (primitiveFiber translation thetaRealization.z)
        ((Contextual.subTm (Contextual.subTm (signature.input.parameters.value signature.input.p) signature.sigma)
          signature.tau).eval (Contextual.algebra IM) environment)) = some (q + (p + b)) := by
  rw [value_twice_eval]
  simp only [Value.termAt_term, Option.map_some]
  have h := generated_value p q b
  change Option.map _ (@Value.termAt IS realization.context (primitiveFiber translation realization.z)
    ((signature.input.parameters.value signature.input.p).eval (Contextual.algebra IM) environment)) = _ at h
  rw [realization.value_eval inputs] at h
  change some (realization.selectedValue.obj
    (sigmaData.map.down.obj (tauData.map.down.obj (thetaAssignment p q b)))).as = _
  rw [tau_assignment, sigma_assignment]
  simpa only [Value.termAt_term, Option.map_some] using h

example : Option.map (fun (t : (IS).Section thetaRealization.context (primitiveFiber translation thetaRealization.z)) =>
    (t.down.obj (thetaAssignment 1 2 0)).as)
    (@Value.termAt IS thetaRealization.context (primitiveFiber translation thetaRealization.z)
      ((Contextual.subTm (Contextual.subTm (signature.input.parameters.value signature.input.p) signature.sigma)
        signature.tau).eval (Contextual.algebra IM) environment)) = some (3 : Int) := generated_value_twice 1 2 0


/-- The selected certificate is preserved at each constructed assignment. -/
theorem certificate_sigma_eval :
    (Contextual.subTm (signature.input.parameters.certificate signature.input.p) signature.sigma).eval
      (Contextual.algebra IM) environment =
      .term deltaRealization.context _ deltaRealization.selectedCertificate :=
  (Contextual.interpret signature.certificate_sigma IM environment inputs).trans
    (deltaRealization.certificate_eval inputs)

theorem certificate_tau_eval :
    (Contextual.subTm (signature.deltaInput.parameters.certificate signature.deltaInput.p) signature.tau).eval
      (Contextual.algebra IM) environment =
      .term thetaRealization.context _ thetaRealization.selectedCertificate :=
  (Contextual.interpret signature.certificate_tau IM environment inputs).trans
    (thetaRealization.certificate_eval inputs)

theorem certificate_twice_eval :
    (Contextual.subTm (Contextual.subTm (signature.input.parameters.certificate signature.input.p) signature.sigma)
      signature.tau).eval (Contextual.algebra IM) environment =
      .term thetaRealization.context _ thetaRealization.selectedCertificate :=
  (Contextual.interpret signature.certificate_twice IM environment inputs).trans
    (thetaRealization.certificate_eval inputs)

/-- Each result is the action of the freshly constructed varying certificate
section, in its full transported-source type. -/
theorem dependentAction_sigma_eval :
    (Contextual.subTm (signature.input.parameters.dependentAction signature.input.p signature.input.p' signature.input.h)
      signature.sigma).eval (Contextual.algebra IM) environment =
      .term deltaRealization.context deltaRealization.dependentActionFamily deltaRealization.dependentAction :=
  (Contextual.interpret signature.dependentAction_sigma IM environment inputs).trans
    (deltaRealization.dependentAction_eval inputs)

theorem dependentAction_tau_eval :
    (Contextual.subTm (signature.deltaInput.parameters.dependentAction signature.deltaInput.p signature.deltaInput.p' signature.deltaInput.h)
      signature.tau).eval (Contextual.algebra IM) environment =
      .term thetaRealization.context thetaRealization.dependentActionFamily thetaRealization.dependentAction :=
  (Contextual.interpret signature.dependentAction_tau IM environment inputs).trans
    (thetaRealization.dependentAction_eval inputs)

theorem dependentAction_twice_eval :
    (Contextual.subTm (Contextual.subTm
      (signature.input.parameters.dependentAction signature.input.p signature.input.p' signature.input.h) signature.sigma)
      signature.tau).eval (Contextual.algebra IM) environment =
      .term thetaRealization.context thetaRealization.dependentActionFamily thetaRealization.dependentAction :=
  (Contextual.interpret signature.dependentAction_twice IM environment inputs).trans
    (thetaRealization.dependentAction_eval inputs)

theorem transportedCertificate_sigma_eval :
    (Contextual.subTm (signature.input.parameters.transportedCertificate signature.input.p signature.input.p' signature.input.h)
      signature.sigma).eval (Contextual.algebra IM) environment =
      .term deltaRealization.context _ deltaRealization.transportedCertificate :=
  (Contextual.interpret signature.transportedCertificate_sigma IM environment inputs).trans
    (deltaRealization.transportedCertificate_eval inputs)

theorem transportedCertificate_tau_eval :
    (Contextual.subTm (signature.deltaInput.parameters.transportedCertificate signature.deltaInput.p signature.deltaInput.p' signature.deltaInput.h)
      signature.tau).eval (Contextual.algebra IM) environment =
      .term thetaRealization.context _ thetaRealization.transportedCertificate :=
  (Contextual.interpret signature.transportedCertificate_tau IM environment inputs).trans
    (thetaRealization.transportedCertificate_eval inputs)

theorem transportedCertificate_twice_eval :
    (Contextual.subTm (Contextual.subTm
      (signature.input.parameters.transportedCertificate signature.input.p signature.input.p' signature.input.h) signature.sigma)
      signature.tau).eval (Contextual.algebra IM) environment =
      .term thetaRealization.context _ thetaRealization.transportedCertificate :=
  (Contextual.interpret signature.transportedCertificate_twice IM environment inputs).trans
    (thetaRealization.transportedCertificate_eval inputs)

/-- The twice-substituted dependent-action type retains its transported source. -/
theorem dependentActionType_twice_eval :
    (Contextual.subTy (Contextual.subTy
      (Contextual.identity (signature.input.parameters.certificateType signature.input.p')
        (signature.input.parameters.transportedCertificate signature.input.p signature.input.p' signature.input.h)
        (signature.input.parameters.certificate signature.input.p')) signature.sigma) signature.tau).eval
      (Contextual.algebra IM) environment =
      .family thetaRealization.context thetaRealization.dependentActionFamily :=
  family_of_eval IM environment
    (((signature.input.parameters.dependentAction_typed signature.input.hp signature.input.hp' signature.input.hh).substitute
      signature.sigma_typed).substitute signature.tau_typed) inputs
    thetaRealization.context thetaRealization.dependentActionFamily thetaRealization.dependentAction dependentAction_twice_eval

/-- Both substitutions retain the negative control as well as the value three. -/
example : Option.map (fun (t : (IS).Section thetaRealization.context (primitiveFiber translation thetaRealization.z)) =>
    (t.down.obj (thetaAssignment 0 2 0)).as)
    (@Value.termAt IS thetaRealization.context (primitiveFiber translation thetaRealization.z)
      ((Contextual.subTm (Contextual.subTm (signature.input.parameters.value signature.input.p) signature.sigma)
        signature.tau).eval (Contextual.algebra IM) environment)) = some (2 : Int) := generated_value_twice 0 2 0

end Examples.GuardedGroupoidMemo
