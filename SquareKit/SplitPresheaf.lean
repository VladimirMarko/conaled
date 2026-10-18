import SquareKit.ElementFamilies
import SquareKit.FamilyCoherence
import Mathlib.CategoryTheory.Limits.Types.Pullbacks
import Mathlib.CategoryTheory.Limits.FunctorCategory.Basic

/-! Experimental split families on sections of a type-valued functor.
These are semantic families and natural sections, not source syntax. -/
namespace SquareKit.SplitPresheaf
open CategoryTheory Limits ElementFamilies
universe u v w
variable {C : Type u} [Category.{v} C]
variable {F G H K : C ⥤ Type w}

abbrev Ty (F : C ⥤ Type w) := F.Elements ⥤ Type w
abbrev tySub (A : Ty F) (σ : G ⟶ F) : Ty G := σ.mapElements ⋙ A

@[simp] theorem tySub_id (A : Ty F) : tySub A (𝟙 F) = A := rfl
@[simp] theorem tySub_comp (A : Ty F) (σ : G ⟶ F) (τ : H ⟶ G) :
    tySub (tySub A σ) τ = tySub A (τ ≫ σ) := rfl

/-- A term supplies values compatible with every element restriction. -/
@[ext] structure Tm (A : Ty F) where
  val : (x : F.Elements) → A.obj x
  natural : ∀ {x y : F.Elements} (f : x ⟶ y), A.map f (val x) = val y

def tmSub {A : Ty F} (t : Tm A) (σ : G ⟶ F) : Tm (tySub A σ) where
  val x := t.val (σ.mapElements.obj x)
  natural f := t.natural (σ.mapElements.map f)

@[simp] theorem tmSub_id {A : Ty F} (t : Tm A) : tmSub t (𝟙 F) = t := rfl
@[simp] theorem tmSub_comp {A : Ty F} (t : Tm A) (σ : G ⟶ F) (τ : H ⟶ G) :
    tmSub (tmSub t σ) τ = tmSub t (τ ≫ σ) := rfl

def transport {A B : Ty F} (h : A = B) (t : Tm A) : Tm B := h ▸ t
@[simp] theorem transport_rfl {A : Ty F} (t : Tm A) : transport rfl t = t := rfl
theorem transport_trans {A B D : Ty F} (h : A = B) (k : B = D) (t : Tm A) :
    transport k (transport h t) = transport (h.trans k) t := by cases h; cases k; rfl

abbrev Ext (A : Ty F) := total F A
abbrev p (A : Ty F) : Ext A ⟶ F := display F A

/-- A dependent pairing into the actual total functor. -/
def pair (A : Ty F) (σ : G ⟶ F) (t : Tm (tySub A σ)) : G ⟶ Ext A where
  app U := ↾fun x => ⟨σ.app U x, t.val (G.elementsMk U x)⟩
  naturality {U V} f := by
    ext x
    symm
    apply total_ext F (NatTrans.naturality_apply σ f x).symm
    change A.map _ (A.map _ _) = _
    have he : along F f (σ.app U x) ≫ vertical F (NatTrans.naturality_apply σ f x).symm =
        σ.mapElements.map (along G f x) := by
      apply Functor.Elements.hom_ext
      simp [vertical]
    have hh := congrArg (fun k => A.map k (t.val (G.elementsMk U x))) he
    erw [A.map_comp] at hh
    exact hh.trans (t.natural (along G f x))

@[simp] theorem pair_p (A : Ty F) (σ : G ⟶ F) (t : Tm (tySub A σ)) : pair A σ t ≫ p A = σ := rfl

/-- Read the dependent value of a section of the total functor. -/
def q (A : Ty F) : Tm (tySub A (p A)) where
  val x := x.val.2
  natural {x y} f := by
    let g := (p A).mapElements.map f
    let ax : (fibers F (Over.mk (p A))).obj ((p A).mapElements.obj x) := ⟨x.val, rfl⟩
    let ay : (fibers F (Over.mk (p A))).obj ((p A).mapElements.obj y) := ⟨y.val, rfl⟩
    have he : (fibers F (Over.mk (p A))).map g ax = ay := Subtype.ext f.map_val
    have hn := NatTrans.naturality_apply (fiberTotalIso F A).hom g ax
    have hh := hn.symm.trans (congrArg ((fiberTotalIso F A).hom.app _) he)
    change A.map g (A.map (vertical F rfl) x.val.2) = A.map (vertical F rfl) y.val.2 at hh
    simp only [vertical_rfl, A.map_id] at hh
    exact hh


@[simp] theorem pair_q (A : Ty F) (σ : G ⟶ F) (t : Tm (tySub A σ)) :
    tmSub (q A) (pair A σ t) = t := rfl

theorem pair_eta (A : Ty F) (k : G ⟶ Ext A) : pair A (k ≫ p A) (tmSub (q A) k) = k := rfl

theorem pair_natural (A : Ty F) (σ : G ⟶ F) (t : Tm (tySub A σ)) (τ : H ⟶ G) :
    pair A (τ ≫ σ) (tmSub t τ) = τ ≫ pair A σ t := rfl

def lift (A : Ty F) (σ : G ⟶ F) : Ext (tySub A σ) ⟶ Ext A :=
  pair A (p (tySub A σ) ≫ σ) (q (tySub A σ))

@[simp] theorem lift_p (A : Ty F) (σ : G ⟶ F) : lift A σ ≫ p A = p (tySub A σ) ≫ σ := rfl
@[simp] theorem lift_id (A : Ty F) : lift A (𝟙 F) = 𝟙 (Ext A) := rfl
@[simp] theorem lift_comp (A : Ty F) (σ : G ⟶ F) (τ : H ⟶ G) :
    lift (tySub A σ) τ ≫ lift A σ = lift A (τ ≫ σ) := rfl

theorem tmSub_triple {A : Ty F} (t : Tm A) (σ : G ⟶ F) (τ : H ⟶ G) (υ : K ⟶ H) :
    tmSub (tmSub (tmSub t σ) τ) υ = tmSub t (υ ≫ (τ ≫ σ)) := rfl

/-- The split extension square is an actual presheaf pullback. -/
theorem extension_pullback (A : Ty F) (σ : G ⟶ F) :
    IsPullback (lift A σ) (p (tySub A σ)) (p A) σ := by
  apply IsPullback.of_isLimit (c := PullbackCone.mk (lift A σ) (p (tySub A σ)) rfl)
  apply evaluationJointlyReflectsLimits
  intro U
  refine (isLimitMapConePullbackConeEquiv _ _).symm ?_
  apply IsPullback.isLimit
  rw [Types.isPullback_iff]
  refine ⟨rfl, ?_, ?_⟩
  · rintro ⟨x,a⟩ ⟨y,b⟩ ⟨hv,hb⟩
    change x = y at hb
    cases hb
    have he : a = b := eq_of_heq (Sigma.mk.inj_iff.mp hv).2
    cases he
    rfl
  · rintro ⟨x,a⟩ y h
    change x = σ.app U y at h
    cases h
    exact ⟨⟨y,a⟩, rfl, rfl⟩

end SquareKit.SplitPresheaf
