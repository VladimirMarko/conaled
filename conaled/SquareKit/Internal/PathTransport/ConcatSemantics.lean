import SquareKit.Internal.PathTransport.Concatenation
import SquareKit.Internal.PathTransport.SourceSemantics

/-!
The first-path source J retains its second endpoint and path in a dependent
telescope. Its identity motive is discrete, so its reflexive branch determines
the resulting section. This identifies the actual source command with pointwise
composition, then evaluates its endpoint substitution and source derivation.
-/

noncomputable section
namespace SquareKit.Internal.PathTransport.GroupoidModel.Instance
open CategoryTheory Typed
universe u
variable (C : Type u) [Groupoid.{u} C] (B : C ⥤ Type u)
local notation "M" => structuralModel C B
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true

/-- Discrete motives let the generic elimination uniqueness theorem apply to
the concrete model's chosen root map, including all dependent tail entries. -/
theorem contextualJ_unique {Γ : (M).Context} {n} (A : (M).Family Γ) (x : (M).Section Γ A)
    (T : StructuralModel.Telescope M (StructuralModel.pathContext M A x) n)
    (D : (M).Family (StructuralModel.Telescope.total M T))
    [∀ g, IsDiscrete (D.obj g)]
    (d : (M).Section
      (StructuralModel.Telescope.total M
        (StructuralModel.Telescope.pullback M T (StructuralModel.rootSub M A x)))
      ((M).subTy D (StructuralModel.rootTail M A x T)))
    (s : Section D)
    (h : s.reindex (StructuralModel.rootTail M A x T).down = d.down) :
    (contextualJ C B A x T D d).down = s := by
  exact eliminateSection_unique (rootTailEquivalence C B A x.down T) D d.down s h
end SquareKit.Internal.PathTransport.GroupoidModel.Instance

noncomputable section
namespace SquareKit.Internal.PathTransport.GroupoidModel.ConcatSemantics
open CategoryTheory Typed Typed.Authoring
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
universe u
variable (C : Type u) [Groupoid.{u} C] (B : C ⥤ Type u)
local notation "M" => Instance.fullModel C B
variable {Γ : RawCtx} {γ : CtxCode.{u+1}}

/-- The generic first path, as a section over the actual based path context. -/
def pathWitness {G : Type u} [Category.{u} G] (x : Section (constant (Γ := G) C)) :
    Section (identityFamily (constant C)
      (x.reindex (PathComparison.retract (constant C) x)) (DerivedSemantics.endpoint x)) :=
  «variable» (PathComparison.PathFamily (constant C) x)

theorem baseReindex_eval {δ : CtxCode.{u+1}} (t : TmCode γ (baseCode γ)) (s : SubCode δ γ) :
    baseReindexCode t s M = ⟨(t M).down.reindex (s M).down⟩ :=
  eq_of_heq (castCode_eval _ _ M)

variable (hΓ : CtxDeriv Γ γ) (x : BasePoint Γ γ)

def projection :
    ↥(show Grpd.{u,u} from telTotal (ConcatFrame.tailCode hΓ x) M) ⥤
      PathComparison.PathCtx (constant C) (x.code M).down :=
  (projectionCode (ConcatFrame.tailCode hΓ x) M).down

theorem fixed_eval : (ConcatFrame.fixed hΓ x).code M =
    ⟨(x.code M).down.reindex
      (projection C B hΓ x ⋙ PathComparison.retract (constant C) (x.code M).down)⟩ := by
  unfold ConcatFrame.fixed
  rw [SourceSemantics.base_reindex_eval, SourceSemantics.base_reindex_eval]
  rfl

theorem y_eval : (ConcatFrame.yAtQ hΓ x).code M =
    ⟨(DerivedSemantics.endpoint (x.code M).down).reindex (projection C B hΓ x)⟩ := by
  rw [ConcatFrame.y_projection, baseReindex_eval, SourceSemantics.moving_eval]
  rfl

def firstPathRaw := (pathWitness C (x.code M).down).reindex (projection C B hΓ x)

theorem firstPath_type :
    identityFamily (constant C) ((ConcatFrame.fixed hΓ x).code M).down
      ((ConcatFrame.yAtQ hΓ x).code M).down =
    identityFamily (constant C)
      ((x.code M).down.reindex (projection C B hΓ x ⋙ PathComparison.retract (constant C) (x.code M).down))
      ((DerivedSemantics.endpoint (x.code M).down).reindex (projection C B hΓ x)) := by
  rw [fixed_eval, y_eval]

def firstPath : Section (identityFamily (constant C) ((ConcatFrame.fixed hΓ x).code M).down
    ((ConcatFrame.yAtQ hΓ x).code M).down) :=
  cast (congrArg Section (firstPath_type C B hΓ x).symm) (firstPathRaw C B hΓ x)

def canonicalConcat := DerivedSemantics.composePaths (constant C)
  ((ConcatFrame.fixed hΓ x).code M).down ((ConcatFrame.yAtQ hΓ x).code M).down
  ((ConcatFrame.zAtQ hΓ x).code M).down (firstPath C B hΓ x) ((ConcatFrame.q hΓ x).code M).down
theorem reindex_heq {G H : Type u} [Category.{u} G] [Category.{u} H]
    {A A' : G ⥤ Grpd.{u,u}} (h : A = A') {s : Section A} {t : Section A'}
    (hs : HEq s t) (F : H ⥤ G) : HEq (s.reindex F) (t.reindex F) := by
  cases h
  cases hs
  rfl

theorem composePaths_root {G : Type u} [Category.{u} G]
    (a b c : Section (constant (Γ := G) C)) (h : a = b)
    (p : Section (identityFamily (constant C) a b))
    (hp : HEq p (reflexivitySection (constant C) a))
    (q : Section (identityFamily (constant C) b c)) :
    HEq (DerivedSemantics.composePaths (constant C) a b c p q) q := by
  cases h
  cases hp
  exact heq_of_eq (DerivedSemantics.composePaths_reflexive_left _ _ _ _)

def rootFunctor := (rootTailCode (baseCode γ) x.code (ConcatFrame.tailCode hΓ x) M).down

theorem root_projection : rootFunctor C B hΓ x ⋙ projection C B hΓ x =
    (projectionCode (telPullback (ConcatFrame.tailCode hΓ x) (rootCode (baseCode γ) x.code)) M).down ⋙
      PathComparison.reflexive (constant C) (x.code M).down := by
  have h := congrArg (fun s => (s M).down)
    (projectionLift_code (ConcatFrame.tailCode hΓ x) (rootCode (baseCode γ) x.code))
  exact h
theorem pathWitness_root {G H : Type u} [Category.{u} G] [Category.{u} H]
    (a : Section (constant (Γ := G) C))
    (F : H ⥤ PathComparison.PathCtx (constant C) a) (R : H ⥤ G)
    (h : F = R ⋙ PathComparison.reflexive (constant C) a) :
    HEq ((pathWitness C a).reindex F)
      (reflexivitySection (constant C) (a.reindex (F ⋙ PathComparison.retract (constant C) a))) := by
  subst F
  rfl

theorem firstPath_root : HEq ((firstPath C B hΓ x).reindex (rootFunctor C B hΓ x))
    (reflexivitySection (constant C)
      (((ConcatFrame.fixed hΓ x).code M).down.reindex (rootFunctor C B hΓ x))) := by
  have hh := reindex_heq (firstPath_type C B hΓ x)
    (cast_heq (congrArg Section (firstPath_type C B hΓ x).symm) (firstPathRaw C B hΓ x))
    (rootFunctor C B hΓ x)
  apply hh.trans
  rw [fixed_eval]
  unfold firstPathRaw
  simp only [Section.reindex_comp]
  exact pathWitness_root C _ _ _ (root_projection C B hΓ x)
theorem down_heq {α β : Type u} (h : α = β) {s : ULift.{u+1} α} {t : ULift.{u+1} β}
    (hs : HEq s t) : HEq s.down t.down := by
  cases h
  cases hs
  rfl

theorem canonicalConcat_root :
    (canonicalConcat C B hΓ x).reindex (rootFunctor C B hΓ x) =
      ((ConcatFrame.command hΓ x).motive.branchCode M).down := by
  have hy := congrArg (fun t => t M) (ConcatFrame.y_root hΓ x)
  simp only [baseReindex_eval] at hy
  have hy' := congrArg ULift.down hy
  have hc := composePaths_root C
    (((ConcatFrame.fixed hΓ x).code M).down.reindex (rootFunctor C B hΓ x))
    (((ConcatFrame.yAtQ hΓ x).code M).down.reindex (rootFunctor C B hΓ x))
    (((ConcatFrame.zAtQ hΓ x).code M).down.reindex (rootFunctor C B hΓ x))
    hy'.symm _ (firstPath_root C B hΓ x)
    (((ConcatFrame.q hΓ x).code M).down.reindex (rootFunctor C B hΓ x))
  have hb := castCode_eval (ConcatFrame.branch_type hΓ x)
    (subTmCode (ConcatFrame.q hΓ x).code
      (rootTailCode (baseCode γ) x.code (ConcatFrame.tailCode hΓ x))) M
  have hb' : HEq ((ConcatFrame.command hΓ x).motive.branchCode M).down
      (((ConcatFrame.q hΓ x).code M).down.reindex (rootFunctor C B hΓ x)) := by
    exact down_heq (congrArg Section (congrArg (fun A => A M) (ConcatFrame.branch_type hΓ x)).symm) hb
  exact eq_of_heq (hc.trans hb'.symm)

def concatJCode := jCode (baseCode γ) x.code (ConcatFrame.tailCode hΓ x)
  (ConcatFrame.command hΓ x).motive.code (ConcatFrame.command hΓ x).motive.branchCode

/-- The actual first-path J command agrees with canonical composition over its tail. -/
theorem concatJ_eval : (concatJCode hΓ x M).down = canonicalConcat C B hΓ x := by
  exact Instance.contextualJ_unique C B (baseCode γ M) (x.code M)
    (ConcatFrame.tailCode hΓ x M)
    (identityFamily (constant C) ((ConcatFrame.fixed hΓ x).code M).down
      ((ConcatFrame.zAtQ hΓ x).code M).down)
    ((ConcatFrame.command hΓ x).motive.branchCode M)
    (canonicalConcat C B hΓ x) (canonicalConcat_root C B hΓ x)

theorem section_hext {G : Type u} [Category.{u} G] {A A' : G ⥤ Grpd.{u,u}}
    [∀ g, IsDiscrete (A.obj g)] (h : A = A') {s : Section A} {t : Section A'}
    (ho : ∀ g, HEq (s.obj g) (t.obj g)) : HEq s t := by
  cases h
  exact heq_of_eq (Section.ext_discrete fun g => eq_of_heq (ho g))

theorem composePaths_congr {G : Type u} [Category.{u} G]
    {a b c a' b' c' : Section (constant (Γ := G) C)}
    (ha : a = a') (hb : b = b') (hc : c = c')
    {p : Section (identityFamily (constant C) a b)} {p' : Section (identityFamily (constant C) a' b')}
    {q : Section (identityFamily (constant C) b c)} {q' : Section (identityFamily (constant C) b' c')}
    (hp : HEq p p') (hq : HEq q q') :
    HEq (DerivedSemantics.composePaths (constant C) a b c p q)
      (DerivedSemantics.composePaths (constant C) a' b' c' p' q') := by
  cases ha; cases hb; cases hc; cases hp; cases hq; rfl

theorem section_obj_heq {G : Type u} [Category.{u} G] {A A' : G ⥤ Grpd.{u,u}}
    (h : A = A') {s : Section A} {t : Section A'} (hs : HEq s t) (g : G) :
    HEq (s.obj g) (t.obj g) := by
  cases h; cases hs; rfl

theorem fiber_heq {G : Type u} [Category.{u} G] {A : G ⥤ Cat.{u,u}}
    {a b : Grothendieck A} (h : a = b) : HEq a.fiber b.fiber := by
  cases h; rfl

variable {y z : BasePoint Γ γ} (p : Path x y) (q : Path y z)
def endpointFunctor := (substitutionCode (ConcatApplication.endpoint hΓ x y z p q) M).down

theorem firstPath_at : HEq ((firstPath C B hΓ x).reindex (endpointFunctor C B hΓ x p q))
    (p.code M).down := by
  have ha := congrArg (fun t => t M) (ConcatApplication.fixed_at hΓ x y z p q)
  have hb := congrArg (fun t => t M) (ConcatApplication.y_at hΓ x y z p q)
  simp only [baseReindex_eval] at ha hb
  have haf := congrArg ULift.down ha
  have hbf := congrArg ULift.down hb
  have hf : endpointFunctor C B hΓ x p q ⋙
      identityFamily (constant C) ((ConcatFrame.fixed hΓ x).code M).down
        ((ConcatFrame.yAtQ hΓ x).code M).down =
      identityFamily (constant C) (x.code M).down (y.code M).down := by
    change identityFamily (constant C)
      (((ConcatFrame.fixed hΓ x).code M).down.reindex (endpointFunctor C B hΓ x p q))
      (((ConcatFrame.yAtQ hΓ x).code M).down.reindex (endpointFunctor C B hΓ x p q)) = _
    exact congrArg₂ (identityFamily (constant (Γ := ↥(show Grpd.{u,u} from γ M)) C)) haf hbf
  apply section_hext hf
  intro g
  have hh := reindex_heq (firstPath_type C B hΓ x)
    (cast_heq (congrArg Section (firstPath_type C B hΓ x).symm) (firstPathRaw C B hΓ x))
    (endpointFunctor C B hΓ x p q)
  have ho := section_obj_heq (congrArg (endpointFunctor C B hΓ x p q ⋙ ·)
    (firstPath_type C B hΓ x)) hh g
  apply ho.trans
  have ht := congrArg (fun s => (s M).down) (ConcatApplication.tail_endpoint hΓ x y z p q)
  have hp := (congrArg (fun F => F.obj g) ht).trans (SourceSemantics.endpoint_obj C B x y p g)
  exact fiber_heq hp

theorem canonicalConcat_at :
    HEq ((canonicalConcat C B hΓ x).reindex (endpointFunctor C B hΓ x p q))
      (DerivedSemantics.composePaths (constant C) (x.code M).down (y.code M).down (z.code M).down
        (p.code M).down (q.code M).down) := by
  have ha := congrArg (fun t => t M) (ConcatApplication.fixed_at hΓ x y z p q)
  have hb := congrArg (fun t => t M) (ConcatApplication.y_at hΓ x y z p q)
  have hc := congrArg (fun t => t M) (ConcatApplication.z_at hΓ x y z p q)
  simp only [baseReindex_eval] at ha hb hc
  have haf := congrArg ULift.down ha
  have hbf := congrArg ULift.down hb
  have hcf := congrArg ULift.down hc
  have hqf : endpointFunctor C B hΓ x p q ⋙
      identityFamily (constant C) ((ConcatFrame.yAtQ hΓ x).code M).down
        ((ConcatFrame.zAtQ hΓ x).code M).down =
      identityFamily (constant C) (y.code M).down (z.code M).down := by
    change identityFamily (constant C)
      (((ConcatFrame.yAtQ hΓ x).code M).down.reindex (endpointFunctor C B hΓ x p q))
      (((ConcatFrame.zAtQ hΓ x).code M).down.reindex (endpointFunctor C B hΓ x p q)) = _
    exact congrArg₂ (identityFamily (constant (Γ := ↥(show Grpd.{u,u} from γ M)) C)) hbf hcf
  have hq := down_heq (congrArg Section hqf) (ConcatApplication.q_at hΓ x y z p q M)
  exact composePaths_congr C haf hbf hcf (firstPath_at C B hΓ x p q) hq

theorem concat_code : (concat hΓ p q).code =
    castCode (ConcatApplication.motive_at hΓ x y z p q)
      (subTmCode (concatJCode hΓ x) (substitutionCode (ConcatApplication.endpoint hΓ x y z p q))) := rfl

theorem subTmCode_eval {δ : CtxCode.{u+1}} {a : TyCode γ} (t : TmCode γ a) (s : SubCode δ γ) :
    (subTmCode t s M).down = (t M).down.reindex (s M).down := rfl

/-- Source concatenation evaluates to composition of the interpreted path sections. -/
theorem concat_section : ((concat hΓ p q).code M).down =
    DerivedSemantics.composePaths (constant C) (x.code M).down (y.code M).down (z.code M).down
      (p.code M).down (q.code M).down := by
  rw [concat_code]
  have hraw := castCode_eval (ConcatApplication.motive_at hΓ x y z p q)
    (subTmCode (concatJCode hΓ x) (substitutionCode (ConcatApplication.endpoint hΓ x y z p q))) M
  have hm := congrArg (fun A => A M) (ConcatApplication.motive_at hΓ x y z p q)
  have hd := down_heq (congrArg Section hm.symm) hraw
  have he : (subTmCode (concatJCode hΓ x)
      (substitutionCode (ConcatApplication.endpoint hΓ x y z p q)) M).down =
      (canonicalConcat C B hΓ x).reindex (endpointFunctor C B hΓ x p q) := by
    rw [subTmCode_eval, concatJ_eval]
    rfl
  have ht := hd.trans (heq_of_eq he)
  exact eq_of_heq (ht.trans (canonicalConcat_at C B hΓ x p q))

theorem concat_obj (g : ↥(show Grpd.{u,u} from γ M)) :
    (((concat hΓ p q).code M).down.obj g).as =
      ((p.code M).down.obj g).as ≫ ((q.code M).down.obj g).as := by
  rw [concat_section]
  rfl

/-- The derivation interpreter gives the same composite at each context object. -/
theorem interpret_concat_obj (g : ↥(show Grpd.{u,u} from γ M)) :
    ((interpretTm M (concat hΓ p q).deriv).down.obj g).as =
      ((interpretTm M p.deriv).down.obj g).as ≫ ((interpretTm M q.deriv).down.obj g).as := by
  rw [interpretTm_agrees, interpretTm_agrees, interpretTm_agrees]
  exact concat_obj C B hΓ x p q g

end SquareKit.Internal.PathTransport.GroupoidModel.ConcatSemantics
