import SquareKit.SplitSheafDescent
import SquareKit.SheafBaseChange
import SquareKit.SheafCover
import Mathlib.CategoryTheory.Sites.RegularEpi

/-! Descent quotients, their universal property and pullback stability. -/
noncomputable section
set_option autoImplicit false
set_option warningAsError true
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
namespace SquareKit.SplitSheafDescent.Quotient
open CategoryTheory Opposite SquareKit SquareKit.SplitSheafDescent
open SquareKit.SplitFunctionDiagram
universe u v
variable {C : Type u} [Category.{v} C] {J : GrothendieckTopology C}
variable {X : Sheaf J (Type (max u v))} {A : SplitSheaf.Ty X}
  {P : SplitSheaf.Ty (SplitSheaf.extension A)} (d : Datum A P)

def quotientMap : SplitSheaf.extension P ⟶ SplitSheaf.extension (family d) :=
  SplitSheaf.totalMap (evaluationIso d).inv ≫ SplitSheaf.lift (family d) (SplitSheaf.p A)

theorem quotientMap_apply (x : X.obj.Elements) (a : A.family.obj x)
    (p : P.family.obj (point A x a)) :
    (quotientMap d).hom.app x.obj ⟨⟨x.val,a⟩,p⟩ =
      ⟨x.val,(evaluationEquiv d x a).symm p⟩ := rfl

theorem evaluation_transport (x : X.obj.Elements) (a b : A.family.obj x)
    (t : (family d).family.obj x) :
    d.transport x a b (evaluationEquiv d x a t) = evaluationEquiv d x b t :=
  t.property.evaluate a b

theorem quotientMap_kernel (x : X.obj.Elements) (a b : A.family.obj x)
    (p : P.family.obj (point A x a)) (q : P.family.obj (point A x b)) :
    (quotientMap d).hom.app x.obj ⟨⟨x.val,a⟩,p⟩ =
      (quotientMap d).hom.app x.obj ⟨⟨x.val,b⟩,q⟩ ↔ d.transport x a b p = q := by
  rw [quotientMap_apply, quotientMap_apply]
  constructor
  · intro h
    have e : (evaluationEquiv d x a).symm p = (evaluationEquiv d x b).symm q :=
      eq_of_heq (Sigma.mk.inj_iff.mp h).2
    have hh := evaluation_transport d x a b ((evaluationEquiv d x a).symm p)
    rw [Equiv.apply_symm_apply, e, Equiv.apply_symm_apply] at hh
    exact hh
  · intro h
    apply congrArg (Sigma.mk x.val)
    apply (evaluationEquiv d x b).injective
    rw [Equiv.apply_symm_apply, ← evaluation_transport, Equiv.apply_symm_apply, h]

instance quotientMap_isLocallySurjective
    [Presheaf.IsLocallySurjective J (SplitSheaf.p A).hom] :
    Presheaf.IsLocallySurjective J (quotientMap d).hom where
  imageSieve_mem {U} t := by
    rcases t with ⟨x,t⟩
    apply J.superset_covering _ (Presheaf.imageSieve_mem J (SplitSheaf.p A).hom x)
    rintro V f ⟨⟨y,a⟩,hy⟩
    change y = X.obj.map f.op x at hy
    subst y
    let z := X.obj.elementsMk (op V) (X.obj.map f.op x)
    let s := (family d).family.map (ElementFamilies.along X.obj f.op x) t
    refine ⟨⟨⟨z.val,a⟩, evaluationEquiv d z a s⟩, ?_⟩
    change (⟨z.val,(evaluationEquiv d z a).symm (evaluationEquiv d z a s)⟩ :
      (SplitSheaf.extension (family d)).obj.obj (op V)) = ⟨z.val,s⟩
    rw [Equiv.symm_apply_apply]


variable [Presheaf.IsLocallySurjective J (SplitSheaf.p A).hom]

instance quotientMap_effectiveEpi : EffectiveEpi (quotientMap d) := by
  have : Epi (quotientMap d) := inferInstance
  have := IsRegularEpiCategory.regularEpiOfEpi (quotientMap d)
  infer_instance

def Balanced {Y : Sheaf J (Type (max u v))} (e : SplitSheaf.extension P ⟶ Y) : Prop :=
  ∀ (x : X.obj.Elements) (a b : A.family.obj x) (p : P.family.obj (point A x a)),
    e.hom.app x.obj ⟨⟨x.val,b⟩,d.transport x a b p⟩ =
      e.hom.app x.obj ⟨⟨x.val,a⟩,p⟩

omit [Presheaf.IsLocallySurjective J (SplitSheaf.p A).hom] in
theorem balanced_coequalizes {Y : Sheaf J (Type (max u v))}
    (e : SplitSheaf.extension P ⟶ Y) (he : Balanced d e)
    {Z : Sheaf J (Type (max u v))} (g h : Z ⟶ SplitSheaf.extension P)
    (gh : g ≫ quotientMap d = h ≫ quotientMap d) : g ≫ e = h ≫ e := by
  apply Sheaf.hom_ext
  ext U z
  have hz := congrArg (fun k : Z ⟶ SplitSheaf.extension (family d) => k.hom.app U z) gh
  change (quotientMap d).hom.app U (g.hom.app U z) =
    (quotientMap d).hom.app U (h.hom.app U z) at hz
  change e.hom.app U (g.hom.app U z) = e.hom.app U (h.hom.app U z)
  generalize hg : g.hom.app U z = gp at hz ⊢
  generalize hh : h.hom.app U z = hp at hz ⊢
  obtain ⟨⟨x,a⟩,p⟩ := gp
  obtain ⟨⟨y,b⟩,q⟩ := hp
  have xy : x = y := congrArg Sigma.fst hz
  subst y
  have hpq := (quotientMap_kernel d (X.obj.elementsMk U x) a b p q).mp hz
  rw [← hpq]
  exact (he (X.obj.elementsMk U x) a b p).symm

def balancedDesc {Y : Sheaf J (Type (max u v))}
    (e : SplitSheaf.extension P ⟶ Y) (he : Balanced d e) :
    SplitSheaf.extension (family d) ⟶ Y :=
  EffectiveEpi.desc (quotientMap d) e (balanced_coequalizes d e he)

theorem balancedDesc_fac {Y : Sheaf J (Type (max u v))}
    (e : SplitSheaf.extension P ⟶ Y) (he : Balanced d e) :
    quotientMap d ≫ balancedDesc d e he = e :=
  EffectiveEpi.fac _ _ _

theorem balancedDesc_unique {Y : Sheaf J (Type (max u v))}
    (e : SplitSheaf.extension P ⟶ Y) (he : Balanced d e)
    (f : SplitSheaf.extension (family d) ⟶ Y) (hf : quotientMap d ≫ f = e) :
    f = balancedDesc d e he :=
  EffectiveEpi.uniq _ _ _ _ hf


omit [Presheaf.IsLocallySurjective J (SplitSheaf.p A).hom] in
theorem quotientMap_balanced {Y : Sheaf J (Type (max u v))}
    (f : SplitSheaf.extension (family d) ⟶ Y) : Balanced d (quotientMap d ≫ f) := by
  intro x a b p
  change f.hom.app x.obj ((quotientMap d).hom.app x.obj ⟨⟨x.val,b⟩,d.transport x a b p⟩) =
    f.hom.app x.obj ((quotientMap d).hom.app x.obj ⟨⟨x.val,a⟩,p⟩)
  exact congrArg (f.hom.app x.obj) ((quotientMap_kernel d x a b p _).mpr rfl).symm

def quotientHomEquiv (Y : Sheaf J (Type (max u v))) :
    (SplitSheaf.extension (family d) ⟶ Y) ≃
      {e : SplitSheaf.extension P ⟶ Y // Balanced d e} where
  toFun f := ⟨quotientMap d ≫ f, quotientMap_balanced d f⟩
  invFun e := balancedDesc d e.val e.property
  left_inv f := (balancedDesc_unique d _ (quotientMap_balanced d f) f rfl).symm
  right_inv e := Subtype.ext (balancedDesc_fac d e.val e.property)

end SquareKit.SplitSheafDescent.Quotient

namespace SquareKit.SplitSheafDescent.QuotientStability
open CategoryTheory Opposite Limits SquareKit
universe u v
variable {C : Type u} [Category.{v} C] {J : GrothendieckTopology C}
variable {S T S' T' : Sheaf J (Type (max u v))}
variable {a : S' ⟶ S} {b : S' ⟶ T'} {q : S ⟶ T} {f : T' ⟶ T}

theorem pullback_isLocallySurjective (h : IsPullback a b q f)
    [Presheaf.IsLocallySurjective J q.hom] : Presheaf.IsLocallySurjective J b.hom where
  imageSieve_mem {U} t := by
    apply J.superset_covering _ (Presheaf.imageSieve_mem J q.hom (f.hom.app (op U) t))
    rintro V k ⟨s, hs⟩
    have eqn : q.hom.app (op V) s = f.hom.app (op V) (T'.obj.map k.op t) :=
      hs.trans (NatTrans.naturality_apply f.hom k.op t).symm
    obtain ⟨s', _, hb⟩ := Types.exists_of_isPullback
      (SheafImage.sections_isPullback h (op V)) s (T'.obj.map k.op t) eqn
    exact ⟨s', hb⟩

theorem pullback_effectiveEpi (h : IsPullback a b q f)
    [Presheaf.IsLocallySurjective J q.hom] : EffectiveEpi b := by
  have := pullback_isLocallySurjective h
  have : Epi b := inferInstance
  have := IsRegularEpiCategory.regularEpiOfEpi b
  infer_instance

end SquareKit.SplitSheafDescent.QuotientStability
