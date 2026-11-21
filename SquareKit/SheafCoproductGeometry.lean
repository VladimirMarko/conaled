import SquareKit.SheafCoproductLocal
import Mathlib.CategoryTheory.Limits.Types.Coproducts
import Mathlib.CategoryTheory.Limits.Types.Pullbacks
import Mathlib.CategoryTheory.Sites.LeftExact

/-! Arbitrary sheaf coproducts are van Kampen colimits. -/
noncomputable section
namespace SquareKit.SheafCoproductGeometry
open CategoryTheory CategoryTheory.Limits
universe u v w

/-- Coproducts of sets, with no finiteness assumption on the index, are van Kampen. -/
theorem types_isVanKampen {I : Type w} {F : Discrete I ⥤ Type w}
    (c : Cocone F) (hc : IsColimit c) : IsVanKampenColimit c := by
  let X : I → Type w := fun i => F.obj ⟨i⟩
  have hF : F = Discrete.functor X := by
    apply Functor.hext
    · rintro ⟨i⟩; rfl
    · rintro ⟨i⟩ ⟨j⟩ f
      obtain rfl := Discrete.eq_of_hom f
      have : f = 𝟙 _ := Subsingleton.elim _ _
      subst f
      simp [X]
  clear_value X
  subst F
  intro F' c' α f e _
  let Y : I → Type w := fun i => F'.obj ⟨i⟩
  have hF' : F' = Discrete.functor Y := by
    apply Functor.hext
    · rintro ⟨i⟩; rfl
    · rintro ⟨i⟩ ⟨j⟩ g
      obtain rfl := Discrete.eq_of_hom g
      have : g = 𝟙 _ := Subsingleton.elim _ _
      subst g
      simp [Y]
  clear_value Y
  subst F'
  have he (i : I) (y : Y i) : f (Cofan.inj c' i y) = Cofan.inj c i (α.app ⟨i⟩ y) :=
    (ConcreteCategory.congr_hom (NatTrans.congr_app e ⟨i⟩) y).symm
  constructor
  · rintro ⟨hc'⟩ ⟨i⟩
    apply (Types.isPullback_iff _ _ _ _).mpr
    refine ⟨(NatTrans.congr_app e ⟨i⟩).symm, ?_, ?_⟩
    · intro x y h
      exact Cofan.inj_injective_of_isColimit hc' i h.1
    · intro y x h
      obtain ⟨j, z, rfl⟩ := Cofan.inj_jointly_surjective_of_isColimit hc' y
      have hx : Cofan.inj c j (α.app ⟨j⟩ z) = Cofan.inj c i x := (he j z).symm.trans h
      have hij := Cofan.eq_of_inj_apply_eq_of_isColimit hc _ _ hx
      subst j
      exact ⟨z, rfl, Cofan.inj_injective_of_isColimit hc i hx⟩
  · intro hp
    apply (Cofan.nonempty_isColimit_iff_bijective_fromSigma c').mpr
    constructor
    · rintro ⟨i,x⟩ ⟨j,y⟩ h
      change Cofan.inj c' i x = Cofan.inj c' j y at h
      have hxy : Cofan.inj c i (α.app ⟨i⟩ x) = Cofan.inj c j (α.app ⟨j⟩ y) :=
        (he i x).symm.trans ((congrArg f h).trans (he j y))
      have hij := Cofan.eq_of_inj_apply_eq_of_isColimit hc _ _ hxy
      subst j
      have : x = y := Types.ext_of_isPullback (hp ⟨i⟩) h
        (Cofan.inj_injective_of_isColimit hc i hxy)
      subst y
      rfl
    · intro y
      obtain ⟨i,x,hx⟩ := Cofan.inj_jointly_surjective_of_isColimit hc (f y)
      obtain ⟨z,hz,_⟩ := Types.exists_of_isPullback (hp ⟨i⟩) y x hx.symm
      exact ⟨⟨i,z⟩, hz⟩

variable {C : Type u} [Category.{v} C] {J : GrothendieckTopology C}
variable {I : Type (max u v)}

/-- Every categorical coproduct of sheaves in the supported universes is van Kampen. -/
theorem isVanKampen {F : Discrete I ⥤ Sheaf J (Type (max u v))}
    (c : Cocone F) (hc : IsColimit c) : IsVanKampenColimit c := by
  let raw := colimit.cocone (F ⋙ sheafToPresheaf J (Type (max u v)))
  have hr : IsVanKampenColimit raw :=
    isVanKampenColimit_of_evaluation _ raw (fun V =>
      types_isVanKampen _ (isColimitOfPreserves ((evaluation _ _).obj V) (colimit.isColimit _)))
  have hs : IsVanKampenColimit (Sheaf.sheafifyCocone raw) := by
    exact IsVanKampenColimit.precompose_isIso _
      (hr.map_reflective (sheafificationAdjunction J (Type (max u v))))
  exact hs.of_iso (IsColimit.uniqueUpToIso
    (Sheaf.isColimitSheafifyCocone raw (colimit.isColimit _)) hc)

open SheafCoproductLocal

variable (Y : I → Sheaf J (Type (max u v)))

/-- The chosen actual sheaf coproduct has the van Kampen property. -/
theorem total_isVanKampen : IsVanKampenColimit (colimit.cocone (diagram Y)) :=
  isVanKampen _ (colimit.isColimit _)

/-- A family of component maps induces a map of the actual sheaf coproducts. -/
def map {E : I → Sheaf J (Type (max u v))} (p : ∀ i, E i ⟶ Y i) :
    total E ⟶ total Y := desc E (fun i => p i ≫ inclusion Y i)

@[simp, reassoc] theorem inclusion_map {E : I → Sheaf J (Type (max u v))}
    (p : ∀ i, E i ⟶ Y i) (i : I) :
    inclusion E i ≫ map Y p = p i ≫ inclusion Y i := inclusion_desc _ _ _

/-- Each component of a coproduct map is recovered by pullback along its summand. -/
theorem isPullback_inclusion_map {E : I → Sheaf J (Type (max u v))}
    (p : ∀ i, E i ⟶ Y i) (i : I) :
    IsPullback (inclusion E i) (p i) (map Y p) (inclusion Y i) := by
  apply ((total_isVanKampen Y) (colimit.cocone (diagram E))
    (Discrete.natTrans fun i => p i.as) (map Y p) ?_ (.of_discrete _)).mp
      ⟨colimit.isColimit _⟩ ⟨i⟩
  apply NatTrans.ext
  funext ⟨i⟩
  exact (inclusion_map Y p i).symm

/-- Injections into an arbitrary sheaf coproduct are monomorphisms. -/
theorem mono_inclusion (i : I) : Mono (inclusion Y i) :=
  mono_of_cofan_isVanKampen (total_isVanKampen Y) ⟨i⟩

/-- Distinct summands meet in the initial sheaf, including on sites with empty covers. -/
theorem isPullback_initial (i j : I) (h : i ≠ j) :
    IsPullback (initial.to (Y i)) (initial.to (Y j)) (inclusion Y i) (inclusion Y j) :=
  isPullback_initial_to_of_cofan_isVanKampen (total_isVanKampen Y) ⟨i⟩ ⟨j⟩
    (fun e => h (Discrete.mk.inj e))

/-- Coproducts preserve a family of pullback squares with a common base-change map. -/
theorem isPullback_desc {X Z : Sheaf J (Type (max u v))}
    (f : ∀ i, Y i ⟶ X) (g : Z ⟶ X)
    {P : I → Sheaf J (Type (max u v))}
    (a : ∀ i, P i ⟶ Y i) (b : ∀ i, P i ⟶ Z)
    (h : ∀ i, IsPullback (a i) (b i) (f i) g) :
    IsPullback (map Y a) (desc P b) (desc Y f) g := by
  exact (total_isVanKampen Y).isUniversal.isPullback_of_isColimit_right f
    (desc Y f) g a b h (colimit.isColimit _) (fun i => inclusion_desc _ _ _)

/-- The comparison between the coproduct of pullbacks and the pullback of a coproduct. -/
def pullbackIso {X Z : Sheaf J (Type (max u v))}
    (f : ∀ i, Y i ⟶ X) (g : Z ⟶ X) :
    total (fun i => pullback (f i) g) ≅ pullback (desc Y f) g :=
  (isPullback_desc Y f g (fun i => pullback.fst (f i) g)
    (fun i => pullback.snd (f i) g) (fun _ => .of_hasPullback _ _)).isoPullback

@[simp, reassoc] theorem pullbackIso_hom_fst {X Z : Sheaf J (Type (max u v))}
    (f : ∀ i, Y i ⟶ X) (g : Z ⟶ X) :
    (pullbackIso Y f g).hom ≫ pullback.fst (desc Y f) g =
      map Y (fun i => pullback.fst (f i) g) := IsPullback.isoPullback_hom_fst _

@[simp, reassoc] theorem pullbackIso_hom_snd {X Z : Sheaf J (Type (max u v))}
    (f : ∀ i, Y i ⟶ X) (g : Z ⟶ X) :
    (pullbackIso Y f g).hom ≫ pullback.snd (desc Y f) g =
      desc (fun i => pullback (f i) g) (fun i => pullback.snd (f i) g) :=
  IsPullback.isoPullback_hom_snd _

/-- The summand pullback square remains a pullback after taking sections. -/
theorem isPullback_inclusion_map_app {E : I → Sheaf J (Type (max u v))}
    (p : ∀ i, E i ⟶ Y i) (i : I) (V : Cᵒᵖ) :
    IsPullback ((inclusion E i).hom.app V) ((p i).hom.app V)
      ((map Y p).hom.app V) ((inclusion Y i).hom.app V) :=
  ((isPullback_inclusion_map Y p i).map (sheafToPresheaf J (Type (max u v)))).map
    ((evaluation _ _).obj V)

/-- On a fiber above a summand, the coproduct injection is a bijection. -/
def fiberInclusion {E : I → Sheaf J (Type (max u v))}
    (p : ∀ i, E i ⟶ Y i) (i : I) (V : Cᵒᵖ) (y : (Y i).obj.obj V) :
    {e : (E i).obj.obj V // (p i).hom.app V e = y} →
      {e : (total E).obj.obj V // (map Y p).hom.app V e = (inclusion Y i).hom.app V y} :=
  fun e => ⟨(inclusion E i).hom.app V e.val, by
    have h := ConcreteCategory.congr_hom (NatTrans.congr_app
      (congrArg (fun f => f.hom) (inclusion_map Y p i)) V) e.val
    change (map Y p).hom.app V ((inclusion E i).hom.app V e.val) =
      (inclusion Y i).hom.app V ((p i).hom.app V e.val) at h
    exact h.trans (congrArg ((inclusion Y i).hom.app V) e.property)⟩

/-- The component fiber and aggregate fiber agree on every section object. -/
theorem fiberInclusion_bijective {E : I → Sheaf J (Type (max u v))}
    (p : ∀ i, E i ⟶ Y i) (i : I) (V : Cᵒᵖ) (y : (Y i).obj.obj V) :
    Function.Bijective (fiberInclusion Y p i V y) := by
  constructor
  · intro x z h
    apply Subtype.ext
    exact Types.ext_of_isPullback (isPullback_inclusion_map_app Y p i V)
      (congrArg Subtype.val h) (x.property.trans z.property.symm)
  · intro e
    obtain ⟨x,hx,hp⟩ := Types.exists_of_isPullback
      (isPullback_inclusion_map_app Y p i V) e.val y e.property
    exact ⟨⟨x,hp⟩, Subtype.ext hx⟩

/-- A section of the total space over the image of one summand uniquely recovers
its component section. -/
def fiberEquiv {E : I → Sheaf J (Type (max u v))}
    (p : ∀ i, E i ⟶ Y i) (i : I) (V : Cᵒᵖ) (y : (Y i).obj.obj V) :
    {e : (total E).obj.obj V // (map Y p).hom.app V e = (inclusion Y i).hom.app V y} ≃
      {e : (E i).obj.obj V // (p i).hom.app V e = y} :=
  (Equiv.ofBijective (fiberInclusion Y p i V y) (fiberInclusion_bijective Y p i V y)).symm

@[simp] theorem fiberEquiv_symm_apply_val {E : I → Sheaf J (Type (max u v))}
    (p : ∀ i, E i ⟶ Y i) (i : I) (V : Cᵒᵖ) (y : (Y i).obj.obj V)
    (e : {e : (E i).obj.obj V // (p i).hom.app V e = y}) :
    ((fiberEquiv Y p i V y).symm e).val = (inclusion E i).hom.app V e.val := rfl

@[simp] theorem inclusion_fiberEquiv_apply {E : I → Sheaf J (Type (max u v))}
    (p : ∀ i, E i ⟶ Y i) (i : I) (V : Cᵒᵖ) (y : (Y i).obj.obj V)
    (e : {e : (total E).obj.obj V //
      (map Y p).hom.app V e = (inclusion Y i).hom.app V y}) :
    (inclusion E i).hom.app V (fiberEquiv Y p i V y e).val = e.val :=
  congrArg Subtype.val ((fiberEquiv Y p i V y).symm_apply_apply e)

/-- Every sheaf over a coproduct is the coproduct of its pullbacks to the summands. -/
def pullbackInclusionsIsColimit {A : Sheaf J (Type (max u v))} (f : A ⟶ total Y) :
    IsColimit (Cofan.mk A (fun i => pullback.snd (inclusion Y i) f)) := by
  apply Nonempty.some
  refine (total_isVanKampen Y).isUniversal _
    (Discrete.natTrans fun i => pullback.fst (inclusion Y i.as) f) f
    ?_ (.of_discrete _) ?_
  · apply NatTrans.ext
    funext ⟨i⟩
    exact pullback.condition
  · intro ⟨i⟩
    exact (IsPullback.of_hasPullback (inclusion Y i) f).flip

/-- Reconstruction from summand restrictions, without an inhabited-index assumption. -/
def decompositionIso {A : Sheaf J (Type (max u v))} (f : A ⟶ total Y) :
    total (fun i => pullback (inclusion Y i) f) ≅ A :=
  (colimit.isColimit _).coconePointUniqueUpToIso (pullbackInclusionsIsColimit Y f)

@[simp, reassoc] theorem inclusion_decompositionIso_hom
    {A : Sheaf J (Type (max u v))} (f : A ⟶ total Y) (i : I) :
    inclusion (fun i => pullback (inclusion Y i) f) i ≫ (decompositionIso Y f).hom =
      pullback.snd (inclusion Y i) f :=
  (colimit.isColimit _).comp_coconePointUniqueUpToIso_hom
    (pullbackInclusionsIsColimit Y f) ⟨i⟩

/-- The reconstruction comparison retains the map to the original coproduct. -/
@[simp, reassoc] theorem decompositionIso_hom_comp
    {A : Sheaf J (Type (max u v))} (f : A ⟶ total Y) :
    (decompositionIso Y f).hom ≫ f =
      map Y (fun i => pullback.fst (inclusion Y i) f) := by
  apply colimit.hom_ext
  intro ⟨i⟩
  change inclusion _ i ≫ _ = inclusion _ i ≫ _
  rw [← Category.assoc, inclusion_decompositionIso_hom, inclusion_map]
  exact pullback.condition.symm

end SquareKit.SheafCoproductGeometry
