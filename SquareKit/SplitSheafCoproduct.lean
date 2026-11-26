import SquareKit.SheafCoproductGeometry
import SquareKit.SplitSheafDescent

/-! Sheaf displays assembled over the categorical coproduct of their contexts. -/
noncomputable section
set_option autoImplicit false
set_option warningAsError true
set_option backward.isDefEq.respectTransparency false
namespace SquareKit.SplitSheafCoproduct
open CategoryTheory Limits Opposite
universe u v
variable {C : Type u} [Category.{v} C] {J : GrothendieckTopology C}
variable {I : Type (max u v)}
variable {Y : I → Sheaf J (Type (max u v))} (P : ∀ i, SplitSheaf.Ty (Y i))

abbrev total : Sheaf J (Type (max u v)) := ∐ (fun i => SplitSheaf.extension (P i))
abbrev base : Sheaf J (Type (max u v)) := ∐ Y

def projection : total P ⟶ base (Y := Y) :=
  Sigma.desc (fun i => SplitSheaf.p (P i) ≫ Sigma.ι Y i)

@[simp, reassoc] lemma inclusion_projection (i : I) :
    Sigma.ι (fun i => SplitSheaf.extension (P i)) i ≫ projection P =
      SplitSheaf.p (P i) ≫ Sigma.ι Y i := Sigma.ι_comp_desc _ _

abbrev assembled : SplitSheaf.Ty (base (Y := Y)) := SplitSheaf.ofDisplay (projection P)

/-- Recovery above an actual coproduct injection uses its proved pullback square. -/
def componentEquiv (i : I) (x : (Y i).obj.Elements) :
    (P i).family.obj x ≃
      (SplitSheaf.tySub (assembled P) (Sigma.ι Y i)).family.obj x :=
  (ElementFamilies.fiberTotalEquiv (Y i).obj (P i).family x).symm.trans
    (SheafCoproductGeometry.fiberEquiv Y (fun i => SplitSheaf.p (P i))
      i x.obj x.val).symm

@[simp] lemma componentEquiv_val (i : I) (x : (Y i).obj.Elements)
    (p : (P i).family.obj x) :
    (componentEquiv P i x p).val =
      (Sigma.ι (fun i => SplitSheaf.extension (P i)) i).hom.app x.obj ⟨x.val,p⟩ := rfl


/-- The original local displays are recovered on their actual fibers. -/
def component (i : I) : P i ≅ SplitSheaf.tySub (assembled P) (Sigma.ι Y i) :=
  SplitSheaf.isoMk ( NatIso.ofComponents (fun x => (componentEquiv P i x).toIso) (by
      intro x y k
      apply ConcreteCategory.hom_ext
      intro p
      apply Subtype.ext
      rcases y with @⟨V,y⟩
      rcases k with ⟨k,hk⟩
      change x.obj ⟶ V at k
      change (Y i).obj.map k x.val = y at hk
      subst y
      exact NatTrans.naturality_apply
        (Sigma.ι (fun i => SplitSheaf.extension (P i)) i).hom k ⟨x.val,p⟩)
    )

variable {P}
variable (Q : SplitSheaf.Ty (base (Y := Y)))
variable (h : ∀ i, P i ⟶ SplitSheaf.tySub Q (Sigma.ι Y i))

/-- Maps out of the assembled display are induced by the coproduct. -/
def descTotal : total P ⟶ SplitSheaf.extension Q :=
  Sigma.desc (fun i => SplitSheaf.totalMap (h i) ≫
    SplitSheaf.lift Q (Sigma.ι Y i))

lemma inclusion_descTotal (i : I) :
    Sigma.ι (fun i => SplitSheaf.extension (P i)) i ≫ descTotal Q h =
      SplitSheaf.totalMap (h i) ≫ SplitSheaf.lift Q (Sigma.ι Y i) :=
  Sigma.ι_comp_desc _ _

lemma descTotal_projection : descTotal Q h ≫ SplitSheaf.p Q = projection P := by
  apply Sigma.hom_ext
  intro i
  rw [← Category.assoc, inclusion_descTotal, inclusion_projection]
  rfl

lemma descTotal_inclusion_apply (i : I) (U : Cᵒᵖ)
    (p : (SplitSheaf.extension (P i)).obj.obj U) :
    (descTotal Q h).hom.app U
      ((Sigma.ι (fun i => SplitSheaf.extension (P i)) i).hom.app U p) =
      ⟨(Sigma.ι Y i).hom.app U p.1, (h i).app _ p.2⟩ :=
  congrArg (fun f => f.hom.app U p) (inclusion_descTotal Q h i)

/-- The section-map obtained from the actual total-space map. -/
def descFamily : (assembled P).family ⟶ Q.family :=
  (ElementFamilies.fiberFunctor (base (Y := Y)).obj).map
    (show Over.mk (projection P).hom ⟶ Over.mk (SplitSheaf.p Q).hom from
      Over.homMk (descTotal Q h).hom (congrArg (fun f => f.hom) (descTotal_projection Q h))) ≫
      (ElementFamilies.fiberTotalIso (base (Y := Y)).obj Q.family).hom

lemma descFamily_component (i : I) (x : (Y i).obj.Elements)
    (p : (P i).family.obj x) :
    (descFamily Q h).app ((Sigma.ι Y i).hom.mapElements.obj x)
      (componentEquiv P i x p) = (h i).app x p := by
  change ElementFamilies.fiberTotalEquiv (base (Y := Y)).obj Q.family
    ((Sigma.ι Y i).hom.mapElements.obj x) ⟨(descTotal Q h).hom.app x.obj ((componentEquiv P i x p).val), _⟩ = _
  have he := descTotal_inclusion_apply Q h i x.obj ⟨x.val,p⟩
  apply (ElementFamilies.fiberTotalEquiv (base (Y := Y)).obj Q.family _).symm.injective
  rw [Equiv.symm_apply_apply]
  apply Subtype.ext
  exact he

lemma descFamily_total (x : (base (Y := Y)).obj.Elements)
    (p : (assembled P).family.obj x) :
    (⟨x.val, (descFamily Q h).app x p⟩ : (SplitSheaf.extension Q).obj.obj x.obj) =
      (descTotal Q h).hom.app x.obj p.val := by
  exact congrArg Subtype.val ((ElementFamilies.fiberTotalEquiv
    (base (Y := Y)).obj Q.family x).symm_apply_apply
      ((ElementFamilies.fiberFunctor (base (Y := Y)).obj).map
        (show Over.mk (projection P).hom ⟶ Over.mk (SplitSheaf.p Q).hom from
          Over.homMk (descTotal Q h).hom
            (congrArg (fun f => f.hom) (descTotal_projection Q h))) |>.app x <| p))

/-- Every family of local maps assembles to an actual display map. -/
def desc : assembled P ⟶ Q := descFamily Q h

lemma desc_component (i : I) :
    (component P i).hom ≫ (SplitSheaf.restriction (Sigma.ι Y i)).map (desc Q h) = h i := by
  apply NatTrans.ext
  funext x
  apply ConcreteCategory.hom_ext
  intro p
  exact descFamily_component Q h i x p

/-- Restriction to all summands retains every display map. -/
lemma arrow_ext {S T : SplitSheaf.Ty (base (Y := Y))} (a b : S ⟶ T)
    (h : ∀ i, (SplitSheaf.restriction (Sigma.ι Y i)).map a = (SplitSheaf.restriction (Sigma.ι Y i)).map b) : a = b := by
  apply NatTrans.ext
  funext x
  apply ConcreteCategory.hom_ext
  intro p
  apply SplitSheafDescent.fiber_ext T x _ (SheafCoproductLocal.liftSieve_cover Y x.val)
  rintro V k ⟨i,y,hy⟩
  rw [← NatTrans.naturality_apply, ← NatTrans.naturality_apply]
  have atLift (z : (base (Y := Y)).obj.obj (op V))
      (q : S.family.obj ((base (Y := Y)).obj.elementsMk (op V) z))
      (hz : (Sigma.ι Y i).hom.app (op V) y = z) :
      a.app _ q = b.app _ q := by
    subst z
    exact congrArg (fun t : SplitSheaf.tySub S (Sigma.ι Y i) ⟶ SplitSheaf.tySub T (Sigma.ι Y i) =>
      t.app ((Y i).obj.elementsMk (op V) y) q) (h i)
  exact atLift _ _ hy

/-- Product restriction uses the existing strict reindexing on all maps. -/
def restrict : SplitSheaf.Ty (base (Y := Y)) ⥤ (∀ i, SplitSheaf.Ty (Y i)) where
  obj S i := SplitSheaf.tySub S (Sigma.ι Y i)
  map a i := (SplitSheaf.restriction (Sigma.ι Y i)).map a
  map_id _ := rfl
  map_comp _ _ := rfl

instance restrict_faithful : (restrict (Y := Y)).Faithful where
  map_injective h := arrow_ext _ _ (congrFun h)



/-- The restricted total spaces form an actual coproduct, by universality. -/
def restrictedIsColimit (S : SplitSheaf.Ty (base (Y := Y))) :
    IsColimit (Cofan.mk (SplitSheaf.extension S)
      (fun i => SplitSheaf.lift S (Sigma.ι Y i))) := by
  apply Nonempty.some
  apply (SheafCoproductGeometry.total_isVanKampenColimit Y).isUniversal _
    (Discrete.natTrans fun i => SplitSheaf.p (SplitSheaf.tySub S (Sigma.ι Y i.as)))
    (SplitSheaf.p S) ?_ (.of_discrete _) ?_
  · apply NatTrans.ext
    funext ⟨i⟩
    exact (SplitSheaf.lift_p S (Sigma.ι Y i)).symm
  · intro ⟨i⟩
    exact SplitSheaf.extension_pullback S (Sigma.ι Y i)

instance descTotal_identity_isIso (S : SplitSheaf.Ty (base (Y := Y))) :
    IsIso (descTotal S (fun _ => 𝟙 _)) := by
  let e := (colimit.isColimit (Discrete.functor (fun i =>
    SplitSheaf.extension (SplitSheaf.tySub S (Sigma.ι Y i))))).coconePointUniqueUpToIso
      (restrictedIsColimit S)
  have he : e.hom = descTotal S (fun _ => 𝟙 _) := by
    apply Sigma.hom_ext
    intro i
    rw [inclusion_descTotal]
    exact (colimit.isColimit _).comp_coconePointUniqueUpToIso_hom (restrictedIsColimit S) ⟨i⟩
  rw [← he]
  infer_instance

lemma totalMap_desc : SplitSheaf.totalMap (desc Q h) =
    (SplitSheaf.displayIso (projection P)).hom ≫ descTotal Q h := by
  ext U p
  exact descFamily_total Q h ((base (Y := Y)).obj.elementsMk U p.1) p.2

/-- Assembly of restrictions recovers the original display, with no inhabited-index assumption. -/
def recovery (S : SplitSheaf.Ty (base (Y := Y))) :
    assembled (fun i => SplitSheaf.tySub S (Sigma.ι Y i)) ≅ S := by
  have : IsIso (SplitSheaf.totalMap (desc S (fun _ => 𝟙 _))) := by
    rw [totalMap_desc]
    infer_instance
  have := SplitSheaf.isIso_of_totalMap (desc S (fun _ => 𝟙 _))
  exact asIso (desc S (fun _ => 𝟙 _))

lemma component_recovery (S : SplitSheaf.Ty (base (Y := Y))) (i : I) :
    (component (fun i => SplitSheaf.tySub S (Sigma.ι Y i)) i).hom ≫
      (SplitSheaf.restriction (Sigma.ι Y i)).map (recovery S).hom = 𝟙 _ := desc_component _ _ _

instance restrict_full : (restrict (Y := Y)).Full where
  map_surjective {S T} h := by
    refine ⟨(recovery S).inv ≫ desc T h, ?_⟩
    funext i
    have hi := component_recovery S i
    have hj := desc_component T h i
    have he : (SplitSheaf.restriction (Sigma.ι Y i)).map (recovery S).inv =
        (component (fun i => SplitSheaf.tySub S (Sigma.ι Y i)) i).hom := by
      apply (cancel_mono ((SplitSheaf.restriction (Sigma.ι Y i)).map (recovery S).hom)).mp
      rw [hi, ← Functor.map_comp, Iso.inv_hom_id]
      rfl
    change (SplitSheaf.restriction (Sigma.ι Y i)).map (recovery S).inv ≫
      (SplitSheaf.restriction (Sigma.ι Y i)).map (desc T h) = h i
    rw [he]
    exact hj

instance restrict_essSurj : (restrict (Y := Y)).EssSurj where
  mem_essImage P := ⟨assembled P, ⟨{
    hom i := (component P i).inv
    inv i := (component P i).hom
    hom_inv_id := by funext i; exact (component P i).inv_hom_id
    inv_hom_id := by funext i; exact (component P i).hom_inv_id }⟩⟩

instance restrict_isEquivalence : (restrict (Y := Y)).IsEquivalence := {}

def equivalence : SplitSheaf.Ty (base (Y := Y)) ≌ (∀ i, SplitSheaf.Ty (Y i)) :=
  (restrict (Y := Y)).asEquivalence

end SquareKit.SplitSheafCoproduct
