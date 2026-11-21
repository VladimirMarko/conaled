import SquareKit.SheafTorsorCoproduct
import SquareKit.SheafActionQuotient

/-! Coproduct assembly retains the equivariant target map and every quotient arrow. -/
noncomputable section
set_option autoImplicit false
set_option warningAsError true
set_option backward.isDefEq.respectTransparency false
namespace SquareKit.SheafActionQuotient.Coproduct
open CategoryTheory Limits Opposite
universe u v
variable {C : Type u} [Category.{v} C] {J : GrothendieckTopology C}
variable {I : Type (max u v)} {G : Sheaf J GrpCat.{max u v}}
variable {M : Sheaf J (Type (max u v))} {a : Action G M}
variable {Y : I → Sheaf J (Type (max u v))} (P : ∀ i, Object a (Y i))

abbrev torsors := fun i => (P i).torsor

def valueMap : SheafTorsor.Coproduct.total (torsors P) ⟶ M :=
  Sigma.desc (fun i => (P i).totalMap)

lemma valueMap_inclusion (i : I) (U : Cᵒᵖ)
    (p : (SplitSheaf.Ext (P i).torsor.family).obj.obj U) :
    (valueMap P).hom.app U
      ((Sigma.ι (fun i => SplitSheaf.Ext (P i).torsor.family) i).hom.app U p) =
      (P i).value ((Y i).obj.elementsMk U p.1) p.2 :=
  congrArg (fun f => f.hom.app U p) (Sigma.ι_comp_desc (fun i => (P i).totalMap) i)

lemma valueMap_action (U : Cᵒᵖ) (g : G.obj.obj U)
    (p : (SheafTorsor.Coproduct.total (torsors P)).obj.obj U) :
    (valueMap P).hom.app U ((SheafTorsor.Coproduct.actionMap (torsors P)).hom.app U (g,p)) =
      a.act U g ((valueMap P).hom.app U p) := by
  apply SheafTorsor.Coproduct.section_ext (torsors P) p
  intro V k i q hq
  rw [← NatTrans.naturality_apply, ← NatTrans.naturality_apply, a.natural,
    ← NatTrans.naturality_apply]
  change (valueMap P).hom.app _ ((SheafTorsor.Coproduct.actionMap (torsors P)).hom.app _
    (G.obj.map k.op g, (SheafTorsor.Coproduct.total (torsors P)).obj.map k.op p)) = _
  rw [← hq, SheafTorsor.Coproduct.actionMap_apply_inclusion,
    valueMap_inclusion, valueMap_inclusion]
  exact (P i).equivariant _ _ _

/-- The object over the actual coproduct is constructed from local torsors and maps. -/
def object : Object a (∐ Y) where
  torsor := SheafTorsor.Coproduct.torsor (torsors P)
  value x p := (valueMap P).hom.app x.obj p.val
  natural f p := by
    rw [← NatTrans.naturality_apply]
    rfl
  equivariant x g p := valueMap_action P x.obj g p.val

/-- Recovery above a summand preserves its full target value. -/
def component (i : I) : P i ≅ reindex (object P) (Sigma.ι Y i) :=
  Arrow.toIso {
    torsorArrow := (SheafTorsor.Coproduct.component (torsors P) i).hom
    preserves x p := valueMap_inclusion P i x.obj ⟨x.val,p⟩ }

variable {P} (Q : Object a (∐ Y)) (h : ∀ i, P i ⟶ reindex Q (Sigma.ι Y i))

lemma descTotal_value :
    SheafTorsor.Coproduct.descTotal Q.torsor (fun i => (h i).torsorArrow) ≫ Q.totalMap =
      valueMap P := by
  apply Sigma.hom_ext
  intro i
  rw [← Category.assoc, SheafTorsor.Coproduct.inclusion_descTotal, valueMap, Sigma.ι_comp_desc]
  ext U p
  exact (h i).preserves _ p.2

/-- Quotient arrows assemble through the torsor construction with target equality proved. -/
def desc : object P ⟶ Q where
  torsorArrow := SheafTorsor.Coproduct.desc Q.torsor (fun i => (h i).torsorArrow)
  preserves x p := by
    have ht := SheafTorsor.Coproduct.descFamily_total Q.torsor
      (fun i => (h i).torsorArrow) x p
    have hm := congrArg (fun f => f.hom.app x.obj p.val) (descTotal_value Q h)
    change Q.totalMap.hom.app x.obj
      (SheafTorsor.Coproduct.descTotal Q.torsor (fun i => (h i).torsorArrow) |>.hom.app x.obj p.val) = _ at hm
    rw [← ht] at hm
    exact hm

lemma desc_component (i : I) :
    (component P i).hom ≫ (desc Q h).reindex (Sigma.ι Y i) = h i := by
  apply Arrow.ext
  exact SheafTorsor.Coproduct.desc_component Q.torsor (fun i => (h i).torsorArrow) i

/-- Product restriction retains the actual quotient maps. -/
def restrict : Object a (∐ Y) ⥤ (∀ i, Object a (Y i)) where
  obj S i := reindex S (Sigma.ι Y i)
  map f i := f.reindex (Sigma.ι Y i)
  map_id _ := rfl
  map_comp _ _ := rfl

instance restrict_faithful : (restrict (a := a) (Y := Y)).Faithful where
  map_injective h := by
    apply Arrow.ext
    apply SheafTorsor.Coproduct.arrow_ext
    intro i
    exact congrArg Arrow.torsorArrow (congrFun h i)

def recovery (S : Object a (∐ Y)) : object (fun i => reindex S (Sigma.ι Y i)) ≅ S :=
  (desc S (fun _ => 𝟙 _)).toIso

lemma component_recovery (S : Object a (∐ Y)) (i : I) :
    (component (fun i => reindex S (Sigma.ι Y i)) i).hom ≫
      (recovery S).hom.reindex (Sigma.ι Y i) = 𝟙 _ := desc_component _ _ _

instance restrict_full : (restrict (a := a) (Y := Y)).Full where
  map_surjective {S T} h := by
    refine ⟨(recovery S).inv ≫ desc T h, ?_⟩
    funext i
    have hi := component_recovery S i
    have hj := desc_component T h i
    have he : (recovery S).inv.reindex (Sigma.ι Y i) =
        (component (fun i => reindex S (Sigma.ι Y i)) i).hom := by
      apply (cancel_mono (C := Object a (Y i)) ((recovery S).hom.reindex (Sigma.ι Y i))).mp
      rw [hi]
      exact congrArg (fun f => f.reindex (Sigma.ι Y i)) (recovery S).inv_hom_id
    change ((recovery S).inv.reindex (Sigma.ι Y i)) ≫
      (desc T h).reindex (Sigma.ι Y i) = h i
    rw [he]
    exact hj

instance restrict_essSurj : (restrict (a := a) (Y := Y)).EssSurj where
  mem_essImage P := ⟨object P, ⟨{
    hom i := (component P i).inv
    inv i := (component P i).hom
    hom_inv_id := by funext i; exact (component P i).inv_hom_id
    inv_hom_id := by funext i; exact (component P i).hom_inv_id }⟩⟩

instance restrict_isEquivalence : (restrict (a := a) (Y := Y)).IsEquivalence := {}

def equivalence : Object a (∐ Y) ≌ (∀ i, Object a (Y i)) :=
  (restrict (a := a) (Y := Y)).asEquivalence

end SquareKit.SheafActionQuotient.Coproduct
