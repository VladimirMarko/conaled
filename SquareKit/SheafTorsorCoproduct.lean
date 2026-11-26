import SquareKit.SheafCoproductGeometry
import SquareKit.SheafTorsorDescent
import SquareKit.SheafFunction

/-! Torsors assembled over the categorical coproduct of their contexts. -/
noncomputable section
set_option autoImplicit false
set_option warningAsError true
set_option backward.isDefEq.respectTransparency false
namespace SquareKit.SheafTorsor.Coproduct
open CategoryTheory Limits Opposite
universe u v
variable {C : Type u} [Category.{v} C] {J : GrothendieckTopology C}
variable {I : Type (max u v)} {G : Sheaf J GrpCat.{max u v}}
variable {Y : I → Sheaf J (Type (max u v))} (P : ∀ i, Torsor G (Y i))

abbrev total : Sheaf J (Type (max u v)) := ∐ (fun i => SplitSheaf.extension (P i).family)
abbrev base : Sheaf J (Type (max u v)) := ∐ Y

def projection : total P ⟶ base (Y := Y) :=
  Sigma.desc (fun i => SplitSheaf.p (P i).family ≫ Sigma.ι Y i)

@[simp, reassoc] lemma inclusion_projection (i : I) :
    Sigma.ι (fun i => SplitSheaf.extension (P i).family) i ≫ projection P =
      SplitSheaf.p (P i).family ≫ Sigma.ι Y i := Sigma.ι_comp_desc _ _

/-- The local action is an actual map of sheaves. -/
def localAction (i : I) :
    SheafRelation.product (groupSheaf G) (SplitSheaf.extension (P i).family) ⟶
      SplitSheaf.extension (P i).family := ⟨{
  app U := TypeCat.ofHom (fun x => (P i).toAction.totalAct U x.1 x.2)
  naturality U V k := by
    apply ConcreteCategory.hom_ext
    rintro ⟨g, p⟩
    exact ((P i).toAction.totalAct_natural k g p).symm }⟩

/-- Currying lets the coproduct universal property assemble the action. -/
def actionMap : SheafRelation.product (groupSheaf G) (total P) ⟶ total P :=
  SheafFunction.uncurry (Sigma.desc (fun i => SheafFunction.curry
    (localAction P i ≫ Sigma.ι (fun i => SplitSheaf.extension (P i).family) i)))

lemma actionMap_inclusion (i : I) :
    SheafFunction.parameterMap (groupSheaf G)
        (Sigma.ι (fun i => SplitSheaf.extension (P i).family) i) ≫ actionMap P =
      localAction P i ≫ Sigma.ι (fun i => SplitSheaf.extension (P i).family) i := by
  apply (Function.LeftInverse.injective (fun f => SheafFunction.beta f))
  rw [SheafFunction.curry_parameter, actionMap, SheafFunction.eta, Sigma.ι_comp_desc]

lemma actionMap_apply_inclusion (i : I) (U : Cᵒᵖ) (g : G.obj.obj U)
    (p : (SplitSheaf.extension (P i).family).obj.obj U) :
    (actionMap P).hom.app U
      (g, (Sigma.ι (fun i => SplitSheaf.extension (P i).family) i).hom.app U p) =
    (Sigma.ι (fun i => SplitSheaf.extension (P i).family) i).hom.app U
      ((P i).toAction.totalAct U g p) :=
  congrArg (fun f => f.hom.app U (g,p)) (actionMap_inclusion P i)

/-- Equality of sections is checked after local decomposition into summands. -/
lemma section_ext {N : Sheaf J (Type (max u v))} {U : C} (x : (total P).obj.obj (op U))
    (s t : N.obj.obj (op U))
    (h : ∀ (V : C) (k : V ⟶ U) (i : I)
      (p : (SplitSheaf.extension (P i).family).obj.obj (op V)),
      (Sigma.ι (fun i => SplitSheaf.extension (P i).family) i).hom.app _ p =
        (total P).obj.map k.op x → N.obj.map k.op s = N.obj.map k.op t) : s = t := by
  apply (((isSheaf_iff_isSheaf_of_type _ _).mp N.property)
    _ (SheafCoproductLocal.liftSieve_cover (fun i => SplitSheaf.extension (P i).family) x)).isSeparatedFor.ext
  rintro V k ⟨i, p, hp⟩
  exact h V k i p hp

lemma action_over (U : Cᵒᵖ) (g : G.obj.obj U) (p : (total P).obj.obj U) :
    (projection P).hom.app U ((actionMap P).hom.app U (g,p)) =
      (projection P).hom.app U p := by
  apply section_ext P p
  intro V k i q hq
  rw [← NatTrans.naturality_apply, ← NatTrans.naturality_apply,
    ← NatTrans.naturality_apply]
  change (projection P).hom.app _ ((actionMap P).hom.app _
    (G.obj.map k.op g, (total P).obj.map k.op p)) = _
  rw [← hq, actionMap_apply_inclusion]
  have h := inclusion_projection P i
  have h' (r : (SplitSheaf.extension (P i).family).obj.obj (op V)) :=
    ConcreteCategory.congr_hom (NatTrans.congr_app (congrArg (fun f => f.hom) h) (op V)) r
  exact (h' _).trans (h' q).symm

lemma action_one (U : Cᵒᵖ) (p : (total P).obj.obj U) :
    (actionMap P).hom.app U ((1 : G.obj.obj U),p) = p := by
  apply section_ext P p
  intro V k i q hq
  rw [← NatTrans.naturality_apply]
  change (actionMap P).hom.app _ (G.obj.map k.op 1, (total P).obj.map k.op p) = _
  rw [(G.obj.map k.op).hom.map_one, ← hq, actionMap_apply_inclusion]
  congr 1
  exact congrArg (Sigma.mk q.1) ((P i).one_act _ q.2)

lemma action_mul (U : Cᵒᵖ) (g h : G.obj.obj U) (p : (total P).obj.obj U) :
    (actionMap P).hom.app U (g*h,p) =
      (actionMap P).hom.app U (g, (actionMap P).hom.app U (h,p)) := by
  apply section_ext P p
  intro V k i q hq
  rw [← NatTrans.naturality_apply, ← NatTrans.naturality_apply]
  change (actionMap P).hom.app _ (G.obj.map k.op (g*h), (total P).obj.map k.op p) =
    (actionMap P).hom.app _ (G.obj.map k.op g,
      (total P).obj.map k.op ((actionMap P).hom.app U (h,p)))
  rw [← NatTrans.naturality_apply]
  change (actionMap P).hom.app _ (G.obj.map k.op (g*h), (total P).obj.map k.op p) =
    (actionMap P).hom.app _ (G.obj.map k.op g,
      (actionMap P).hom.app _ (G.obj.map k.op h, (total P).obj.map k.op p))
  rw [(G.obj.map k.op).hom.map_mul, ← hq, actionMap_apply_inclusion,
    actionMap_apply_inclusion, actionMap_apply_inclusion]
  congr 1
  exact congrArg (Sigma.mk q.1) ((P i).mul_act _ _ _ q.2)

def action : Action G (base (Y := Y)) :=
  Action.ofDisplay (projection P) (fun U g p => (actionMap P).hom.app U (g,p))
    (action_over P) (action_one P) (action_mul P)
    (by
      intro U V k g p
      rw [← NatTrans.naturality_apply]
      rfl)

/-- Recovery above an actual coproduct injection uses its proved pullback square. -/
def componentEquiv (i : I) (x : (Y i).obj.Elements) :
    (P i).family.family.obj x ≃
      ((action P).reindex (Sigma.ι Y i)).family.family.obj x :=
  (ElementFamilies.fiberTotalEquiv (Y i).obj (P i).family.family x).symm.trans
    (SheafCoproductGeometry.fiberEquiv Y (fun i => SplitSheaf.p (P i).family)
      i x.obj x.val).symm

@[simp] lemma componentEquiv_val (i : I) (x : (Y i).obj.Elements)
    (p : (P i).family.family.obj x) :
    (componentEquiv P i x p).val =
      (Sigma.ι (fun i => SplitSheaf.extension (P i).family) i).hom.app x.obj ⟨x.val,p⟩ := rfl

lemma componentEquiv_action (i : I) (x : (Y i).obj.Elements)
    (g : G.obj.obj x.obj) (p : (P i).family.family.obj x) :
    componentEquiv P i x ((P i).act x g p) =
      ((action P).reindex (Sigma.ι Y i)).act x g (componentEquiv P i x p) := by
  apply Subtype.ext
  exact (actionMap_apply_inclusion P i x.obj g ⟨x.val,p⟩).symm

lemma component_principal (i : I) (x : (Y i).obj.Elements)
    (p q : ((action P).reindex (Sigma.ι Y i)).family.family.obj x) :
    ∃! g : G.obj.obj x.obj,
      ((action P).reindex (Sigma.ι Y i)).act x g p = q := by
  obtain ⟨p, rfl⟩ := (componentEquiv P i x).surjective p
  obtain ⟨q, rfl⟩ := (componentEquiv P i x).surjective q
  obtain ⟨g, hg, hu⟩ := (P i).principal x p q
  refine ⟨g, ?_, ?_⟩
  · exact (componentEquiv_action P i x g p).symm.trans (congrArg (componentEquiv P i x) hg)
  · intro h hh
    apply hu
    apply (componentEquiv P i x).injective
    rwa [componentEquiv_action]

lemma principal (x : (base (Y := Y)).obj.Elements)
    (p q : (action P).family.family.obj x) :
    ∃! g : G.obj.obj x.obj, (action P).act x g p = q := by
  obtain ⟨g, hg, hu⟩ := (action P).total_principal_of_sieve x.obj.unop ⟨x.val,p⟩ ⟨x.val,q⟩
    (SheafCoproductLocal.liftSieve Y (Sigma.ι Y) x.val)
    (SheafCoproductLocal.liftSieve_cover Y x.val) (by
      rintro V k ⟨i,y,hy⟩
      exact (action P).principal_at_lift (Sigma.ι Y i) (component_principal P i)
        _ _ _ rfl y hy)
  refine ⟨g, eq_of_heq (Sigma.mk.inj_iff.mp hg).2, ?_⟩
  intro h hh
  exact hu h (congrArg (Sigma.mk x.val) hh)

lemma projection_isLocallySurjective : Presheaf.IsLocallySurjective J (projection P).hom where
  imageSieve_mem {U} x := by
    apply J.transitive (SheafCoproductLocal.liftSieve_cover Y x)
    rintro V k ⟨i,y,hy⟩
    apply J.superset_covering _
      (Presheaf.imageSieve_mem J (SplitSheaf.p (P i).family).hom y)
    rintro W l ⟨p,hp⟩
    refine ⟨(Sigma.ι (fun i => SplitSheaf.extension (P i).family) i).hom.app _ p, ?_⟩
    have hf := congrArg (fun f => f.hom.app (op W) p) (inclusion_projection P i)
    change (projection P).hom.app _ _ = (Sigma.ι Y i).hom.app _ p.1 at hf
    change p.1 = (Y i).obj.map l.op y at hp
    apply hf.trans
    rw [hp, NatTrans.naturality_apply, hy, op_comp, (base (Y := Y)).obj.map_comp]
    rfl

/-- Effective assembly over the coproduct; principalness and local existence are derived. -/
def torsor : Torsor G (base (Y := Y)) where
  toAction := action P
  principal := principal P
  isLocallySurjective := by
    have := projection_isLocallySurjective P
    change Presheaf.IsLocallySurjective J (SplitSheaf.p (SplitSheaf.ofDisplay (projection P))).hom
    have h := Presheaf.isLocallySurjective_iff_of_fac J
      (congrArg (fun f => f.hom) (SplitSheaf.displayIso_projection (projection P)))
    exact h.mpr inferInstance

/-- The local torsors are recovered with their actual actions. -/
def component (i : I) : P i ≅ reindex (torsor P) (Sigma.ι Y i) :=
  Arrow.toIso {
    iso := NatIso.ofComponents (fun x => (componentEquiv P i x).toIso) (by
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
        (Sigma.ι (fun i => SplitSheaf.extension (P i).family) i).hom k ⟨x.val,p⟩)
    equivariant := componentEquiv_action P i }

variable {P}
variable (Q : Torsor G (base (Y := Y)))
variable (h : ∀ i, P i ⟶ reindex Q (Sigma.ι Y i))

/-- Compatible maps out of the assembled torsor are induced by the coproduct. -/
def descTotal : total P ⟶ SplitSheaf.extension Q.family :=
  Sigma.desc (fun i => (equivariantArrowEquiv.symm (h i)).totalMap ≫
    SplitSheaf.lift Q.family (Sigma.ι Y i))

lemma inclusion_descTotal (i : I) :
    Sigma.ι (fun i => SplitSheaf.extension (P i).family) i ≫ descTotal Q h =
      (equivariantArrowEquiv.symm (h i)).totalMap ≫ SplitSheaf.lift Q.family (Sigma.ι Y i) :=
  Sigma.ι_comp_desc _ _

lemma descTotal_projection : descTotal Q h ≫ SplitSheaf.p Q.family = projection P := by
  apply Sigma.hom_ext
  intro i
  rw [← Category.assoc, inclusion_descTotal, inclusion_projection]
  rfl

lemma descTotal_inclusion_apply (i : I) (U : Cᵒᵖ)
    (p : (SplitSheaf.extension (P i).family).obj.obj U) :
    (descTotal Q h).hom.app U
      ((Sigma.ι (fun i => SplitSheaf.extension (P i).family) i).hom.app U p) =
      ⟨(Sigma.ι Y i).hom.app U p.1, (h i).iso.hom.app _ p.2⟩ :=
  congrArg (fun f => f.hom.app U p) (inclusion_descTotal Q h i)

lemma descTotal_action (U : Cᵒᵖ) (g : G.obj.obj U) (p : (total P).obj.obj U) :
    (descTotal Q h).hom.app U ((actionMap P).hom.app U (g,p)) =
      Q.toAction.totalAct U g ((descTotal Q h).hom.app U p) := by
  apply section_ext P p
  intro V k i q hq
  rw [← NatTrans.naturality_apply, ← NatTrans.naturality_apply,
    Q.toAction.totalAct_natural, ← NatTrans.naturality_apply]
  change (descTotal Q h).hom.app _ ((actionMap P).hom.app _
      (G.obj.map k.op g, (total P).obj.map k.op p)) =
    Q.toAction.totalAct _ (G.obj.map k.op g)
      ((descTotal Q h).hom.app _ ((total P).obj.map k.op p))
  rw [← hq, actionMap_apply_inclusion, descTotal_inclusion_apply, descTotal_inclusion_apply]
  exact congrArg (Sigma.mk _) ((h i).equivariant _ _ q.2)

/-- The section-map obtained from the actual total-space map. -/
def descFamily : (torsor P).family.family ⟶ Q.family.family :=
  (ElementFamilies.fiberFunctor (base (Y := Y)).obj).map
    (show Over.mk (projection P).hom ⟶ Over.mk (SplitSheaf.p Q.family).hom from
      Over.homMk (descTotal Q h).hom (congrArg (fun f => f.hom) (descTotal_projection Q h))) ≫
      (ElementFamilies.fiberTotalIso (base (Y := Y)).obj Q.family.family).hom

lemma descFamily_component (i : I) (x : (Y i).obj.Elements)
    (p : (P i).family.family.obj x) :
    (descFamily Q h).app ((Sigma.ι Y i).hom.mapElements.obj x)
      (componentEquiv P i x p) = (h i).iso.hom.app x p := by
  change ElementFamilies.fiberTotalEquiv (base (Y := Y)).obj Q.family.family
    ((Sigma.ι Y i).hom.mapElements.obj x) ⟨(descTotal Q h).hom.app x.obj ((componentEquiv P i x p).val), _⟩ = _
  have he := descTotal_inclusion_apply Q h i x.obj ⟨x.val,p⟩
  apply (ElementFamilies.fiberTotalEquiv (base (Y := Y)).obj Q.family.family _).symm.injective
  rw [Equiv.symm_apply_apply]
  apply Subtype.ext
  exact he

lemma descFamily_total (x : (base (Y := Y)).obj.Elements)
    (p : (torsor P).family.family.obj x) :
    (⟨x.val, (descFamily Q h).app x p⟩ : (SplitSheaf.extension Q.family).obj.obj x.obj) =
      (descTotal Q h).hom.app x.obj p.val := by
  exact congrArg Subtype.val ((ElementFamilies.fiberTotalEquiv
    (base (Y := Y)).obj Q.family.family x).symm_apply_apply
      ((ElementFamilies.fiberFunctor (base (Y := Y)).obj).map
        (show Over.mk (projection P).hom ⟶ Over.mk (SplitSheaf.p Q.family).hom from
          Over.homMk (descTotal Q h).hom
            (congrArg (fun f => f.hom) (descTotal_projection Q h))) |>.app x <| p))

def descEquivariant : EquivariantMap (torsor P) Q where
  hom := descFamily Q h
  equivariant x g p := by
    have hh := descTotal_action Q h x.obj g p.val
    change (descTotal Q h).hom.app x.obj ((torsor P).act x g p).val = _ at hh
    rw [← descFamily_total, ← descFamily_total] at hh
    exact eq_of_heq (Sigma.mk.inj_iff.mp hh).2

/-- Every family of equivariant local arrows assembles to an actual torsor arrow. -/
def desc : torsor P ⟶ Q := (descEquivariant Q h).toArrow

lemma desc_component (i : I) :
    (component P i).hom ≫ (desc Q h).reindex (Sigma.ι Y i) = h i := by
  apply Arrow.ext
  apply NatTrans.ext
  funext x
  apply ConcreteCategory.hom_ext
  intro p
  exact descFamily_component Q h i x p

/-- Restriction to all summands retains every torsor arrow. -/
lemma arrow_ext {S T : Torsor G (base (Y := Y))} (a b : S ⟶ T)
    (h : ∀ i, a.reindex (Sigma.ι Y i) = b.reindex (Sigma.ι Y i)) : a = b := by
  apply Arrow.ext
  apply NatTrans.ext
  funext x
  apply ConcreteCategory.hom_ext
  intro p
  apply Descent.fiber_ext T.family x _ (SheafCoproductLocal.liftSieve_cover Y x.val)
  rintro V k ⟨i,y,hy⟩
  rw [← NatTrans.naturality_apply, ← NatTrans.naturality_apply]
  have atLift (z : (base (Y := Y)).obj.obj (op V))
      (q : S.family.family.obj ((base (Y := Y)).obj.elementsMk (op V) z))
      (hz : (Sigma.ι Y i).hom.app (op V) y = z) :
      a.iso.hom.app _ q = b.iso.hom.app _ q := by
    subst z
    exact congrArg (fun t : reindex S (Sigma.ι Y i) ⟶ reindex T (Sigma.ι Y i) =>
      t.iso.hom.app ((Y i).obj.elementsMk (op V) y) q) (h i)
  exact atLift _ _ hy

/-- Product restriction uses the existing strict reindexing on all maps. -/
def restrict : Torsor G (base (Y := Y)) ⥤ (∀ i, Torsor G (Y i)) where
  obj S i := reindex S (Sigma.ι Y i)
  map a i := a.reindex (Sigma.ι Y i)
  map_id _ := rfl
  map_comp _ _ := rfl

instance restrict_faithful : (restrict (G := G) (Y := Y)).Faithful where
  map_injective h := arrow_ext _ _ (congrFun h)

/-- Assembly of the restrictions maps back to the original torsor. -/
def recovery (S : Torsor G (base (Y := Y))) :
    torsor (fun i => reindex S (Sigma.ι Y i)) ≅ S :=
  (desc S (fun _ => 𝟙 _)).toIso

lemma component_recovery (S : Torsor G (base (Y := Y))) (i : I) :
    (component (fun i => reindex S (Sigma.ι Y i)) i).hom ≫
      (recovery S).hom.reindex (Sigma.ι Y i) = 𝟙 _ := desc_component _ _ _

instance restrict_full : (restrict (G := G) (Y := Y)).Full where
  map_surjective {S T} h := by
    refine ⟨(recovery S).inv ≫ desc T h, ?_⟩
    funext i
    have hi := component_recovery S i
    have hj := desc_component T h i
    have he : (recovery S).inv.reindex (Sigma.ι Y i) =
        (component (fun i => reindex S (Sigma.ι Y i)) i).hom := by
      apply (cancel_mono (C := Torsor G (Y i)) ((recovery S).hom.reindex (Sigma.ι Y i))).mp
      rw [hi]
      exact congrArg (fun a => a.reindex (Sigma.ι Y i)) (recovery S).inv_hom_id
    change ((recovery S).inv.reindex (Sigma.ι Y i)) ≫
      (desc T h).reindex (Sigma.ι Y i) = h i
    rw [he]
    exact hj

instance restrict_essSurj : (restrict (G := G) (Y := Y)).EssSurj where
  mem_essImage P := ⟨torsor P, ⟨{
    hom i := (component P i).inv
    inv i := (component P i).hom
    hom_inv_id := by funext i; exact (component P i).inv_hom_id
    inv_hom_id := by funext i; exact (component P i).hom_inv_id }⟩⟩

instance restrict_isEquivalence : (restrict (G := G) (Y := Y)).IsEquivalence := {}

/-- Effective coproduct assembly, including all arrows and empty-index families. -/
def equivalence : Torsor G (base (Y := Y)) ≌ (∀ i, Torsor G (Y i)) :=
  (restrict (G := G) (Y := Y)).asEquivalence

end SquareKit.SheafTorsor.Coproduct
