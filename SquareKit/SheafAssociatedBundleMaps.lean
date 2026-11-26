import SquareKit.SheafAssociatedBundle

/-! Associated maps retain noninvertible fiber maps and arbitrary group changes. -/
noncomputable section
set_option autoImplicit false
namespace SquareKit.SheafAssociatedBundle
open CategoryTheory Opposite ElementFamilies
universe u v
variable {C : Type u} [Category.{v} C] {J : GrothendieckTopology C}
  {G H K : Sheaf J GrpCat.{max u v}} {M N L : Sheaf J (Type (max u v))}
  {X : Sheaf J (Type (max u v))}

/-- A map of acted-on sheaves, equivariant along a given group homomorphism. -/
structure ActionMap (φ : G ⟶ H) (a : SheafActionQuotient.Action G M)
    (b : SheafActionQuotient.Action H N) where
  hom : M ⟶ N
  equivariant (U : Cᵒᵖ) (g : G.obj.obj U) (m : M.obj.obj U) :
    hom.hom.app U (a.act U g m) = b.act U (φ.hom.app U g) (hom.hom.app U m)

@[ext] theorem ActionMap.ext {φ : G ⟶ H} {a : SheafActionQuotient.Action G M}
    {b : SheafActionQuotient.Action H N} (f g : ActionMap φ a b)
    (h : f.hom = g.hom) : f = g := by cases f; cases g; cases h; rfl

def ActionMap.ident (a : SheafActionQuotient.Action G M) : ActionMap (𝟙 G) a a where
  hom := 𝟙 M
  equivariant _ _ _ := rfl

def ActionMap.comp {φ : G ⟶ H} {ψ : H ⟶ K}
    {a : SheafActionQuotient.Action G M} {b : SheafActionQuotient.Action H N}
    {c : SheafActionQuotient.Action K L} (f : ActionMap φ a b) (g : ActionMap ψ b c) :
    ActionMap (φ ≫ ψ) a c where
  hom := f.hom ≫ g.hom
  equivariant U h m := by
    change g.hom.hom.app U (f.hom.hom.app U (a.act U h m)) = _
    rw [f.equivariant, g.equivariant]
    rfl

variable {φ : G ⟶ H} {ψ : H ⟶ K}
  {P : SheafTorsor.Torsor G X} {Q : SheafTorsor.Torsor H X} {R : SheafTorsor.Torsor K X}
  {a : SheafActionQuotient.Action G M} {b : SheafActionQuotient.Action H N}
  {c : SheafActionQuotient.Action K L}

/-- Compatible maps of torsors and fibers induce an invariant map of pairs. -/
def mapPairs (f : SheafTorsor.SemilinearMap φ P Q) (g : ActionMap φ a b) :
    InvariantMap P a (associated Q b) where
  value x p m := classOf Q b x (f.hom.app x p) (g.hom.hom.app x.obj m)
  natural k p m := by
    rw [classOf_natural, ← NatTrans.naturality_apply, ← NatTrans.naturality_apply]
  invariant x h p m := by rw [f.equivariant, g.equivariant, classOf_diagonal]

/-- The induced map need not be invertible: its fiber map may identify points. -/
def map (f : SheafTorsor.SemilinearMap φ P Q) (g : ActionMap φ a b) :
    associated P a ⟶ associated Q b := (mapPairs f g).descend

@[simp] theorem map_classOf (f : SheafTorsor.SemilinearMap φ P Q) (g : ActionMap φ a b)
    (x : X.obj.Elements) (p : P.family.family.obj x) (m : M.obj.obj x.obj) :
    (map f g).app x (classOf P a x p m) =
      classOf Q b x (f.hom.app x p) (g.hom.hom.app x.obj m) :=
  (mapPairs f g).descend_classOf x p m

theorem map_id : map (SheafTorsor.SemilinearMap.ident P) (ActionMap.ident a) = 𝟙 (associated P a) := by
  apply hom_ext
  intro x p m
  exact map_classOf _ _ x p m

theorem map_comp (f : SheafTorsor.SemilinearMap φ P Q) (g : ActionMap φ a b)
    (h : SheafTorsor.SemilinearMap ψ Q R) (k : ActionMap ψ b c) :
    map (f.comp h) (g.comp k) = map f g ≫ map h k := by
  apply hom_ext
  intro x p m
  change (map (f.comp h) (g.comp k)).app x (classOf P a x p m) =
    (map h k).app x ((map f g).app x (classOf P a x p m))
  rw [map_classOf, map_classOf, map_classOf]
  rfl

/-- Equivariant maps from the torsor total, with no associated display supplied. -/
def EquivariantTarget (P : SheafTorsor.Torsor G X) (a : SheafActionQuotient.Action G M) :=
  { F : SplitSheaf.extension P.family ⟶ M // ∀ x g p,
    F.hom.app x.obj ⟨x.val,P.act x g p⟩ = a.act x.obj g (F.hom.app x.obj ⟨x.val,p⟩) }

open SplitFunctionDiagram SplitSheafDescent in
set_option backward.isDefEq.respectTransparency false in
/-- An equivariant target gives a section by its compatible values on every lift. -/
def targetSection (F : EquivariantTarget P a) : SplitSheaf.Tm (associated P a) where
  val x := ⟨(SplitSheafPi.lam P.family (SplitSheaf.constantTerm M F.val)).val x, by
    intro y f p q
    have hn := (SplitSheafPi.lam P.family (SplitSheaf.constantTerm M F.val)).natural f
    change restrict _ _ f _ = _ at hn
    erw [hn, evaluate_lam]
    change a.act y.obj (SheafTorsor.fiberDifference P y p q)
      (F.val.hom.app y.obj ⟨y.val,p⟩) = F.val.hom.app y.obj ⟨y.val,q⟩
    rw [← F.property, SheafTorsor.fiberDifference_act]⟩
  natural f := Subtype.ext ((SplitSheafPi.lam P.family (SplitSheaf.constantTerm M F.val)).natural f)

theorem evaluate_targetSection (F : EquivariantTarget P a) (x : X.obj.Elements)
    (p : P.family.family.obj x) :
    evaluate P a x p ((targetSection F).val x) = F.val.hom.app x.obj ⟨x.val,p⟩ :=
  congrFun (SplitFunctionDiagram.evaluate_lam P.family.family
    (SplitSheaf.constantTerm M F.val) x) p

/-- Evaluation of a section gives an actual equivariant map from the torsor total. -/
def sectionTarget (s : SplitSheaf.Tm (associated P a)) : EquivariantTarget P a := ⟨⟨{
  app U := ↾fun z => evaluate P a (X.obj.elementsMk U z.1) z.2
    (s.val (X.obj.elementsMk U z.1))
  naturality {U V} f := by
    ext z
    have h := evaluate_natural P a (along X.obj f z.1) z.2
      (s.val (X.obj.elementsMk U z.1))
    rw [s.natural] at h
    exact h }⟩, by
  intro x g p
  change evaluate P a x (P.act x g p) (s.val x) = a.act x.obj g (evaluate P a x p (s.val x))
  rw [evaluate_change P a x p, SheafTorsor.fiberDifference_act_self]⟩

/-- Sections agree when their values at all local torsor lifts agree. -/
theorem section_ext (s t : SplitSheaf.Tm (associated P a))
    (h : ∀ x p, evaluate P a x p (s.val x) = evaluate P a x p (t.val x)) : s = t := by
  apply SplitPresheaf.Tm.ext
  funext x
  apply Subtype.ext
  apply SplitSheafDescent.value_ext
  intro y f p
  change evaluate P a y p ((associated P a).family.map f (s.val x)) =
    evaluate P a y p ((associated P a).family.map f (t.val x))
  exact (congrArg (evaluate P a y p) (s.natural f)).trans
    ((h y p).trans (congrArg (evaluate P a y p) (t.natural f)).symm)

/-- Equivariant target maps and associated-display sections are different presentations
of the same data for a fixed torsor. -/
def targetSectionEquiv : EquivariantTarget P a ≃ SplitSheaf.Tm (associated P a) where
  toFun := targetSection
  invFun := sectionTarget
  left_inv F := by
    apply Subtype.ext
    ext U z
    exact evaluate_targetSection F (X.obj.elementsMk U z.1) z.2
  right_inv s := by
    apply section_ext
    intro x p
    exact evaluate_targetSection (sectionTarget s) x p

/-- The existing action-quotient object determines its associated section. -/
def objectSection (F : SheafActionQuotient.Object a X) : SplitSheaf.Tm (associated F.torsor a) :=
  targetSection ⟨F.totalMap, F.equivariant⟩

theorem objectSection_value (F : SheafActionQuotient.Object a X) (x : X.obj.Elements)
    (p : F.torsor.family.family.obj x) :
    evaluate F.torsor a x p ((objectSection F).val x) = F.value x p :=
  evaluate_targetSection ⟨F.totalMap, F.equivariant⟩ x p

set_option backward.isDefEq.respectTransparency false in
/-- With a fixed action, association is a functor on every torsor arrow. -/
def functor (a : SheafActionQuotient.Action G M) (X : Sheaf J (Type (max u v))) :
    SheafTorsor.Torsor G X ⥤ SplitSheaf.Ty X where
  obj P := associated P a
  map f := map (SheafTorsor.SemilinearMap.ofArrow f) (ActionMap.ident a)
  map_id P := by
    apply hom_ext
    intro x p m
    exact map_classOf _ _ x p m
  map_comp f g := map_comp (SheafTorsor.SemilinearMap.ofArrow f) (ActionMap.ident a)
    (SheafTorsor.SemilinearMap.ofArrow g) (ActionMap.ident a)

@[simp] theorem functor_map_classOf {P Q : SheafTorsor.Torsor G X}
    (f : P ⟶ Q) (x : X.obj.Elements)
    (p : P.family.family.obj x) (m : M.obj.obj x.obj) :
    ((functor a X).map f).app x (classOf P a x p m) = classOf Q a x (f.iso.hom.app x p) m :=
  map_classOf _ _ x p m


/-- The regular left action on the underlying group sheaf. -/
def regularAction (G : Sheaf J GrpCat.{max u v}) :
    SheafActionQuotient.Action G (SheafTorsor.groupSheaf G) where
  act U g h := g * (show G.obj.obj U from h)
  one_act U m := one_mul (show G.obj.obj U from m)
  mul_act U g h m := mul_assoc g h (show G.obj.obj U from m)
  natural f g h := (G.obj.map f).hom.map_mul g h

set_option backward.isDefEq.respectTransparency false in
/-- The regular associated fiber recovers the torsor with the diagonal convention. -/
def regularRecoveryPairs (P : SheafTorsor.Torsor G X) :
    InvariantMap P (regularAction G) P.family where
  value x p m := P.act x (show G.obj.obj x.obj from m)⁻¹ p
  natural f p m := by
    rw [P.natural, (G.obj.map f.hom).hom.map_inv]
    rfl
  invariant x g p m := by
    change G.obj.obj x.obj at m
    change P.act x (g * m)⁻¹ (P.act x g p) = P.act x m⁻¹ p
    rw [← P.mul_act, mul_inv_rev, mul_assoc, inv_mul_cancel, mul_one]

def regularRecoveryMap (P : SheafTorsor.Torsor G X) :
    associated P (regularAction G) ⟶ P.family := (regularRecoveryPairs P).descend

@[simp] theorem regularRecoveryMap_classOf (P : SheafTorsor.Torsor G X)
    (x : X.obj.Elements) (p : P.family.family.obj x) (m : G.obj.obj x.obj) :
    (regularRecoveryMap P).app x (classOf P (regularAction G) x p m) = P.act x m⁻¹ p :=
  (regularRecoveryPairs P).descend_classOf x p m

set_option backward.isDefEq.respectTransparency false in
theorem regularRecoveryMap_evaluate (P : SheafTorsor.Torsor G X)
    (x : X.obj.Elements) (p : P.family.family.obj x)
    (s : (associated P (regularAction G)).family.obj x) :
    (regularRecoveryMap P).app x s =
      P.act x (show G.obj.obj x.obj from evaluate P (regularAction G) x p s)⁻¹ p := by
  conv_lhs => rw [← classOf_evaluate P (regularAction G) x p s]
  exact regularRecoveryMap_classOf P x p _

set_option backward.isDefEq.respectTransparency false in
instance regularRecoveryMap_isIso (P : SheafTorsor.Torsor G X) : IsIso (regularRecoveryMap P) := by
  have hi : @IsIso (X.obj.Elements ⥤ Type (max u v)) _ _ _ (regularRecoveryMap P) := by
    apply SplitSheafDescent.isIso_of_local_bijective P.family
    intro x p
    constructor
    · intro s t h
      apply (evaluate P (regularAction G) x p).injective
      have he := (regularRecoveryMap_evaluate P x p s).symm.trans
        (h.trans (regularRecoveryMap_evaluate P x p t))
      have hi : (show G.obj.obj x.obj from evaluate P (regularAction G) x p s)⁻¹ =
          (show G.obj.obj x.obj from evaluate P (regularAction G) x p t)⁻¹ :=
        (SheafTorsor.fiberEquiv P x p).injective he
      have hh := congrArg (fun z : G.obj.obj x.obj => z⁻¹) hi
      simpa only [inv_inv] using hh
    · intro q
      refine ⟨classOf P (regularAction G) x p ((SheafTorsor.fiberDifference P x p q)⁻¹ : G.obj.obj x.obj), ?_⟩
      rw [regularRecoveryMap_classOf, inv_inv, SheafTorsor.fiberDifference_act]
  let e := SplitSheaf.isoMk (asIso (show (associated P (regularAction G)).family ⟶ P.family.family
    from regularRecoveryMap P))
  exact ⟨⟨e.inv, e.hom_inv_id, e.inv_hom_id⟩⟩

/-- Regular associated fibers recover the actual torsor display, including its projection. -/
def regularIso (P : SheafTorsor.Torsor G X) : associated P (regularAction G) ≅ P.family :=
  asIso (regularRecoveryMap P)

/-- Every sheaf admits the trivial group action, without inhabitedness assumptions. -/
def trivialAction (G : Sheaf J GrpCat.{max u v}) (M : Sheaf J (Type (max u v))) :
    SheafActionQuotient.Action G M where
  act _ _ m := m
  one_act _ _ := rfl
  mul_act _ _ _ _ := rfl
  natural _ _ _ := rfl

def trivialRecoveryPairs (P : SheafTorsor.Torsor G X) (M : Sheaf J (Type (max u v))) :
    InvariantMap P (trivialAction G M) (SplitSheaf.constant M X) where
  value _ _ m := m
  natural _ _ _ := rfl
  invariant _ _ _ _ := rfl

def trivialRecoveryMap (P : SheafTorsor.Torsor G X) (M : Sheaf J (Type (max u v))) :
    associated P (trivialAction G M) ⟶ SplitSheaf.constant M X := (trivialRecoveryPairs P M).descend

@[simp] theorem trivialRecoveryMap_classOf (P : SheafTorsor.Torsor G X)
    (M : Sheaf J (Type (max u v))) (x : X.obj.Elements) (p : P.family.family.obj x)
    (m : M.obj.obj x.obj) :
    (trivialRecoveryMap P M).app x (classOf P (trivialAction G M) x p m) = m :=
  (trivialRecoveryPairs P M).descend_classOf x p m

set_option backward.isDefEq.respectTransparency false in
instance trivialRecoveryMap_isIso (P : SheafTorsor.Torsor G X) (M : Sheaf J (Type (max u v))) :
    IsIso (trivialRecoveryMap P M) := by
  have hi : @IsIso (X.obj.Elements ⥤ Type (max u v)) _ _ _ (trivialRecoveryMap P M) := by
    apply SplitSheafDescent.isIso_of_local_bijective P.family
    intro x p
    have he : ∀ s, (trivialRecoveryMap P M).app x s = evaluate P (trivialAction G M) x p s := by
      intro s
      conv_lhs => rw [← classOf_evaluate P (trivialAction G M) x p s]
      exact trivialRecoveryMap_classOf P M x p _
    constructor
    · intro s t h
      apply (evaluate P (trivialAction G M) x p).injective
      rw [← he s, ← he t, h]
    · intro m
      exact ⟨classOf P (trivialAction G M) x p m, trivialRecoveryMap_classOf P M x p m⟩
  let e := SplitSheaf.isoMk (asIso (show
    (associated P (trivialAction G M)).family ⟶ (SplitSheaf.constant M X).family
      from trivialRecoveryMap P M))
  exact ⟨⟨e.inv, e.hom_inv_id, e.inv_hom_id⟩⟩

/-- A trivial fiber action recovers the constant display for any sheaf fiber. -/
def trivialIso (P : SheafTorsor.Torsor G X) (M : Sheaf J (Type (max u v))) :
    associated P (trivialAction G M) ≅ SplitSheaf.constant M X := asIso (trivialRecoveryMap P M)

set_option backward.isDefEq.respectTransparency false in
/-- Recovery of the regular fiber preserves every torsor arrow. -/
theorem regularIso_natural {P Q : SheafTorsor.Torsor G X} (f : P ⟶ Q) :
    (functor (regularAction G) X).map f ≫ (regularIso Q).hom =
      (regularIso P).hom ≫ f.iso.hom := by
  apply hom_ext
  intro x p m
  change (regularRecoveryMap Q).app x
    (((functor (regularAction G) X).map f).app x (classOf P (regularAction G) x p m)) =
    f.iso.hom.app x ((regularRecoveryMap P).app x (classOf P (regularAction G) x p m))
  rw [functor_map_classOf, regularRecoveryMap_classOf, regularRecoveryMap_classOf]
  exact (f.equivariant x _ p).symm

/-- Trivial-fiber recovery also preserves all torsor arrows. -/
theorem trivialIso_natural {P Q : SheafTorsor.Torsor G X} (f : P ⟶ Q)
    (M : Sheaf J (Type (max u v))) :
    (functor (trivialAction G M) X).map f ≫ (trivialIso Q M).hom = (trivialIso P M).hom := by
  apply hom_ext
  intro x p m
  change (trivialRecoveryMap Q M).app x
    (((functor (trivialAction G M) X).map f).app x (classOf P (trivialAction G M) x p m)) =
    (trivialRecoveryMap P M).app x (classOf P (trivialAction G M) x p m)
  rw [functor_map_classOf, trivialRecoveryMap_classOf, trivialRecoveryMap_classOf]

/-- Postcomposition of a section by an arbitrary display map. -/
def mapSection {A B : SplitSheaf.Ty X} (f : A ⟶ B) (s : SplitSheaf.Tm A) : SplitSheaf.Tm B where
  val x := f.app x (s.val x)
  natural k := (NatTrans.naturality_apply f k _).symm.trans (congrArg (f.app _) (s.natural k))

set_option backward.isDefEq.respectTransparency false in
theorem evaluate_map (f : SheafTorsor.SemilinearMap φ P Q) (g : ActionMap φ a b)
    (x : X.obj.Elements) (p : P.family.family.obj x) (s : (associated P a).family.obj x) :
    evaluate Q b x (f.hom.app x p) ((map f g).app x s) =
      g.hom.hom.app x.obj (evaluate P a x p s) := by
  conv_lhs => rw [← classOf_evaluate P a x p s]
  rw [map_classOf, evaluate_classOf]

/-- A locally inhabited source torsor supplies enough local lifts to compare sections,
even when the group-changing map is not surjective. -/
theorem section_ext_along (f : SheafTorsor.SemilinearMap φ P Q)
    (s t : SplitSheaf.Tm (associated Q b))
    (h : ∀ x p, evaluate Q b x (f.hom.app x p) (s.val x) =
      evaluate Q b x (f.hom.app x p) (t.val x)) : s = t := by
  apply SplitPresheaf.Tm.ext
  funext x
  apply SplitSheafDescent.fiber_ext (associated Q b) x
    (Presheaf.imageSieve (SplitSheaf.p P.family).hom x.val)
    (Presheaf.imageSieve_mem J (SplitSheaf.p P.family).hom x.val)
  rintro V k ⟨⟨z,p⟩,hz⟩
  change z = X.obj.map k.op x.val at hz
  subst z
  rw [s.natural, t.natural]
  exact (evaluate Q b _ (f.hom.app _ p)).injective (h _ p)

/-- The section bridge preserves all compatible torsor and fiber maps. -/
theorem targetSection_natural (f : SheafTorsor.SemilinearMap φ P Q) (g : ActionMap φ a b)
    (F : EquivariantTarget P a) (E : EquivariantTarget Q b)
    (h : ∀ x p, E.val.hom.app x.obj ⟨x.val,f.hom.app x p⟩ =
      g.hom.hom.app x.obj (F.val.hom.app x.obj ⟨x.val,p⟩)) :
    mapSection (map f g) (targetSection F) = targetSection E := by
  apply section_ext_along f
  intro x p
  change evaluate Q b x (f.hom.app x p) ((map f g).app x ((targetSection F).val x)) = _
  rw [evaluate_map, evaluate_targetSection, evaluate_targetSection]
  exact (h x p).symm

/-- In particular, every arrow of the existing action-quotient category preserves
its associated section. -/
theorem objectSection_natural {F E : SheafActionQuotient.Object a X}
    (h : F ⟶ E) :
    mapSection ((functor a X).map h.torsorArrow) (objectSection F) = objectSection E :=
  targetSection_natural (SheafTorsor.SemilinearMap.ofArrow h.torsorArrow) (ActionMap.ident a)
    ⟨F.totalMap,F.equivariant⟩ ⟨E.totalMap,E.equivariant⟩ h.preserves

end SquareKit.SheafAssociatedBundle
