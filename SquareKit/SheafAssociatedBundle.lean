import SquareKit.SheafTorsorSemilinear
import SquareKit.SheafActionQuotient
import SquareKit.SplitSheafDescent

/-! Associated sheaf displays constructed by descent along the torsor itself. -/
noncomputable section
set_option autoImplicit false
namespace SquareKit.SheafAssociatedBundle
open CategoryTheory Opposite ElementFamilies SplitSheafDescent SplitFunctionDiagram
universe u v
variable {C : Type u} [Category.{v} C] {J : GrothendieckTopology C}
  {G : Sheaf J GrpCat.{max u v}} {M : Sheaf J (Type (max u v))}
  {X : Sheaf J (Type (max u v))}
variable (P : SheafTorsor.Torsor G X) (a : SheafActionQuotient.Action G M)

/-- The fiber before descent is the actual sheaf M over the torsor total. -/
abbrev localFamily := SplitSheaf.constant M (SplitSheaf.extension P.family)

set_option backward.isDefEq.respectTransparency false in
/-- Local values change by the unique group element changing the torsor lift. -/
def datum : Datum P.family (localFamily P (M := M)) where
  transport x p q m := a.act x.obj (SheafTorsor.fiberDifference P x p q) m
  identity x p m := by
    rw [SheafTorsor.fiberDifference_self, a.one_act]
  cocycle x p q r m := by
    rw [← a.mul_act, ← SheafTorsor.fiberDifference_comp]
  natural f p q m := by
    change M.obj.map f.hom (a.act _ _ m) = _
    rw [a.natural, SheafTorsor.fiberDifference_natural]
    rfl

/-- The associated display is a sheaf of compatible values at every restriction stage. -/
def associated : SplitSheaf.Ty X := family (datum P a)

/-- A torsor lift identifies the associated fiber with M, without choosing a global lift. -/
def evaluate (x : X.obj.Elements) (p : P.family.family.obj x) :
    (associated P a).family.obj x ≃ M.obj.obj x.obj :=
  evaluationEquiv (datum P a) x p

/-- The class of a pair, expressed in the constructed sheaf. -/
def classOf (x : X.obj.Elements) (p : P.family.family.obj x) (m : M.obj.obj x.obj) :
    (associated P a).family.obj x := (evaluate P a x p).symm m

@[simp] theorem evaluate_classOf (x : X.obj.Elements) (p : P.family.family.obj x)
    (m : M.obj.obj x.obj) : evaluate P a x p (classOf P a x p m) = m :=
  (evaluate P a x p).apply_symm_apply m

@[simp] theorem classOf_evaluate (x : X.obj.Elements) (p : P.family.family.obj x)
    (s : (associated P a).family.obj x) :
    classOf P a x p (evaluate P a x p s) = s := (evaluate P a x p).symm_apply_apply s

/-- Evaluation at another lift uses the specified action, including its order. -/
theorem evaluate_change (x : X.obj.Elements) (p q : P.family.family.obj x)
    (s : (associated P a).family.obj x) :
    evaluate P a x q s =
      a.act x.obj (SheafTorsor.fiberDifference P x p q) (evaluate P a x p s) :=
  (s.property.evaluate p q).symm

/-- Associated classes identify the diagonal left action on both entries. -/
theorem classOf_diagonal (x : X.obj.Elements) (g : G.obj.obj x.obj)
    (p : P.family.family.obj x) (m : M.obj.obj x.obj) :
    classOf P a x (P.act x g p) (a.act x.obj g m) = classOf P a x p m := by
  apply (evaluate P a x (P.act x g p)).injective
  rw [evaluate_classOf, evaluate_change P a x p, evaluate_classOf]
  rw [SheafTorsor.fiberDifference_eq P x p (P.act x g p) g rfl]

/-- Evaluation is natural on all arrows in the base category of elements. -/
theorem evaluate_natural {x y : X.obj.Elements} (f : x ⟶ y)
    (p : P.family.family.obj x) (s : (associated P a).family.obj x) :
    evaluate P a y (P.family.family.map f p) ((associated P a).family.map f s) =
      M.obj.map f.hom (evaluate P a x p s) := by
  exact NatTrans.naturality_apply (evaluationIso (datum P a)).hom
    (pairArrow P.family.family f p) s

/-- Quotient representatives restrict by restricting both components. -/
theorem classOf_natural {x y : X.obj.Elements} (f : x ⟶ y)
    (p : P.family.family.obj x) (m : M.obj.obj x.obj) :
    (associated P a).family.map f (classOf P a x p m) =
      classOf P a y (P.family.family.map f p) (M.obj.map f.hom m) := by
  apply (evaluate P a y (P.family.family.map f p)).injective
  rw [evaluate_natural, evaluate_classOf, evaluate_classOf]

/-- The actual quotient map has domain the total constant family, hence P.total × M. -/
def quotient : SplitSheaf.extension (localFamily P (M := M)) ⟶ SplitSheaf.extension (associated P a) := ⟨{
  app U := ↾fun z => ⟨z.1.1, classOf P a (X.obj.elementsMk U z.1.1) z.1.2 z.2⟩
  naturality {U V} f := by
    ext z
    exact congrArg (Sigma.mk _) (classOf_natural P a (along X.obj f z.1.1) z.1.2 z.2).symm }⟩

@[simp] theorem quotient_projection : quotient P a ≫ SplitSheaf.p (associated P a) =
    SplitSheaf.p (localFamily P (M := M)) ≫ SplitSheaf.p P.family := rfl

set_option backward.isDefEq.respectTransparency false in
/-- Every associated section is locally represented by an actual pair. -/
instance quotient_locallySurjective : Presheaf.IsLocallySurjective J (quotient P a).hom where
  imageSieve_mem {U} z := by
    have h := Presheaf.imageSieve_mem J (SplitSheaf.p P.family).hom z.1
    apply J.superset_covering _ h
    intro V k hk
    obtain ⟨⟨y,p⟩,hy⟩ := hk
    change y = X.obj.map k.op z.1 at hy
    subst y
    let x := X.obj.elementsMk (op V) (X.obj.map k.op z.1)
    let s := (associated P a).family.map (along X.obj k.op z.1) z.2
    refine ⟨⟨⟨x.val,p⟩, evaluate P a x p s⟩, ?_⟩
    change (⟨x.val, classOf P a x p (evaluate P a x p s)⟩ :
      (SplitSheaf.extension (associated P a)).obj.obj (op V)) = ⟨x.val,s⟩
    rw [classOf_evaluate]

/-- An invariant map of pairs with values in an arbitrary sheaf display. -/
structure InvariantMap (Y : SplitSheaf.Ty X) where
  value (x : X.obj.Elements) : P.family.family.obj x → M.obj.obj x.obj → Y.family.obj x
  natural {x y : X.obj.Elements} (f : x ⟶ y) (p : P.family.family.obj x)
    (m : M.obj.obj x.obj) :
    Y.family.map f (value x p m) = value y (P.family.family.map f p) (M.obj.map f.hom m)
  invariant (x : X.obj.Elements) (g : G.obj.obj x.obj)
    (p : P.family.family.obj x) (m : M.obj.obj x.obj) :
    value x (P.act x g p) (a.act x.obj g m) = value x p m

@[ext] theorem InvariantMap.ext {Y : SplitSheaf.Ty X} (f g : InvariantMap P a Y)
    (h : f.value = g.value) : f = g := by cases f; cases g; cases h; rfl

variable {P a}

set_option backward.isDefEq.respectTransparency false in
/-- The invariant map supplies an all-map morphism of the actual descent data. -/
def InvariantMap.datumMap {Y : SplitSheaf.Ty X} (f : InvariantMap P a Y) :
    Map (datum P a) (canonicalDatum P.family Y) where
  hom := {
    app z := ↾fun m => f.value (X.obj.elementsMk z.obj z.val.1) z.val.2 m
    naturality {z w} k := by
      ext m
      rcases z with @⟨U, x, p⟩
      rcases w with @⟨V, y, q⟩
      rcases k with ⟨k, hk⟩
      change U ⟶ V at k
      have hx : X.obj.map k x = y := congrArg Sigma.fst hk
      subst y
      have hp : P.family.family.map (along X.obj k x) p = q :=
        eq_of_heq (Sigma.mk.inj_iff.mp hk).2
      subst q
      exact (f.natural (along X.obj k x) p m).symm }
  transport x p q m := by
    change f.value x q (a.act x.obj (SheafTorsor.fiberDifference P x p q) m) = f.value x p m
    simpa only [SheafTorsor.fiberDifference_act] using
      f.invariant x (SheafTorsor.fiberDifference P x p q) p m

/-- Descent constructs the unique map induced by an invariant pair map. -/
def InvariantMap.descend {Y : SplitSheaf.Ty X} (f : InvariantMap P a Y) :
    associated P a ⟶ Y := f.datumMap.descend ≫ (canonicalRecovery P.family Y).inv

set_option backward.isDefEq.respectTransparency false in
theorem InvariantMap.descend_classOf {Y : SplitSheaf.Ty X} (f : InvariantMap P a Y)
    (x : X.obj.Elements) (p : P.family.family.obj x) (m : M.obj.obj x.obj) :
    f.descend.app x (classOf P a x p m) = f.value x p m := by
  let e := canonicalRecovery P.family Y
  have hh := congrArg (fun k => k.app x (f.datumMap.descend.app x (classOf P a x p m)))
    e.inv_hom_id
  have he := congrArg (evaluationEquiv (canonicalDatum P.family Y) x p) hh
  change evaluationEquiv (canonicalDatum P.family Y) x p
      ((canonicalFamilyMap P.family Y).app x
        (e.inv.app x (f.datumMap.descend.app x (classOf P a x p m)))) =
    evaluationEquiv (canonicalDatum P.family Y) x p
      (f.datumMap.descend.app x (classOf P a x p m)) at he
  rw [canonicalFamilyMap_evaluate, Map.evaluation] at he
  change f.descend.app x (classOf P a x p m) =
    f.value x p (evaluate P a x p (classOf P a x p m)) at he
  rw [evaluate_classOf] at he
  exact he

/-- Every map out of the associated display is determined by its pair classes,
even when the torsor has no section at the current stage. -/
theorem hom_ext {Y : SplitSheaf.Ty X} (f g : associated P a ⟶ Y)
    (h : ∀ (x : X.obj.Elements) (p : P.family.family.obj x) (m : M.obj.obj x.obj),
      f.app x (classOf P a x p m) = g.app x (classOf P a x p m)) : f = g := by
  apply NatTrans.ext
  funext x
  apply ConcreteCategory.hom_ext
  intro s
  apply fiber_ext Y x (Presheaf.imageSieve (SplitSheaf.p P.family).hom x.val)
    (Presheaf.imageSieve_mem J (SplitSheaf.p P.family).hom x.val)
  rintro V k ⟨⟨z,p⟩,hz⟩
  change z = X.obj.map k.op x.val at hz
  subst z
  let y := X.obj.elementsMk (op V) (X.obj.map k.op x.val)
  let l := along X.obj k.op x.val
  have he := h y p (evaluate P a y p ((associated P a).family.map l s))
  rw [classOf_evaluate] at he
  exact (NatTrans.naturality_apply f l s).symm.trans
    (he.trans (NatTrans.naturality_apply g l s))

/-- Precomposing a display map with the quotient produces its invariant pair map. -/
def precompose {Y : SplitSheaf.Ty X} (f : associated P a ⟶ Y) : InvariantMap P a Y where
  value x p m := f.app x (classOf P a x p m)
  natural k p m := by
    rw [← NatTrans.naturality_apply, classOf_natural]
  invariant x g p m := congrArg (f.app x) (classOf_diagonal P a x g p m)

theorem descend_precompose {Y : SplitSheaf.Ty X} (f : associated P a ⟶ Y) :
    (precompose f).descend = f := by
  apply hom_ext
  intro x p m
  exact (precompose f).descend_classOf x p m

theorem precompose_descend {Y : SplitSheaf.Ty X} (f : InvariantMap P a Y) :
    precompose f.descend = f := by
  apply InvariantMap.ext
  funext x p m
  exact f.descend_classOf x p m

/-- The quotient universal property retains every map to every sheaf display. -/
def universal (Y : SplitSheaf.Ty X) : (associated P a ⟶ Y) ≃ InvariantMap P a Y where
  toFun := precompose
  invFun := InvariantMap.descend
  left_inv := descend_precompose
  right_inv := precompose_descend

variable (P a)

/-- Pairs over a base section, with both entries restricted naturally. -/
def pairFamily : X.obj.Elements ⥤ Type (max u v) where
  obj x := P.family.family.obj x × M.obj.obj x.obj
  map f := ↾fun z => (P.family.family.map f z.1, M.obj.map f.hom z.2)
  map_id x := by ext z <;> simp
  map_comp f g := by ext z <;> simp [Functor.map_comp]

/-- The pair domain is the actual product with the torsor total, over X. -/
def pairTotalIso : SplitPresheaf.extension (pairFamily P (M := M)) ≅
    (SplitSheaf.extension (localFamily P (M := M))).obj where
  hom := { app U := ↾fun z => ⟨⟨z.1,z.2.1⟩,z.2.2⟩ }
  inv := { app U := ↾fun z => ⟨z.1.1,z.1.2,z.2⟩ }

/-- The quotient domain as a sheaf display, retaining every map. -/
def pairs : SplitSheaf.Ty X where
  family := pairFamily P (M := M)
  isSheaf := (Presheaf.isSheaf_of_iso_iff (J := J) (pairTotalIso P (M := M))).2
    (SplitSheaf.extension (localFamily P (M := M))).property

/-- The quotient is a map in the full category of sheaf displays. -/
def quotientMap : pairs P (M := M) ⟶ associated P a where
  app x := ↾fun z => classOf P a x z.1 z.2
  naturality {x y} f := by ext z; exact (classOf_natural P a f z.1 z.2).symm

/-- Invariance is a property of an actual natural map from the pair display. -/
def InvariantHom (Y : SplitSheaf.Ty X) :=
  { f : pairs P (M := M) ⟶ Y // ∀ x g p m,
      f.app x (P.act x g p, a.act x.obj g m) = f.app x (p,m) }

variable {P a}

set_option backward.isDefEq.respectTransparency false in
def invariantHomEquiv (Y : SplitSheaf.Ty X) : InvariantMap P a Y ≃ InvariantHom P a Y where
  toFun f := ⟨{
    app x := ↾fun z => f.value x z.1 z.2
    naturality {x y} k := by ext z; exact (f.natural k z.1 z.2).symm }, f.invariant⟩
  invFun f := {
    value x p m := f.val.app x (p,m)
    natural k p m := by
      have h := congrArg (fun t => t (p,m)) (f.val.naturality k)
      exact h.symm
    invariant := f.property }
  left_inv f := by apply InvariantMap.ext; rfl
  right_inv f := by apply Subtype.ext; rfl

/-- The constructed quotient has the universal property in the full sheaf-display category. -/
def quotientUniversal (Y : SplitSheaf.Ty X) :
    (associated P a ⟶ Y) ≃ InvariantHom P a Y :=
  (universal Y).trans (invariantHomEquiv Y)

theorem quotientUniversal_hom {Y : SplitSheaf.Ty X} (f : associated P a ⟶ Y) :
    (quotientUniversal Y f).val = quotientMap P a ≫ f := rfl

/-- Every invariant display arrow factors uniquely through the constructed quotient. -/
theorem quotient_existsUnique {Y : SplitSheaf.Ty X} (f : InvariantHom P a Y) :
    ∃! h : associated P a ⟶ Y, quotientMap P a ≫ h = f.val := by
  refine ⟨(quotientUniversal Y).symm f, ?_, ?_⟩
  · exact congrArg Subtype.val ((quotientUniversal Y).apply_symm_apply f)
  · intro h hh
    apply (quotientUniversal Y).injective
    apply Subtype.ext
    exact hh.trans (congrArg Subtype.val ((quotientUniversal Y).apply_symm_apply f)).symm

end SquareKit.SheafAssociatedBundle
