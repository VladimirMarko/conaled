import SquareKit.SheafGroupoidBundle

/-! The regular bundle of a generalized object, with all arrow fibers. -/
noncomputable section
set_option autoImplicit false
set_option warningAsError true
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
namespace SquareKit.SheafGroupoid.Bundle
open CategoryTheory Opposite
universe u v
variable {C : Type u} [Category.{v} C] {J : GrothendieckTopology C}
variable (G : Operations J) [G.Laws] {X : Sheaf J (Type (max u v))}

/-- The sheaf family of all arrows over their two endpoints. -/
def homFamily : SplitSheaf.Ty (SheafRelation.product G.objects G.objects) :=
  SplitSheaf.ofDisplay (SheafRelation.lift G.source G.target)

def regularFamily (m : G.Object X) : SplitSheaf.Ty (base G X) :=
  SplitSheaf.tySub (homFamily G) (SheafRelation.lift (SheafRelation.snd X G.objects)
    (SheafRelation.fst X G.objects ≫ m.map))

def value (m : G.Object X) (x : X.obj.Elements) : G.Section x.obj :=
  ⟨m.map.hom.app x.obj x.val⟩

/-- A regular fiber is exactly the full hom set into the given object. -/
def regularFiberEquiv (m : G.Object X) (x : X.obj.Elements) (n : G.Section x.obj) :
    Fiber G X (regularFamily G m) x n ≃ (n ⟶ value G m x) :=
  ({ toFun := fun p => ⟨p.val, congrArg Prod.fst p.property, congrArg Prod.snd p.property⟩
     invFun := fun p => ⟨p.val, Prod.ext p.property.1 p.property.2⟩
     left_inv := fun _ => rfl
     right_inv := fun _ => rfl } :
    Fiber G X (regularFamily G m) x n ≃
      {g : G.arrows.obj.obj x.obj //
        G.source.hom.app x.obj g = n.val ∧ G.target.hom.app x.obj g = (value G m x).val}).trans
    (G.sectionArrowEquiv n (value G m x)).symm

@[simp] theorem regularFiberEquiv_map (m : G.Object X) (x : X.obj.Elements)
    (n : G.Section x.obj) (p : Fiber G X (regularFamily G m) x n) :
    (regularFiberEquiv G m x n p).map = sectionEquiv.symm p.val := rfl

@[simp] theorem regularFiberEquiv_natural_map (m : G.Object X)
    {x y : X.obj.Elements} (f : x ⟶ y) (n : G.Section x.obj)
    (p : Fiber G X (regularFamily G m) x n) :
    (regularFiberEquiv G m y (n.restrict G f.hom)
      ((regularFamily G m).family.map (pointArrow G X f n) p)).map =
      (sectionParameter J).map f.hom.unop ≫ (regularFiberEquiv G m x n p).map := by
  apply sectionEquiv.injective
  rw [sectionEquiv_naturality]
  simp only [regularFiberEquiv_map]
  erw [sectionEquiv.apply_symm_apply, sectionEquiv.apply_symm_apply]
  rfl

/-- Right action on the regular bundle is composition of actual groupoid arrows. -/
def regularAction (m : G.Object X) : Action G X where
  family := regularFamily G m
  act x {n q} g p := (regularFiberEquiv G m x n).symm
    (g ≫ regularFiberEquiv G m x q p)
  act_id x n p := by simp
  act_comp x n q r g h p := by simp [Category.assoc]
  natural {x y} f n q g p := by
    apply (regularFiberEquiv G m y (n.restrict G f.hom)).injective
    apply Operations.Arrow.ext
    rw [regularFiberEquiv_natural_map]
    dsimp only [Operations.sectionRestriction]
    simp only [Equiv.apply_symm_apply]
    change (sectionParameter J).map f.hom.unop ≫
        (g.comp G (regularFiberEquiv G m x q p)).map =
      ((Operations.SectionArrow.restrict G f.hom g).comp G
        (regularFiberEquiv G m y (q.restrict G f.hom)
          ((regularFamily G m).family.map (pointArrow G X f q) p))).map
    simp only [Operations.Arrow.comp, Operations.SectionArrow.restrict_map,
      regularFiberEquiv_natural_map]
    rw [← Category.assoc]
    congr 1
    apply CategoryTheory.Limits.pullback.hom_ext <;> simp

/-- The regular bundle is principal and has its identity section. -/
def regular (m : G.Object X) : Principal G X where
  toAction := regularAction G m
  principal x n q p r := by
    let p' := regularFiberEquiv G m x n p
    let r' := regularFiberEquiv G m x q r
    refine ⟨r' ≫ inv p', ?_, ?_⟩
    · apply (regularFiberEquiv G m x q).injective
      simp [regularAction, p', r', Category.assoc]
    · intro g hg
      have he := congrArg (regularFiberEquiv G m x q) hg
      change regularFiberEquiv G m x q ((regularFiberEquiv G m x q).symm
        (g ≫ p')) = r' at he
      rw [Equiv.apply_symm_apply] at he
      rw [← he]
      simp [Category.assoc]
  isLocallySurjective := Presheaf.isLocallySurjective_of_surjective J _ (fun U x =>
    ⟨⟨(x,(value G m (X.obj.elementsMk U x)).val),
      (regularFiberEquiv G m (X.obj.elementsMk U x) _).symm (𝟙 _)⟩, rfl⟩)

/-- Evaluate a generalized arrow at a section of its parameter sheaf. -/
def arrowValue {m n : G.Object X} (f : G.Arrow m n) (x : X.obj.Elements) :
    value G m x ⟶ value G n x :=
  (G.sectionArrowEquiv _ _).symm ⟨f.map.hom.app x.obj x.val, by
    exact ⟨congrArg (fun k => k.hom.app x.obj x.val) f.source,
      congrArg (fun k => k.hom.app x.obj x.val) f.target⟩⟩

@[simp] theorem arrowValue_map {m n : G.Object X} (f : G.Arrow m n)
    (x : X.obj.Elements) :
    (arrowValue G f x).map = sectionEquiv.symm x.val ≫ f.map := by
  apply sectionEquiv.injective
  rw [sectionEquiv_comp]
  change sectionEquiv (sectionEquiv.symm (f.map.hom.app x.obj x.val)) = _
  rw [sectionEquiv.apply_symm_apply, sectionEquiv.apply_symm_apply]

@[simp] theorem arrowValue_natural_map {m n : G.Object X} (f : G.Arrow m n)
    {x y : X.obj.Elements} (k : x ⟶ y) :
    (arrowValue G f y).map =
      (sectionParameter J).map k.hom.unop ≫ (arrowValue G f x).map := by
  apply sectionEquiv.injective
  rw [sectionEquiv_naturality]
  simp only [arrowValue_map, sectionEquiv_comp]
  rw [sectionEquiv.apply_symm_apply, sectionEquiv.apply_symm_apply]
  rw [← NatTrans.naturality_apply, k.map_val]

def regularMapValue {m n : G.Object X} (f : m ⟶ n) (x : X.obj.Elements)
    (a : G.Section x.obj) (p : Fiber G X (regularFamily G m) x a) :
    Fiber G X (regularFamily G n) x a :=
  (regularFiberEquiv G n x a).symm (regularFiberEquiv G m x a p ≫ arrowValue G f x)

theorem regularMapValue_natural {m n : G.Object X} (f : m ⟶ n)
    {x y : X.obj.Elements} (k : x ⟶ y) (a : G.Section x.obj)
    (p : Fiber G X (regularFamily G m) x a) :
    regularMapValue G f y (a.restrict G k.hom)
        ((regularFamily G m).family.map (pointArrow G X k a) p) =
      (regularFamily G n).family.map (pointArrow G X k a) (regularMapValue G f x a p) := by
  apply (regularFiberEquiv G n y (a.restrict G k.hom)).injective
  apply Operations.Arrow.ext
  rw [regularFiberEquiv_natural_map]
  dsimp only [regularMapValue]
  rw [Equiv.apply_symm_apply, Equiv.apply_symm_apply]
  change (Operations.Arrow.comp G _ _).map =
    (sectionParameter J).map k.hom.unop ≫ (Operations.Arrow.comp G _ _).map
  dsimp only [Operations.Arrow.comp]
  rw [← Category.assoc]
  congr 1
  apply CategoryTheory.Limits.pullback.hom_ext
  · simpa only [Category.assoc, Limits.pullback.lift_fst, Limits.pullback.lift_fst_assoc]
      using regularFiberEquiv_natural_map G m k a p
  · simpa only [Category.assoc, Limits.pullback.lift_snd, Limits.pullback.lift_snd_assoc]
      using arrowValue_natural_map G f k

/-- The regular-unit arrow acts by postcomposition. -/
def regularMap {m n : G.Object X} (f : m ⟶ n) : Map (regular G m) (regular G n) where
  hom := {
    app z := ↾regularMapValue G f (X.obj.elementsMk z.obj z.val.1) ⟨z.val.2⟩
    naturality := by
      intro z w k
      apply ConcreteCategory.hom_ext
      intro p
      rcases z with @⟨U, ⟨x, a⟩⟩
      rcases w with @⟨V, ⟨y, b⟩⟩
      rcases k with ⟨k,hk⟩
      change U ⟶ V at k
      have hx : X.obj.map k x = y := congrArg Prod.fst hk
      have ha : G.objects.obj.map k a = b := congrArg Prod.snd hk
      subst y; subst b
      exact regularMapValue_natural G f (ElementFamilies.along X.obj k x) ⟨a⟩ p }
  equivariant x a b g p := by
    apply (regularFiberEquiv G n x a).injective
    change regularFiberEquiv G n x a ((regularFiberEquiv G n x a).symm
      (regularFiberEquiv G m x a ((regularFiberEquiv G m x a).symm
        (g ≫ regularFiberEquiv G m x b p)) ≫ arrowValue G f x)) =
      regularFiberEquiv G n x a ((regularFiberEquiv G n x a).symm
        (g ≫ regularFiberEquiv G n x b ((regularFiberEquiv G n x b).symm
          (regularFiberEquiv G m x b p ≫ arrowValue G f x))))
    simp only [Equiv.apply_symm_apply, Category.assoc]

/-- The identity element of the regular bundle at each parameter section. -/
def regularIdentity (m : G.Object X) (x : X.obj.Elements) :
    Fiber G X (regularFamily G m) x (value G m x) :=
  ⟨G.unit.hom.app x.obj (m.map.hom.app x.obj x.val), Prod.ext
    (congrArg (fun k => k.hom.app x.obj (m.map.hom.app x.obj x.val)) G.unit_source)
    (congrArg (fun k => k.hom.app x.obj (m.map.hom.app x.obj x.val)) G.unit_target)⟩

@[simp] theorem regularFiberEquiv_identity (m : G.Object X) (x : X.obj.Elements) :
    regularFiberEquiv G m x (value G m x) (regularIdentity G m x) = 𝟙 _ := by
  apply Operations.Arrow.ext
  apply sectionEquiv.injective
  rw [regularFiberEquiv_map]
  erw [sectionEquiv.apply_symm_apply]
  change G.unit.hom.app x.obj (m.map.hom.app x.obj x.val) =
    sectionEquiv ((Operations.Section.represent G (value G m x)).map ≫ G.unit)
  rw [sectionEquiv_comp]
  change _ = G.unit.hom.app x.obj (sectionEquiv (sectionEquiv.symm _))
  rw [sectionEquiv.apply_symm_apply]
  rfl

/-- The identity points give a genuine sheaf map, not just pointwise witnesses. -/
def regularIdentitySection (m : G.Object X) : X ⟶ SplitSheaf.extension (regularFamily G m) :=
  ⟨{ app U := ↾fun x => ⟨(x,(value G m (X.obj.elementsMk U x)).val),
        regularIdentity G m (X.obj.elementsMk U x)⟩
     naturality := by
       intro U V k
       apply ConcreteCategory.hom_ext
       intro x
       have hm := NatTrans.naturality_apply m.map.hom k x
       have hu := NatTrans.naturality_apply G.unit.hom k (m.map.hom.app U x)
       dsimp [regularIdentity, value, regularFamily, homFamily, SplitSheaf.tySub,
         SplitSheaf.ofDisplay, SplitPresheaf.tySub, SplitPresheaf.extension,
         ElementFamilies.total] at *
       congr 1
       · exact Prod.ext rfl hm
       · apply (Subtype.heq_iff_coe_eq (by
           intro z
           change (G.source.hom.app V z, G.target.hom.app V z) =
               (m.map.hom.app V (X.obj.map k x), m.map.hom.app V (X.obj.map k x)) ↔
             (G.source.hom.app V z, G.target.hom.app V z) =
               (G.objects.obj.map k (m.map.hom.app U x), m.map.hom.app V (X.obj.map k x))
           rw [hm])).2
         exact (congrArg (G.unit.hom.app V) hm).trans hu }⟩

@[simp] theorem regularFiberEquiv_symm_val (m : G.Object X) (x : X.obj.Elements)
    (a : G.Section x.obj) (g : a ⟶ value G m x) :
    ((regularFiberEquiv G m x a).symm g).val = sectionEquiv g.map := rfl

/-- Read the actual groupoid arrow from a point of a regular bundle. -/
def regularArrowProjection (m : G.Object X) :
    SplitSheaf.extension (regularFamily G m) ⟶ G.arrows :=
  ⟨{ app _ := ↾fun p => p.2.val }⟩

/-- An equivariant map is recovered by its value on the identity section. -/
def readRegular {m n : G.Object X} (f : Map (regular G m) (regular G n)) : m ⟶ n where
  map := regularIdentitySection G m ≫ SplitSheaf.totalMap f.hom ≫ regularArrowProjection G n
  source := by
    ext U x
    exact congrArg Prod.fst (f.hom.app (point G X (X.obj.elementsMk U x)
      (value G m (X.obj.elementsMk U x))) (regularIdentity G m (X.obj.elementsMk U x))).property
  target := by
    ext U x
    exact congrArg Prod.snd (f.hom.app (point G X (X.obj.elementsMk U x)
      (value G m (X.obj.elementsMk U x))) (regularIdentity G m (X.obj.elementsMk U x))).property

@[simp] theorem readRegular_regularMap {m n : G.Object X} (f : m ⟶ n) :
    readRegular G (regularMap G f) = f := by
  apply Operations.Arrow.ext
  ext U x
  change (regularMapValue G f (X.obj.elementsMk U x) _
    (regularIdentity G m (X.obj.elementsMk U x))).val = f.map.hom.app U x
  unfold regularMapValue
  rw [regularFiberEquiv_identity, Category.id_comp, regularFiberEquiv_symm_val,
    arrowValue_map, sectionEquiv_comp, sectionEquiv.apply_symm_apply]

@[simp] theorem arrowValue_readRegular {m n : G.Object X}
    (f : Map (regular G m) (regular G n)) (x : X.obj.Elements) :
    arrowValue G (readRegular G f) x = regularFiberEquiv G n x (value G m x)
      (f.hom.app (point G X x (value G m x)) (regularIdentity G m x)) := by
  apply Operations.Arrow.ext
  rfl

@[simp] theorem regularMap_readRegular {m n : G.Object X}
    (f : Map (regular G m) (regular G n)) : regularMap G (readRegular G f) = f := by
  apply Map.ext
  apply NatTrans.ext
  funext z
  apply ConcreteCategory.hom_ext
  intro p
  rcases z with @⟨U, ⟨x,a⟩⟩
  let y := X.obj.elementsMk U x
  let b : G.Section U := ⟨a⟩
  change regularMapValue G (readRegular G f) y b p = f.hom.app (point G X y b) p
  have h := f.equivariant y (regularFiberEquiv G m y b p) (regularIdentity G m y)
  change f.hom.app (point G X y b) ((regularFiberEquiv G m y b).symm
      (regularFiberEquiv G m y b p ≫ regularFiberEquiv G m y (value G m y)
        (regularIdentity G m y))) =
    (regularFiberEquiv G n y b).symm (regularFiberEquiv G m y b p ≫
      regularFiberEquiv G n y (value G m y)
        (f.hom.app (point G X y (value G m y)) (regularIdentity G m y))) at h
  rw [regularFiberEquiv_identity, Category.comp_id, Equiv.symm_apply_apply] at h
  unfold regularMapValue
  rw [arrowValue_readRegular]
  exact h.symm

/-- Full hom recovery for the actual regular unit. -/
def regularMapEquiv (m n : G.Object X) : (m ⟶ n) ≃ (regular G m ⟶ regular G n) where
  toFun := regularMap G
  invFun := readRegular G
  left_inv := readRegular_regularMap G
  right_inv := regularMap_readRegular G

@[simp] theorem arrowValue_id (m : G.Object X) (x : X.obj.Elements) :
    arrowValue G (𝟙 m) x = 𝟙 (value G m x) := by
  apply Operations.Arrow.ext
  rw [arrowValue_map]
  change sectionEquiv.symm x.val ≫ m.map ≫ G.unit = sectionEquiv.symm (value G m x).val ≫ G.unit
  rw [← Category.assoc]
  congr 1
  apply sectionEquiv.injective
  rw [sectionEquiv_comp, sectionEquiv.apply_symm_apply, sectionEquiv.apply_symm_apply]
  rfl

@[simp] theorem arrowValue_comp {m n q : G.Object X} (f : m ⟶ n) (g : n ⟶ q)
    (x : X.obj.Elements) : arrowValue G (f ≫ g) x = arrowValue G f x ≫ arrowValue G g x := by
  apply Operations.Arrow.ext
  rw [arrowValue_map]
  change sectionEquiv.symm x.val ≫ (Operations.Arrow.comp G f g).map =
    (Operations.Arrow.comp G (arrowValue G f x) (arrowValue G g x)).map
  simp only [Operations.Arrow.comp, arrowValue_map]
  rw [← Category.assoc]
  congr 1
  apply Limits.pullback.hom_ext <;> simp

@[simp] theorem regularMap_id (m : G.Object X) : regularMap G (𝟙 m) = 𝟙 (regular G m) := by
  apply Map.ext
  apply NatTrans.ext
  funext z
  apply ConcreteCategory.hom_ext
  intro p
  change regularMapValue G (𝟙 m) (X.obj.elementsMk z.obj z.val.1) ⟨z.val.2⟩ p = p
  simp [regularMapValue]

@[simp] theorem regularMap_comp {m n q : G.Object X} (f : m ⟶ n) (g : n ⟶ q) :
    regularMap G (f ≫ g) = Map.comp (regularMap G f) (regularMap G g) := by
  apply Map.ext
  apply NatTrans.ext
  funext z
  apply ConcreteCategory.hom_ext
  intro p
  change regularMapValue G (f ≫ g) (X.obj.elementsMk z.obj z.val.1) ⟨z.val.2⟩ p =
    regularMapValue G g (X.obj.elementsMk z.obj z.val.1) ⟨z.val.2⟩
      (regularMapValue G f (X.obj.elementsMk z.obj z.val.1) ⟨z.val.2⟩ p)
  simp [regularMapValue, Category.assoc]

/-- The unit on each fiber, retaining its actual arrow map. -/
def regularFunctor : G.Object X ⥤ Principal G X where
  obj := regular G
  map := regularMap G
  map_id := regularMap_id G
  map_comp := regularMap_comp G

def regularFullyFaithful : (regularFunctor G (X := X)).FullyFaithful where
  preimage := readRegular G
  map_preimage := regularMap_readRegular G
  preimage_map := readRegular_regularMap G

@[simp] theorem regular_reindex {Y : Sheaf J (Type (max u v))} (r : Y ⟶ X)
    (m : G.Object X) : reindex (regular G m) r = regular G (m.restrict G r) := rfl

@[simp] theorem regularFunctor_restriction {Y : Sheaf J (Type (max u v))} (r : Y ⟶ X) :
    regularFunctor G ⋙ restriction r = G.restriction r ⋙ regularFunctor G := rfl

end SquareKit.SheafGroupoid.Bundle
