import SquareKit.SheafGroupoidSections
import SquareKit.SplitSheafCategory
import SquareKit.SheafRelation

/-! Principal groupoid bundles as sheaf families indexed by the base and anchor.
The anchor index makes the action's source and target explicit. -/
noncomputable section
set_option autoImplicit false
set_option warningAsError true
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
namespace SquareKit.SheafGroupoid.Bundle
open CategoryTheory Opposite
universe u v
variable {C : Type u} [Category.{v} C] {J : GrothendieckTopology C}
variable (G : Operations J) [G.Laws] (X : Sheaf J (Type (max u v)))

abbrev base := SheafRelation.product X G.objects

def point (x : X.obj.Elements) (m : G.Section x.obj) : (base G X).obj.Elements :=
  (base G X).obj.elementsMk x.obj (x.val, m.val)

def pointArrow {x y : X.obj.Elements} (f : x ⟶ y) (m : G.Section x.obj) :
    point G X x m ⟶ point G X y (m.restrict G f.hom) :=
  ⟨f.hom, Prod.ext f.map_val rfl⟩

abbrev Fiber (P : SplitSheaf.Ty (base G X)) (x : X.obj.Elements)
    (m : G.Section x.obj) := P.family.obj (point G X x m)

/-- A contravariant groupoid action on points with a specified anchor. -/
structure Action where
  family : SplitSheaf.Ty (base G X)
  act (x : X.obj.Elements) {m n : G.Section x.obj} (g : m ⟶ n) :
    Fiber G X family x n → Fiber G X family x m
  act_id (x : X.obj.Elements) (m : G.Section x.obj) (p : Fiber G X family x m) :
    act x (𝟙 m) p = p
  act_comp (x : X.obj.Elements) {m n q : G.Section x.obj}
    (g : m ⟶ n) (h : n ⟶ q) (p : Fiber G X family x q) :
    act x (g ≫ h) p = act x g (act x h p)
  natural {x y : X.obj.Elements} (f : x ⟶ y) {m n : G.Section x.obj}
    (g : m ⟶ n) (p : Fiber G X family x n) :
    family.family.map (pointArrow G X f m) (act x g p) =
      act y ((G.sectionRestriction f.hom).map g)
        (family.family.map (pointArrow G X f n) p)

/-- Forgetting the anchor yields the actual total space over the parameter. -/
def Action.projection (P : Action G X) : SplitSheaf.extension P.family ⟶ X :=
  SplitSheaf.p P.family ≫ SheafRelation.fst X G.objects

/-- Principality retains unique actual arrows; local existence permits empty
section fibers and does not choose a global point. -/
structure Principal extends Action G X where
  principal (x : X.obj.Elements) (m n : G.Section x.obj)
    (p : Fiber G X family x m) (q : Fiber G X family x n) :
    ∃! g : n ⟶ m, act x g p = q
  isLocallySurjective : Presheaf.IsLocallySurjective J toAction.projection.hom

attribute [instance] Principal.isLocallySurjective

variable {G X}

/-- All natural equivariant maps, before deriving their invertibility. -/
structure Map (P Q : Principal G X) where
  hom : P.family.family ⟶ Q.family.family
  equivariant (x : X.obj.Elements) {m n : G.Section x.obj}
    (g : m ⟶ n) (p : Fiber G X P.family x n) :
    hom.app (point G X x m) (P.act x g p) =
      Q.act x g (hom.app (point G X x n) p)

@[ext] theorem Map.ext {P Q : Principal G X} (f g : Map P Q) (h : f.hom = g.hom) :
    f = g := by cases f; cases g; cases h; rfl

def Map.ident (P : Principal G X) : Map P P where
  hom := 𝟙 _
  equivariant _ _ _ _ _ := rfl

def Map.comp {P Q R : Principal G X} (f : Map P Q) (g : Map Q R) : Map P R where
  hom := f.hom ≫ g.hom
  equivariant x m n a p := by
    change g.hom.app _ (f.hom.app _ (P.act x a p)) = _
    rw [f.equivariant, g.equivariant]
    rfl

instance : Category (Principal G X) where
  Hom := Map
  id := Map.ident
  comp := Map.comp
  id_comp f := by apply Map.ext; exact Category.id_comp _
  comp_id f := by apply Map.ext; exact Category.comp_id _
  assoc f g h := by apply Map.ext; exact Category.assoc _ _ _

namespace Map
variable {P Q : Principal G X} (f : Map P Q)

/-- Principality forces every equivariant map to be injective on each anchor fiber. -/
theorem injective (x : X.obj.Elements) (m : G.Section x.obj) :
    Function.Injective (f.hom.app (point G X x m)) := by
  intro p q he
  obtain ⟨g, hg, _⟩ := P.principal x m m p q
  obtain ⟨h, _, hu⟩ := Q.principal x m m
    (f.hom.app (point G X x m) p) (f.hom.app (point G X x m) p)
  have h1 : Q.act x g (f.hom.app (point G X x m) p) =
      f.hom.app (point G X x m) p := by
    rw [← f.equivariant, hg, he]
  have h2 := Q.act_id x m (f.hom.app (point G X x m) p)
  have hg1 : g = 𝟙 m := (hu g h1).trans (hu (𝟙 m) h2).symm
  rw [hg1, P.act_id] at hg
  exact hg

abbrev totalMap : SplitSheaf.extension P.family ⟶ SplitSheaf.extension Q.family :=
  SplitSheaf.totalMap f.hom

theorem totalMap_injective (U : Cᵒᵖ) : Function.Injective (f.totalMap.hom.app U) := by
  rintro ⟨⟨x,m⟩,p⟩ ⟨⟨y,n⟩,q⟩ he
  have hb : (x,m) = (y,n) := congrArg Sigma.fst he
  cases hb
  have hp : f.hom.app (point G X (X.obj.elementsMk U x) ⟨m⟩) p =
      f.hom.app (point G X (X.obj.elementsMk U x) ⟨m⟩) q :=
    eq_of_heq (Sigma.mk.inj_iff.mp he).2
  exact congrArg (Sigma.mk (x,m)) (f.injective _ _ hp)

theorem totalMap_isLocallySurjective : Presheaf.IsLocallySurjective J f.totalMap.hom where
  imageSieve_mem {U} q := by
    rcases q with ⟨⟨x,m⟩,q⟩
    apply J.superset_covering _ (Presheaf.imageSieve_mem J P.toAction.projection.hom x)
    rintro V k ⟨⟨⟨y,n⟩,p⟩,hp⟩
    change y = X.obj.map k.op x at hp
    subst y
    let z := X.obj.elementsMk (op V) (X.obj.map k.op x)
    let m' : G.Section (op V) := ⟨G.objects.obj.map k.op m⟩
    let q' : Fiber G X Q.family z m' := Q.family.family.map
      (ElementFamilies.along (base G X).obj k.op (x,m)) q
    obtain ⟨g,hg,_⟩ := Q.principal z ⟨n⟩ m'
      (f.hom.app (point G X z ⟨n⟩) p) q'
    refine ⟨⟨(z.val,m'.val), P.act z g p⟩, ?_⟩
    change (⟨(z.val,m'.val), f.hom.app (point G X z m') (P.act z g p)⟩ :
      (SplitSheaf.extension Q.family).obj.obj (op V)) = ⟨_,q'⟩
    rw [f.equivariant, hg]

instance totalMap_isIso : IsIso f.totalMap :=
  (Sheaf.isLocallyBijective_iff_isIso f.totalMap).mp
    ⟨Presheaf.isLocallyInjective_of_injective J _ f.totalMap_injective,
      f.totalMap_isLocallySurjective⟩

/-- No equivariant maps are omitted: each underlying family map is invertible. -/
theorem hom_isIso : IsIso f.hom := by
  have : IsIso ((Over.forget (base G X)).map ((SplitSheaf.toOver).map f.hom)) :=
    f.totalMap_isIso
  have : IsIso ((SplitSheaf.toOver).map f.hom) :=
    isIso_of_reflects_iso _ (Over.forget (base G X))
  have : (SplitSheaf.toOver (X := base G X)).IsEquivalence :=
    inferInstanceAs (SplitSheaf.overEquivalence (X := base G X)).functor.IsEquivalence
  have : IsIso (show P.family ⟶ Q.family from f.hom) :=
    isIso_of_reflects_iso (show P.family ⟶ Q.family from f.hom) SplitSheaf.toOver
  let e : P.family ≅ Q.family := asIso (show P.family ⟶ Q.family from f.hom)
  exact ⟨⟨e.inv, e.hom_inv_id, e.inv_hom_id⟩⟩

/-- The inverse is derived from local existence and principality. -/
def inverse : Map Q P := by
  let := f.hom_isIso
  refine ⟨inv f.hom, ?_⟩
  intro x m n g p
  apply f.injective x m
  have cancel (a : G.Section x.obj) (z : Fiber G X Q.family x a) :
      f.hom.app (point G X x a) ((inv f.hom).app (point G X x a) z) = z :=
    congrArg (fun h => h.app (point G X x a) z) (IsIso.inv_hom_id f.hom)
  rw [cancel, f.equivariant, cancel]

@[simp] theorem inverse_comp : f.inverse.comp f = Map.ident Q := by
  apply Map.ext
  let := f.hom_isIso
  exact IsIso.inv_hom_id f.hom

@[simp] theorem comp_inverse : f.comp f.inverse = Map.ident P := by
  apply Map.ext
  let := f.hom_isIso
  exact IsIso.hom_inv_id f.hom

end Map

instance : Groupoid (Principal G X) where
  inv := Map.inverse
  inv_comp := Map.inverse_comp
  comp_inv := Map.comp_inverse


variable {Y Z : Sheaf J (Type (max u v))}

/-- Parameter substitution keeps the anchor unchanged. -/
def baseMap (r : Y ⟶ X) : base G Y ⟶ base G X :=
  SheafRelation.lift (SheafRelation.fst Y G.objects ≫ r) (SheafRelation.snd Y G.objects)

def Action.reindex (P : Action G X) (r : Y ⟶ X) : Action G Y where
  family := SplitSheaf.tySub P.family (baseMap r)
  act x := P.act (r.hom.mapElements.obj x)
  act_id x := P.act_id (r.hom.mapElements.obj x)
  act_comp x := P.act_comp (r.hom.mapElements.obj x)
  natural f _ _ g p := P.natural (r.hom.mapElements.map f) g p

def reindex (P : Principal G X) (r : Y ⟶ X) : Principal G Y where
  toAction := P.toAction.reindex r
  principal x := P.principal (r.hom.mapElements.obj x)
  isLocallySurjective := ⟨by
    intro U y
    apply J.superset_covering _ (Presheaf.imageSieve_mem J P.toAction.projection.hom
      (r.hom.app (op U) y))
    rintro V k ⟨⟨⟨x,m⟩,p⟩,hp⟩
    change x = X.obj.map k.op (r.hom.app (op U) y) at hp
    have hx : x = r.hom.app (op V) (Y.obj.map k.op y) :=
      hp.trans (NatTrans.naturality_apply r.hom k.op y).symm
    clear hp
    subst x
    exact ⟨⟨(Y.obj.map k.op y,m),p⟩, rfl⟩⟩

def Map.reindex {P Q : Principal G X} (f : Map P Q) (r : Y ⟶ X) :
    Map (Bundle.reindex P r) (Bundle.reindex Q r) where
  hom := Functor.whiskerLeft (baseMap r).hom.mapElements f.hom
  equivariant x := f.equivariant (r.hom.mapElements.obj x)

/-- Substitution acts on every equivariant map. -/
def restriction (r : Y ⟶ X) : Principal G X ⥤ Principal G Y where
  obj P := reindex P r
  map f := f.reindex r

@[simp] theorem reindex_id (P : Principal G X) : reindex P (𝟙 X) = P := rfl
@[simp] theorem reindex_comp (P : Principal G X) (r : Y ⟶ X) (s : Z ⟶ Y) :
    reindex (reindex P r) s = reindex P (s ≫ r) := rfl
@[simp] theorem restriction_id : restriction (G := G) (𝟙 X) = 𝟭 (Principal G X) := rfl
@[simp] theorem restriction_comp (r : Y ⟶ X) (s : Z ⟶ Y) :
    restriction (G := G) r ⋙ restriction s = restriction (s ≫ r) := rfl

end SquareKit.SheafGroupoid.Bundle
