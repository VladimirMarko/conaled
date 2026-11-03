import SquareKit.SplitSheafConstant
import Mathlib.Algebra.Category.Grp.Limits
import Mathlib.CategoryTheory.Sites.LocallyBijective

/-! Locally trivial torsors for a sheaf of groups. The split-family interface
represents actual sheaves in a slice, and makes base substitution explicit.
Local existence uses covering sieves, without a chosen global section. -/
noncomputable section
namespace SquareKit.SheafTorsor
open CategoryTheory Opposite
universe u v w
variable {C : Type u} [Category.{v} C] {J : GrothendieckTopology C}

/-- An action on a sheaf family, natural under restriction of both the group
section and the base section. -/
structure Action (G : Sheaf J GrpCat.{w}) (X : Sheaf J (Type w)) where
  family : SplitSheaf.Ty X
  act (x : X.obj.Elements) : G.obj.obj x.obj → family.family.obj x → family.family.obj x
  one_act (x : X.obj.Elements) (p : family.family.obj x) : act x 1 p = p
  mul_act (x : X.obj.Elements) (g h : G.obj.obj x.obj) (p : family.family.obj x) :
    act x (g * h) p = act x g (act x h p)
  natural {x y : X.obj.Elements} (f : x ⟶ y) (g : G.obj.obj x.obj)
    (p : family.family.obj x) :
    family.family.map f (act x g p) = act y (G.obj.map f.hom g) (family.family.map f p)

/-- The principal condition allows empty section fibers. Local existence is
required separately and permits nontrivial torsors. -/
structure Torsor (G : Sheaf J GrpCat.{w}) (X : Sheaf J (Type w)) extends Action G X where
  principal (x : X.obj.Elements) (p q : family.family.obj x) :
    ∃! g : G.obj.obj x.obj, act x g p = q
  locallySurjective : Presheaf.IsLocallySurjective J (SplitSheaf.p family).hom

attribute [instance] Torsor.locallySurjective
variable {G : Sheaf J GrpCat.{w}} {X Y Z : Sheaf J (Type w)}

/-- Equivariant isomorphisms of the actual slice families. -/
structure Arrow (P Q : Torsor G X) where
  iso : P.family.family ≅ Q.family.family
  equivariant (x : X.obj.Elements) (g : G.obj.obj x.obj) (p : P.family.family.obj x) :
    iso.hom.app x (P.act x g p) = Q.act x g (iso.hom.app x p)

@[ext] theorem Arrow.ext {P Q : Torsor G X} (f g : Arrow P Q)
    (h : f.iso.hom = g.iso.hom) : f = g := by
  cases f
  cases g
  congr 1
  exact CategoryTheory.Iso.ext h

def Arrow.ident (P : Torsor G X) : Arrow P P where
  iso := Iso.refl _
  equivariant _ _ _ := rfl

def Arrow.comp {P Q R : Torsor G X} (f : Arrow P Q) (g : Arrow Q R) : Arrow P R where
  iso := f.iso ≪≫ g.iso
  equivariant x h p := by
    change g.iso.hom.app x (f.iso.hom.app x (P.act x h p)) = _
    rw [f.equivariant, g.equivariant]
    rfl

instance : Category (Torsor G X) where
  Hom := Arrow
  id := Arrow.ident
  comp := Arrow.comp
  id_comp f := by apply Arrow.ext; exact Category.id_comp _
  comp_id f := by apply Arrow.ext; exact Category.comp_id _
  assoc f g h := by apply Arrow.ext; exact Category.assoc _ _ _

def Arrow.inverse {P Q : Torsor G X} (f : Arrow P Q) : Arrow Q P where
  iso := f.iso.symm
  equivariant x g q := by
    have hinj : Function.Injective (f.iso.hom.app x) := by
      intro a b h
      have ha := congrArg (fun k => k.app x a) f.iso.hom_inv_id
      have hb := congrArg (fun k => k.app x b) f.iso.hom_inv_id
      exact ha.symm.trans ((congrArg (f.iso.inv.app x) h).trans hb)
    apply hinj
    have hq (z : Q.family.family.obj x) :
        f.iso.hom.app x (f.iso.inv.app x z) = z :=
      congrArg (fun k => k.app x z) f.iso.inv_hom_id
    change f.iso.hom.app x (f.iso.inv.app x (Q.act x g q)) =
      f.iso.hom.app x (P.act x g (f.iso.inv.app x q))
    rw [hq, f.equivariant, hq]

instance : Groupoid (Torsor G X) where
  inv := Arrow.inverse
  inv_comp f := by apply Arrow.ext; exact f.iso.inv_hom_id
  comp_inv f := by apply Arrow.ext; exact f.iso.hom_inv_id

/-- Package the explicit inverse without choosing a second one. -/
def Arrow.toIso {P Q : Torsor G X} (f : Arrow P Q) : P ≅ Q where
  hom := f
  inv := f.inverse
  hom_inv_id := by apply Arrow.ext; exact f.iso.hom_inv_id
  inv_hom_id := by apply Arrow.ext; exact f.iso.inv_hom_id

/-- Substitution of a group action uses the existing split sheaf pullback. -/
def Action.reindex (P : Action G X) (f : Y ⟶ X) : Action G Y where
  family := SplitSheaf.tySub P.family f
  act x := P.act (f.hom.mapElements.obj x)
  one_act x := P.one_act (f.hom.mapElements.obj x)
  mul_act x := P.mul_act (f.hom.mapElements.obj x)
  natural k g p := P.natural (f.hom.mapElements.map k) g p

/-- Pullback preserves local existence; the covering witnesses are pulled
back along the base section and retained in the new total space. -/
theorem reindex_locallySurjective (P : Torsor G X) (f : Y ⟶ X) :
    Presheaf.IsLocallySurjective J (SplitSheaf.p (SplitSheaf.tySub P.family f)).hom where
  imageSieve_mem {U} y := by
    have h := Presheaf.imageSieve_mem J (SplitSheaf.p P.family).hom (f.hom.app (op U) y)
    apply J.superset_covering _ h
    intro V k hk
    obtain ⟨⟨x, p⟩, hp⟩ := hk
    have he : x = f.hom.app (op V) (Y.obj.map k.op y) :=
      hp.trans (NatTrans.naturality_apply f.hom k.op y).symm
    subst x
    exact ⟨⟨Y.obj.map k.op y, p⟩, rfl⟩

def reindex (P : Torsor G X) (f : Y ⟶ X) : Torsor G Y where
  toAction := P.toAction.reindex f
  principal x := P.principal (f.hom.mapElements.obj x)
  locallySurjective := reindex_locallySurjective P f

def Arrow.reindex {P Q : Torsor G X} (h : Arrow P Q) (f : Y ⟶ X) :
    Arrow (reindex P f) (reindex Q f) where
  iso := Functor.isoWhiskerLeft f.hom.mapElements h.iso
  equivariant x := h.equivariant (f.hom.mapElements.obj x)

/-- Restriction acts on equivariant arrows as well as on objects. -/
def restriction (f : Y ⟶ X) : Torsor G X ⥤ Torsor G Y where
  obj P := reindex P f
  map h := h.reindex f

@[simp] theorem reindex_id (P : Torsor G X) : reindex P (𝟙 X) = P := rfl
@[simp] theorem reindex_comp (P : Torsor G X) (f : Y ⟶ X) (g : Z ⟶ Y) :
    reindex (reindex P f) g = reindex P (g ≫ f) := rfl

@[simp] theorem restriction_id : restriction (G := G) (𝟙 X) = 𝟭 (Torsor G X) := rfl
@[simp] theorem restriction_comp (f : Y ⟶ X) (g : Z ⟶ Y) :
    restriction (G := G) f ⋙ restriction g = restriction (g ≫ f) := rfl

/-- The underlying sheaf keeps all section-level group operations. -/
abbrev groupSheaf (G : Sheaf J GrpCat.{w}) : Sheaf J (Type w) :=
  (sheafCompose J (forget GrpCat.{w})).obj G

/-- The trivial torsor is a checked instance, not the definition of all torsors. -/
def trivial (G : Sheaf J GrpCat.{w}) (X : Sheaf J (Type w)) : Torsor G X where
  family := SplitSheaf.constant (groupSheaf G) X
  act x := (fun (g p : G.obj.obj x.obj) => g * p)
  one_act x := (one_mul : ∀ p : G.obj.obj x.obj, 1 * p = p)
  mul_act x := (mul_assoc : ∀ g h p : G.obj.obj x.obj, (g * h) * p = g * (h * p))
  natural f g p := (G.obj.map f.hom).hom.map_mul g p
  principal x p q := by
    change G.obj.obj x.obj at p q
    change ∃! g : G.obj.obj x.obj, g * p = q
    refine ⟨q * p⁻¹, ?_, ?_⟩
    · exact inv_mul_cancel_right q p
    · intro g hg
      exact (eq_mul_inv_iff_mul_eq).mpr hg
  locallySurjective := Presheaf.isLocallySurjective_of_surjective J _ (fun U y =>
    ⟨⟨y, (1 : G.obj.obj U)⟩, rfl⟩)

@[simp] theorem trivial_reindex (f : Y ⟶ X) : reindex (trivial G X) f = trivial G Y := rfl

/-- A label over the base acts by right translation on the regular torsor.
Left multiplication is the torsor action, so equivariance follows by associativity. -/
def regularArrow (g : X ⟶ groupSheaf G) : Arrow (trivial G X) (trivial G X) where
  iso := NatIso.ofComponents (fun x =>
    (Equiv.mulRight (show G.obj.obj x.obj from g.hom.app x.obj x.val)).toIso) (by
      intro x y f
      ext p
      change G.obj.obj x.obj at p
      symm
      change G.obj.map f.hom (p * (show G.obj.obj x.obj from g.hom.app x.obj x.val)) =
        G.obj.map f.hom p * (show G.obj.obj y.obj from g.hom.app y.obj y.val)
      rw [(G.obj.map f.hom).hom.map_mul]
      congr 1
      exact (NatTrans.naturality_apply g.hom f.hom x.val).symm.trans
        (congrArg (g.hom.app y.obj) f.map_val))
  equivariant x h p := by
    change G.obj.obj x.obj at p
    change (h * p) * (show G.obj.obj x.obj from g.hom.app x.obj x.val) =
      h * (p * (show G.obj.obj x.obj from g.hom.app x.obj x.val))
    exact mul_assoc _ _ _

/-- Distinct group labels give distinct automorphisms, even if another
associated action on a fiber is ineffective. -/
theorem regularArrow_injective : Function.Injective (regularArrow (G := G) (X := X)) := by
  intro g h he
  ext U x
  have hv := congrArg (fun k : Arrow (trivial G X) (trivial G X) =>
    k.iso.hom.app (X.obj.elementsMk U x) (1 : G.obj.obj U)) he
  change (1 : G.obj.obj U) * (show G.obj.obj U from g.hom.app U x) =
    1 * (show G.obj.obj U from h.hom.app U x) at hv
  have h1 (z : G.obj.obj U) : 1 * z = z := one_mul z
  rw [h1, h1] at hv
  exact hv

@[simp] theorem regularArrow_reindex (g : X ⟶ groupSheaf G) (f : Y ⟶ X) :
    (regularArrow g).reindex f = regularArrow (f ≫ g) := rfl

/-- Choosing one section trivializes exactly its own fiber. -/
def fiberEquiv (P : Torsor G X) (x : X.obj.Elements) (p : P.family.family.obj x) :
    G.obj.obj x.obj ≃ P.family.family.obj x :=
  Equiv.ofBijective (P.act x · p) ⟨by
    intro g h he
    obtain ⟨k, hk, hu⟩ := P.principal x p (P.act x g p)
    exact (hu g rfl).trans (hu h he.symm).symm,
    fun q => (P.principal x p q).exists⟩

/-- A global section constructs a trivialization by the torsor action. -/
def ofSection (P : Torsor G X) (t : SplitSheaf.Tm P.family) : Arrow (trivial G X) P where
  iso := NatIso.ofComponents (fun x => (fiberEquiv P x (t.val x)).toIso) (by
    intro x y f
    ext g
    change G.obj.obj x.obj at g
    change P.act y (G.obj.map f.hom g) (t.val y) =
      P.family.family.map f (P.act x g (t.val x))
    rw [P.natural, t.natural])
  equivariant x g h := P.mul_act x g h (t.val x)

/-- A trivialization supplies a global section by evaluating at the identity. -/
def sectionOfArrow {P : Torsor G X} (f : Arrow (trivial G X) P) : SplitSheaf.Tm P.family where
  val x := f.iso.hom.app x (1 : G.obj.obj x.obj)
  natural {x y} k := by
    have h := NatTrans.naturality_apply f.iso.hom k (1 : G.obj.obj x.obj)
    change f.iso.hom.app y (G.obj.map k.hom 1) = _ at h
    rw [(G.obj.map k.hom).hom.map_one] at h
    exact h.symm

/-- Global triviality is a theorem equivalent to the existence of a section,
not a hidden assumption of the object type. -/
theorem trivializable_iff_section (P : Torsor G X) :
    Nonempty (Arrow (trivial G X) P) ↔ Nonempty (SplitSheaf.Tm P.family) :=
  ⟨fun ⟨f⟩ => ⟨sectionOfArrow f⟩, fun ⟨t⟩ => ⟨ofSection P t⟩⟩

/-- Equivariant maps are not required to carry an inverse as input. -/
structure EquivariantMap (P Q : Torsor G X) where
  hom : P.family.family ⟶ Q.family.family
  equivariant (x : X.obj.Elements) (g : G.obj.obj x.obj) (p : P.family.family.obj x) :
    hom.app x (P.act x g p) = Q.act x g (hom.app x p)

namespace EquivariantMap
variable {P Q : Torsor G X} (f : EquivariantMap P Q)

theorem injective (x : X.obj.Elements) : Function.Injective (f.hom.app x) := by
  intro p q he
  obtain ⟨g, hg, hu⟩ := P.principal x p q
  have hh : Q.act x g (f.hom.app x p) = Q.act x 1 (f.hom.app x p) := by
    rw [← f.equivariant, hg, ← he, Q.one_act]
  have hg1 : g = 1 := (fiberEquiv Q x (f.hom.app x p)).injective hh
  rw [hg1, P.one_act] at hg
  exact hg

def totalMap : SplitSheaf.Ext P.family ⟶ SplitSheaf.Ext Q.family :=
  ⟨ElementFamilies.totalNat X.obj f.hom⟩

theorem totalMap_injective (U : Cᵒᵖ) : Function.Injective (f.totalMap.hom.app U) := by
  rintro ⟨x, p⟩ ⟨y, q⟩ he
  have hb : x = y := congrArg Sigma.fst he
  subst y
  have hv : f.hom.app (X.obj.elementsMk U x) p = f.hom.app (X.obj.elementsMk U x) q :=
    eq_of_heq (Sigma.mk.inj_iff.mp he).2
  exact congrArg (fun p => Sigma.mk x p) (f.injective _ hv)

theorem totalMap_locallySurjective : Presheaf.IsLocallySurjective J f.totalMap.hom where
  imageSieve_mem {U} q := by
    have h := Presheaf.imageSieve_mem J (SplitSheaf.p P.family).hom q.1
    apply J.superset_covering _ h
    intro V k hk
    obtain ⟨⟨x, p⟩, hp⟩ := hk
    change x = X.obj.map k.op q.1 at hp
    subst x
    let y := X.obj.elementsMk (op V) (X.obj.map k.op q.1)
    let q' := Q.family.family.map (ElementFamilies.along X.obj k.op q.1) q.2
    obtain ⟨g, hg, hu⟩ := Q.principal y (f.hom.app y p) q'
    refine ⟨⟨X.obj.map k.op q.1, P.act y g p⟩, ?_⟩
    change (⟨X.obj.map k.op q.1, f.hom.app y (P.act y g p)⟩ :
      ElementFamilies.Total X.obj Q.family.family (op V)) = ⟨_, q'⟩
    rw [f.equivariant, hg]

instance totalMap_isIso : IsIso f.totalMap :=
  (Sheaf.isLocallyBijective_iff_isIso f.totalMap).mp
    ⟨Presheaf.isLocallyInjective_of_injective J _ f.totalMap_injective,
      f.totalMap_locallySurjective⟩

theorem bijective (x : X.obj.Elements) : Function.Bijective (f.hom.app x) := by
  refine ⟨f.injective x, ?_⟩
  intro q
  have hi : Function.Bijective (f.totalMap.hom.app x.obj) :=
    (CategoryTheory.isIso_iff_bijective _).mp inferInstance
  obtain ⟨⟨y, p⟩, hp⟩ := hi.surjective ⟨x.val, q⟩
  have hy : y = x.val := congrArg Sigma.fst hp
  subst y
  exact ⟨p, eq_of_heq (Sigma.mk.inj_iff.mp hp).2⟩

/-- Local existence and principality construct the inverse. Therefore the
chosen groupoid includes every equivariant map, not a selected subcollection. -/
def toArrow : Arrow P Q where
  iso := NatIso.ofComponents (fun x => (Equiv.ofBijective (f.hom.app x) (f.bijective x)).toIso)
    (fun {_ _} k => f.hom.naturality k)
  equivariant := f.equivariant

end EquivariantMap

/-- Forgetting the inverse loses no equivariant maps, because local
principality has constructed an inverse for every one of them. -/
def equivariantArrowEquiv {P Q : Torsor G X} : EquivariantMap P Q ≃ Arrow P Q where
  toFun := EquivariantMap.toArrow
  invFun f := ⟨f.iso.hom, f.equivariant⟩
  left_inv f := by cases f; rfl
  right_inv f := by apply Arrow.ext; rfl

end SquareKit.SheafTorsor
