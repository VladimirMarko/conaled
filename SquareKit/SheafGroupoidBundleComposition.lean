import SquareKit.SheafGroupoidBundleDescentMaps
import SquareKit.SheafCover
import SquareKit.SheafGroupoidBundleDescent
import Mathlib.CategoryTheory.Sites.RegularEpi

/-! Commuting left actions and composition by effective bundle descent. -/
noncomputable section
set_option autoImplicit false
set_option warningAsError true
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
namespace SquareKit.SheafGroupoid.Bundle
open CategoryTheory Opposite SquareKit SquareKit.SheafGroupoid
open SquareKit.SheafGroupoid.Bundle
universe u v
variable {C : Type u} [Category.{v} C] {J : GrothendieckTopology C}
variable {H K : Operations J} [H.Laws] [K.Laws]
variable {X : Sheaf J (Type (max u v))} (P : Principal H X)

def connector (x : X.obj.Elements) {m n : H.Section x.obj}
    (p : Fiber H X P.family x m) (q : Fiber H X P.family x n) : n ⟶ m :=
  (P.principal x m n p q).choose

theorem connector_spec (x : X.obj.Elements) {m n : H.Section x.obj}
    (p : Fiber H X P.family x m) (q : Fiber H X P.family x n) :
    P.act x (connector P x p q) p = q :=
  (P.principal x m n p q).choose_spec.1

theorem connector_unique (x : X.obj.Elements) {m n : H.Section x.obj}
    (p : Fiber H X P.family x m) (q : Fiber H X P.family x n)
    (h : n ⟶ m) (hh : P.act x h p = q) : h = connector P x p q :=
  (P.principal x m n p q).choose_spec.2 h hh

@[simp] theorem connector_self (x : X.obj.Elements) {m : H.Section x.obj}
    (p : Fiber H X P.family x m) : connector P x p p = 𝟙 m :=
  (connector_unique P x p p (𝟙 m) (P.act_id x m p)).symm

theorem connector_comp (x : X.obj.Elements) {m n l : H.Section x.obj}
    (p : Fiber H X P.family x m) (q : Fiber H X P.family x n)
    (r : Fiber H X P.family x l) :
    connector P x q r ≫ connector P x p q = connector P x p r := by
  apply connector_unique
  rw [P.act_comp, connector_spec, connector_spec]

@[simp] theorem connector_inverse (x : X.obj.Elements) {m n : H.Section x.obj}
    (p : Fiber H X P.family x m) (q : Fiber H X P.family x n) :
    connector P x q p = Groupoid.inv (connector P x p q) := by
  symm
  apply connector_unique
  calc
    _ = P.act x (Groupoid.inv (connector P x p q))
        (P.act x (connector P x p q) p) :=
      congrArg (P.act x (Groupoid.inv (connector P x p q))) (connector_spec P x p q).symm
    _ = P.act x (Groupoid.inv (connector P x p q) ≫ connector P x p q) p :=
      (P.act_comp x _ _ p).symm
    _ = p := by rw [Groupoid.inv_comp]; exact P.act_id x _ p

theorem connector_natural {x y : X.obj.Elements} (f : x ⟶ y)
    {m n : H.Section x.obj} (p : Fiber H X P.family x m)
    (q : Fiber H X P.family x n) :
    (H.sectionRestriction f.hom).map (connector P x p q) =
      connector P y (P.family.family.map (pointArrow H X f m) p)
        (P.family.family.map (pointArrow H X f n) q) := by
  apply connector_unique
  rw [← P.natural, connector_spec]

-- The regular-bundle specialization checks the orientation against actual arrows.
theorem connector_regular (m : H.Object X) (x : X.obj.Elements)
    {n l : H.Section x.obj} (p : Fiber H X (regular H m).family x n)
    (q : Fiber H X (regular H m).family x l) :
    connector (regular H m) x p q =
      regularFiberEquiv H m x l q ≫ Groupoid.inv (regularFiberEquiv H m x n p) := by
  symm
  apply connector_unique
  apply (regularFiberEquiv H m x l).injective
  simp [regular, regularAction, Category.assoc]

abbrev atSection {U : Cᵒᵖ} (m : H.Section U) := H.objects.obj.elementsMk U m.val

-- Covariant left H action on the base of Q, commuting with its right K action.
-- These fields are primitive action laws, not descent or quotient conclusions.
structure LeftAction (Q : Principal K H.objects) where
  act {U : Cᵒᵖ} {m n : H.Section U} (h : m ⟶ n) (k : K.Section U) :
    Fiber K H.objects Q.family (atSection m) k →
      Fiber K H.objects Q.family (atSection n) k
  identity {U : Cᵒᵖ} (m : H.Section U) (k : K.Section U)
    (q : Fiber K H.objects Q.family (atSection m) k) : act (𝟙 m) k q = q
  comp {U : Cᵒᵖ} {m n l : H.Section U} (h : m ⟶ n) (g : n ⟶ l)
    (k : K.Section U) (q : Fiber K H.objects Q.family (atSection m) k) :
    act g k (act h k q) = act (h ≫ g) k q
  natural {U V : Cᵒᵖ} (f : U ⟶ V) {m n : H.Section U} (h : m ⟶ n)
    (k : K.Section U) (q : Fiber K H.objects Q.family (atSection m) k) :
    Q.family.family.map (pointArrow K H.objects
      (ElementFamilies.along H.objects.obj f n.val) k) (act h k q) =
      act ((H.sectionRestriction f).map h) (k.restrict K f)
        (Q.family.family.map (pointArrow K H.objects
          (ElementFamilies.along H.objects.obj f m.val) k) q)
  commute {U : Cᵒᵖ} {m n : H.Section U} (h : m ⟶ n)
    {k l : K.Section U} (g : k ⟶ l)
    (q : Fiber K H.objects Q.family (atSection m) l) :
    act h k (Q.act (atSection m) g q) = Q.act (atSection n) g (act h l q)


abbrev cover := SplitSheaf.ofDisplay P.toAction.projection

abbrev coverAnchor (x : X.obj.Elements) (a : (cover P).family.obj x) :
    H.Section x.obj := ⟨a.val.1.2⟩

def coverPoint (x : X.obj.Elements) (a : (cover P).family.obj x) :
    Fiber H X P.family x (coverAnchor P x a) := by
  rcases x with @⟨U,x⟩
  rcases a with ⟨⟨⟨y,m⟩,p⟩,h⟩
  change y = x at h
  subst y
  exact p

theorem coverPoint_natural {x y : X.obj.Elements} (f : x ⟶ y)
    (a : (cover P).family.obj x) :
    P.family.family.map (pointArrow H X f (coverAnchor P x a)) (coverPoint P x a) =
      coverPoint P y ((cover P).family.map f a) := by
  rcases x with @⟨U,x⟩
  rcases y with @⟨V,y⟩
  rcases f with ⟨f,h⟩
  change U ⟶ V at f
  change X.obj.map f x = y at h
  subst y
  rcases a with ⟨⟨⟨z,m⟩,p⟩,h⟩
  change z = x at h
  subst z
  rfl

def coverAnchorMap : SplitSheaf.extension (cover P) ⟶ H.objects where
  hom := {
    app _ := ↾fun z => z.2.val.1.2
    naturality _ _ _ := rfl }

variable (Q : Principal K H.objects) (L : LeftAction Q)

abbrev localBundle := Bundle.reindex Q (coverAnchorMap P)

-- The connector is reversed here to give a covariant H-arrow a → b.
def transport (x : X.obj.Elements) (a b : (cover P).family.obj x)
    (k : K.Section x.obj)
    (q : Fiber K _ (localBundle P Q).family (Descent.liftPoint (cover P) x a) k) :
    Fiber K _ (localBundle P Q).family (Descent.liftPoint (cover P) x b) k :=
  L.act (connector P x (coverPoint P x b) (coverPoint P x a)) k q

theorem transport_identity (x : X.obj.Elements) (a : (cover P).family.obj x)
    (k : K.Section x.obj)
    (q : Fiber K _ (localBundle P Q).family (Descent.liftPoint (cover P) x a) k) :
    transport P Q L x a a k q = q := by
  unfold transport
  rw [connector_self]
  exact L.identity (coverAnchor P x a) k q

theorem transport_cocycle (x : X.obj.Elements) (a b c : (cover P).family.obj x)
    (k : K.Section x.obj)
    (q : Fiber K _ (localBundle P Q).family (Descent.liftPoint (cover P) x a) k) :
    transport P Q L x b c k (transport P Q L x a b k q) =
      transport P Q L x a c k q := by
  unfold transport
  rw [L.comp, connector_comp]

theorem transport_equivariant (x : X.obj.Elements) (a b : (cover P).family.obj x)
    {k l : K.Section x.obj} (g : k ⟶ l)
    (q : Fiber K _ (localBundle P Q).family (Descent.liftPoint (cover P) x a) l) :
    transport P Q L x a b k ((localBundle P Q).act (Descent.liftPoint (cover P) x a) g q) =
      (localBundle P Q).act (Descent.liftPoint (cover P) x b) g (transport P Q L x a b l q) := by
  change L.act (connector P x (coverPoint P x b) (coverPoint P x a)) k
    (Q.act (atSection (coverAnchor P x a)) g q) =
    Q.act (atSection (coverAnchor P x b)) g
      (L.act (connector P x (coverPoint P x b) (coverPoint P x a)) l q)
  exact L.commute (connector P x (coverPoint P x b) (coverPoint P x a)) g q

theorem transport_natural {x y : X.obj.Elements} (f : x ⟶ y)
    (a b : (cover P).family.obj x) (k : K.Section x.obj)
    (q : Fiber K _ (localBundle P Q).family (Descent.liftPoint (cover P) x a) k) :
    (localBundle P Q).family.family.map
      (pointArrow K (SplitSheaf.extension (cover P)) (SplitFunctionDiagram.pairArrow (cover P).family f b) k)
      (transport P Q L x a b k q) =
    transport P Q L y ((cover P).family.map f a) ((cover P).family.map f b)
      (k.restrict K f.hom)
      ((localBundle P Q).family.family.map
        (pointArrow K (SplitSheaf.extension (cover P)) (SplitFunctionDiagram.pairArrow (cover P).family f a) k) q) := by
  change Q.family.family.map
    (pointArrow K H.objects
      (ElementFamilies.along H.objects.obj f.hom (coverAnchor P x b).val) k)
    (L.act (connector P x (coverPoint P x b) (coverPoint P x a)) k q) =
    L.act (connector P y (coverPoint P y ((cover P).family.map f b))
      (coverPoint P y ((cover P).family.map f a))) (k.restrict K f.hom)
    (Q.family.family.map
      (pointArrow K H.objects
        (ElementFamilies.along H.objects.obj f.hom (coverAnchor P x a).val) k) q)
  rw [L.natural]
  rw [connector_natural P f, coverPoint_natural P f, coverPoint_natural P f]

def compositionDatum : Descent.Datum (cover P) (localBundle P Q) where
  transport := transport P Q L
  identity := transport_identity P Q L
  cocycle := transport_cocycle P Q L
  natural := transport_natural P Q L
  equivariant := transport_equivariant P Q L

-- Actual existing descent is applicable; this is only the resulting right bundle.
-- It does not claim a balanced quotient, residual left action or bicategory laws.
def compositionRightBundle : Principal K X :=
  Descent.principal (compositionDatum P Q L)

end SquareKit.SheafGroupoid.Bundle

namespace SquareKit.SheafGroupoid.Bundle
open CategoryTheory Opposite
universe u v
variable {C : Type u} [Category.{v} C] {J : GrothendieckTopology C}
variable {G K : Operations J} [G.Laws] [K.Laws]
@[ext] theorem LeftAction.ext {R : Principal K G.objects} (L M : LeftAction R)
    (h : ∀ (U : Cᵒᵖ) (x y : G.Section U) (g : x ⟶ y) (k : K.Section U)
      (t : Fiber K G.objects R.family (atSection x) k), L.act g k t = M.act g k t) : L = M := by
  cases L
  cases M
  congr
  funext U x y g k t
  exact h U x y g k t

end SquareKit.SheafGroupoid.Bundle
