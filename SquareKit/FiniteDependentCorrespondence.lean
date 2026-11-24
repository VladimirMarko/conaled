import SquareKit.GroupoidCorrespondence
import SquareKit.DoubleDelooping
import SquareKit.Internal.PathTransport.TwoFamilyCoherence
import Mathlib.Data.ZMod.Basic
import Mathlib.Tactic.Abel
import Examples.SecondIdentity

/-! A finite strict fiber retaining parallel mod-four witnesses. -/
namespace SquareKit.FiniteDependentCorrespondence
open CategoryTheory Bicategory
open Internal.PathTransport
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true

abbrev Q := ZMod 2
abbrev R := ZMod 4

/-- Fiber arrows, with mod-four witness cells as their category morphisms. -/
abbrev FiberArrow := Q

def π : R →+ FiberArrow := (ZMod.castHom (by decide : 2 ∣ 4) Q).toAddMonoidHom

abbrev FiberCell (m n : FiberArrow) := {r : R // m = n + π r}

scoped instance : Groupoid FiberArrow where
  Hom := FiberCell
  id m := ⟨0, by simp⟩
  comp r s := ⟨r.val + s.val, by
    rcases r with ⟨r, hr⟩; rcases s with ⟨s, hs⟩
    dsimp at *
    rw [map_add, hr, hs]
    abel⟩
  id_comp r := Subtype.ext (zero_add r.val)
  comp_id r := Subtype.ext (add_zero r.val)
  assoc r s t := Subtype.ext (add_assoc r.val s.val t.val)
  inv r := ⟨-r.val, by rcases r with ⟨r, hr⟩; dsimp at *; rw [map_neg, hr]; abel⟩
  inv_comp r := Subtype.ext (neg_add_cancel r.val)
  comp_inv r := Subtype.ext (add_neg_cancel r.val)

@[simp] theorem transport_label {m n : FiberArrow} (h : m = n) :
    (eqToHom h : m ⟶ n).val = 0 := by cases h; rfl

@[simp] theorem comp_label {m n k : FiberArrow} (r : m ⟶ n) (s : n ⟶ k) :
    (r ≫ s).val = r.val + s.val := rfl

/-- The sole fiber object. Its hom-groupoid is not thin. -/
def FiniteFiber := Unit

instance : Bicategory FiniteFiber where
  Hom _ _ := FiberArrow
  id _ := 0
  comp m n := m + n
  homCategory _ _ := inferInstanceAs (Category FiberArrow)
  whiskerLeft k _ _ r := ⟨r.val, by rcases r with ⟨r, hr⟩; dsimp at *; rw [hr]; abel⟩
  whiskerRight r k := ⟨r.val, by rcases r with ⟨r, hr⟩; dsimp at *; rw [hr]; abel⟩
  associator m n k := eqToIso (add_assoc m n k)
  leftUnitor m := eqToIso (zero_add m)
  rightUnitor m := eqToIso (add_zero m)
  whiskerLeft_id _ _ := rfl
  whiskerLeft_comp := by intros; rfl
  id_whiskerLeft := by intros; apply Subtype.ext; simp
  comp_whiskerLeft := by intros; apply Subtype.ext; simp
  id_whiskerRight _ _ := rfl
  comp_whiskerRight _ _ _ := rfl
  whiskerRight_id := by intros; apply Subtype.ext; simp
  whiskerRight_comp := by intros; apply Subtype.ext; simp
  whisker_assoc := by intros; apply Subtype.ext; simp
  whisker_exchange := by intros; apply Subtype.ext; exact add_comm _ _
  pentagon := by intros; apply Subtype.ext; simp
  triangle := by intros; apply Subtype.ext; simp

instance : Bicategory.Strict FiniteFiber where
  id_comp m := by change (0 : FiberArrow) + m = m; exact zero_add (show FiberArrow from m)
  comp_id m := by exact add_zero (show FiberArrow from m)
  assoc m n k := by exact add_assoc (show FiberArrow from m) (show FiberArrow from n) (show FiberArrow from k)
  leftUnitor_eqToIso _ := rfl
  rightUnitor_eqToIso _ := rfl
  associator_eqToIso _ _ _ := rfl

instance (x y : FiniteFiber) : Groupoid (x ⟶ y) :=
  inferInstanceAs (Groupoid FiberArrow)

abbrev Base := DoubleDelooping.Space (Multiplicative Q)

def action (α : Multiplicative Q) : StrictTwoTransformation.Trans
    (StrictPseudofunctor.id FiniteFiber) (StrictPseudofunctor.id FiniteFiber) where
  app _ := Multiplicative.toAdd α
  naturality f := add_comm (show FiberArrow from f) (Multiplicative.toAdd α)
  naturality₂ r := by
    apply Subtype.ext
    change r.val + (eqToHom _ : (_ : FiberArrow) ⟶ _).val =
      (eqToHom _ : (_ : FiberArrow) ⟶ _).val + r.val
    simp

def finiteFamily : TwoFamily.Family Base := StrictPseudofunctor.mk'' {
  obj := fun _ => (⟨FiniteFiber⟩ : StrictTwoCategory)
  map := fun _ => StrictPseudofunctor.id _
  map₂ := action
  map₂_id := fun _ => by apply StrictTwoTransformation.Trans.ext; intro a; rfl
  map₂_comp := fun α β => by
    apply StrictTwoTransformation.Trans.ext; intro a
    exact add_comm (Multiplicative.toAdd β) (Multiplicative.toAdd α)
  map_id := fun _ => rfl
  map_comp := fun _ _ => (StrictTwoTransformation.functor_comp_id _).symm
  map₂_whisker_left := fun f _ _ α => by
    apply StrictTwoTransformation.Trans.ext; intro a
    repeat rw [StrictTwoTransformation.Trans.comp_app]
    repeat rw [StrictTwoTransformation.Trans.eqToHom_app]
    change (show a ⟶ a from Multiplicative.toAdd α) =
      𝟙 a ≫ Multiplicative.toAdd α ≫ 𝟙 a
    exact ((Category.id_comp _).trans (Category.comp_id _)).symm
  map₂_whisker_right := fun α f => by
    apply StrictTwoTransformation.Trans.ext; intro a
    repeat rw [StrictTwoTransformation.Trans.comp_app]
    repeat rw [StrictTwoTransformation.Trans.eqToHom_app]
    change (show a ⟶ a from Multiplicative.toAdd α) =
      𝟙 a ≫ Multiplicative.toAdd α ≫ 𝟙 a
    exact ((Category.id_comp _).trans (Category.comp_id _)).symm
}

def point : TwoFamily.Total finiteFamily :=
  ⟨DoubleDelooping.point _, ()⟩

def arrow (m : Q) : TwoFamily.Hom finiteFamily point point :=
  TwoGroupoidHom.arrow (TwoFamily.evaluation finiteFamily point.fiber)
    point.fiber (DoubleDelooping.arrow _) m

abbrev Coordinates (m n : Q) := {p : Q × R // m = n + p.1 + π p.2}

def dependentCellEquiv (m n : Q) : Coordinates m n ≃ (arrow m ⟶ arrow n) where
  toFun d := TwoGroupoidHom.cell (Multiplicative.ofAdd d.val.1)
    ⟨d.val.2, by change m = d.val.1 + n + π d.val.2; simpa only [add_comm d.val.1 n] using d.property⟩
  invFun c := ⟨(Multiplicative.toAdd c.base, c.fiber.val), by
    have h := c.fiber.property
    exact h.trans (by change (Multiplicative.toAdd c.base) + n + π c.fiber.val = n + (Multiplicative.toAdd c.base) + π c.fiber.val; rw [add_comm (Multiplicative.toAdd c.base) n])⟩
  left_inv _ := rfl
  right_inv _ := rfl

abbrev H := TwoFamily.Hom finiteFamily point point

@[simp] theorem fiber_whiskerLeft_label {x y z : FiniteFiber} (k : x ⟶ y)
    {m n : y ⟶ z} (r : m ⟶ n) : (k ◁ r).val = r.val := rfl
@[simp] theorem fiber_whiskerRight_label {x y z : FiniteFiber}
    {m n : x ⟶ y} (r : m ⟶ n) (k : y ⟶ z) : (r ▷ k).val = r.val := rfl

@[simp] theorem total_comp_label {p q r : H} (c : p ⟶ q) (d : q ⟶ r) :
    (c ≫ d).fiber.val = c.fiber.val + d.fiber.val := by
  rw [TwoFamily.fiber_comp]
  change c.fiber.val + (d.fiber.val + (eqToHom _ : (_ : FiberArrow) ⟶ _).val) = _
  simp only [transport_label, add_zero]

@[simp] theorem total_transport_label {p q : H} (h : p = q) :
    (eqToHom h).fiber.val = 0 := by
  rw [TwoFamily.total_eqToHom_fiber]
  exact transport_label _

@[simp] theorem total_whiskerRight_label {p q : H} (c : p ⟶ q) (k : H) :
    (TwoFamily.whiskerRight finiteFamily c k).fiber.val = c.fiber.val := by
  change ((eqToHom _ : (_ : FiberArrow) ⟶ _) ≫
    (_ ◁ (StrictPseudofunctor.id FiniteFiber).map₂ c.fiber) ▷ k.fiber ≫
    eqToHom _).val = c.fiber.val
  simp only [comp_label, transport_label, fiber_whiskerRight_label, fiber_whiskerLeft_label, zero_add, add_zero]
  rfl

@[simp] theorem total_whiskerLeft_label (k : H) {p q : H} (c : p ⟶ q) :
    (TwoFamily.whiskerLeft finiteFamily k c).fiber.val = c.fiber.val := by
  change (_ ◁ (_ ◁ c.fiber) ≫ (eqToHom _ : (_ : FiberArrow) ⟶ _)).val = _
  change c.fiber.val + (eqToHom _ : (_ : FiberArrow) ⟶ _).val = _
  simp only [transport_label, add_zero]

@[simp] theorem object_transport {x y : FiniteFiber} (h : x = y) :
    (show Q from eqToHom h) = 0 := by cases h; rfl

@[simp] theorem arrow_compose (m n : Q) :
    TwoFamily.compose finiteFamily (arrow m) (arrow n) = arrow (m + n) := by
  unfold TwoFamily.compose
  congr 1
  change (show Q from (eqToHom _ : point.fiber ⟶ point.fiber)) + (m + n) = m + n
  rw [object_transport, zero_add]

def selectedOne : arrow 0 ⟶ arrow 0 := dependentCellEquiv 0 0 ⟨(1,1), by decide⟩
def selectedThree : arrow 0 ⟶ arrow 0 := dependentCellEquiv 0 0 ⟨(1,3), by decide⟩

theorem selected_distinct : selectedOne ≠ selectedThree := by
  intro h
  have bad := congrArg (fun c : arrow 0 ⟶ arrow 0 => c.fiber.val) h
  exact (by decide : (1 : R) ≠ 3) bad

theorem zero_replacement_rejected : ¬ (0 : Q) = 0 + 1 + π 0 := by decide

theorem no_reconstruction : ¬ ∃ observe : Q → Nat,
    ∀ c : arrow 0 ⟶ arrow 0, observe (Multiplicative.toAdd c.base) = c.fiber.val.val := by
  rintro ⟨observe, h⟩
  have h₁ : observe 1 = 1 := h selectedOne
  have h₃ : observe 1 = 3 := h selectedThree
  exact (by decide : (1 : Nat) ≠ 3) (h₁.symm.trans h₃)

@[ext] theorem cell_ext {p q : H} {c d : p ⟶ q}
    (hb : c.base = d.base) (hr : c.fiber.val = d.fiber.val) : c = d := by
  cases c with | mk a r =>
    cases d with | mk b s =>
      dsimp at hb hr
      subst b
      have h : r = s := Subtype.ext hr
      cases h
      rfl

@[simp] theorem total_identity_label (p : H) : (𝟙 p : p ⟶ p).fiber.val = 0 :=
  total_transport_label rfl

theorem selectedOne_square : selectedOne ≫ selectedOne =
    dependentCellEquiv 0 0 ⟨(0,2), by decide⟩ := by
  apply cell_ext
  · rfl
  · rw [total_comp_label]; rfl

theorem selectedOne_square_ne_identity : selectedOne ≫ selectedOne ≠ 𝟙 (arrow 0) := by
  intro h
  have bad := congrArg (fun c : arrow 0 ⟶ arrow 0 => c.fiber.val) h
  rw [total_comp_label, total_identity_label] at bad
  exact (by decide : (2 : R) ≠ 0) bad

theorem selectedOne_three : selectedOne ≫ selectedThree = 𝟙 (arrow 0) := by
  apply cell_ext
  · rfl
  · rw [total_comp_label, total_identity_label]; rfl

def J : Discrete Q ⥤ H := Discrete.functor arrow

abbrev Boundary := CategoryTheory.Comma J J
abbrev Tail := CategoryTheory.Comma (GroupoidCorrespondence.terminal (Discrete Q))
  (GroupoidCorrespondence.terminal (Discrete (Q × Q)))
abbrev Left := CategoryTheory.Comma (GroupoidCorrespondence.terminal Boundary)
  (GroupoidCorrespondence.terminal (Discrete (Q × Q)))
abbrev Right := CategoryTheory.Comma J
  (CategoryTheory.Comma.fst (GroupoidCorrespondence.terminal (Discrete Q))
    (GroupoidCorrespondence.terminal (Discrete (Q × Q))) ⋙ J)

/-- The normal form retains the actual dependent total cell. -/
abbrev Normal := Σ m n : Q, (arrow m ⟶ arrow n) × Q × Q

def leftNormal : Left ≃ Normal where
  toFun c := ⟨c.left.left.as, c.left.right.as, c.left.hom, c.right.as⟩
  invFun c := ⟨⟨⟨c.1⟩, ⟨c.2.1⟩, c.2.2.1⟩, ⟨c.2.2.2⟩, 𝟙 _⟩
  left_inv c := by rcases c with ⟨⟨⟨m⟩, ⟨n⟩, c⟩, ⟨k,l⟩, h⟩; rfl
  right_inv _ := rfl

def rightNormal : Right ≃ Normal where
  toFun c := ⟨c.left.as, c.right.left.as, c.hom, c.right.right.as⟩
  invFun c := ⟨⟨c.1⟩, ⟨⟨c.2.1⟩, ⟨c.2.2.2⟩, 𝟙 _⟩, c.2.2.1⟩
  left_inv c := by rcases c with ⟨⟨m⟩, ⟨⟨n⟩, ⟨k,l⟩, h⟩, c⟩; rfl
  right_inv _ := rfl

def reassociate : Left ≌ Right :=
  (GroupoidCorrespondence.discreteEquivalence leftNormal).trans
    (GroupoidCorrespondence.discreteEquivalence rightNormal).symm

@[simp] theorem reassociate_full (c : Left) :
    rightNormal (reassociate.functor.obj c) = leftNormal c := rfl

/-- The boundary arrow of H is definitionally this same total 2-cell. -/
theorem dimensional_bridge (c : Left) :
    (reassociate.functor.obj c).hom =
      (show arrow c.left.left.as ⟶ arrow c.left.right.as from c.left.hom) := rfl

/-- Endpoint/cell packets retain complete cells, not just observations. -/
abbrev Packet := Σ p q : H, p ⟶ q

def interpretLeft (c : Left) : Packet :=
  ⟨_, _, TwoFamily.whiskerRight finiteFamily
    (TwoFamily.whiskerRight finiteFamily c.left.hom (arrow c.right.as.1))
    (arrow c.right.as.2)⟩

def interpretRight (c : Right) : Packet :=
  ⟨_, _, TwoFamily.whiskerRight finiteFamily c.hom
    (TwoFamily.compose finiteFamily (arrow c.right.right.as.1) (arrow c.right.right.as.2))⟩

theorem threefold (c : Left) :
    (interpretRight (reassociate.functor.obj c)).2.2 =
      eqToHom (Category.assoc (obj := TwoFamily.Total finiteFamily) (arrow c.left.left.as)
        (arrow c.right.as.1) (arrow c.right.as.2)).symm ≫
      (interpretLeft c).2.2 ≫
      eqToHom (Category.assoc (obj := TwoFamily.Total finiteFamily) (arrow c.left.right.as)
        (arrow c.right.as.1) (arrow c.right.as.2)) :=
  TwoFamily.whisker_right_compose finiteFamily c.left.hom
    (arrow c.right.as.1) (arrow c.right.as.2)
    (Category.assoc (obj := TwoFamily.Total finiteFamily) _ _ _)
    (Category.assoc (obj := TwoFamily.Total finiteFamily) _ _ _)

namespace Boolean
abbrev Q := Bool
/-- The prescribed Boolean/mod-two group equivalence, in additive notation. -/
def encode : Bool ≃+ FiniteDependentCorrespondence.Q :=
  Examples.SecondIdentity.encode.toAdditive

/-- Fiber arrows, with mod-four witness cells as their category morphisms. -/
abbrev FiberArrow := Q

def π : R →+ FiberArrow := encode.symm.toAddMonoidHom.comp
  FiniteDependentCorrespondence.π

abbrev FiberCell (m n : FiberArrow) := {r : R // m = n + π r}

scoped instance : Groupoid FiberArrow where
  Hom := FiberCell
  id m := ⟨0, by simp⟩
  comp r s := ⟨r.val + s.val, by
    rcases r with ⟨r, hr⟩; rcases s with ⟨s, hs⟩
    dsimp at *
    rw [map_add, hr, hs]
    abel⟩
  id_comp r := Subtype.ext (zero_add r.val)
  comp_id r := Subtype.ext (add_zero r.val)
  assoc r s t := Subtype.ext (add_assoc r.val s.val t.val)
  inv r := ⟨-r.val, by rcases r with ⟨r, hr⟩; dsimp at *; rw [map_neg, hr]; abel⟩
  inv_comp r := Subtype.ext (neg_add_cancel r.val)
  comp_inv r := Subtype.ext (add_neg_cancel r.val)

@[simp] theorem transport_label {m n : FiberArrow} (h : m = n) :
    (eqToHom h : m ⟶ n).val = 0 := by cases h; rfl

@[simp] theorem comp_label {m n k : FiberArrow} (r : m ⟶ n) (s : n ⟶ k) :
    (r ≫ s).val = r.val + s.val := rfl

/-- The sole fiber object. Its hom-groupoid is not thin. -/
def FiniteFiber := Unit

instance : Bicategory FiniteFiber where
  Hom _ _ := FiberArrow
  id _ := 0
  comp m n := m + n
  homCategory _ _ := inferInstanceAs (Category FiberArrow)
  whiskerLeft k _ _ r := ⟨r.val, by rcases r with ⟨r, hr⟩; dsimp at *; rw [hr]; abel⟩
  whiskerRight r k := ⟨r.val, by rcases r with ⟨r, hr⟩; dsimp at *; rw [hr]; abel⟩
  associator m n k := eqToIso (add_assoc m n k)
  leftUnitor m := eqToIso (zero_add m)
  rightUnitor m := eqToIso (add_zero m)
  whiskerLeft_id _ _ := rfl
  whiskerLeft_comp := by intros; rfl
  id_whiskerLeft := by intros; apply Subtype.ext; simp
  comp_whiskerLeft := by intros; apply Subtype.ext; simp
  id_whiskerRight _ _ := rfl
  comp_whiskerRight _ _ _ := rfl
  whiskerRight_id := by intros; apply Subtype.ext; simp
  whiskerRight_comp := by intros; apply Subtype.ext; simp
  whisker_assoc := by intros; apply Subtype.ext; simp
  whisker_exchange := by intros; apply Subtype.ext; exact add_comm _ _
  pentagon := by intros; apply Subtype.ext; simp
  triangle := by intros; apply Subtype.ext; simp

instance : Bicategory.Strict FiniteFiber where
  id_comp m := by change (0 : FiberArrow) + m = m; exact zero_add (show FiberArrow from m)
  comp_id m := by exact add_zero (show FiberArrow from m)
  assoc m n k := by exact add_assoc (show FiberArrow from m) (show FiberArrow from n) (show FiberArrow from k)
  leftUnitor_eqToIso _ := rfl
  rightUnitor_eqToIso _ := rfl
  associator_eqToIso _ _ _ := rfl

instance (x y : FiniteFiber) : Groupoid (x ⟶ y) :=
  inferInstanceAs (Groupoid FiberArrow)

abbrev Base := DoubleDelooping.Space (Multiplicative Q)

def action (α : Multiplicative Q) : StrictTwoTransformation.Trans
    (StrictPseudofunctor.id FiniteFiber) (StrictPseudofunctor.id FiniteFiber) where
  app _ := Multiplicative.toAdd α
  naturality f := add_comm (show FiberArrow from f) (Multiplicative.toAdd α)
  naturality₂ r := by
    apply Subtype.ext
    change r.val + (eqToHom _ : (_ : FiberArrow) ⟶ _).val =
      (eqToHom _ : (_ : FiberArrow) ⟶ _).val + r.val
    simp

def finiteFamily : TwoFamily.Family Base := StrictPseudofunctor.mk'' {
  obj := fun _ => (⟨FiniteFiber⟩ : StrictTwoCategory)
  map := fun _ => StrictPseudofunctor.id _
  map₂ := action
  map₂_id := fun _ => by apply StrictTwoTransformation.Trans.ext; intro a; rfl
  map₂_comp := fun α β => by
    apply StrictTwoTransformation.Trans.ext; intro a
    exact add_comm (Multiplicative.toAdd β) (Multiplicative.toAdd α)
  map_id := fun _ => rfl
  map_comp := fun _ _ => (StrictTwoTransformation.functor_comp_id _).symm
  map₂_whisker_left := fun f _ _ α => by
    apply StrictTwoTransformation.Trans.ext; intro a
    repeat rw [StrictTwoTransformation.Trans.comp_app]
    repeat rw [StrictTwoTransformation.Trans.eqToHom_app]
    change (show a ⟶ a from Multiplicative.toAdd α) =
      𝟙 a ≫ Multiplicative.toAdd α ≫ 𝟙 a
    exact ((Category.id_comp _).trans (Category.comp_id _)).symm
  map₂_whisker_right := fun α f => by
    apply StrictTwoTransformation.Trans.ext; intro a
    repeat rw [StrictTwoTransformation.Trans.comp_app]
    repeat rw [StrictTwoTransformation.Trans.eqToHom_app]
    change (show a ⟶ a from Multiplicative.toAdd α) =
      𝟙 a ≫ Multiplicative.toAdd α ≫ 𝟙 a
    exact ((Category.id_comp _).trans (Category.comp_id _)).symm
}

def point : TwoFamily.Total finiteFamily :=
  ⟨DoubleDelooping.point _, ()⟩

def arrow (m : Q) : TwoFamily.Hom finiteFamily point point :=
  TwoGroupoidHom.arrow (TwoFamily.evaluation finiteFamily point.fiber)
    point.fiber (DoubleDelooping.arrow _) m

abbrev Coordinates (m n : Q) := {p : Q × R // m = n + p.1 + π p.2}

def dependentCellEquiv (m n : Q) : Coordinates m n ≃ (arrow m ⟶ arrow n) where
  toFun d := TwoGroupoidHom.cell (Multiplicative.ofAdd d.val.1)
    ⟨d.val.2, by change m = d.val.1 + n + π d.val.2; simpa only [add_comm d.val.1 n] using d.property⟩
  invFun c := ⟨(Multiplicative.toAdd c.base, c.fiber.val), by
    have h := c.fiber.property
    exact h.trans (by change (Multiplicative.toAdd c.base) + n + π c.fiber.val = n + (Multiplicative.toAdd c.base) + π c.fiber.val; rw [add_comm (Multiplicative.toAdd c.base) n])⟩
  left_inv _ := rfl
  right_inv _ := rfl

abbrev H := TwoFamily.Hom finiteFamily point point

@[simp] theorem fiber_whiskerLeft_label {x y z : FiniteFiber} (k : x ⟶ y)
    {m n : y ⟶ z} (r : m ⟶ n) : (k ◁ r).val = r.val := rfl
@[simp] theorem fiber_whiskerRight_label {x y z : FiniteFiber}
    {m n : x ⟶ y} (r : m ⟶ n) (k : y ⟶ z) : (r ▷ k).val = r.val := rfl

@[simp] theorem total_comp_label {p q r : H} (c : p ⟶ q) (d : q ⟶ r) :
    (c ≫ d).fiber.val = c.fiber.val + d.fiber.val := by
  rw [TwoFamily.fiber_comp]
  change c.fiber.val + (d.fiber.val + (eqToHom _ : (_ : FiberArrow) ⟶ _).val) = _
  simp only [transport_label, add_zero]

@[simp] theorem total_transport_label {p q : H} (h : p = q) :
    (eqToHom h).fiber.val = 0 := by
  rw [TwoFamily.total_eqToHom_fiber]
  exact transport_label _

@[simp] theorem total_whiskerRight_label {p q : H} (c : p ⟶ q) (k : H) :
    (TwoFamily.whiskerRight finiteFamily c k).fiber.val = c.fiber.val := by
  change ((eqToHom _ : (_ : FiberArrow) ⟶ _) ≫
    (_ ◁ (StrictPseudofunctor.id FiniteFiber).map₂ c.fiber) ▷ k.fiber ≫
    eqToHom _).val = c.fiber.val
  simp only [comp_label, transport_label, fiber_whiskerRight_label, fiber_whiskerLeft_label, zero_add, add_zero]
  rfl

@[simp] theorem total_whiskerLeft_label (k : H) {p q : H} (c : p ⟶ q) :
    (TwoFamily.whiskerLeft finiteFamily k c).fiber.val = c.fiber.val := by
  change (_ ◁ (_ ◁ c.fiber) ≫ (eqToHom _ : (_ : FiberArrow) ⟶ _)).val = _
  change c.fiber.val + (eqToHom _ : (_ : FiberArrow) ⟶ _).val = _
  simp only [transport_label, add_zero]

@[simp] theorem object_transport {x y : FiniteFiber} (h : x = y) :
    (show Q from eqToHom h) = 0 := by cases h; rfl

@[simp] theorem arrow_compose (m n : Q) :
    TwoFamily.compose finiteFamily (arrow m) (arrow n) = arrow (m + n) := by
  unfold TwoFamily.compose
  congr 1
  change (show Q from (eqToHom _ : point.fiber ⟶ point.fiber)) + (m + n) = m + n
  rw [object_transport, zero_add]

@[ext] theorem cell_ext {p q : H} {c d : p ⟶ q}
    (hb : c.base = d.base) (hr : c.fiber.val = d.fiber.val) : c = d := by
  cases c with | mk a r =>
    cases d with | mk b s =>
      dsimp at hb hr
      subst b
      have h : r = s := Subtype.ext hr
      cases h
      rfl

@[simp] theorem total_identity_label (p : H) : (𝟙 p : p ⟶ p).fiber.val = 0 :=
  total_transport_label rfl

def J : Discrete Q ⥤ H := Discrete.functor arrow

abbrev Boundary := CategoryTheory.Comma J J
abbrev Tail := CategoryTheory.Comma (GroupoidCorrespondence.terminal (Discrete Q))
  (GroupoidCorrespondence.terminal (Discrete (Q × Q)))
abbrev Left := CategoryTheory.Comma (GroupoidCorrespondence.terminal Boundary)
  (GroupoidCorrespondence.terminal (Discrete (Q × Q)))
abbrev Right := CategoryTheory.Comma J
  (CategoryTheory.Comma.fst (GroupoidCorrespondence.terminal (Discrete Q))
    (GroupoidCorrespondence.terminal (Discrete (Q × Q))) ⋙ J)

/-- The normal form retains the actual dependent total cell. -/
abbrev Normal := Σ m n : Q, (arrow m ⟶ arrow n) × Q × Q

def leftNormal : Left ≃ Normal where
  toFun c := ⟨c.left.left.as, c.left.right.as, c.left.hom, c.right.as⟩
  invFun c := ⟨⟨⟨c.1⟩, ⟨c.2.1⟩, c.2.2.1⟩, ⟨c.2.2.2⟩, 𝟙 _⟩
  left_inv c := by rcases c with ⟨⟨⟨m⟩, ⟨n⟩, c⟩, ⟨k,l⟩, h⟩; rfl
  right_inv _ := rfl

def rightNormal : Right ≃ Normal where
  toFun c := ⟨c.left.as, c.right.left.as, c.hom, c.right.right.as⟩
  invFun c := ⟨⟨c.1⟩, ⟨⟨c.2.1⟩, ⟨c.2.2.2⟩, 𝟙 _⟩, c.2.2.1⟩
  left_inv c := by rcases c with ⟨⟨m⟩, ⟨⟨n⟩, ⟨k,l⟩, h⟩, c⟩; rfl
  right_inv _ := rfl

def reassociate : Left ≌ Right :=
  (GroupoidCorrespondence.discreteEquivalence leftNormal).trans
    (GroupoidCorrespondence.discreteEquivalence rightNormal).symm

@[simp] theorem reassociate_full (c : Left) :
    rightNormal (reassociate.functor.obj c) = leftNormal c := rfl

/-- The boundary arrow of H is definitionally this same total 2-cell. -/
theorem dimensional_bridge (c : Left) :
    (reassociate.functor.obj c).hom =
      (show arrow c.left.left.as ⟶ arrow c.left.right.as from c.left.hom) := rfl

/-- Endpoint/cell packets retain complete cells, not just observations. -/
abbrev Packet := Σ p q : H, p ⟶ q

def interpretLeft (c : Left) : Packet :=
  ⟨_, _, TwoFamily.whiskerRight finiteFamily
    (TwoFamily.whiskerRight finiteFamily c.left.hom (arrow c.right.as.1))
    (arrow c.right.as.2)⟩

def interpretRight (c : Right) : Packet :=
  ⟨_, _, TwoFamily.whiskerRight finiteFamily c.hom
    (TwoFamily.compose finiteFamily (arrow c.right.right.as.1) (arrow c.right.right.as.2))⟩

theorem threefold (c : Left) :
    (interpretRight (reassociate.functor.obj c)).2.2 =
      eqToHom (Category.assoc (obj := TwoFamily.Total finiteFamily) (arrow c.left.left.as)
        (arrow c.right.as.1) (arrow c.right.as.2)).symm ≫
      (interpretLeft c).2.2 ≫
      eqToHom (Category.assoc (obj := TwoFamily.Total finiteFamily) (arrow c.left.right.as)
        (arrow c.right.as.1) (arrow c.right.as.2)) :=
  TwoFamily.whisker_right_compose finiteFamily c.left.hom
    (arrow c.right.as.1) (arrow c.right.as.2)
    (Category.assoc (obj := TwoFamily.Total finiteFamily) _ _ _)
    (Category.assoc (obj := TwoFamily.Total finiteFamily) _ _ _)

end Boolean
@[simp] theorem Boolean.encode_pi (r : R) : Boolean.encode (Boolean.π r) = FiniteDependentCorrespondence.π r :=
  Boolean.encode.apply_symm_apply _

@[simp] theorem arrow_fiber (p : H) : arrow p.fiber = p := by
  rcases p with ⟨⟨⟩, f⟩
  rfl
@[simp] theorem Boolean.arrow_fiber (p : Boolean.H) : Boolean.arrow p.fiber = p := by
  rcases p with ⟨⟨⟩, f⟩
  rfl

def encodeHom : Boolean.H ⥤ H where
  obj p := arrow (Boolean.encode p.fiber)
  map {p q} c := TwoGroupoidHom.cell
    (Examples.SecondIdentity.encode c.base) ⟨c.fiber.val, by
      have h := congrArg Boolean.encode c.fiber.property
      change Boolean.encode p.fiber = Boolean.encode
        (Multiplicative.toAdd c.base + (show Bool from q.fiber) + Boolean.π c.fiber.val) at h
      change Boolean.encode p.fiber = Boolean.encode (Multiplicative.toAdd c.base) +
        Boolean.encode q.fiber + π c.fiber.val
      simpa only [map_add, Boolean.encode_pi] using h⟩
  map_id p := by
    apply cell_ext
    · exact Examples.SecondIdentity.encode.map_one
    · exact (Boolean.total_identity_label p).trans (total_identity_label _).symm
  map_comp c d := by
    apply cell_ext
    · exact Examples.SecondIdentity.encode.map_mul d.base c.base
    · rw [total_comp_label]; exact Boolean.total_comp_label c d

def decodeHom : H ⥤ Boolean.H where
  obj p := Boolean.arrow (Boolean.encode.symm p.fiber)
  map {p q} c := TwoGroupoidHom.cell
    (Examples.SecondIdentity.encode.symm c.base) ⟨c.fiber.val, by
      have h := congrArg Boolean.encode.symm c.fiber.property
      change Boolean.encode.symm p.fiber = Boolean.encode.symm
        (Multiplicative.toAdd c.base + (show Q from q.fiber) + π c.fiber.val) at h
      change Boolean.encode.symm p.fiber = Boolean.encode.symm (Multiplicative.toAdd c.base) +
        Boolean.encode.symm q.fiber + Boolean.π c.fiber.val
      simpa only [map_add, Boolean.π, AddMonoidHom.comp_apply, AddEquiv.toAddMonoidHom_eq_coe, AddMonoidHom.coe_ofClass] using h⟩
  map_id p := by
    apply Boolean.cell_ext
    · exact Examples.SecondIdentity.encode.symm.map_one
    · exact (total_identity_label p).trans (Boolean.total_identity_label _).symm
  map_comp c d := by
    apply Boolean.cell_ext
    · exact Examples.SecondIdentity.encode.symm.map_mul d.base c.base
    · rw [Boolean.total_comp_label]; exact total_comp_label c d

@[simp] theorem total_transport_base {p q : H} (h : p = q) :
    (eqToHom h).base = (1 : Multiplicative Q) := by cases h; rfl
@[simp] theorem Boolean.total_transport_base {p q : Boolean.H} (h : p = q) :
    (eqToHom h).base = (1 : Multiplicative Bool) := by cases h; rfl

@[simp] theorem encodeHom_label {p q : Boolean.H} (c : p ⟶ q) :
    (encodeHom.map c).fiber.val = c.fiber.val := rfl
@[simp] theorem decodeHom_label {p q : H} (c : p ⟶ q) :
    (decodeHom.map c).fiber.val = c.fiber.val := rfl

@[simp] theorem decode_encode_obj (p : Boolean.H) : decodeHom.obj (encodeHom.obj p) = p := by
  change Boolean.arrow (Boolean.encode.symm (Boolean.encode p.fiber)) = p
  rw [Boolean.encode.symm_apply_apply, Boolean.arrow_fiber]
@[simp] theorem encode_decode_obj (p : H) : encodeHom.obj (decodeHom.obj p) = p := by
  change arrow (Boolean.encode (Boolean.encode.symm p.fiber)) = p
  rw [Boolean.encode.apply_symm_apply, arrow_fiber]

/-- Cross-base hom equivalence, retaining the actual mod-four fiber witness. -/
def homRepresentation : Boolean.H ≌ H where
  functor := encodeHom
  inverse := decodeHom
  unitIso := NatIso.ofComponents (fun p => eqToIso (decode_encode_obj p).symm) (by
    intro p q c
    simp only [eqToIso.hom, Functor.comp_map, Functor.id_map]
    apply Boolean.cell_ext
    · simp only [Pseudofunctor.CoGrothendieck.categoryStruct_comp_base,
        Boolean.total_transport_base]
      change (1 : Examples.SecondIdentity.Bit) * c.base =
        Examples.SecondIdentity.encode.symm (Examples.SecondIdentity.encode c.base) * 1
      simp
    · simp only [Boolean.total_comp_label, Boolean.total_transport_label,
        encodeHom_label, decodeHom_label, zero_add, add_zero])
  counitIso := NatIso.ofComponents (fun p => eqToIso (encode_decode_obj p)) (by
    intro p q c
    simp only [eqToIso.hom, Functor.comp_map, Functor.id_map]
    apply cell_ext
    · simp only [Pseudofunctor.CoGrothendieck.categoryStruct_comp_base,
        total_transport_base]
      change (1 : Examples.SecondIdentity.Label) * Examples.SecondIdentity.encode
        (Examples.SecondIdentity.encode.symm c.base) = (show Examples.SecondIdentity.Label from c.base) * 1
      simp
    · simp only [total_comp_label, total_transport_label,
        encodeHom_label, decodeHom_label, zero_add, add_zero])
  functor_unitIso_comp p := by
    change encodeHom.map (eqToHom (decode_encode_obj p).symm) ≫
      eqToHom (encode_decode_obj (encodeHom.obj p)) = 𝟙 _
    rw [eqToHom_map, eqToHom_trans]
    rfl

def encodeDiscrete : Discrete Bool ⥤ Discrete Q :=
  Discrete.functor (fun b => ⟨Boolean.encode b⟩)
def encodePair : Discrete (Bool × Bool) ⥤ Discrete (Q × Q) :=
  Discrete.functor (fun b => ⟨Boolean.encode b.1, Boolean.encode b.2⟩)

def encodeAlignment : encodeDiscrete ⋙ J ≅ Boolean.J ⋙ encodeHom :=
  Discrete.natIso (fun _ => Iso.refl _)

def mapBoundary : Boolean.Boundary ⥤ Boundary :=
  CategoryTheory.Comma.map encodeAlignment.hom encodeAlignment.inv

private def terminalAlignment {C D : Type*} [Category C] [Category D] (F : C ⥤ D) :
    F ⋙ GroupoidCorrespondence.terminal D ≅
      GroupoidCorrespondence.terminal C ⋙ 𝟭 GroupoidCorrespondence.Point :=
  NatIso.ofComponents (fun _ => Iso.refl _) (by intros; apply Subsingleton.elim)

def mapTail : Boolean.Tail ⥤ Tail :=
  CategoryTheory.Comma.map (terminalAlignment encodeDiscrete).hom
    (terminalAlignment encodePair).inv

/-- The left map acts directly on the inner comma and the later pair. -/
def mapLeft : Boolean.Left ⥤ Left :=
  CategoryTheory.Comma.map (terminalAlignment mapBoundary).hom
    (terminalAlignment encodePair).inv

def tailAlignment :
    (CategoryTheory.Comma.fst (GroupoidCorrespondence.terminal (Discrete Bool))
      (GroupoidCorrespondence.terminal (Discrete (Bool × Bool))) ⋙ Boolean.J) ⋙ encodeHom ≅
    mapTail ⋙ (CategoryTheory.Comma.fst (GroupoidCorrespondence.terminal (Discrete Q))
      (GroupoidCorrespondence.terminal (Discrete (Q × Q))) ⋙ J) :=
  NatIso.ofComponents (fun _ => Iso.refl _) (by
    intro p q f
    have h := IsDiscrete.eq_of_hom f
    subst q
    have hf : f = 𝟙 p := Subsingleton.elim _ _
    subst f
    simp)

/-- The right map acts directly on its two comma components. -/
def mapRight : Boolean.Right ⥤ Right :=
  CategoryTheory.Comma.map encodeAlignment.hom tailAlignment.hom

@[simp] theorem mapBoundary_cell (c : Boolean.Boundary) :
    (mapBoundary.obj c).hom = encodeHom.map c.hom := by
  change 𝟙 _ ≫ encodeHom.map c.hom ≫ 𝟙 _ = _
  simp only [Category.id_comp, Category.comp_id]

@[simp] theorem mapRight_cell (c : Boolean.Right) :
    (mapRight.obj c).hom = encodeHom.map c.hom := by
  change 𝟙 _ ≫ encodeHom.map c.hom ≫ 𝟙 _ = _
  simp only [Category.id_comp, Category.comp_id]

/-- Both independently defined maps have the same complete normal form. -/
theorem representation_reassociate_obj (c : Boolean.Left) :
    reassociate.functor.obj (mapLeft.obj c) =
      mapRight.obj (Boolean.reassociate.functor.obj c) := by
  apply rightNormal.injective
  change (⟨_, _, (mapBoundary.obj c.left).hom, _⟩ : Normal) = ⟨_, _, _, _⟩
  rw [mapBoundary_cell, mapRight_cell]
  rfl

def representationComparison : mapLeft ⋙ reassociate.functor ≅
    Boolean.reassociate.functor ⋙ mapRight :=
  NatIso.ofComponents (fun c => eqToIso (representation_reassociate_obj c))
    (by intros; apply Subsingleton.elim)

def objectRepresentation : Boolean.H ≃ H where
  toFun := encodeHom.obj
  invFun := decodeHom.obj
  left_inv := decode_encode_obj
  right_inv := encode_decode_obj

def packetRepresentation : Boolean.Packet ≃ Packet :=
  Equiv.sigmaCongr objectRepresentation (fun p =>
    Equiv.sigmaCongr objectRepresentation (fun q =>
      homRepresentation.fullyFaithfulFunctor.homEquiv (X := p) (Y := q)))

def normalRepresentation : Boolean.Normal ≃ Normal :=
  Equiv.sigmaCongr Boolean.encode (fun m =>
    Equiv.sigmaCongr Boolean.encode (fun n =>
      (homRepresentation.fullyFaithfulFunctor.homEquiv
        (X := Boolean.arrow m) (Y := Boolean.arrow n)).prodCongr
        (Boolean.encode.prodCongr Boolean.encode)))

@[simp] theorem mapLeft_full (c : Boolean.Left) :
    leftNormal (mapLeft.obj c) = normalRepresentation (Boolean.leftNormal c) := by
  change (⟨_, _, (mapBoundary.obj c.left).hom, _⟩ : Normal) = ⟨_, _, _, _⟩
  rw [mapBoundary_cell]
  rfl

@[simp] theorem mapRight_full (c : Boolean.Right) :
    rightNormal (mapRight.obj c) = normalRepresentation (Boolean.rightNormal c) := by
  change (⟨_, _, (mapRight.obj c).hom, _⟩ : Normal) = ⟨_, _, _, _⟩
  rw [mapRight_cell]
  rfl

theorem mapLeft_recovery (c : Boolean.Left) :
    Boolean.leftNormal.symm (normalRepresentation.symm (leftNormal (mapLeft.obj c))) = c := by
  rw [mapLeft_full, normalRepresentation.symm_apply_apply, Boolean.leftNormal.symm_apply_apply]

theorem mapRight_recovery (c : Boolean.Right) :
    Boolean.rightNormal.symm (normalRepresentation.symm (rightNormal (mapRight.obj c))) = c := by
  rw [mapRight_full, normalRepresentation.symm_apply_apply, Boolean.rightNormal.symm_apply_apply]

@[simp] theorem encode_compose (p q : Boolean.H) :
    encodeHom.obj (TwoFamily.compose Boolean.finiteFamily p q) =
      TwoFamily.compose finiteFamily (encodeHom.obj p) (encodeHom.obj q) := by
  rw [← Boolean.arrow_fiber p, ← Boolean.arrow_fiber q, Boolean.arrow_compose]
  change arrow (Boolean.encode ((show Bool from p.fiber) + (show Bool from q.fiber))) =
    TwoFamily.compose finiteFamily (arrow (Boolean.encode p.fiber)) (arrow (Boolean.encode q.fiber))
  rw [arrow_compose, map_add]

@[simp] theorem total_whiskerRight_base {p q : H} (c : p ⟶ q) (k : H) :
    (TwoFamily.whiskerRight finiteFamily c k).base = c.base := rfl
@[simp] theorem Boolean.total_whiskerRight_base {p q : Boolean.H} (c : p ⟶ q) (k : Boolean.H) :
    (TwoFamily.whiskerRight Boolean.finiteFamily c k).base = c.base := rfl

/-- Composition compatibility displays both endpoint conversions. -/
theorem encode_whiskerRight {p q : Boolean.H} (c : p ⟶ q) (k : Boolean.H) :
    encodeHom.map (TwoFamily.whiskerRight Boolean.finiteFamily c k) =
      eqToHom (encode_compose p k) ≫
        TwoFamily.whiskerRight finiteFamily (encodeHom.map c) (encodeHom.obj k) ≫
        eqToHom (encode_compose q k).symm := by
  apply cell_ext
  · simp only [Pseudofunctor.CoGrothendieck.categoryStruct_comp_base,
      total_transport_base, total_whiskerRight_base]
    change Examples.SecondIdentity.encode c.base =
      (1 * Examples.SecondIdentity.encode c.base) * 1
    simp only [mul_one, one_mul]
  · simp only [encodeHom_label, Boolean.total_whiskerRight_label,
      total_comp_label, total_transport_label, total_whiskerRight_label, zero_add, add_zero]

private theorem packet_eq {p q p' q' : H} (hp : p = p') (hq : q = q')
    (c : p ⟶ q) (d : p' ⟶ q') (h : c = eqToHom hp ≫ d ≫ eqToHom hq.symm) :
    (⟨p, q, c⟩ : Packet) = ⟨p', q', d⟩ := by
  subst p'; subst q'
  simp only [eqToHom_refl, Category.id_comp, Category.comp_id] at h
  subst d
  rfl

def whiskerPacket (t : Packet) (k : H) : Packet :=
  ⟨_, _, TwoFamily.whiskerRight finiteFamily t.2.2 k⟩
def Boolean.whiskerPacket (t : Boolean.Packet) (k : Boolean.H) : Boolean.Packet :=
  ⟨_, _, TwoFamily.whiskerRight Boolean.finiteFamily t.2.2 k⟩

theorem encode_whisker_packet (t : Boolean.Packet) (k : Boolean.H) :
    packetRepresentation (Boolean.whiskerPacket t k) =
      whiskerPacket (packetRepresentation t) (encodeHom.obj k) :=
  packet_eq (encode_compose t.1 k) (encode_compose t.2.1 k) _ _
    (encode_whiskerRight t.2.2 k)

theorem interpretLeft_representation (c : Boolean.Left) :
    packetRepresentation (Boolean.interpretLeft c) = interpretLeft (mapLeft.obj c) := by
  change packetRepresentation (Boolean.whiskerPacket
    (Boolean.whiskerPacket ⟨_, _, c.left.hom⟩ (Boolean.arrow c.right.as.1))
    (Boolean.arrow c.right.as.2)) =
    whiskerPacket (whiskerPacket ⟨_, _, (mapBoundary.obj c.left).hom⟩
      (arrow (Boolean.encode c.right.as.1))) (arrow (Boolean.encode c.right.as.2))
  rw [mapBoundary_cell, encode_whisker_packet, encode_whisker_packet]
  rfl

theorem interpretRight_representation (c : Boolean.Right) :
    packetRepresentation (Boolean.interpretRight c) = interpretRight (mapRight.obj c) := by
  change packetRepresentation (Boolean.whiskerPacket ⟨_, _, c.hom⟩
    (TwoFamily.compose Boolean.finiteFamily (Boolean.arrow c.right.right.as.1)
      (Boolean.arrow c.right.right.as.2))) =
    whiskerPacket ⟨_, _, (mapRight.obj c).hom⟩
      (TwoFamily.compose finiteFamily (arrow (Boolean.encode c.right.right.as.1))
        (arrow (Boolean.encode c.right.right.as.2)))
  rw [mapRight_cell, encode_whisker_packet, encode_compose]
  rfl

theorem interpreted_reassociation_representation (c : Boolean.Left) :
    packetRepresentation (Boolean.interpretRight (Boolean.reassociate.functor.obj c)) =
      interpretRight (reassociate.functor.obj (mapLeft.obj c)) := by
  rw [interpretRight_representation, ← representation_reassociate_obj]

theorem interpretLeft_recovery (c : Boolean.Left) :
    packetRepresentation.symm (interpretLeft (mapLeft.obj c)) = Boolean.interpretLeft c := by
  rw [← interpretLeft_representation, packetRepresentation.symm_apply_apply]

theorem interpretRight_recovery (c : Boolean.Right) :
    packetRepresentation.symm (interpretRight (mapRight.obj c)) = Boolean.interpretRight c := by
  rw [← interpretRight_representation, packetRepresentation.symm_apply_apply]


@[simp] theorem total_compose_fiber (p q : H) :
    (TwoFamily.compose finiteFamily p q).fiber =
      (show Q from p.fiber) + (show Q from q.fiber) := by
  change (show Q from (eqToHom _ : point.fiber ⟶ point.fiber)) +
    ((show Q from p.fiber) + (show Q from q.fiber)) = _
  rw [object_transport, zero_add]

/-- All four visible coordinates, including the genuine witness label. -/
def packetView (t : Packet) : Q × Q × Q × R :=
  (t.1.fiber, t.2.1.fiber, Multiplicative.toAdd t.2.2.base, t.2.2.fiber.val)

theorem interpretLeft_view (c : Left) : packetView (interpretLeft c) =
    ((c.left.left.as + c.right.as.1) + c.right.as.2,
     (c.left.right.as + c.right.as.1) + c.right.as.2,
     Multiplicative.toAdd c.left.hom.base, c.left.hom.fiber.val) := by
  simp only [packetView, interpretLeft, total_compose_fiber,
    total_whiskerRight_base, total_whiskerRight_label]
  rfl

theorem packetView_injective : Function.Injective packetView := by
  rintro ⟨p,q,c⟩ ⟨p',q',d⟩ h
  have hp : p.fiber = p'.fiber := congrArg Prod.fst h
  have hq : q.fiber = q'.fiber := congrArg (fun v => v.2.1) h
  have ep : p = p' := (arrow_fiber p).symm.trans ((congrArg arrow hp).trans (arrow_fiber p'))
  have eq : q = q' := (arrow_fiber q).symm.trans ((congrArg arrow hq).trans (arrow_fiber q'))
  subst p'; subst q'
  have hb : c.base = d.base := congrArg (fun v => v.2.2.1) h
  have hr : c.fiber.val = d.fiber.val := congrArg (fun v => v.2.2.2) h
  cases cell_ext hb hr
  rfl

theorem interpretRight_view (c : Right) : packetView (interpretRight c) =
    (c.left.as + (c.right.right.as.1 + c.right.right.as.2),
     c.right.left.as + (c.right.right.as.1 + c.right.right.as.2),
     Multiplicative.toAdd c.hom.base, c.hom.fiber.val) := by
  simp only [packetView, interpretRight, total_compose_fiber,
    total_whiskerRight_base, total_whiskerRight_label]
  rfl

theorem interpretation_reassociate (c : Left) :
    interpretRight (reassociate.functor.obj c) = interpretLeft c := by
  apply packetView_injective
  rw [interpretRight_view, interpretLeft_view]
  change (c.left.left.as + (c.right.as.1 + c.right.as.2),
    c.left.right.as + (c.right.as.1 + c.right.as.2), _, _) = _
  simp only [add_assoc]
  rfl

def leftCell {m n : Q} (c : arrow m ⟶ arrow n) (k l : Q) : Left :=
  leftNormal.symm ⟨m, n, c, k, l⟩

theorem selectedOne_tail11 :
    packetView (interpretLeft (leftCell selectedOne 1 1)) = (0,0,1,1) := by
  rw [interpretLeft_view]
  rfl

theorem selectedThree_tail11 :
    packetView (interpretLeft (leftCell selectedThree 1 1)) = (0,0,1,3) := by
  rw [interpretLeft_view]
  rfl

theorem selectedOne_tail10 :
    packetView (interpretLeft (leftCell selectedOne 1 0)) = (1,1,1,1) := by
  rw [interpretLeft_view]
  rfl

theorem selectedThree_tail10 :
    packetView (interpretLeft (leftCell selectedThree 1 0)) = (1,1,1,3) := by
  rw [interpretLeft_view]
  rfl

/-- Erasure keeps endpoints and the base action, but drops the parallel witness. -/
def retained (t : Packet) : Q × Q × Q :=
  ((packetView t).1, (packetView t).2.1, (packetView t).2.2.1)
def observed (t : Packet) : Nat := (packetView t).2.2.2.val

theorem interpreted_no_reconstruction (k l : Q) :
    ¬ ∃ observe : (Q × Q × Q) → Nat, ∀ c : arrow 0 ⟶ arrow 0,
      observe (retained (interpretLeft (leftCell c k l))) =
        observed (interpretLeft (leftCell c k l)) := by
  rintro ⟨observe, h⟩
  have h₁ := h selectedOne
  have h₃ := h selectedThree
  simp only [retained, observed, interpretLeft_view] at h₁ h₃
  have bad : (1 : Nat) = 3 := h₁.symm.trans h₃
  exact (by decide : (1 : Nat) ≠ 3) bad

theorem interpreted_zero_rejected (k l : Q) :
    ¬ ((0 + k) + l : Q) = ((0 + k) + l) + 1 + π 0 := by
  simp only [map_zero, add_zero]
  intro h
  have bad := add_left_cancel (show ((0 + k) + l) + 0 = ((0 + k) + l) + 1 by simpa only [add_zero] using h)
  exact (by decide : (0 : Q) ≠ 1) bad

def Boolean.leftCell {m n : Bool} (c : Boolean.arrow m ⟶ Boolean.arrow n)
    (k l : Bool) : Boolean.Left := Boolean.leftNormal.symm ⟨m, n, c, k, l⟩

def Boolean.selectedOne : Boolean.arrow false ⟶ Boolean.arrow false :=
  Boolean.dependentCellEquiv false false ⟨(true,1), by decide⟩
def Boolean.selectedThree : Boolean.arrow false ⟶ Boolean.arrow false :=
  Boolean.dependentCellEquiv false false ⟨(true,3), by decide⟩

theorem mapLeft_selectedOne (k l : Bool) :
    mapLeft.obj (Boolean.leftCell Boolean.selectedOne k l) =
      leftCell selectedOne (Boolean.encode k) (Boolean.encode l) := by
  apply leftNormal.injective
  rw [mapLeft_full]
  rfl

theorem mapLeft_selectedThree (k l : Bool) :
    mapLeft.obj (Boolean.leftCell Boolean.selectedThree k l) =
      leftCell selectedThree (Boolean.encode k) (Boolean.encode l) := by
  apply leftNormal.injective
  rw [mapLeft_full]
  rfl

theorem represented_no_reconstruction (k l : Bool) :
    ¬ ∃ observe : (Q × Q × Q) → Nat, ∀ c : Boolean.arrow false ⟶ Boolean.arrow false,
      observe (retained (interpretLeft (mapLeft.obj (Boolean.leftCell c k l)))) =
        observed (interpretLeft (mapLeft.obj (Boolean.leftCell c k l))) := by
  rintro ⟨observe, h⟩
  have h₁ := h Boolean.selectedOne
  have h₃ := h Boolean.selectedThree
  rw [mapLeft_selectedOne] at h₁
  rw [mapLeft_selectedThree] at h₃
  simp only [retained, observed, interpretLeft_view] at h₁ h₃
  have bad : (1 : Nat) = 3 := h₁.symm.trans h₃
  exact (by decide : (1 : Nat) ≠ 3) bad

/-- The typing failure persists at either selected represented endpoint. -/
theorem represented_zero_rejected (k l : Bool) :
    ¬ ((0 + Boolean.encode k) + Boolean.encode l : Q) =
      ((0 + Boolean.encode k) + Boolean.encode l) + 1 + π 0 :=
  interpreted_zero_rejected _ _

/-- Both label coordinates add under actual vertical composition. -/
theorem vertical_coordinates {m n k : Q} (c : arrow m ⟶ arrow n) (d : arrow n ⟶ arrow k) :
    ((dependentCellEquiv m k).symm (c ≫ d)).val =
      (Multiplicative.toAdd c.base + Multiplicative.toAdd d.base, c.fiber.val + d.fiber.val) := by
  apply Prod.ext
  · exact add_comm (Multiplicative.toAdd d.base) (Multiplicative.toAdd c.base)
  · exact total_comp_label c d

instance : IsLocallyGroupoid (finiteFamily.obj point.base) :=
  fun _ _ => inferInstanceAs (IsGroupoid FiberArrow)

@[instance_reducible] noncomputable def homGroupoid : Groupoid H :=
  Groupoid.ofIsIso (fun _ => inferInstance)

theorem inverse_label {p q : H} (c : p ⟶ q) :
    (TwoGroupoidHom.inverse c).fiber.val = -c.fiber.val := by
  have h := congrArg (fun d : p ⟶ p => d.fiber.val) (TwoGroupoidHom.comp_inverse c)
  rw [total_comp_label, total_identity_label] at h
  exact eq_neg_of_add_eq_zero_right h

theorem inverse_coordinates {m n : Q} (c : arrow m ⟶ arrow n) :
    ((dependentCellEquiv n m).symm (TwoGroupoidHom.inverse c)).val =
      (-Multiplicative.toAdd c.base, -c.fiber.val) := by
  apply Prod.ext
  · change Multiplicative.toAdd (inv c.base) = -Multiplicative.toAdd c.base
    rw [SingleObj.inv_as_inv]
    rfl
  · exact inverse_label c

/-- Horizontal composition is actual right/left whiskering followed by composition. -/
theorem horizontal_labels {p q r s : H} (c : p ⟶ q) (d : r ⟶ s) :
    ((TwoFamily.whiskerRight finiteFamily c r ≫
      TwoFamily.whiskerLeft finiteFamily q d).base,
     (TwoFamily.whiskerRight finiteFamily c r ≫
      TwoFamily.whiskerLeft finiteFamily q d).fiber.val) =
    ((show Multiplicative Q from d.base) * (show Multiplicative Q from c.base), c.fiber.val + d.fiber.val) := by
  apply Prod.ext
  · rfl
  · rw [total_comp_label, total_whiskerRight_label, total_whiskerLeft_label]

/-- Every fiber arrow has an actual strict inverse. -/
theorem fiber_one_inverse {x y : FiniteFiber} (m : x ⟶ y) :
    ∃ n : y ⟶ x, m ≫ n = 𝟙 x ∧ n ≫ m = 𝟙 y :=
  ⟨-(show Q from m), add_neg_cancel (show Q from m), neg_add_cancel (show Q from m)⟩

instance : Finite FiniteFiber := inferInstanceAs (Finite Unit)
instance : Finite Boolean.FiniteFiber := inferInstanceAs (Finite Unit)

def arrowEquiv : Q ≃ H where
  toFun := arrow
  invFun p := p.fiber
  left_inv _ := rfl
  right_inv := arrow_fiber

instance : Finite H := Finite.of_equiv Q arrowEquiv
instance (p q : H) : Finite (p ⟶ q) := by
  rw [← arrow_fiber p, ← arrow_fiber q]
  exact Finite.of_equiv _ (dependentCellEquiv _ _)

def interpretLeftFunctor : Left ⥤ Discrete Packet where
  obj c := ⟨interpretLeft c⟩
  map f := Discrete.eqToHom (congrArg interpretLeft (IsDiscrete.eq_of_hom f))

def interpretRightFunctor : Right ⥤ Discrete Packet where
  obj c := ⟨interpretRight c⟩
  map f := Discrete.eqToHom (congrArg interpretRight (IsDiscrete.eq_of_hom f))

theorem whiskerPacket_view (t : Packet) (k : H) : packetView (whiskerPacket t k) =
    ((show Q from t.1.fiber) + (show Q from k.fiber), (show Q from t.2.1.fiber) + (show Q from k.fiber),
      Multiplicative.toAdd t.2.2.base, t.2.2.fiber.val) := by
  simp only [packetView, whiskerPacket, total_compose_fiber,
    total_whiskerRight_base, total_whiskerRight_label]

theorem packet_boundary (t : Packet) : (packetView t).1 =
    (packetView t).2.1 + (packetView t).2.2.1 + π (packetView t).2.2.2 := by
  have h := t.2.2.fiber.property
  change (show Q from t.1.fiber) = Multiplicative.toAdd t.2.2.base +
    (show Q from t.2.1.fiber) + π t.2.2.fiber.val at h
  change (show Q from t.1.fiber) = (show Q from t.2.1.fiber) +
    Multiplicative.toAdd t.2.2.base + π t.2.2.fiber.val
  simpa only [add_comm (Multiplicative.toAdd t.2.2.base) (show Q from t.2.1.fiber)] using h

/-- No actual total cell has the selected endpoints, base action, and erased witness. -/
theorem packet_zero_rejected (m : Q) : ¬ ∃ t : Packet, packetView t = (m,m,1,0) := by
  rintro ⟨t,h⟩
  have bad := packet_boundary t
  rw [h] at bad
  have impossible : (0 : Q) = 1 := add_left_cancel
    (show m + 0 = m + 1 by simpa only [map_zero, add_zero] using bad)
  exact (by decide : (0 : Q) ≠ 1) impossible

/-- First whiskering changes both endpoints and retains the witness. -/
theorem first_whisker_one :
    packetView (whiskerPacket ⟨arrow 0, arrow 0, selectedOne⟩ (arrow 1)) = (1,1,1,1) := by
  rw [whiskerPacket_view]
  rfl

theorem first_whisker_three :
    packetView (whiskerPacket ⟨arrow 0, arrow 0, selectedThree⟩ (arrow 1)) = (1,1,1,3) := by
  rw [whiskerPacket_view]
  rfl

instance : Finite Boolean.H := Finite.of_equiv H objectRepresentation.symm
instance (p q : Boolean.H) : Finite (p ⟶ q) :=
  Finite.of_equiv (encodeHom.obj p ⟶ encodeHom.obj q)
    (homRepresentation.fullyFaithfulFunctor.homEquiv (X := p) (Y := q)).symm

theorem right_no_reconstruction (k l : Q) :
    ¬ ∃ observe : (Q × Q × Q) → Nat, ∀ c : arrow 0 ⟶ arrow 0,
      observe (retained (interpretRight (reassociate.functor.obj (leftCell c k l)))) =
        observed (interpretRight (reassociate.functor.obj (leftCell c k l))) := by
  simpa only [interpretation_reassociate] using interpreted_no_reconstruction k l

theorem represented_right_no_reconstruction (k l : Bool) :
    ¬ ∃ observe : (Q × Q × Q) → Nat, ∀ c : Boolean.arrow false ⟶ Boolean.arrow false,
      observe (retained (interpretRight
        (mapRight.obj (Boolean.reassociate.functor.obj (Boolean.leftCell c k l))))) =
      observed (interpretRight
        (mapRight.obj (Boolean.reassociate.functor.obj (Boolean.leftCell c k l)))) := by
  simpa only [← representation_reassociate_obj, interpretation_reassociate] using
    represented_no_reconstruction k l

/-- The other whiskering also preserves the complete fiber witness. -/
theorem encode_whiskerLeft (k : Boolean.H) {p q : Boolean.H} (c : p ⟶ q) :
    encodeHom.map (TwoFamily.whiskerLeft Boolean.finiteFamily k c) =
      eqToHom (encode_compose k p) ≫
        TwoFamily.whiskerLeft finiteFamily (encodeHom.obj k) (encodeHom.map c) ≫
        eqToHom (encode_compose k q).symm := by
  apply cell_ext
  · simp only [Pseudofunctor.CoGrothendieck.categoryStruct_comp_base, total_transport_base]
    change Examples.SecondIdentity.encode c.base = (1 * Examples.SecondIdentity.encode c.base) * 1
    simp only [mul_one, one_mul]
  · simp only [encodeHom_label, Boolean.total_whiskerLeft_label,
      total_comp_label, total_transport_label, total_whiskerLeft_label, zero_add, add_zero]

end SquareKit.FiniteDependentCorrespondence
