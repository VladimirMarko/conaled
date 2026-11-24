import Mathlib.CategoryTheory.Comma.Basic
import Mathlib.CategoryTheory.SingleObj
import SquareKit.IndexedSumBaseChange

/-! A selected comma-boundary chain and recovery of ordinary discrete pullbacks. -/
set_option autoImplicit false
noncomputable section
namespace SquareKit.GroupoidCorrespondence
open CategoryTheory Limits
universe u v w v₁ v₂ v₃

instance commaIsDiscrete {A : Type u} {B : Type v} {C : Type w}
    [Category.{v₁} A] [Category.{v₂} B] [Category.{v₃} C] [IsDiscrete A] [IsDiscrete B]
    (L : A ⥤ C) (R : B ⥤ C) : IsDiscrete (Comma L R) where
  subsingleton X Y := ⟨fun f g => CommaMorphism.ext (Subsingleton.elim _ _) (Subsingleton.elim _ _)⟩
  eq_of_hom {X Y} f := by
    obtain ⟨a,b,h⟩ := X
    obtain ⟨a',b',h'⟩ := Y
    have ha := IsDiscrete.eq_of_hom f.left
    have hb := IsDiscrete.eq_of_hom f.right
    dsimp at ha hb
    subst a'
    subst b'
    have hl : f.left = 𝟙 a := Subsingleton.elim _ _
    have hr : f.right = 𝟙 b := Subsingleton.elim _ _
    have hh := f.w
    rw [hl,hr,CategoryTheory.Functor.map_id,CategoryTheory.Functor.map_id,Category.id_comp,Category.comp_id] at hh
    cases hh
    rfl

/-- Lift an object equivalence of a discrete category, retaining every morphism. -/
def discreteEquivalence {C : Type u} [Category.{v} C] [IsDiscrete C]
    {X : Type w} (e : C ≃ X) : C ≌ Discrete X where
  functor := {
    obj := fun c => ⟨e c⟩
    map := fun f => Discrete.eqToHom (congrArg e (IsDiscrete.eq_of_hom f)) }
  inverse := Discrete.functor e.symm
  unitIso := NatIso.ofComponents (fun c => eqToIso (e.symm_apply_apply c).symm)
  counitIso := NatIso.ofComponents (fun c => Discrete.eqToIso (e.apply_symm_apply c.as))

abbrev Point := Discrete PUnit.{1}

def terminal (C : Type u) [Category.{v} C] : C ⥤ Point := (Functor.const C).obj ⟨PUnit.unit⟩
def point (G : Type u) [Group G] : Point ⥤ SingleObj G :=
  Discrete.functor (fun _ => SingleObj.star G)
abbrev Boundary (G : Type u) [Group G] := Comma (point G) (point G)

instance (G : Type u) [Group G] : Groupoid (Boundary G) :=
  Groupoid.ofIsIso (fun _ => inferInstance)

def boundary (G : Type u) [Group G] (g : G) : Boundary G := ⟨⟨PUnit.unit⟩,⟨PUnit.unit⟩,g⟩

def boundaryEquiv (G : Type u) [Group G] : Boundary G ≃ G where
  toFun c := c.hom
  invFun := boundary G
  left_inv c := by rcases c with ⟨⟨⟨⟩⟩,⟨⟨⟩⟩,h⟩; rfl
  right_inv _ := rfl

def boundaryEquivalence (G : Type u) [Group G] : Boundary G ≌ Discrete G :=
  discreteEquivalence (boundaryEquiv G)

abbrev Tail := Comma (terminal Point) (terminal (Discrete Bool))
abbrev Left (G : Type u) [Group G] := Comma (terminal (Boundary G)) (terminal (Discrete Bool))
abbrev Right (G : Type u) [Group G] := Comma (point G) (Comma.fst (terminal Point) (terminal (Discrete Bool)) ⋙ point G)

instance : Groupoid Tail := Groupoid.ofIsIso (fun _ => inferInstance)
instance (G : Type u) [Group G] : Groupoid (Left G) := Groupoid.ofIsIso (fun _ => inferInstance)
instance (G : Type u) [Group G] : Groupoid (Right G) := Groupoid.ofIsIso (fun _ => inferInstance)

def left (G : Type u) [Group G] (g : G) (b : Bool) : Left G :=
  ⟨boundary G g,⟨b⟩,𝟙 _⟩
def right (G : Type u) [Group G] (g : G) (b : Bool) : Right G :=
  ⟨⟨PUnit.unit⟩,⟨⟨PUnit.unit⟩,⟨b⟩,𝟙 _⟩,g⟩

def leftEquiv (G : Type u) [Group G] : Left G ≃ G × Bool where
  toFun c := (c.left.hom,c.right.as)
  invFun p := left G p.1 p.2
  left_inv c := by rcases c with ⟨⟨⟨⟨⟩⟩,⟨⟨⟩⟩,h⟩,⟨b⟩,k⟩; rfl
  right_inv _ := rfl

def rightEquiv (G : Type u) [Group G] : Right G ≃ G × Bool where
  toFun c := (c.hom,c.right.right.as)
  invFun p := right G p.1 p.2
  left_inv c := by rcases c with ⟨⟨⟨⟩⟩,⟨⟨⟨⟩⟩,⟨b⟩,k⟩,h⟩; rfl
  right_inv _ := rfl

def reassociate (G : Type u) [Group G] : Left G ≌ Right G :=
  (discreteEquivalence (leftEquiv G)).trans (discreteEquivalence (rightEquiv G)).symm

theorem reassociate_boundary (G : Type u) [Group G] (c : Left G) :
    ((reassociate G).functor.obj c).hom = c.left.hom := rfl
theorem reassociate_boolean (G : Type u) [Group G] (c : Left G) :
    ((reassociate G).functor.obj c).right.right = c.right := rfl

/-- A discrete comma retains the actual matching equation. -/
def discreteMap {A X : Type u} (f : A ⟶ X) : Discrete A ⥤ Discrete X :=
  Discrete.functor (fun a => ⟨f a⟩)

def discreteCommaEquiv {A B X : Type u} (f : A ⟶ X) (g : B ⟶ X) :
    Comma (discreteMap f) (discreteMap g) ≃ Types.PullbackObj f g where
  toFun c := ⟨(c.left.as,c.right.as),Discrete.eq_of_hom c.hom⟩
  invFun c := ⟨⟨c.val.1⟩,⟨c.val.2⟩,Discrete.eqToHom c.property⟩
  left_inv c := by rcases c with ⟨⟨a⟩,⟨b⟩,h⟩; cases h; rfl
  right_inv _ := rfl

/-- Recovery lands in Mathlib's chosen pullback, not a new choice. -/
def discretePullback {A B X : Type u} (f : A ⟶ X) (g : B ⟶ X) :
    Comma (discreteMap f) (discreteMap g) ≌ Discrete (pullback f g) :=
  discreteEquivalence ((discreteCommaEquiv f g).trans (Types.pullbackIsoPullback f g).toEquiv.symm)

@[simp] theorem discretePullback_fst {A B X : Type u} (f : A ⟶ X) (g : B ⟶ X)
    (c : Comma (discreteMap f) (discreteMap g)) :
    pullback.fst f g ((discretePullback f g).functor.obj c).as = c.left.as :=
  ConcreteCategory.congr_hom (Types.pullbackIsoPullback_inv_fst f g) (discreteCommaEquiv f g c)
@[simp] theorem discretePullback_snd {A B X : Type u} (f : A ⟶ X) (g : B ⟶ X)
    (c : Comma (discreteMap f) (discreteMap g)) :
    pullback.snd f g ((discretePullback f g).functor.obj c).as = c.right.as :=
  ConcreteCategory.congr_hom (Types.pullbackIsoPullback_inv_snd f g) (discreteCommaEquiv f g c)

/-- Exact connection to the existing selected payload encoder. -/
theorem discretePullback_encode {A X : Type u} (f : A ⟶ X) (V : Over X)
    (a : A) (x : {v : V.left // V.hom v = f a}) :
    ((discretePullback V.hom f).functor.obj
      ⟨⟨x.val⟩,⟨a⟩,Discrete.eqToHom x.property⟩).as =
      IndexedSumBaseChange.encode f V a x := rfl

/-- The base representation change acts on actual group arrows. -/
def groupEquivalence {G : Type u} {H : Type v} [Group G] [Group H]
    (e : G ≃* H) : SingleObj G ≌ SingleObj H where
  functor := SingleObj.mapHom G H e.toMonoidHom
  inverse := SingleObj.mapHom H G e.symm.toMonoidHom
  unitIso := NatIso.ofComponents (fun _ => Iso.refl _) (by
    intro a b f
    change 1 * f = e.symm (e f) * 1
    simp)
  counitIso := NatIso.ofComponents (fun _ => Iso.refl _) (by
    intro a b f
    change 1 * e (e.symm f) = f * 1
    simp)

  functor_unitIso_comp _ := by
    change 1 * e 1 = 1
    simp

/-- Mathlib's postcomposition keeps the two apices and applies the base map
only to the comma boundary. -/
def boundaryPost {G : Type u} {H : Type v} [Group G] [Group H] (e : G ≃* H) :=
  Comma.post (point G) (point G) (groupEquivalence e).functor

/-- Canonical endpoint alignment for the point functors. -/
def pointComparison {G : Type u} {H : Type v} [Group G] [Group H] (e : G ≃* H) :
    point G ⋙ (groupEquivalence e).functor ≅ point H :=
  Discrete.natIso (fun _ => Iso.refl _)

def changeBoundary {G : Type u} {H : Type v} [Group G] [Group H] (e : G ≃* H) :
    Boundary G ≌ Boundary H := by
  letI : (boundaryPost e).IsEquivalence := by
    dsimp [boundaryPost]
    infer_instance
  exact (boundaryPost e).asEquivalence |>.trans
    ((Comma.mapLeftIso (R := point G ⋙ (groupEquivalence e).functor) (pointComparison e)).trans
      (Comma.mapRightIso (L := point H) (pointComparison e)))

@[simp] theorem changeBoundary_hom {G : Type u} {H : Type v} [Group G] [Group H]
    (e : G ≃* H) (c : Boundary G) : ((changeBoundary e).functor.obj c).hom = e c.hom := by
  change 1 * (e c.hom * 1) = _
  simp

/-- Change both composite presentations through their complete normal forms. -/
def changeLeft {G : Type u} {H : Type v} [Group G] [Group H] (e : G ≃* H) : Left G ≌ Left H :=
  (Comma.equivProd _ _).trans
    (((changeBoundary e).prod (CategoryTheory.Equivalence.refl : Discrete Bool ≌ Discrete Bool)).trans
      (Comma.equivProd _ _).symm)

def changeRight {G : Type u} {H : Type v} [Group G] [Group H] (e : G ≃* H) : Right G ≌ Right H :=
  (reassociate G).symm.trans ((changeLeft e).trans (reassociate H))

@[simp] theorem changeLeft_boundary {G : Type u} {H : Type v} [Group G] [Group H]
    (e : G ≃* H) (c : Left G) : ((changeLeft e).functor.obj c).left.hom = e c.left.hom :=
  changeBoundary_hom e c.left
@[simp] theorem changeLeft_boolean {G : Type u} {H : Type v} [Group G] [Group H]
    (e : G ≃* H) (c : Left G) : ((changeLeft e).functor.obj c).right = c.right := rfl

/-- The selected representation square commutes on the entire comma object. -/
theorem representation_reassociate {G : Type u} {H : Type v} [Group G] [Group H]
    (e : G ≃* H) (c : Left G) :
    (reassociate H).functor.obj ((changeLeft e).functor.obj c) =
      (changeRight e).functor.obj ((reassociate G).functor.obj c) := by
  change right H _ _ = right H _ _
  rfl


/-- Both selected units are the existing comma/product unit equivalences. -/
def rightUnit (G : Type u) [Group G] :
    Comma (terminal (Boundary G)) (𝟭 Point) ≌ Boundary G :=
  Comma.toPUnitIdEquiv _ _
def leftUnit (G : Type u) [Group G] :
    Comma (𝟭 Point) (terminal (Boundary G)) ≌ Boundary G :=
  Comma.toIdPUnitEquiv _ _

/-- Forget only the third Boolean apex, retaining the whole first boundary. -/
def forgetBoolean (G : Type u) [Group G] : Left G ⥤ Comma (terminal (Boundary G)) (𝟭 Point) where
  obj c := ⟨c.left,⟨PUnit.unit⟩,𝟙 _⟩
  map f := ⟨f.left,𝟙 _,by apply Subsingleton.elim⟩

def headFromRight (G : Type u) [Group G] : Right G ⥤ Boundary G where
  obj c := ⟨c.left,c.right.left,c.hom⟩
  map f := ⟨f.left,f.right.left,f.w⟩

/-- Selected associativity followed by the unit projection recovers the same
whole comma boundary as projecting the left-associated composite. -/
theorem reassociate_unit (G : Type u) [Group G] (c : Left G) :
    (headFromRight G).obj ((reassociate G).functor.obj c) =
      (rightUnit G).functor.obj ((forgetBoolean G).obj c) :=
  (boundaryEquiv G).left_inv c.left

def reassociateUnitIso (G : Type u) [Group G] :
    (reassociate G).functor ⋙ headFromRight G ≅ forgetBoolean G ⋙ (rightUnit G).functor :=
  NatIso.ofComponents (fun c => eqToIso (reassociate_unit G c))

theorem leftUnit_recovery (G : Type u) [Group G] (c : Boundary G) :
    (leftUnit G).functor.obj ((leftUnit G).inverse.obj c) = c := rfl
theorem rightUnit_recovery (G : Type u) [Group G] (c : Boundary G) :
    (rightUnit G).functor.obj ((rightUnit G).inverse.obj c) = c := rfl

theorem reassociate_roundtrip (G : Type u) [Group G] (c : Left G) :
    (reassociate G).inverse.obj ((reassociate G).functor.obj c) = c :=
  IsDiscrete.eq_of_hom ((reassociate G).unitIso.inv.app c)
theorem reassociate_reverse_roundtrip (G : Type u) [Group G] (c : Right G) :
    (reassociate G).functor.obj ((reassociate G).inverse.obj c) = c :=
  IsDiscrete.eq_of_hom ((reassociate G).counitIso.hom.app c)

def representationReassociateIso {G : Type u} {H : Type v} [Group G] [Group H] (e : G ≃* H) :
    (changeLeft e).functor ⋙ (reassociate H).functor ≅
      (reassociate G).functor ⋙ (changeRight e).functor :=
  NatIso.ofComponents (fun c => eqToIso (representation_reassociate e c))

@[simp] theorem changeRight_boundary {G : Type u} {H : Type v} [Group G] [Group H]
    (e : G ≃* H) (c : Right G) : ((changeRight e).functor.obj c).hom = e c.hom :=
  changeBoundary_hom e (boundary G c.hom)
@[simp] theorem changeRight_boolean {G : Type u} {H : Type v} [Group G] [Group H]
    (e : G ≃* H) (c : Right G) : ((changeRight e).functor.obj c).right.right = c.right.right := rfl

theorem changeLeft_roundtrip {G : Type u} {H : Type v} [Group G] [Group H]
    (e : G ≃* H) (c : Left G) : (changeLeft e).inverse.obj ((changeLeft e).functor.obj c) = c :=
  IsDiscrete.eq_of_hom ((changeLeft e).unitIso.inv.app c)

theorem discretePullback_roundtrip {A B X : Type u} (f : A ⟶ X) (g : B ⟶ X)
    (c : Comma (discreteMap f) (discreteMap g)) :
    (discretePullback f g).inverse.obj ((discretePullback f g).functor.obj c) = c :=
  IsDiscrete.eq_of_hom ((discretePullback f g).unitIso.inv.app c)

@[simp] theorem discretePullback_inverse_fst {A B X : Type u} (f : A ⟶ X) (g : B ⟶ X)
    (c : pullback f g) : ((discretePullback f g).inverse.obj ⟨c⟩).left.as = pullback.fst f g c :=
  Types.pullbackIsoPullback_hom_fst f g c
@[simp] theorem discretePullback_inverse_snd {A B X : Type u} (f : A ⟶ X) (g : B ⟶ X)
    (c : pullback f g) : ((discretePullback f g).inverse.obj ⟨c⟩).right.as = pullback.snd f g c :=
  Types.pullbackIsoPullback_hom_snd f g c


/-- The tail composition has the existing left unit equivalence. -/
def tailUnit : Tail ≌ Discrete Bool := Comma.toIdPUnitEquiv _ _

/-- Reassociation respects the selected tail unitor on the entire final apex. -/
theorem reassociate_tail_unit (G : Type u) [Group G] (c : Left G) :
    tailUnit.functor.obj ((reassociate G).functor.obj c).right = c.right := rfl

/-- Together the selected unit projections recover the complete normalized
composite, not merely its final singleton endpoint. -/
theorem selected_unit_projections (G : Type u) [Group G] (c : Left G) :
    ((headFromRight G).obj ((reassociate G).functor.obj c),
      tailUnit.functor.obj ((reassociate G).functor.obj c).right) =
      ((rightUnit G).functor.obj ((forgetBoolean G).obj c),c.right) := by
  rw [reassociate_unit, reassociate_tail_unit]
end SquareKit.GroupoidCorrespondence
