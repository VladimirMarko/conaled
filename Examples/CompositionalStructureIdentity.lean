import SquareKit.Internal.Cubical.CartesianStructureIdentity
import Examples.CubicalFiniteStateIdentity
import Mathlib.Order.Lattice

/-! Generated preservation and law transport for monoids, orders and lattices.
Boolean complementation separates correct backwards argument transport from an
unchanged operation or relation. Native paths retain the supplied ua witness. -/
set_option autoImplicit false
set_option warningAsError true
namespace Examples.CompositionalStructureIdentity
open SquareKit.StructureIdentity

abbrev binary := Description.function .carrier (.function .carrier .carrier)
abbrev relation := Description.function .carrier (.function .carrier (.fixed Prop))
abbrev rawMonoid := Description.product .carrier binary
abbrev rawLattice := Description.product binary binary
abbrev oneContext := Description.product (.fixed Unit) .carrier
abbrev twoContext := Description.product (.fixed Unit) (.product .carrier .carrier)
abbrev threeContext := Description.product (.fixed Unit) (.product .carrier (.product .carrier .carrier))

def unitExpr {C : Description} : Expression rawMonoid C .carrier := .first .data
def mulExpr {C : Description} (a b : Expression rawMonoid C .carrier) :
    Expression rawMonoid C .carrier := .apply (.apply (.second .data) a) b

def monoid : Specification where
  description := rawMonoid
  law := .and
    (.all .carrier (.and
      (.equal (mulExpr unitExpr (.second .var)) (.second .var))
      (.equal (mulExpr (.second .var) unitExpr) (.second .var))))
    (.all (.product .carrier (.product .carrier .carrier))
      (let a : Expression rawMonoid threeContext .carrier := .first (.second .var)
       let b : Expression rawMonoid threeContext .carrier := .first (.second (.second .var))
       let c : Expression rawMonoid threeContext .carrier := .second (.second (.second .var))
       .equal (mulExpr (mulExpr a b) c) (mulExpr a (mulExpr b c))))

theorem monoid_laws {X : Type} (s : rawMonoid.Data X) :
    monoid.law.Eval (C := .fixed Unit) s () ↔
      (∀ x, s.2 s.1 x = x ∧ s.2 x s.1 = x) ∧
      (∀ x y z, s.2 (s.2 x y) z = s.2 x (s.2 y z)) := by
  constructor
  · intro h
    exact ⟨h.1, fun x y z => h.2 (x, y, z)⟩
  · intro h
    exact ⟨h.1, fun p => h.2 p.1 p.2.1 p.2.2⟩

def relExpr {C : Description} (a b : Expression relation C .carrier) :
    Formula relation C := .holds (.apply (.apply .data a) b)

def order : Specification where
  description := relation
  law := .and
    (.all .carrier (relExpr (.second .var) (.second .var)))
    (.and
      (.all (.product .carrier .carrier)
        (let a : Expression relation twoContext .carrier := .first (.second .var)
         let b : Expression relation twoContext .carrier := .second (.second .var)
         .implies (.and (relExpr a b) (relExpr b a)) (.equal a b)))
      (.all (.product .carrier (.product .carrier .carrier))
        (let a : Expression relation threeContext .carrier := .first (.second .var)
         let b : Expression relation threeContext .carrier := .first (.second (.second .var))
         let c : Expression relation threeContext .carrier := .second (.second (.second .var))
         .implies (.and (relExpr a b) (relExpr b c)) (relExpr a c))))

theorem order_laws {X : Type} (r : X → X → Prop) :
    order.law.Eval (D := relation) (C := .fixed Unit) (X := X) r () ↔
      (∀ x, r x x) ∧ (∀ x y, r x y → r y x → x = y) ∧
      (∀ x y z, r x y → r y z → r x z) := by
  constructor
  · intro h
    exact ⟨h.1, (fun x y hxy hyx => h.2.1 (x,y) ⟨hxy,hyx⟩),
      fun x y z hxy hyz => h.2.2 (x,y,z) ⟨hxy,hyz⟩⟩
  · intro h
    exact ⟨h.1, (fun p hp => h.2.1 p.1 p.2 hp.1 hp.2),
      fun p hp => h.2.2 p.1 p.2.1 p.2.2 hp.1 hp.2⟩

def opExpr {C : Description} (upper : Bool) (a b : Expression rawLattice C .carrier) :
    Expression rawLattice C .carrier :=
  .apply (.apply (if upper then .second .data else .first .data) a) b

def commutative (upper : Bool) : Formula rawLattice (.fixed Unit) :=
  .all (.product .carrier .carrier)
    (let a : Expression rawLattice twoContext .carrier := .first (.second .var)
     let b : Expression rawLattice twoContext .carrier := .second (.second .var)
     .equal (opExpr upper a b) (opExpr upper b a))

def associative (upper : Bool) : Formula rawLattice (.fixed Unit) :=
  .all (.product .carrier (.product .carrier .carrier))
    (let a : Expression rawLattice threeContext .carrier := .first (.second .var)
     let b : Expression rawLattice threeContext .carrier := .first (.second (.second .var))
     let c : Expression rawLattice threeContext .carrier := .second (.second (.second .var))
     .equal (opExpr upper (opExpr upper a b) c) (opExpr upper a (opExpr upper b c)))

def absorption (upper : Bool) : Formula rawLattice (.fixed Unit) :=
  .all (.product .carrier .carrier)
    (let a : Expression rawLattice twoContext .carrier := .first (.second .var)
     let b : Expression rawLattice twoContext .carrier := .second (.second .var)
     .equal (opExpr upper a (opExpr (!upper) a b)) a)

def lattice : Specification where
  description := rawLattice
  law := .and (.and (commutative false) (commutative true))
    (.and (.and (associative false) (associative true))
      (.and (absorption false) (absorption true)))

/-- The generated equations supply precisely Mathlib's algebraic lattice constructor. -/
@[instance_reducible] def latticeStructure {X : Type} (s : lattice.Model X) : Lattice X :=
  letI : Max X := ⟨s.val.2⟩
  letI : Min X := ⟨s.val.1⟩
  Lattice.mk'
    (fun a b => s.property.1.2 (a,b))
    (fun a b c => s.property.2.1.2 (a,b,c))
    (fun a b => s.property.1.1 (a,b))
    (fun a b c => s.property.2.1.1 (a,b,c))
    (fun a b => s.property.2.2.2 (a,b))
    (fun a b => s.property.2.2.1 (a,b))

def latticeModel (X : Type) [Lattice X] : lattice.Model X := by
  refine ⟨((fun x y => @Min.min X inferInstance x y), (fun x y => @Max.max X inferInstance x y)), ?_⟩
  dsimp [lattice, commutative, associative, absorption, opExpr, Formula.Eval, Expression.eval,
    Description.Data]
  exact ⟨⟨(fun p => inf_comm p.1 p.2), (fun p => sup_comm p.1 p.2)⟩,
    ⟨⟨(fun p => inf_assoc p.1 p.2.1 p.2.2), (fun p => sup_assoc p.1 p.2.1 p.2.2)⟩,
      ⟨(fun p => inf_sup_self), (fun p => sup_inf_self)⟩⟩⟩

theorem latticeStructure_inf {X : Type} (s : lattice.Model X) (x y : X) :
    (latticeStructure s).inf x y = s.val.1 x y := rfl

theorem latticeStructure_sup {X : Type} (s : lattice.Model X) (x y : X) :
    (latticeStructure s).sup x y = s.val.2 x y := rfl

theorem binary_preserves {X Y : Type} (e : X ≃ Y)
    (f : X → X → X) (g : Y → Y → Y) :
    binary.Preserves e f g ↔ ∀ x y, e (f x y) = g (e x) (e y) := by
  constructor
  · intro h x y
    exact h x (e x) rfl y (e y) rfl
  · intro h x x' hx y y' hy
    change e x = x' at hx
    change e y = y' at hy
    subst x'
    subst y'
    exact h x y

theorem relation_preserves {X Y : Type} (e : X ≃ Y)
    (r : X → X → Prop) (q : Y → Y → Prop) :
    relation.Preserves e r q ↔ ∀ x y, r x y ↔ q (e x) (e y) := by
  constructor
  · intro h x y
    exact Iff.of_eq (h x (e x) rfl y (e y) rfl)
  · intro h x x' hx y y' hy
    change e x = x' at hx
    change e y = y' at hy
    subst x'
    subst y'
    exact propext (h x y)

def boolMonoid : monoid.Model Bool := ⟨(false, Bool.xor), by
  apply (monoid_laws _).mpr
  simp [Description.Data]⟩
def boolOrder : order.Model Bool := ⟨(fun x y => x = false ∨ y = true), by
  apply (order_laws (X := Bool) _).mpr
  simp [Bool.forall_bool]
  exact ⟨⟨rfl, rfl⟩, fun _ _ => Or.inl rfl⟩⟩
def boolLattice : lattice.Model Bool := ⟨(Bool.and, Bool.or), by
  dsimp [lattice, commutative, associative, absorption, opExpr, Formula.Eval, Expression.eval]
  simp [Description.Data, Prod.forall, Bool.forall_bool]⟩

def complement : Bool ≃ Bool where
  toFun := Bool.not
  invFun := Bool.not
  left_inv := Bool.not_not
  right_inv := Bool.not_not

def transportedMonoid := monoid.transport complement boolMonoid
def transportedOrder := order.transport complement boolOrder
def transportedLattice := lattice.transport complement boolLattice

example : transportedMonoid.val.1 = true := rfl
example : transportedMonoid.val.2 false false = true := rfl
example : transportedLattice.val.1 false true = true := rfl
example : transportedLattice.val.2 false true = false := rfl
example : transportedLattice.val.1 true true = true := rfl
example : transportedLattice.val.2 false false = false := rfl
example : transportedOrder.val true false := by
  change false = false ∨ true = true
  exact Or.inl rfl

theorem unchanged_lattice_rejected :
    ¬ lattice.Preserves complement boolLattice boolLattice := by
  intro h
  have bad := (binary_preserves complement Bool.and Bool.and).mp h.1 false true
  exact Bool.noConfusion bad

theorem unchanged_relation_rejected :
    ¬ order.Preserves complement boolOrder boolOrder := by
  intro h
  have bad := (relation_preserves complement _ _).mp h false true
  have hn : ¬ boolOrder.val true false := by
    change ¬ (true = false ∨ false = true)
    decide
  exact hn (bad.mp (Or.inl rfl))

theorem monoid_unit_transferred :
    ∀ x, transportedMonoid.val.2 transportedMonoid.val.1 x = x :=
  fun x => ((monoid_laws _).mp transportedMonoid.property).1 x |>.1

theorem order_antisymmetry_transferred :
    ∀ x y, transportedOrder.val x y → transportedOrder.val y x → x = y :=
  ((order_laws _).mp transportedOrder.property).2.1

def idempotent : Formula rawMonoid .carrier :=
  .equal (mulExpr .var .var) .var

def falseIdempotent : idempotent.Solutions boolMonoid.val := ⟨false, rfl⟩

def idempotentsTransport : idempotent.Solutions boolMonoid.val ≃
    idempotent.Solutions transportedMonoid.val :=
  idempotent.solutionEquiv complement ((rawMonoid.preserves_iff _ _ _).mpr rfl)

example : (idempotentsTransport falseIdempotent).val = true := rfl

example :
    transportedMonoid.val.2 (idempotentsTransport falseIdempotent).val
      (idempotentsTransport falseIdempotent).val = (idempotentsTransport falseIdempotent).val :=
  (idempotentsTransport falseIdempotent).property

example : idempotentsTransport.symm (idempotentsTransport falseIdempotent) = falseIdempotent :=
  idempotentsTransport.symm_apply_apply _

example : monoid.transport complement.symm transportedMonoid = boolMonoid :=
  (monoid.transport complement).symm_apply_apply boolMonoid

open CategoryTheory SquareKit.Cubical SquareKit.Cubical.Presheaf
open CubicalStructuredState CubicalUnivalenceTransport CubicalFiniteStateIdentity

noncomputable def nativeLatticePath :=
  (Presheaf.StructureIdentity.specificationUaIdentity
    (codeIso complement).hom (HomotopyEquivalence.ofIso (codeIso complement))
    lattice boolLattice transportedLattice).symm
      ⟨by
        rw [admittedCarrier_of_iso]
        exact (lattice.preserves_iff _ _ _).mpr rfl⟩

noncomputable def cartesianLatticePath :=
  Cartesian.StructureIdentity.restrictPath lattice.toTransport _ _ _ _ _ nativeLatticePath

theorem native_lattice_recovery :
    (Presheaf.StructureIdentity.specificationUaIdentity
      (codeIso complement).hom (HomotopyEquivalence.ofIso (codeIso complement))
      lattice boolLattice transportedLattice).symm
      ((Presheaf.StructureIdentity.specificationUaIdentity
        (codeIso complement).hom (HomotopyEquivalence.ofIso (codeIso complement))
        lattice boolLattice transportedLattice) nativeLatticePath) = nativeLatticePath :=
  Equiv.symm_apply_apply _ _

abbrev rawState := Description.product .carrier
  (.product (.function .carrier .carrier) (.function .carrier (.fixed Prop)))

def stateInvariant {C : Description} (a : Expression rawState C .carrier) :
    Formula rawState C := .holds (.apply (.second (.second .data)) a)

def state : Specification where
  description := rawState
  law := .and (stateInvariant (.first .data))
    (.all .carrier (.implies (stateInvariant (.second .var))
      (stateInvariant (.apply (.first (.second .data)) (.second .var)))))

/-- Both invariant proofs are retained in the established package interface. -/
def stateModelEquiv (X : Type) : state.Model X ≃ CubicalStateTransport.StatePackage X where
  toFun s := {
    initial := s.val.1
    step := s.val.2.1
    Invariant := s.val.2.2
    initial_valid := s.property.1
    preserves := s.property.2 }
  invFun s := ⟨(s.initial, s.step, s.Invariant), ⟨s.initial_valid, s.preserves⟩⟩
  left_inv s := Subtype.ext rfl
  right_inv s := by
    apply CubicalStatePackageFamily.statePackage_ext <;> rfl

theorem state_transport {X Y : Type} (e : X ≃ Y) (s : state.Model X) :
    stateModelEquiv Y (state.transport e s) = (stateModelEquiv X s).conjugate e := by
  apply CubicalStatePackageFamily.statePackage_ext <;> rfl

theorem state_preservation {X Y : Type} (e : X ≃ Y) (s : state.Model X) (t : state.Model Y) :
    state.Preserves e s t ↔ CubicalStructuredState.Preserves e
      (stateModelEquiv X s) (stateModelEquiv Y t) := by
  rw [state.preserves_iff]
  constructor
  · intro h
    apply CubicalStructuredState.Preserves.of_eq
    exact (state_transport e s).symm.trans (congrArg (stateModelEquiv Y) h)
  · intro h
    apply (stateModelEquiv Y).injective
    exact (state_transport e s).trans h.package_eq

/-- The new generated path interface recovers the established native package
path, including both proof fields, for the same supplied equivalence witness. -/
noncomputable def statePathEquiv {X Y : Type}
    (f : decode (CubicalGlue.constantLocal terminal X).code ⟶
      decode (CubicalGlue.constantLocal terminal Y).code)
    (E : HomotopyEquivalence f) (s : state.Model X) (t : state.Model Y) :
    Presheaf.StructureIdentity.UaPath state.toTransport s t f E ≃
      CubicalStructuredState.StructuredPath (admittedLine f E) (admittedPresentation f E)
        (admittedCarrier f E) (stateModelEquiv X s) (stateModelEquiv Y t) where
  toFun p := (uaStructureIdentity f E _ _).symm
    ((state_preservation _ s t).mp
      ((Presheaf.StructureIdentity.specificationUaIdentity f E state s t) p).down)
  invFun p := (Presheaf.StructureIdentity.specificationUaIdentity f E state s t).symm
    ⟨(state_preservation _ s t).mpr ((uaStructureIdentity f E _ _) p)⟩
  left_inv p := by
    apply (Presheaf.StructureIdentity.specificationUaIdentity f E state s t).injective
    apply Subsingleton.elim
  right_inv p := by
    apply (uaStructureIdentity f E _ _).injective
    apply Subsingleton.elim

theorem unchanged_native_lattice_rejected :
    ¬ Nonempty (Presheaf.StructureIdentity.UaPath lattice.toTransport
      boolLattice boolLattice (codeIso complement).hom
      (HomotopyEquivalence.ofIso (codeIso complement))) := by
  rintro ⟨p⟩
  have h := ((Presheaf.StructureIdentity.specificationUaIdentity
    (codeIso complement).hom (HomotopyEquivalence.ofIso (codeIso complement))
    lattice boolLattice boolLattice) p).down
  rw [admittedCarrier_of_iso] at h
  exact unchanged_lattice_rejected h

theorem cartesian_path_recovery :
    (Cartesian.StructureIdentity.restrictionEquiv lattice.toTransport _ _ _ _ _).symm
      cartesianLatticePath = nativeLatticePath := by
  apply (Cartesian.StructureIdentity.restrictionEquiv lattice.toTransport _ _ _ _ _).injective
  rw [Equiv.apply_symm_apply]
  exact (Cartesian.StructureIdentity.restrictionEquiv_apply lattice.toTransport _ _ _ _ _
    nativeLatticePath).symm

def firstSwap : Fin 3 ≃ Fin 3 := Equiv.swap 0 1
def secondSwap : Fin 3 ≃ Fin 3 := Equiv.swap 1 2

example : Description.carrier.transport (firstSwap.trans secondSwap) (0 : Fin 3) = (2 : Fin 3) := by
  rw [Description.transport_trans]
  change secondSwap (firstSwap 0) = 2
  decide

example : Description.carrier.transport (secondSwap.trans firstSwap) (0 : Fin 3) = (1 : Fin 3) := by
  rw [Description.transport_trans]
  change firstSwap (secondSwap 0) = 1
  decide

/-- The generic law transport recovers the previous even/odd invariant client. -/
example :
    (stateModelEquiv Int (state.transport CubicalStateTransport.successor
      ((stateModelEquiv Int).symm CubicalStateTransport.evenPackage))).Invariant 3 := by
  rw [state_transport, Equiv.apply_symm_apply]
  change CubicalStateTransport.oddPackage.Invariant 3
  exact (CubicalStateTransport.odd_invariant 3).mpr rfl

end Examples.CompositionalStructureIdentity
