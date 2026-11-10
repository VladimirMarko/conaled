import SquareKit.CartesianMap
import Mathlib.CategoryTheory.Category.Quiv

/-! Fixed-universe Felix CAT is Mathlib Quiv: its objects carry no category operations. -/
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
namespace SquareKit.RawQuiv
universe u v
-- The two levels are intentionally fixed independently, as in Mathlib Quiv.
set_option linter.checkUnivs false in
abbrev Obj := CategoryTheory.Quiv.{v,u}
def ops : CategoryOps Obj.{u,v} := ofCategory Obj.{u,v}

def unitObj : Obj.{u,v} := ⟨PUnit.{u+1}, ⟨fun _ _ => PUnit.{v+1}⟩⟩
def productObj (A B : Obj.{u,v}) : Obj.{u,v} :=
  ⟨A × B, ⟨fun a b => (a.1 ⟶ b.1) × (a.2 ⟶ b.2)⟩⟩

def terminal : TerminalOps ops.{u,v} where
  unit := unitObj
  terminal := {obj := fun _ => PUnit.unit, map := fun _ => PUnit.unit}

def products : ProductOps ops.{u,v} where
  prod := productObj
  fst := {obj := Prod.fst, map := Prod.fst}
  snd := {obj := Prod.snd, map := Prod.snd}
  pair F G := {obj := fun a => (F.obj a,G.obj a), map := fun f => (F.map f,G.map f)}

/-- Recover the bundled quiver of raw category data, forgetting identities and composition. -/
def ofOps {O : Type u} (C : CategoryOps.{u,v} O) : Obj.{u,v} := ⟨O,⟨C.Hom⟩⟩

def ofRawMap {O P : Type u} {C : CategoryOps.{u,v} O} {D : CategoryOps.{u,v} P}
    (F : RawMap C D) : ops.Hom (ofOps C) (ofOps D) := ⟨F.obj,F.map⟩

def toRawMap {O P : Type u} {C : CategoryOps.{u,v} O} {D : CategoryOps.{u,v} P}
    (F : ops.Hom (ofOps C) (ofOps D)) : RawMap C D := ⟨F.obj,F.map⟩

@[simp] theorem raw_roundtrip {O P : Type u} {C : CategoryOps.{u,v} O} {D : CategoryOps.{u,v} P}
    (F : RawMap C D) : toRawMap (ofRawMap F) = F := rfl
@[simp] theorem quiv_roundtrip {O P : Type u} {C : CategoryOps.{u,v} O} {D : CategoryOps.{u,v} P}
    (F : ops.Hom (ofOps C) (ofOps D)) : ofRawMap (toRawMap F) = F := rfl

/-- These are precisely the operation-preservation fields of CAT.Functor. -/
abbrev FunctorLaws {O P : Type u} {C : CategoryOps.{u,v} O} {D : CategoryOps.{u,v} P}
    (F : ops.Hom (ofOps C) (ofOps D)) (E : HomEquiv C) (H : HomEquiv D) :=
  MapLaws (toRawMap F) E H
abbrev CartesianFunctorLaws {O P : Type u} {C : CategoryOps.{u,v} O} {D : CategoryOps.{u,v} P}
    (F : ops.Hom (ofOps C) (ofOps D)) {S : ProductOps C} {T : ProductOps D}
    (H : HomEquiv D) (i : ProductMap (toRawMap F) S T) := ProductMapLaws H i
end SquareKit.RawQuiv
