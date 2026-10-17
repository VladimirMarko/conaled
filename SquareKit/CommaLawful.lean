import SquareKit.Comma
import Mathlib.CategoryTheory.Comma.Basic

namespace SquareKit.Comma
universe u₁ v₁ u₂ v₂ u₃ v₃

section Lawful
open CategoryTheory
variable {A : Type u₁} {B : Type u₂} {T : Type u₃}
variable [Category.{v₁} A] [Category.{v₂} B] [Category.{v₃} T]
variable (F : A ⥤ T) (G : B ⥤ T)

/-- In the equality-lawful case the object data is exactly Mathlib's comma data. -/
def toMathlib (a : Obj (RawMap.ofFunctor F) (RawMap.ofFunctor G)) : CategoryTheory.Comma F G :=
  ⟨a.left, a.right, a.connector⟩
def fromMathlib (a : CategoryTheory.Comma F G) : Obj (RawMap.ofFunctor F) (RawMap.ofFunctor G) :=
  ⟨a.left, a.right, a.hom⟩
@[simp] theorem from_toMathlib (a : Obj (RawMap.ofFunctor F) (RawMap.ofFunctor G)) :
    fromMathlib F G (toMathlib F G a) = a := rfl
@[simp] theorem to_fromMathlib (a : CategoryTheory.Comma F G) :
    toMathlib F G (fromMathlib F G a) = a := rfl

def homToMathlib {a b : Obj (RawMap.ofFunctor F) (RawMap.ofFunctor G)}
    (f : Hom (equality _) a b) : toMathlib F G a ⟶ toMathlib F G b :=
  ⟨f.left, f.right, f.commutes⟩
def homFromMathlib {a b : CategoryTheory.Comma F G} (f : a ⟶ b) :
    Hom (equality _) (fromMathlib F G a) (fromMathlib F G b) := ⟨f.left, f.right, f.w⟩
@[simp] theorem homFrom_toMathlib {a b : Obj (RawMap.ofFunctor F) (RawMap.ofFunctor G)}
    (f : Hom (equality _) a b) : homFromMathlib F G (homToMathlib F G f) = f := rfl
@[simp] theorem homTo_fromMathlib {a b : CategoryTheory.Comma F G} (f : a ⟶ b) :
    homToMathlib F G (homFromMathlib F G f) = f := rfl

def mathlibMap : RawMap
    (ops (equalityCongr _) (ofCategoryLaws T) (RawMap.ofFunctor_laws F) (RawMap.ofFunctor_laws G))
    (ofCategory (CategoryTheory.Comma F G)) := ⟨toMathlib F G, homToMathlib F G⟩

theorem mathlibMap_laws : MapLaws (mathlibMap F G)
    (equiv (equalityCongr _) (ofCategoryLaws T) (RawMap.ofFunctor_laws F) (RawMap.ofFunctor_laws G))
    (equality _) where
  congr h := CategoryTheory.CommaMorphism.ext h.1 h.2
  ident := rfl
  comp _ _ := rfl

/-- This includes equality of both components, not merely equal interpreted arrows. -/
theorem mathlibMap_reflects : (mathlibMap F G).Reflects
    (equiv (equalityCongr _) (ofCategoryLaws T) (RawMap.ofFunctor_laws F) (RawMap.ofFunctor_laws G))
    (equality _) := fun h => ⟨congrArg CategoryTheory.CommaMorphism.left h,
      congrArg CategoryTheory.CommaMorphism.right h⟩
end Lawful

section Quotients
variable {A : Type u₁} {B : Type u₂} {T : Type u₃}
variable {C : CategoryOps.{u₁,v₁} A} {D : CategoryOps.{u₂,v₂} B}
variable {K : CategoryOps.{u₃,v₃} T}
variable {E : HomEquiv C} {J : HomEquiv D} {H : HomEquiv K}
variable {F : RawMap C K} {G : RawMap D K}
variable (CC : CategoryCongr C E) (CL : CategoryLaws C E)
variable (DC : CategoryCongr D J) (DL : CategoryLaws D J)
variable (KC : CategoryCongr K H) (KL : CategoryLaws K H)
variable (FL : MapLaws F E H) (GL : MapLaws G J H)

/-- Quotienting a connector produces a lawful comma object without choosing representatives. -/
def quotientObject (a : Obj F G) :
    letI := HomQuotient.category CC CL
    letI := HomQuotient.category DC DL
    letI := HomQuotient.category KC KL
    CategoryTheory.Comma
    (F.quotientFunctor FL CC CL KC KL) (G.quotientFunctor GL DC DL KC KL) :=
  by
    letI := HomQuotient.category CC CL
    letI := HomQuotient.category DC DL
    letI := HomQuotient.category KC KL
    exact ⟨⟨a.left⟩, ⟨a.right⟩, HomQuotient.classOf a.connector⟩

def quotientHom {a b : Obj F G} (f : Hom H a b) :
    letI := HomQuotient.category CC CL
    letI := HomQuotient.category DC DL
    letI := HomQuotient.category KC KL
    CategoryTheory.CommaMorphism (quotientObject CC CL DC DL KC KL FL GL a)
      (quotientObject CC CL DC DL KC KL FL GL b) := by
    letI := HomQuotient.category CC CL
    letI := HomQuotient.category DC DL
    letI := HomQuotient.category KC KL
    exact {
      left := HomQuotient.classOf f.left
      right := HomQuotient.classOf f.right
      w := Quotient.sound f.commutes }

/-- The bridge is itself a structure-preserving map, so it can compose with
Mathlib's comma projections or descend further to the source hom quotient. -/
def quotientMap :
    letI := HomQuotient.category CC CL
    letI := HomQuotient.category DC DL
    letI := HomQuotient.category KC KL
    RawMap (ops KC KL FL GL)
    (ofCategory (CategoryTheory.Comma
      (F.quotientFunctor FL CC CL KC KL) (G.quotientFunctor GL DC DL KC KL))) :=
by
    letI := HomQuotient.category CC CL
    letI := HomQuotient.category DC DL
    letI := HomQuotient.category KC KL
    exact ⟨quotientObject CC CL DC DL KC KL FL GL, quotientHom CC CL DC DL KC KL FL GL⟩

theorem quotientMap_laws :
    letI := HomQuotient.category CC CL
    letI := HomQuotient.category DC DL
    letI := HomQuotient.category KC KL
    MapLaws (quotientMap CC CL DC DL KC KL FL GL)
    (equiv KC KL FL GL) (equality _) := by
    let := HomQuotient.category CC CL
    let := HomQuotient.category DC DL
    let := HomQuotient.category KC KL
    exact {
      congr := fun h => CategoryTheory.CommaMorphism.ext (Quotient.sound h.1) (Quotient.sound h.2)
      ident := rfl
      comp := fun _ _ => rfl }

theorem quotientMap_eq_iff {a b : Obj F G} (f g : Hom H a b) :
    letI := HomQuotient.category CC CL
    letI := HomQuotient.category DC DL
    letI := HomQuotient.category KC KL
    (quotientMap CC CL DC DL KC KL FL GL).map f =
      (quotientMap CC CL DC DL KC KL FL GL).map g ↔ (equiv KC KL FL GL).Rel f g := by
    let := HomQuotient.category CC CL
    let := HomQuotient.category DC DL
    let := HomQuotient.category KC KL
    constructor
    · intro h
      exact ⟨Quotient.exact (congrArg CategoryTheory.CommaMorphism.left h),
      Quotient.exact (congrArg CategoryTheory.CommaMorphism.right h)⟩
    · exact (quotientMap_laws CC CL DC DL KC KL FL GL).congr
end Quotients
end SquareKit.Comma
