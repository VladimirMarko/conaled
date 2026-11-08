import SquareKit.AssemblyLiftMonad
import Mathlib.CategoryTheory.Comma.Over.Basic

/-! Base-retaining lifting for assembly slices (#386).
Bottom remains available separately over every base element. -/

universe u
namespace Realizability.Assembly

/-- Defined values must belong to the retained fiber; bottom imposes no
condition on that fiber. -/
def sliceCondition {A B : Assembly.{u}} (p : Hom A B)
    (bt : (prod B (programLift A)).Carrier) : Prop :=
  ∀ x, bt.2 = some x → p.toFun x = bt.1

def sliceLift {A B : Assembly.{u}} (p : Hom A B) : Assembly.{u} :=
  restrict (prod B (programLift A)) (sliceCondition p)

def sliceBase {A B : Assembly.{u}} (p : Hom A B) : Hom (sliceLift p) B :=
  (inclusion _ _).comp (fst _ _)

def sliceValue {A B : Assembly.{u}} (p : Hom A B) : Hom (sliceLift p) (programLift A) :=
  (inclusion _ _).comp (snd _ _)

/-- Package compatible tracked base and optional-value maps. -/
def slicePack {A B D : Assembly.{u}} (p : Hom A B) (b : Hom D B)
    (v : Hom D (programLift A))
    (h : ∀ d x, v.toFun d = some x → p.toFun x = b.toFun d) : Hom D (sliceLift p) :=
  factor _ (pair b v) h

@[simp] theorem slicePack_base {A B D : Assembly.{u}} (p : Hom A B) (b : Hom D B)
    (v : Hom D (programLift A)) (h : ∀ d x, v.toFun d = some x → p.toFun x = b.toFun d) :
    (slicePack p b v h).comp (sliceBase p) = b := Hom.ext fun _ => rfl

@[simp] theorem slicePack_value {A B D : Assembly.{u}} (p : Hom A B) (b : Hom D B)
    (v : Hom D (programLift A)) (h : ∀ d x, v.toFun d = some x → p.toFun x = b.toFun d) :
    (slicePack p b v h).comp (sliceValue p) = v := Hom.ext fun _ => rfl

theorem slice_ext {A B D : Assembly.{u}} (p : Hom A B) (f g : Hom D (sliceLift p))
    (hb : f.comp (sliceBase p) = g.comp (sliceBase p))
    (hv : f.comp (sliceValue p) = g.comp (sliceValue p)) : f = g := by
  apply Hom.ext
  intro x
  apply Subtype.ext
  exact Prod.ext (congrArg (fun k => k.toFun x) hb) (congrArg (fun k => k.toFun x) hv)

/-- Lift a map between fibers over the same base. -/
def sliceMap {A A' B : Assembly.{u}} (p : Hom A B) (q : Hom A' B)
    (f : Hom A A') (hf : f.comp q = p) : Hom (sliceLift p) (sliceLift q) :=
  slicePack q (sliceBase p) ((sliceValue p).comp (programLiftMap f)) fun d y h => by
    change Option.map f.toFun d.val.2 = some y at h
    cases hv : d.val.2 with
    | none => simp [hv] at h
    | some x =>
      have hxy : f.toFun x = y := by simpa [hv] using h
      subst y
      exact (congrArg (fun k => k.toFun x) hf).trans (d.property x hv)

def sliceUnit {A B : Assembly.{u}} (p : Hom A B) : Hom A (sliceLift p) :=
  slicePack p p (programLiftUnit A) fun _ _ h => by cases h; rfl

theorem sliceUnit_base {A B : Assembly.{u}} (p : Hom A B) :
    (sliceUnit p).comp (sliceBase p) = p := Hom.ext fun _ => rfl

/-- Change both base and total space along an actual commuting square. -/
def sliceMapAlong {A A' B B' : Assembly.{u}} (p : Hom A B) (q : Hom A' B')
    (b : Hom B B') (f : Hom A A') (hf : f.comp q = p.comp b) :
    Hom (sliceLift p) (sliceLift q) :=
  slicePack q ((sliceBase p).comp b) ((sliceValue p).comp (programLiftMap f)) fun d y h => by
    change Option.map f.toFun d.val.2 = some y at h
    cases hv : d.val.2 with
    | none => simp [hv] at h
    | some x =>
      have hxy : f.toFun x = y := by simpa [hv] using h
      subst y
      exact (congrArg (fun k => k.toFun x) hf).trans
        (congrArg b.toFun (d.property x hv))

/-- Classify a partial map in the slice using P1's classifier on its actual
inherited-realizer domain. -/
noncomputable def sliceClassify {A B D : Assembly.{u}} (p : Hom A B) (b : Hom D B)
    (f : PartialMap D A)
    (hf : ∀ x h, p.toFun (f.map.toFun ⟨x, h⟩) = b.toFun x) : Hom D (sliceLift p) :=
  slicePack p b f.classify fun x y hy => by
    obtain ⟨h, rfl⟩ := (f.classify_graph x y).mp hy
    exact hf x h

theorem sliceClassify_graph {A B D : Assembly.{u}} (p : Hom A B) (b : Hom D B)
    (f : PartialMap D A) (hf : ∀ x h, p.toFun (f.map.toFun ⟨x, h⟩) = b.toFun x)
    (x : D.Carrier) (y : A.Carrier) :
    ((sliceClassify p b f hf).toFun x).val.2 = some y ↔
      ∃ h, f.map.toFun ⟨x, h⟩ = y := f.classify_graph x y

theorem sliceClassify_unique {A B D : Assembly.{u}} (p : Hom A B) (b : Hom D B)
    (f : PartialMap D A) (hf : ∀ x h, p.toFun (f.map.toFun ⟨x, h⟩) = b.toFun x)
    (g : Hom D (sliceLift p)) (hb : g.comp (sliceBase p) = b)
    (hv : ∀ x y, (g.toFun x).val.2 = some y ↔ ∃ h, f.map.toFun ⟨x, h⟩ = y) :
    g = sliceClassify p b f hf := by
  apply slice_ext p
  · exact hb
  · exact f.classify_unique (g.comp (sliceValue p)) hv

/-- The recovered domain and map satisfy the slice constraint on every
admitted input, including maps whose domain has no computable decision. -/
theorem slice_unclassify_compatible {A B D : Assembly.{u}} (p : Hom A B) (b : Hom D B)
    (g : Hom D (sliceLift p)) (hb : g.comp (sliceBase p) = b)
    (x : D.Carrier) (h : (unclassify (g.comp (sliceValue p))).domain x) :
    p.toFun ((unclassify (g.comp (sliceValue p))).map.toFun ⟨x, h⟩) = b.toFun x :=
  ((g.toFun x).property _ (definedMap_spec (g.comp (sliceValue p)) ⟨x, h⟩)).trans
    (congrArg (fun k => k.toFun x) hb)

theorem sliceClassify_unclassify {A B D : Assembly.{u}} (p : Hom A B) (b : Hom D B)
    (g : Hom D (sliceLift p)) (hb : g.comp (sliceBase p) = b) :
    sliceClassify p b (unclassify (g.comp (sliceValue p)))
      (slice_unclassify_compatible p b g hb) = g := by
  apply slice_ext p
  · exact hb.symm
  · exact classify_unclassify (g.comp (sliceValue p))

/-- An empty partial map into any assembly, without a target inhabitant. -/
def nowhere (D A : Assembly.{u}) : PartialMap D A where
  domain _ := False
  admissible := admissible_empty D
  map := ⟨fun x => False.elim x.property, fun _ => Part.none, Nat.Partrec.none,
    fun x => False.elim x.property⟩

/-- Bottom is available uniformly at every base, with an actual tracker. -/
noncomputable def sliceBottom {A B : Assembly.{u}} (p : Hom A B) : Hom B (sliceLift p) :=
  sliceClassify p (Hom.id B) (nowhere B A) fun _ h => False.elim h

theorem sliceBottom_base {A B : Assembly.{u}} (p : Hom A B) :
    (sliceBottom p).comp (sliceBase p) = Hom.id B := Hom.ext fun _ => rfl

theorem sliceBottom_value {A B : Assembly.{u}} (p : Hom A B) (b : B.Carrier) :
    ((sliceBottom p).toFun b).val.2 = none := (nowhere B A).value_none b id

open CategoryTheory

def sliceLiftFunctor (B : Assembly.{u}) : Over B ⥤ Over B where
  obj X := Over.mk (sliceBase X.hom)
  map f := Over.homMk (sliceMap _ _ f.left (Over.w f)) (Hom.ext fun _ => rfl)
  map_id X := by
    apply Over.OverMorphism.ext
    apply Hom.ext
    rintro ⟨⟨b, t⟩, h⟩
    cases t <;> rfl
  map_comp f g := by
    apply Over.OverMorphism.ext
    apply Hom.ext
    rintro ⟨⟨b, t⟩, h⟩
    cases t <;> rfl

end Realizability.Assembly
