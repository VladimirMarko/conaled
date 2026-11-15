import SquareKit.AssemblySliceLift

/-! Classifier-derived comparison between base change and slice lifting. -/

universe u
namespace Realizability.Assembly

/-- The underlying optional-value observation on a pulled-back slice lift. -/
def pulledValue {A B C : Assembly.{u}} (p : Hom A B) (f : Hom C B) :
    Hom (pullback f (sliceBase p)) (programLift A) :=
  (pullbackSnd f (sliceBase p)).comp (sliceValue p)

/-- Recover the actual partial value in the pulled-back fiber. The domain is
P1's admissible domain of the optional observation. -/
noncomputable def baseChangePartial {A B C : Assembly.{u}} (p : Hom A B) (f : Hom C B) :
    PartialMap (pullback f (sliceBase p)) (pullback f p) where
  domain := definedDomain (pulledValue p f)
  admissible := definedDomain_admissible (pulledValue p f)
  map := pullbackLift f p
    ((inclusion _ _).comp (pullbackFst f (sliceBase p)))
    (definedMap (pulledValue p f)) (Hom.ext fun d =>
      d.val.property.trans ((d.val.val.2).property _ (definedMap_spec (pulledValue p f) d)).symm)

/-- The forward comparison is obtained by classifying this recovered partial
map; it does not assume an equivalence of lifts. -/
noncomputable def baseChangeLift {A B C : Assembly.{u}} (p : Hom A B) (f : Hom C B) :
    Hom (pullback f (sliceBase p)) (sliceLift (pullbackFst f p)) :=
  sliceClassify (pullbackFst f p) (pullbackFst f (sliceBase p)) (baseChangePartial p f)
    (fun _ _ => rfl)

/-- Forget the redundant defined base coordinate, while retaining the current
base even on bottom. -/
def baseChangeUnlift {A B C : Assembly.{u}} (p : Hom A B) (f : Hom C B) :
    Hom (sliceLift (pullbackFst f p)) (pullback f (sliceBase p)) :=
  pullbackLift f (sliceBase p) (sliceBase (pullbackFst f p))
    (sliceMapAlong (pullbackFst f p) p f (pullbackSnd f p) (pullback_square f p).symm)
    (Hom.ext fun _ => rfl)

theorem baseChangeLift_graph {A B C : Assembly.{u}} (p : Hom A B) (f : Hom C B)
    (d : (pullback f (sliceBase p)).Carrier) (z : (pullback f p).Carrier) :
    ((baseChangeLift p f).toFun d).val.2 = some z ↔
      z.val.1 = d.val.1 ∧ d.val.2.val.2 = some z.val.2 := by
  apply ((baseChangePartial p f).classify_graph d z).trans
  constructor
  · rintro ⟨h, he⟩
    subst z
    exact ⟨rfl, definedMap_spec (pulledValue p f) ⟨d, h⟩⟩
  · rintro ⟨hz, hv⟩
    refine ⟨⟨z.val.2, hv⟩, ?_⟩
    apply Subtype.ext
    apply Prod.ext
    · exact hz.symm
    · exact Option.some.inj ((definedMap_spec (pulledValue p f) ⟨d, ⟨z.val.2, hv⟩⟩).symm.trans hv)

theorem baseChangeLift_none {A B C : Assembly.{u}} (p : Hom A B) (f : Hom C B)
    (d : (pullback f (sliceBase p)).Carrier) (h : d.val.2.val.2 = none) :
    ((baseChangeLift p f).toFun d).val.2 = none := by
  cases he : ((baseChangeLift p f).toFun d).val.2 with
  | none => rfl
  | some z =>
    have hz := ((baseChangeLift_graph p f d z).mp he).2
    have hc : (none : Option A.Carrier) = some z.val.2 := h.symm.trans hz
    cases hc

theorem baseChangeLift_base {A B C : Assembly.{u}} (p : Hom A B) (f : Hom C B) :
    (baseChangeLift p f).comp (sliceBase (pullbackFst f p)) = pullbackFst f (sliceBase p) :=
  Hom.ext fun _ => rfl

theorem baseChangeUnlift_base {A B C : Assembly.{u}} (p : Hom A B) (f : Hom C B) :
    (baseChangeUnlift p f).comp (pullbackFst f (sliceBase p)) = sliceBase (pullbackFst f p) :=
  Hom.ext fun _ => rfl

/-- Optional values are equal when their exact defined graphs agree. -/
private theorem option_ext {α : Type u} {a b : Option α}
    (h : ∀ x, a = some x ↔ b = some x) : a = b := by
  cases a with
  | none => cases hb : b with
    | none => rfl
    | some x => exact False.elim (by simpa using (h x).mpr hb)
  | some x => exact ((h x).mp rfl).symm

theorem baseChangeLift_unlift {A B C : Assembly.{u}} (p : Hom A B) (f : Hom C B) :
    (baseChangeLift p f).comp (baseChangeUnlift p f) = Hom.id (pullback f (sliceBase p)) := by
  apply Hom.ext
  intro d
  apply Subtype.ext
  apply Prod.ext
  · rfl
  · apply Subtype.ext
    apply Prod.ext
    · exact d.property
    · apply option_ext
      intro x
      change Option.map (fun z : (pullback f p).Carrier => z.val.2)
        ((baseChangeLift p f).toFun d).val.2 = some x ↔ d.val.2.val.2 = some x
      constructor
      · intro hm
        obtain ⟨z, hz, rfl⟩ := Option.map_eq_some_iff.mp hm
        exact ((baseChangeLift_graph p f d z).mp hz).2
      · intro hx
        let z : (pullback f p).Carrier :=
          ⟨(d.val.1, x), d.property.trans (d.val.2.property x hx).symm⟩
        exact Option.map_eq_some_iff.mpr ⟨z, (baseChangeLift_graph p f d z).mpr ⟨rfl, hx⟩, rfl⟩

theorem baseChangeUnlift_lift {A B C : Assembly.{u}} (p : Hom A B) (f : Hom C B) :
    (baseChangeUnlift p f).comp (baseChangeLift p f) = Hom.id (sliceLift (pullbackFst f p)) := by
  apply Hom.ext
  intro d
  apply Subtype.ext
  apply Prod.ext
  · rfl
  · apply option_ext
    intro z
    apply (baseChangeLift_graph p f ((baseChangeUnlift p f).toFun d) z).trans
    change z.val.1 = d.val.1 ∧ Option.map (fun z : (pullback f p).Carrier => z.val.2)
      d.val.2 = some z.val.2 ↔ d.val.2 = some z
    constructor
    · rintro ⟨hb, hv⟩
      obtain ⟨z', hz', he⟩ := Option.map_eq_some_iff.mp hv
      have hh : z' = z := Subtype.ext (Prod.ext ((d.property z' hz').trans hb.symm) he)
      exact hh ▸ hz'
    · intro hz
      exact ⟨d.property z hz, by simp [hz]⟩

open CategoryTheory

/-- The comparison is an isomorphism in the ordinary slice category. -/
noncomputable def baseChangeIso {A B C : Assembly.{u}} (p : Hom A B) (f : Hom C B) :
    Over.mk (T := Assembly.{u}) (pullbackFst f (sliceBase p)) ≅
      Over.mk (T := Assembly.{u}) (sliceBase (pullbackFst f p)) where
  hom := Over.homMk (baseChangeLift p f) (baseChangeLift_base p f)
  inv := Over.homMk (baseChangeUnlift p f) (baseChangeUnlift_base p f)
  hom_inv_id := Over.OverMorphism.ext (baseChangeLift_unlift p f)
  inv_hom_id := Over.OverMorphism.ext (baseChangeUnlift_lift p f)

end Realizability.Assembly
