import Examples.AgdaTransferModels
import SquareKit.GroupoidTransportRoutes

/-! The same source transport construction through two composed routes.
The two-element family has monodromy; constant object cardinality does not
make it a constant functor. This tests first identity, not higher identities. -/
noncomputable section
namespace Examples.GroupoidRoutes
open CategoryTheory SquareKit.GroupoidTransport
open SquareKit.Internal.PathTransport
open Examples.GroupoidTransport
open Typed Typed.Authoring
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true

def parity : ZMod 4 →+* ZMod 2 := ZMod.castHom (by decide) (ZMod 2)

/-- The generator exchanges the two fibre elements. -/
abbrev binary : C4 ⥤ Type where
  obj _ := ZMod 2
  map p := ↾fun b => parity (Multiplicative.toAdd p) + b
  map_id _ := by ext b; exact zero_add b
  map_comp p q := by
    ext b
    change parity (Multiplicative.toAdd q + Multiplicative.toAdd p) + b = _
    rw [map_add, add_assoc]
    rfl

theorem generator_zero : binary.map (label 1) (0 : ZMod 2) = 1 := by
  change parity 1 + 0 = 1
  decide
theorem generator_one : binary.map (label 1) (1 : ZMod 2) = 0 := by
  change parity 1 + 1 = 0
  decide
theorem kernel_two (b : ZMod 2) : binary.map (label 2) b = b := by
  change (0 : ZMod 2) + b = b
  exact zero_add b

/-- Dependence is in transport, not in cardinality: there is no natural
isomorphism to the constant two-element family. -/
theorem not_constant : ¬ Nonempty (binary ≅ (Functor.const C4).obj (ZMod 2)) := by
  rintro ⟨e⟩
  have h := ConcreteCategory.congr_hom (e.hom.naturality (label 1)) (0 : ZMod 2)
  change e.hom.app point (binary.map (label 1) 0) = e.hom.app point 0 at h
  rw [generator_zero] at h
  exact (by decide : (1 : ZMod 2) ≠ 0) ((e.app point).toEquiv.injective h)

/-- Dependent pairs retain the arrow witnessing the change in fibre value. -/
def pair (b : ZMod 2) : binary.Elements := .mk (obj := point) b
def swapPair : pair 0 ⟶ pair 1 := Functor.Elements.homMk (label 1) generator_zero

theorem swapPair_label : swapPair.hom = label 1 := rfl

/-- Reverse the cyclic base label. This is a covariant functor because C₄ is abelian. -/
def reverseBase : C4 ⥤ C4 where
  obj _ := point
  map p := Multiplicative.ofAdd (-Multiplicative.toAdd p)
  map_id _ := by change Multiplicative.ofAdd (-(0 : ZMod 4)) = _; rfl
  map_comp p q := by
    change Multiplicative.ofAdd (-(Multiplicative.toAdd q + Multiplicative.toAdd p)) =
      Multiplicative.ofAdd (-Multiplicative.toAdd q + -Multiplicative.toAdd p)
    rw [neg_add]

/-- Change the fibre coordinate by one while reversing base labels. -/
def flipRoute : Route binary binary where
  base := reverseBase
  fiber :=
    { app := fun _ => ↾fun b => b + 1
      naturality := by
        intro x y p
        ext b
        have law : ∀ (n : ZMod 4) (b : ZMod 2),
            (parity n + b) + 1 = parity (-n) + (b + 1) := by decide
        exact law (Multiplicative.toAdd p) b }

abbrev doubleRoute := flipRoute.comp flipRoute

theorem route_label (n : ZMod 4) : flipRoute.base.map (label n) = label (-n) := rfl

theorem double_label (n : ZMod 4) : doubleRoute.base.map (label n) = label n := by
  change Multiplicative.ofAdd (-(-n)) = Multiplicative.ofAdd n
  rw [neg_neg]

theorem double_fiber (b : ZMod 2) : doubleRoute.fiber.app point b = b := by
  have h : ∀ b : ZMod 2, (b + 1) + 1 = b := by decide
  exact h b

/-- Source path observation is independent of the possibly ineffective action. -/
theorem double_source_label (B : C4 ⥤ Type) (b : B.obj point) (n : ZMod 4) :
    doubleRoute.base.map (Examples.AgdaTransferModels.sourceLabel B b n) = label n := by
  rw [Examples.AgdaTransferModels.sourceLabel_eq, double_label]

theorem routed_labels_injective :
    Function.Injective (fun n => doubleRoute.base.map (label n)) := by
  simpa only [double_label] using labels_injective

example : doubleRoute.base.map (label 2) ≠ doubleRoute.base.map (label 0) := by
  intro h
  exact (by decide : (2 : ZMod 4) ≠ 0) (routed_labels_injective h)

example (n : ZMod 4) :
    doubleRoute.base.map (Examples.AgdaTransferModels.sourceLabel ineffective (0 : Fin 2) n) =
      label n := double_source_label ineffective (0 : Fin 2) n

/-- The existing generated source transport term interpreted at arbitrary family B. -/
def sourceTransport (B : C4 ⥤ Type) (p q : point ⟶ point) (b : B.obj point) : B.obj point :=
  ((interpretTm (GroupoidModel.Instance.fullModel C4 B)
    Examples.AgdaTransferModels.firstTransport.deriv).down.obj
      (GroupoidModel.UniversalTransfer.inputs C4 B point point point p q b)).as

theorem sourceTransport_eq (B : C4 ⥤ Type) (p q : point ⟶ point) (b : B.obj point) :
    sourceTransport B p q b = B.map p b := by
  unfold sourceTransport
  rw [interpretTm_agrees]
  unfold Examples.AgdaTransferModels.firstTransport
  rw [GroupoidModel.SourceSemantics.transport_obj]
  rw [eq_of_heq (GroupoidModel.UniversalTransfer.first_obj C4 B point point point p q b),
    eq_of_heq (GroupoidModel.UniversalTransfer.element_obj C4 B point point point p q b)]
  rfl

/-- The same source term commutes with each coordinate route. -/
theorem source_route (p q : point ⟶ point) (b : ZMod 2) :
    flipRoute.fiber.app point (sourceTransport binary p q b) =
      sourceTransport binary (flipRoute.base.map p) (flipRoute.base.map q)
        (flipRoute.fiber.app point b) := by
  rw [sourceTransport_eq, sourceTransport_eq]
  exact flipRoute.transport p b

theorem composed_source_route (p q : point ⟶ point) (b : ZMod 2) :
    doubleRoute.fiber.app point (sourceTransport binary p q b) =
      sourceTransport binary (doubleRoute.base.map p) (doubleRoute.base.map q)
        (doubleRoute.fiber.app point b) := by
  rw [sourceTransport_eq, sourceTransport_eq]
  exact doubleRoute.transport p b

example : sourceTransport binary (label 1) (label 0) 0 = 1 := by
  rw [sourceTransport_eq]
  exact generator_zero

example : sourceTransport binary (doubleRoute.base.map (label 1))
    (doubleRoute.base.map (label 0)) (doubleRoute.fiber.app point 0) = 1 := by
  rw [← composed_source_route, sourceTransport_eq, generator_zero, double_fiber]

/-- Ordinary clients reuse the interpreted source concatenation law. -/
theorem two_transports (p q : point ⟶ point) (b : ZMod 2) :
    doubleRoute.fiber.app point (binary.map (p ≫ q) b) =
      binary.map (doubleRoute.base.map q)
        (binary.map (doubleRoute.base.map p) (doubleRoute.fiber.app point b)) :=
by
  rw [doubleRoute.transport, doubleRoute.base.map_comp]
  exact SquareKit.GroupoidTransport.transport_concat C4 binary _ _ _

namespace SourceSubstitution
open Typed.Authoring.UniversalTransfer

/-- A real source-context weakening adds an unused base point. -/
def extra := TyDeriv.base context
def projection := SubDeriv.weaken context extra

/-- The existing source rule substitutes both the path and fibre element.
This equality of model-indexed codes applies before choosing either route. -/
theorem weakened_transport :
    ((transport context first element).reindex projection).code =
      (transport (CtxDeriv.ext context extra)
        (first.reindex context projection) (element.reindex projection)).code :=
  transport_code_reindex context (CtxDeriv.ext context extra) first element projection
end SourceSubstitution

/-- Substitute the nonidentity base functor before taking either route. -/
theorem substitution_source (p q : point ⟶ point) (b : ZMod 2) :
    (doubleRoute.reindex reverseBase).fiber.app point
      (sourceTransport (reverseBase ⋙ binary) p q b) =
    sourceTransport binary (doubleRoute.base.map (reverseBase.map p))
      (doubleRoute.base.map (reverseBase.map q)) (doubleRoute.fiber.app point b) := by
  rw [sourceTransport_eq, sourceTransport_eq]
  exact doubleRoute.substitution_transport reverseBase p b

theorem substitution_composition :
    doubleRoute.reindex reverseBase = (flipRoute.reindex reverseBase).comp flipRoute :=
  Route.reindex_comp flipRoute flipRoute reverseBase

/-- Base substitution also retains the arrow-valued identity family. -/
theorem identity_substitution :
    GroupoidIdentity.family (reverseBase ⋙ 𝟭 C4) (reverseBase ⋙ 𝟭 C4) =
      reverseBase ⋙ GroupoidIdentity.family (𝟭 C4) (𝟭 C4) :=
  GroupoidIdentity.family_substitution reverseBase (𝟭 C4) (𝟭 C4)

theorem substituted_label (n : ZMod 4) :
    (doubleRoute.reindex reverseBase).base.map (label n) = label (-n) :=
  double_label (-n)

example : (doubleRoute.reindex reverseBase).base.map (label 1) = label 3 := by
  rw [substituted_label]
  rfl

/-- All fibre values lie in one orbit, but are not equal. -/
def SameOrbit (b c : ZMod 2) : Prop := ∃ p : point ⟶ point, binary.map p b = c

theorem sameOrbit_all (b c : ZMod 2) : SameOrbit b c := by
  have h : ∀ b c : ZMod 2, ∃ n : ZMod 4, parity n + b = c := by decide
  obtain ⟨n, hn⟩ := h b c
  exact ⟨label n, hn⟩

abbrev OrbitBase := Discrete Unit
def orbitPoint : OrbitBase := Discrete.mk ()
abbrev orbitFamily : OrbitBase ⥤ Type := (Functor.const OrbitBase).obj Unit

/-- Truncate both isotropy and the fibre orbit to the terminal data. -/
def forgetRoute : Route binary orbitFamily where
  base := (Functor.const C4).obj orbitPoint
  fiber := { app := fun _ => ↾fun _ => (), naturality := by intros; rfl }

def orbitForget (b : ZMod 2) : Unit := forgetRoute.fiber.app point b
def labelForget (p : point ⟶ point) : orbitPoint ⟶ orbitPoint := forgetRoute.base.map p

theorem orbit_exact (b c : ZMod 2) : orbitForget b = orbitForget c ↔ SameOrbit b c :=
  ⟨fun _ => sameOrbit_all b c, fun _ => rfl⟩

theorem no_fiber_observation :
    ¬ ∃ observe : Unit → ZMod 2, ∀ b, observe (orbitForget b) = b := by
  rintro ⟨f, h⟩
  have bad := (h 0).symm.trans (h 1)
  exact (by decide : (0 : ZMod 2) ≠ 1) bad

theorem no_label_observation :
    ¬ ∃ observe : (orbitPoint ⟶ orbitPoint) → ZMod 4, ∀ n, observe (labelForget (label n)) = n := by
  rintro ⟨f, h⟩
  have bad := (h 0).symm.trans (h 2)
  exact (by decide : (0 : ZMod 4) ≠ 2) bad

example : labelForget (label 1) = labelForget (label 0) := rfl
example : orbitForget (binary.map (label 1) 0) = orbitForget 0 := rfl
end Examples.GroupoidRoutes
