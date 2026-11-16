import SquareKit.StructureIdentity
import Examples.CubicalStructuredState
import SquareKit.Internal.Cubical.CartesianRealization

/-! Native structure families over presented discrete carriers.
The structure functor and its preservation relation are generated separately
from the native path construction. The supplied ua witness is retained. -/
set_option autoImplicit false
set_option warningAsError true
namespace SquareKit.Cubical.Presheaf.StructureIdentity
open CategoryTheory
open SquareKit.StructureIdentity
universe u

variable (F : Transport.{u}) {Γ : Context.{u}} (A : Family Γ) {S : Type u}
  (j : A ≅ constantFamily Γ S)

/-- Generalized elements are complete structures on the actual carrier fibers. -/
def family : Family Γ :=
  familyFromPresentation (fun x => F.Data (A.obj x)) (fun x => F.map (j.app x).toEquiv)

def presentation : family F A j ≅ constantFamily Γ (F.Data S) :=
  familyPresentation (fun x => F.Data (A.obj x)) (fun x => F.map (j.app x).toEquiv)

noncomputable def localFamily : LocalFamily Γ :=
  LocalFamily.ofNative ⟨⟨family F A j,
    presentationFilling (presentation F A j)⟩,
    presentationFilling_lawful (presentation F A j)⟩

def pull (s : F.Data S) : Term (family F A j) :=
  Term.map (presentation F A j).inv
    ⟨fun _ => s, fun _ => rfl⟩

theorem section_value (s : F.Data S) (x : Γ.Elements) :
    (pull F A j s).val x = (F.map (j.app x).toEquiv).symm s := rfl

theorem observe_pull (s : F.Data S) (x : Γ.Elements) :
    (presentation F A j).hom.app x ((pull F A j s).val x) = s :=
  (F.map (j.app x).toEquiv).apply_symm_apply s

end SquareKit.Cubical.Presheaf.StructureIdentity

namespace SquareKit.Cubical.Presheaf.StructureIdentity
open CategoryTheory SquareKit.StructureIdentity
open Examples.CubicalStatePackageUa

variable (F : Transport.{0}) {S T : Type}
  (A : Family (total (interval terminal.{0})))
  (j : A ≅ constantFamily (total (interval terminal.{0})) T)
  (e : S ≃ T) (s : F.Data S) (t : F.Data T)

/-- A native dependent path of complete structures along a presented carrier line.
The starting structure is written in the target chart by the derived transport. -/
abbrev StructuredPath :=
  Term (path (family F A j)
    ((pull F A j (F.map e s)).reindex (endpointSub terminal false))
    ((pull F A j t).reindex (endpointSub terminal true)))

theorem path_preserves (p : StructuredPath F A j e s t) : F.map e s = t := by
  let q := Term.map (presentation F A j).hom (pathApp p)
  have h₀ := congrArg (fun v => (presentation F A j).hom.app (endpointPoint false) (v.val point))
    (pathApp_zero p)
  have h₁ := congrArg (fun v => (presentation F A j).hom.app (endpointPoint true) (v.val point))
    (pathApp_one p)
  have hq := constant_section_interval q point ((endpoint terminal false).val point)
    ((endpoint terminal true).val point)
  exact (observe_pull F A j (F.map e s) (endpointPoint false)).symm.trans
    (h₀.symm.trans (hq.trans (h₁.trans (observe_pull F A j t (endpointPoint true)))))

def preservesPath (h : F.map e s = t) : StructuredPath F A j e s t :=
  pathLam (pull F A j (F.map e s)) rfl
    (congrArg (fun a => (pull F A j a).reindex (endpointSub terminal true)) h)

theorem path_recovery (p : StructuredPath F A j e s t) :
    preservesPath F A j e s t (path_preserves F A j e s t p) = p := by
  apply pathApp_injective
  apply presented_section_unique (presentation F A j)
  exact (pathApp_zero _).trans (pathApp_zero p).symm

/-- Exact recovery of native sections in the admitted discrete fragment. -/
def identityEquiv : StructuredPath F A j e s t ≃ PLift (F.map e s = t) where
  toFun p := ⟨path_preserves F A j e s t p⟩
  invFun h := preservesPath F A j e s t h.down
  left_inv := path_recovery F A j e s t
  right_inv _ := Subsingleton.elim _ _

open Examples.CubicalStructuredState Examples.CubicalGlue

variable (f : decode (constantLocal terminal S).code ⟶ decode (constantLocal terminal T).code)
  (E : HomotopyEquivalence f)

/-- The actual ua line retains the supplied native equivalence witness. -/
noncomputable abbrev UaPath :=
  StructuredPath F (admittedLine f E).family (admittedPresentation f E) (admittedCarrier f E) s t

noncomputable def uaIdentityEquiv : UaPath F s t f E ≃
    PLift (F.map (admittedCarrier f E) s = t) :=
  identityEquiv F _ _ _ s t

set_option backward.isDefEq.respectTransparency false in
/-- The generated structure at the source endpoint is the original structure,
when read using the actual source decoder rather than the target chart. -/
theorem ua_source (s : F.Data S) :
    F.map ((admittedStart f E).app point).toEquiv
      ((pull F (admittedLine f E).family (admittedPresentation f E)
        (F.map (admittedCarrier f E) s)).val (endpointPoint false)) = s := by
  have he := congrArg (fun k => (k.app point).toEquiv) (admittedPresentation_zero f E)
  simp only [NatIso.trans_app, Iso.toEquiv_comp] at he
  change ((admittedPresentation f E).app (endpointPoint false)).toEquiv =
    ((admittedStart f E).app point).toEquiv.trans (admittedCarrier f E) at he
  rw [section_value, he, F.map_trans]
  change F.map ((admittedStart f E).app point).toEquiv
    ((F.map ((admittedStart f E).app point).toEquiv).symm
      ((F.map (admittedCarrier f E)).symm (F.map (admittedCarrier f E) s))) = s
  rw [Equiv.symm_apply_apply, Equiv.apply_symm_apply]

set_option backward.isDefEq.respectTransparency false in
theorem ua_target (s : F.Data S) :
    F.map ((admittedFinish f E).app point).toEquiv
      ((pull F (admittedLine f E).family (admittedPresentation f E)
        (F.map (admittedCarrier f E) s)).val (endpointPoint true)) =
      F.map (admittedCarrier f E) s := by
  have he := congrArg (fun k => (k.app point).toEquiv) (admittedPresentation_one f E)
  change ((admittedPresentation f E).app (endpointPoint true)).toEquiv =
    ((admittedFinish f E).app point).toEquiv at he
  rw [section_value, he]
  exact (F.map _).apply_symm_apply _

/-- The chosen lawful filler returns the same complete section as the direct
constructor, not just the same observed endpoint. -/
theorem filling_recovery (v : F.Data T) :
    IntervalTransport.forward (localFamily F A j).toNative.filling (𝟙 terminal)
      ((pull F A j v).reindex (endpointSub terminal false)) = pull F A j v :=
  presented_section_unique (presentation F A j) _ _
    (IntervalTransport.forward_zero (localFamily F A j).toNative.filling
      (localFamily F A j).toNative.lawful (𝟙 terminal) _)

noncomputable def descriptionUaIdentity (D : Description.{0})
    (s : D.Data S) (t : D.Data T) :
    UaPath D.toTransport s t f E ≃ PLift (D.Preserves (admittedCarrier f E) s t) :=
  (uaIdentityEquiv D.toTransport s t f E).trans
    { toFun := fun h => ⟨(D.preserves_iff _ _ _).mpr h.down⟩
      invFun := fun h => ⟨(D.preserves_iff _ _ _).mp h.down⟩
      left_inv := fun _ => Subsingleton.elim _ _
      right_inv := fun _ => Subsingleton.elim _ _ }

noncomputable def specificationUaIdentity (L : Specification)
    (s : L.Model S) (t : L.Model T) :
    UaPath L.toTransport s t f E ≃ PLift (L.Preserves (admittedCarrier f E) s t) :=
  (uaIdentityEquiv L.toTransport s t f E).trans
    { toFun := fun h => ⟨(L.preserves_iff _ _ _).mpr h.down⟩
      invFun := fun h => ⟨(L.preserves_iff _ _ _).mp h.down⟩
      left_inv := fun _ => Subsingleton.elim _ _
      right_inv := fun _ => Subsingleton.elim _ _ }

end SquareKit.Cubical.Presheaf.StructureIdentity
