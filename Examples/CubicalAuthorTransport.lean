import Examples.CubicalFiniteStateIdentity
import SquareKit.Internal.Cubical.HomotopyEquivalenceComposition
import SquareKit.Internal.Cubical.SelectedInverse

/-! A bounded author interface retaining the supplied native equivalence and
whole dependent state package. Public examples are calibration, not trial data. -/
set_option autoImplicit false
set_option warningAsError true
namespace Examples.CubicalAuthorTransport
open CategoryTheory SquareKit.Cubical SquareKit.Cubical.Presheaf
open CubicalStateTransport CubicalStatePackageFamily CubicalStructuredState CubicalStatePackageUa
open CubicalUnivalenceTransport CubicalGlue

/-- Admission is restricted to the documented discrete carrier codes. The
complete supplied fiber contraction is retained, not reconstructed from an iso. -/
structure Change (S T : Type) where
  map : decode (constantLocal terminal S).code ⟶ decode (constantLocal terminal T).code
  equivalence : HomotopyEquivalence map

namespace Change
variable {S T V : Type}

noncomputable def ofEquiv (e : S ≃ T) : Change S T :=
  ⟨(codeIso e).hom, HomotopyEquivalence.ofIso (codeIso e)⟩

noncomputable def carrier (c : Change S T) : S ≃ T := admittedCarrier c.map c.equivalence

noncomputable def line (c : Change S T) := admittedLine c.map c.equivalence

noncomputable def universePath (c : Change S T) :=
  Univalence.ua _ _ c.map c.equivalence

noncomputable def nativeSection (c : Change S T) (p : StatePackage S) :=
  transported c.map c.equivalence p

/-- The result is decoded from actual package filling along the ua line. -/
noncomputable def transport (c : Change S T) (p : StatePackage S) : StatePackage T :=
  targetPackage c.map c.equivalence p

noncomputable abbrev PackagePath (c : Change S T) (p : StatePackage S) (q : StatePackage T) :=
  StructuredPath (line c) (admittedPresentation c.map c.equivalence) (carrier c) p q

noncomputable def packageIdentity (c : Change S T) (p : StatePackage S) (q : StatePackage T) :
    PackagePath c p q ≃ Preserves (carrier c) p q :=
  uaStructureIdentity c.map c.equivalence p q

noncomputable def path (c : Change S T) {p : StatePackage S} {q : StatePackage T}
    (h : Preserves (carrier c) p q) : PackagePath c p q :=
  (packageIdentity c p q).symm h

theorem native_recovery (c : Change S T) (p : StatePackage S) :
    nativeSection c p = CubicalStatePackageFamily.pullPackage (line c)
      (admittedPresentation c.map c.equivalence) (p.conjugate (carrier c)) :=
  transported_recovery c.map c.equivalence p

theorem transport_eq (c : Change S T) (p : StatePackage S) :
    transport c p = p.conjugate (carrier c) := targetPackage_eq c.map c.equivalence p

theorem transport_of_preserves (c : Change S T) {p : StatePackage S} {q : StatePackage T}
    (h : Preserves (carrier c) p q) : transport c p = q :=
  (transport_eq c p).trans h.package_eq

theorem path_recovery (c : Change S T) {p : StatePackage S} {q : StatePackage T}
    (r : PackagePath c p q) : path c (packageIdentity c p q r) = r :=
  (packageIdentity c p q).symm_apply_apply r

private noncomputable def toNativePath
    (f : decode (constantLocal terminal S).code ⟶ decode (constantLocal terminal T).code)
    (E : HomotopyEquivalence f) {p : StatePackage S} {q : StatePackage T}
    (r : (Change.mk f E).PackagePath p q) :
    StructuredPath (admittedLine f E) (admittedPresentation f E) (admittedCarrier f E) p q := by
  simpa only [PackagePath, line, carrier] using r

/-- Construct a facade path with a native-typed result. Supplying the native map
and its original witness here avoids normalizing bundled projections inside
concrete cubical path families. The construction still uses `Change.path`. -/
noncomputable def nativePath
    (f : decode (constantLocal terminal S).code ⟶ decode (constantLocal terminal T).code)
    (E : HomotopyEquivalence f) {p : StatePackage S} {q : StatePackage T}
    (h : Preserves (admittedCarrier f E) p q) :
    StructuredPath (admittedLine f E) (admittedPresentation f E) (admittedCarrier f E) p q :=
  toNativePath f E ((Change.mk f E).path h)

/-- The bridge retains the exact native constructor, not merely its decoded
observations or an independently chosen equivalence witness. -/
theorem nativePath_eq
    (f : decode (constantLocal terminal S).code ⟶ decode (constantLocal terminal T).code)
    (E : HomotopyEquivalence f) {p : StatePackage S} {q : StatePackage T}
    (h : Preserves (admittedCarrier f E) p q) :
    nativePath f E h = (uaStructureIdentity f E p q).symm h := by
  rfl

/-- Recovery at the native-typed boundary. This is the same fixed-equivalence
inverse law used by `path_recovery`, with no conversion of a concrete family. -/
theorem native_path_recovery
    (f : decode (constantLocal terminal S).code ⟶ decode (constantLocal terminal T).code)
    (E : HomotopyEquivalence f) {p : StatePackage S} {q : StatePackage T}
    (r : StructuredPath (admittedLine f E) (admittedPresentation f E)
      (admittedCarrier f E) p q) :
    (uaStructureIdentity f E p q).symm ((uaStructureIdentity f E p q) r) = r :=
  (uaStructureIdentity f E p q).symm_apply_apply r

theorem carrier_ofEquiv (e : S ≃ T) : (ofEquiv e).carrier = e :=
  CubicalFiniteStateIdentity.admittedCarrier_of_iso e

theorem transport_ofEquiv (e : S ≃ T) (p : StatePackage S) :
    (ofEquiv e).transport p = p.conjugate e := by
  rw [transport_eq, carrier_ofEquiv]

/-- Composition uses the generic contraction-of-composite-fibers theorem. -/
noncomputable def trans (c : Change S T) (d : Change T V) : Change S V where
  map := c.map ≫ d.map
  equivalence := c.equivalence.comp d.equivalence
    (decodedLocalFamily (constantLocal terminal S).code).toNative.filling
    (decodedLocalFamily (constantLocal terminal S).code).toNative.lawful
    (decodedLocalFamily (constantLocal terminal T).code).toNative.filling
    (decodedLocalFamily (constantLocal terminal T).code).toNative.lawful
    (decodedLocalFamily (constantLocal terminal V).code).toNative.filling
    (decodedLocalFamily (constantLocal terminal V).code).toNative.lawful

theorem carrier_apply (c : Change S T) (s : S) : c.carrier s =
    (constantLocal terminal T).decodeCodeIso.hom.app point
      (c.map.app point ((constantLocal terminal S).decodeCodeIso.inv.app point s)) := rfl

theorem carrier_trans (c : Change S T) (d : Change T V) :
    (c.trans d).carrier = c.carrier.trans d.carrier := by
  apply Equiv.ext
  intro s
  change (constantLocal terminal V).decodeCodeIso.hom.app point
      (d.map.app point (c.map.app point ((constantLocal terminal S).decodeCodeIso.inv.app point s))) =
    (constantLocal terminal V).decodeCodeIso.hom.app point
      (d.map.app point ((constantLocal terminal T).decodeCodeIso.inv.app point
        ((constantLocal terminal T).decodeCodeIso.hom.app point
          (c.map.app point ((constantLocal terminal S).decodeCodeIso.inv.app point s)))))
  simp

/-- Equality of decoded packages, including dependent fields. This is not an
identity between independently selected universe paths or native sections. -/
theorem transport_trans (c : Change S T) (d : Change T V) (p : StatePackage S) :
    (c.trans d).transport p = d.transport (c.transport p) := by
  rw [transport_eq, transport_eq, transport_eq, carrier_trans, conjugate_trans]

/-- Reverse the exact supplied center map using the general native inverse
construction. Discreteness is used only in the later decoded observation. -/
noncomputable def reverse (c : Change S T) : Change T S where
  map := c.equivalence.selectedInverse
  equivalence := c.equivalence.selectedInverseEquivalence
    (decodedLocalFamily (constantLocal terminal S).code).toNative.filling
    (decodedLocalFamily (constantLocal terminal S).code).toNative.lawful
    (decodedLocalFamily (constantLocal terminal T).code).toNative.filling
    (decodedLocalFamily (constantLocal terminal T).code).toNative.lawful

theorem carrier_reverse (c : Change S T) : c.reverse.carrier = c.carrier.symm := by
  apply Equiv.ext
  intro t
  rfl

theorem transport_roundtrip (c : Change S T) (p : StatePackage S) :
    c.reverse.transport (c.transport p) = p := by
  rw [transport_eq, transport_eq, carrier_reverse]
  exact conjugate_symm p c.carrier

end Change
end Examples.CubicalAuthorTransport
