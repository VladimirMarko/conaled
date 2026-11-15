import SquareKit.Internal.Cubical.UniverseDecode

/-! A universe path acts by the chosen filling of the universal decoding family. -/
set_option autoImplicit false
set_option warningAsError true
namespace SquareKit.Cubical.Presheaf.SmallUniverse
open CategoryTheory
universe u
variable {Γ : Context.{u+1}} {a b : Γ ⟶ smallFamilyCodes.{u}}

theorem liftedDecode_reindex {Δ : Context.{u+1}} (c : Γ ⟶ smallFamilyCodes.{u}) (σ : Δ ⟶ Γ) :
    reindex (liftedDecode c) σ = liftedDecode (σ ≫ c) := rfl

namespace NativeUnivalence
variable (p : Term (homogeneousPath (family Γ) (term a) (term b)))

theorem decode_zero :
    reindex (liftedDecode (codeOfPath p)) (endpointSub Γ false) = liftedDecode a :=
  congrArg liftedDecode (codeOfPath_zero p)

theorem decode_one :
    reindex (liftedDecode (codeOfPath p)) (endpointSub Γ true) = liftedDecode b :=
  congrArg liftedDecode (codeOfPath_one p)

/-- The map is actual interval transport in the universally decoded family. -/
noncomputable def pathToMap : liftedDecode a ⟶ liftedDecode b :=
  IntervalTransport.mapTo (NativeDecode.filling (codeOfPath p))
    (liftedDecode a) (liftedDecode b) (decode_zero p) (decode_one p)

/-- No inverse or contractibility witness is assumed: native homotopy fibers
are contracted by the chosen lawful interval filling. -/
noncomputable def pathToEquivalence : HomotopyEquivalence (pathToMap p) :=
  IntervalTransport.equivalenceTo (NativeDecode.filling (codeOfPath p))
    (NativeDecode.filling_lawful (codeOfPath p))
    (liftedDecode a) (liftedDecode b) (decode_zero p) (decode_one p)

end NativeUnivalence
end SquareKit.Cubical.Presheaf.SmallUniverse
