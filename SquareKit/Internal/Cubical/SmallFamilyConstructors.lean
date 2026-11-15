import SquareKit.Internal.Cubical.SmallFamilyClassification
import SquareKit.Internal.Cubical.SumFillingSubstitution
import SquareKit.Internal.Cubical.FunctionFillingSubstitution
import SquareKit.Internal.Cubical.PathFillingSubstitution

/-! Constructor codes use the existing selected native providers after decoding
small lawful inputs. Products and dependent paths remain semantic constructions. -/
set_option autoImplicit false
set_option warningAsError true
namespace SquareKit.Cubical.Presheaf
open CategoryTheory
universe u

namespace LocalFamily

def sigma {Γ : Context.{u}} (A : LocalFamily Γ) (B : LocalFamily (total A.family)) : LocalFamily Γ :=
  ofNative ⟨⟨Presheaf.sigma A.family B.family,
    sigmaFilling A.toNative.filling A.toNative.lawful B.toNative.filling⟩,
    sigmaFilling_lawful A.toNative.filling A.toNative.lawful B.toNative.filling B.toNative.lawful⟩

noncomputable def pi {Γ : Context.{u}} (A : LocalFamily Γ) (B : LocalFamily (total A.family)) : LocalFamily Γ :=
  ofNative ⟨⟨Presheaf.pi A.family B.family,
    piFilling A.toNative.filling A.toNative.lawful B.toNative.filling⟩,
    piFilling_lawful A.toNative.filling A.toNative.lawful B.toNative.filling B.toNative.lawful⟩

noncomputable def path {Γ : Context.{u}} (B : LocalFamily (total (interval Γ)))
    (a₀ : Term (Presheaf.reindex B.family (endpointSub Γ false)))
    (a₁ : Term (Presheaf.reindex B.family (endpointSub Γ true))) : LocalFamily Γ :=
  ofNative ⟨⟨Presheaf.path B.family a₀ a₁,
    pathFilling B.toNative.filling B.toNative.lawful a₀ a₁⟩,
    pathFilling_lawful B.toNative.filling B.toNative.lawful a₀ a₁⟩

def discrete {Γ : Context.{u}} {T : Type u} (q : Term (constantFamily Γ T))
    (S : T → Type u) : LocalFamily Γ :=
  ofNative ⟨⟨discreteFamily q S, discreteFilling q S⟩, discreteFilling_lawful q S⟩

end LocalFamily

def sigmaCode {Γ : Context.{u}} (a : raisedContext Γ ⟶ smallFamilyCodes.{u})
    (b : raisedContext (total (decode a)) ⟶ smallFamilyCodes.{u}) :
    raisedContext Γ ⟶ smallFamilyCodes.{u} :=
  ((decodedLocalFamily a).sigma (decodedLocalFamily b)).code

noncomputable def piCode {Γ : Context.{u}} (a : raisedContext Γ ⟶ smallFamilyCodes.{u})
    (b : raisedContext (total (decode a)) ⟶ smallFamilyCodes.{u}) :
    raisedContext Γ ⟶ smallFamilyCodes.{u} :=
  ((decodedLocalFamily a).pi (decodedLocalFamily b)).code

noncomputable def pathCode {Γ : Context.{u}}
    (b : raisedContext (total (interval Γ)) ⟶ smallFamilyCodes.{u})
    (a₀ : Term (Presheaf.reindex (decode b) (endpointSub Γ false)))
    (a₁ : Term (Presheaf.reindex (decode b) (endpointSub Γ true))) :
    raisedContext Γ ⟶ smallFamilyCodes.{u} :=
  ((decodedLocalFamily b).path a₀ a₁).code

def discreteCode {Γ : Context.{u}} {T : Type u} (q : Term (constantFamily Γ T))
    (S : T → Type u) : raisedContext Γ ⟶ smallFamilyCodes.{u} :=
  (LocalFamily.discrete q S).code

def sigmaCode_decode {Γ : Context.{u}} (a : raisedContext Γ ⟶ smallFamilyCodes.{u})
    (b : raisedContext (total (decode a)) ⟶ smallFamilyCodes.{u}) :
    decode (sigmaCode a b) ≅ sigma (decode a) (decode b) :=
  ((decodedLocalFamily a).sigma (decodedLocalFamily b)).decodeCodeIso

noncomputable def piCode_decode {Γ : Context.{u}} (a : raisedContext Γ ⟶ smallFamilyCodes.{u})
    (b : raisedContext (total (decode a)) ⟶ smallFamilyCodes.{u}) :
    decode (piCode a b) ≅ pi (decode a) (decode b) :=
  ((decodedLocalFamily a).pi (decodedLocalFamily b)).decodeCodeIso

noncomputable def pathCode_decode {Γ : Context.{u}}
    (b : raisedContext (total (interval Γ)) ⟶ smallFamilyCodes.{u})
    (a₀ : Term (Presheaf.reindex (decode b) (endpointSub Γ false)))
    (a₁ : Term (Presheaf.reindex (decode b) (endpointSub Γ true))) :
    decode (pathCode b a₀ a₁) ≅ path (decode b) a₀ a₁ :=
  ((decodedLocalFamily b).path a₀ a₁).decodeCodeIso

def discreteCode_decode {Γ : Context.{u}} {T : Type u} (q : Term (constantFamily Γ T))
    (S : T → Type u) : decode (discreteCode q S) ≅ discreteFamily q S :=
  (LocalFamily.discrete q S).decodeCodeIso

end SquareKit.Cubical.Presheaf
