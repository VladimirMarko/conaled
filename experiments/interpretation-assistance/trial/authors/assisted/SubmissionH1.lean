import SquareKit.InterpretationDiagnostics
import TaskSetup462

import TaskSetup462
namespace AssistedH1
open Tasks462.H1 SquareKit.DiagonalConstruction
theorem extension : changeCodes.Extension source := by
  intro b _
  rfl
end AssistedH1

namespace Requested
def selectedSource := Tasks462.H1.source
def route := Tasks462.H1.changeCodes
def requirement_0 : Prop := SquareKit.DiagonalConstruction.Map.Extension route selectedSource
#transport_requirement Requested.requirement_0
def requestPresent : Unit := ()
#check selectedSource.code
#check selectedSource.witness
#check route.code selectedSource.code
#check route.value selectedSource.witness
theorem certificate_0 : requirement_0 := AssistedH1.extension
def result := route.selectedExtension selectedSource certificate_0
theorem observation : result.witness = route.value selectedSource.witness :=
  route.extension_witness selectedSource certificate_0
#check result.code
#check result.witness
#transport_audit Requested.result

end Requested

namespace AssistedH1
open Tasks462.H1 SquareKit.DiagonalConstruction
abbrev full := Requested.result

theorem full_code : full.code = some false := rfl
theorem full_witness : full.witness = false := rfl
theorem full_representation (b : Option Bool) :
    targetEval full.code b = diagonal targetEval targetStep b := full.represents b
theorem full_none : targetEval full.code none = diagonal targetEval targetStep none :=
  full_representation none

theorem not_surjective : ¬ Function.Surjective changeCodes.code := by
  intro h
  obtain ⟨a, ha⟩ := h none
  cases ha

def image := changeCodes.selectedImage source

theorem image_code : image.code.val = full.code := rfl
theorem image_witness : image.witness = full.witness := rfl
theorem image_representation (b : {b // ∃ a, changeCodes.code a = b}) :
    targetEval image.code.val b.val =
      diagonal (fun b c : {b // ∃ a, changeCodes.code a = b} => targetEval b.val c.val)
        targetStep b := image.represents b
theorem image_excludes_none (b : {b // ∃ a, changeCodes.code a = b}) :
    b.val ≠ none := by
  obtain ⟨a, ha⟩ := b.property
  intro hn
  rw [hn] at ha
  cases ha

theorem wrong_source : ¬ (∀ a, sourceEval true a = diagonal sourceEval sourceStep a) := by
  intro h
  have impossible := h false
  cases impossible
end AssistedH1
