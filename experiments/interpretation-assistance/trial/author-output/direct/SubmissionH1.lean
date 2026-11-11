import TaskSetup462

namespace Tasks462.H1.Direct
open SquareKit.DiagonalConstruction

theorem extension : changeCodes.Extension source := by
  intro b _
  rfl

def fullTarget : Selected targetEval targetStep :=
  changeCodes.selectedExtension source extension

theorem full_code : fullTarget.code = some false := rfl
theorem full_witness : fullTarget.witness = false := rfl

theorem full_represents (b : Option Bool) :
    targetEval fullTarget.code b = diagonal targetEval targetStep b :=
  fullTarget.represents b

theorem full_represents_none :
    targetEval fullTarget.code none = diagonal targetEval targetStep none :=
  full_represents none

theorem not_surjective : ¬ Function.Surjective changeCodes.code := by
  intro h
  obtain ⟨a, ha⟩ := h none
  cases ha

abbrev ImageDomain := {b : Option Bool // ∃ a, changeCodes.code a = b}

def imageTarget : Selected (fun b c : ImageDomain => targetEval b.val c.val) targetStep :=
  changeCodes.selectedImage source

theorem image_code : imageTarget.code.val = fullTarget.code := rfl
theorem image_witness : imageTarget.witness = fullTarget.witness := rfl

theorem image_represents (b : ImageDomain) :
    targetEval imageTarget.code.val b.val =
      diagonal (fun b c : ImageDomain => targetEval b.val c.val) targetStep b :=
  imageTarget.represents b

theorem image_excludes_none (b : ImageDomain) : b.val ≠ none := by
  obtain ⟨a, ha⟩ := b.property
  intro hb
  have impossible : some a = none := ha.trans hb
  cases impossible

theorem true_fails : ¬ (∀ a, sourceEval true a = diagonal sourceEval sourceStep a) := by
  intro h
  have impossible : true = false := h false
  cases impossible

end Tasks462.H1.Direct
