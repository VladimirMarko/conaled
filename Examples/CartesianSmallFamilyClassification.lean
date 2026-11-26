import SquareKit.Internal.Cubical.CartesianSmallFamilyClassification
import SquareKit.Internal.Cubical.CartesianNerve
import SquareKit.Internal.Cubical.CartesianGlueFilling

/-! Classification retains selected variable-source operations and their substitution.
The generic cases impose no discrete or finite presentation on the family. -/
set_option autoImplicit false
set_option warningAsError true
namespace Examples.CartesianSmallFamilyClassification
open CategoryTheory SquareKit.Cubical.Cartesian
universe u

/-- Restriction to represented tests does not lose any chosen global output. -/
theorem global_roundtrip {Γ : Context.{u}} {A : Family Γ} (F : Filling A) (hF : F.Lawful) :
    F.toLocal.toFilling (Filling.toLocal_lawful hF) = F := F.toLocal_toFilling hF

/-- The classifier's inverse recovers every selected local operation. -/
theorem classifier_roundtrip {Γ : Context.{u}} (A : LocalFamily Γ) :
    (localFamilyEquiv Γ).symm ((localFamilyEquiv Γ) A) = A :=
  (localFamilyEquiv Γ).left_inv A

/-- Distinct lawful choices remain distinct even on the same underlying family. -/
theorem choices_separated {Γ : Context.{u}} (A B : LocalFamily Γ)
    (h : A.filling ≍ B.filling → False) : A.code ≠ B.code := by
  intro e
  have hab := (localFamilyEquiv Γ).injective e
  cases hab
  exact h HEq.rfl

noncomputable def finThree (Γ : Context) : LocalFamily Γ :=
  LocalFamily.ofFilling (constantFamily Γ (Fin 3)) (presentedFilling (Iso.refl _))
    (presentedFilling_lawful (Iso.refl _))

def variableSource : Term (interval (representable ⟨1⟩)) where
  val x := x.val
  property f := f.map_val

def duplicate : (⟨1⟩ : Cube) ⟶ ⟨2⟩ := fun _ => .var 0

/-- Duplicating a variable preserves the whole code, including its filling. -/
theorem finThree_duplicate :
    ((finThree (representable ⟨2⟩)).reindex (representableMap duplicate)).code =
      raisedSub (representableMap duplicate) ≫ (finThree (representable ⟨2⟩)).code :=
  (finThree (representable ⟨2⟩)).code_reindex _

/-- Decoding and refilling retains an arbitrary variable-source box output. -/
theorem finThree_variable_fill
    (p : total (interval (representable ⟨1⟩)) ⟶ representable ⟨1⟩)
    (φ : Subcontext (representable ⟨1⟩))
    (b : OpenBox (reindex (decode (finThree (representable ⟨1⟩)).code) p) φ variableSource) :
    (finThree (representable ⟨1⟩)).filling.fill p φ variableSource
      (b.map (Functor.whiskerLeft p.mapElements (finThree (representable ⟨1⟩)).decodeCodeIso.hom)) =
    Term.map (Functor.whiskerLeft p.mapElements (finThree (representable ⟨1⟩)).decodeCodeIso.hom)
      ((decodedLocalFilling (finThree (representable ⟨1⟩)).code).fill p φ variableSource b) :=
  (finThree (representable ⟨1⟩)).decodeCode_filling p φ variableSource b

/-- This client classifies the existing global tuple decoder with its actual filler. -/
noncomputable def tupleDecoder : LocalFamily finiteNerve.{u} :=
  LocalFamily.ofFilling TupleDecoder.family TupleDecoder.filling TupleDecoder.filling_lawful

theorem tupleDecoder_roundtrip : decodedLocalFamily tupleDecoder.{u}.code = tupleDecoder :=
  tupleDecoder.decodeCode_record

/-- In this global client the raised decoder lives in Type (u+1).
Small represented charts supply the separate U_u overlap construction. -/
theorem tupleDecoder_selected :
    HEq (decodedLocalFamily tupleDecoder.{u}.code).toFilling TupleDecoder.filling := by
  rw [tupleDecoder_roundtrip]
  exact heq_of_eq (TupleDecoder.filling.toLocal_toFilling TupleDecoder.filling_lawful)

/-- A proper endpoint face does not contain the whole interval line. -/
theorem endpoint_not_whole {Γ : Context.{u}} (x : Γ.Elements) :
    ¬ (Glue.intervalAll (intervalFace Γ true)).Holds x := by
  intro h
  have hx := Glue.intervalAll_specialize (intervalFace Γ true) x h ((endpoint Γ false).val x)
  change (endpoint Γ false).val x = (endpoint Γ true).val x at hx
  have hd := congrArg (fun z => z.down 0) hx
  cases hd

noncomputable def endpointGlue (Γ : Context) : LocalFamily (total (interval Γ)) :=
  let A := finThree (total (interval Γ))
  let φ := intervalFace Γ true
  let T := A.reindex (restrictInclusion φ)
  LocalFamily.normalizedGlue φ A T (𝟙 T.family)
    (HomotopyEquivalence.ofIso (Iso.refl T.family) T.toFilling T.toFilling_lawful)

/-- A line may enter the gluing face only at its endpoint; its supplied whole
selected operation is nevertheless recovered on restriction to that face. -/
theorem endpointGlue_record (Γ : Context) :
    (endpointGlue Γ).reindex (restrictInclusion (intervalFace Γ true)) =
      (finThree (total (interval Γ))).reindex (restrictInclusion (intervalFace Γ true)) :=
  LocalFamily.normalizedGlue_full _ _ _ _ _

theorem endpointGlue_code (Γ : Context) :
    raisedSub (restrictInclusion (intervalFace Γ true)) ≫ (endpointGlue Γ).code =
      ((finThree (total (interval Γ))).reindex (restrictInclusion (intervalFace Γ true))).code :=
  LocalFamily.normalizedGlue_code_full _ _ _ _ _

end Examples.CartesianSmallFamilyClassification
