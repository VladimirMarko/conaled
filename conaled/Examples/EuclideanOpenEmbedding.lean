import SquareKit.SmoothOpenOperations
import SquareKit.SmoothOpenKL
import Mathlib.Analysis.SpecialFunctions.ExpDeriv

/-! Experimental ordinary-domain consumers of the fully faithful smooth sheaf
embedding: reciprocal, exponential, composition and empty domains. -/
noncomputable section
open scoped ContDiff
namespace Examples.EuclideanOpenEmbedding
open CategoryTheory SquareKit SmoothAlgebra EuclideanOpen

abbrev punctured : Domain := ⟨1,generator 0⟩

theorem punctured_proper : Points punctured ≠ Set.univ := by
  intro h
  have hz : (fun _ : Fin 1 => (0 : ℝ)) ∈ Points punctured := h ▸ Set.mem_univ _
  exact hz rfl

def reciprocal : punctured ⟶ full 1 :=
  {toFun x := ⟨fun _ => (x.val 0)⁻¹,one_ne_zero⟩
   smooth _ := (OpenFunctions.representative_iff _ (fun x => (x 0)⁻¹) (fun _ => rfl)).mpr
     ((contDiff_apply ℝ (fun _ : Fin 1 => ℝ) 0).contDiffOn.inv (fun _ hx => hx))}

theorem reciprocal_value (x : Points punctured) :
    (show Map punctured (full 1) from reciprocal) x = ⟨fun _ => (x.val 0)⁻¹,one_ne_zero⟩ := rfl

theorem no_continuous_reciprocal_extension :
    ¬ ∃ F : ℝ → ℝ, Continuous F ∧ ∀ x, x ≠ 0 → F x = x⁻¹ := by
  rintro ⟨F,hF,h⟩
  have he : (fun x : ℝ => x * F x) = fun _ => (1 : ℝ) :=
    Continuous.ext_on (dense_compl_singleton (0 : ℝ)) (continuous_id.mul hF) continuous_const
      (fun x hx => by rw [h x hx]; exact mul_inv_cancel₀ hx)
  have hz := congrFun he 0
  norm_num at hz

/-- The map is admissible even though its ambient vector map has no continuous extension. -/
theorem no_ambient_extension :
    ¬ ∃ F : (Fin 1 → ℝ) → (Fin 1 → ℝ), Continuous F ∧
      ∀ x : Points punctured, F x.val = ((show Map punctured (full 1) from reciprocal) x).val := by
  rintro ⟨F,hF,he⟩
  apply no_continuous_reciprocal_extension
  refine ⟨fun x => F (fun _ => x) 0, (continuous_apply 0).comp (hF.comp (continuous_pi (fun _ => continuous_id))),?_⟩
  intro x hx
  exact congrFun (he ⟨fun _ => x,hx⟩) 0

abbrev expOperation : Operation 1 :=
  ⟨fun x => Real.exp (x 0),Real.contDiff_exp.comp (contDiff_apply ℝ (fun _ : Fin 1 => ℝ) 0)⟩
abbrev exponential := EuclideanOpen.operation expOperation

theorem exponential_comparison :
    embedding.map exponential ≫ fullLineIso.hom =
      (fullPowerIso 1).hom ≫ SmoothOpenSite.operation expOperation := operation_comparison expOperation

theorem interpreted_exponential :
    embedding.map exponential ≫ fullLineIso.hom =
      fullLineIso.hom ≫ SmoothOpenSite.interpret Real.exp Real.contDiff_exp := by
  calc
    _ = (fullPowerIso 1).hom ≫ SmoothOpenSite.operation expOperation := exponential_comparison
    _ = _ := rfl

def expReciprocal : punctured ⟶ full 1 := reciprocal ≫ exponential

theorem composition_value (x : Points punctured) :
    ((show Map punctured (full 1) from expReciprocal) x).val 0 = Real.exp ((x.val 0)⁻¹) := rfl

theorem composition_comparison :
    embedding.map expReciprocal = embedding.map reciprocal ≫ embedding.map exponential :=
  embedding.map_comp _ _

/-- The full-faithfulness inverse recovers the nonextendable ordinary map. -/
theorem recover_reciprocal :
    (homEquiv punctured (full 1)).symm (embedding.map reciprocal) = reciprocal := inverse_forward reciprocal

theorem recover_composite :
    (homEquiv punctured (full 1)).symm (embedding.map reciprocal ≫ embedding.map exponential) = expReciprocal := by
  rw [← composition_comparison]
  exact inverse_forward expReciprocal

/-- Arbitrary sheaf arrows between these representables are recovered, not only chosen forward maps. -/
theorem all_arrows (h : embedding.obj punctured ⟶ embedding.obj (full 1)) :
    embedding.map ((homEquiv punctured (full 1)).symm h) = h := forward_inverse h

abbrev emptyDomain : Domain := ⟨0,0⟩

theorem empty_points : IsEmpty (Points emptyDomain) := ⟨fun x => x.property rfl⟩

def emptyMap (U : Domain) : emptyDomain ⟶ U :=
  {toFun x := (x.property rfl).elim
   smooth _ := fun _ hx => (hx rfl).elim}

theorem empty_maps_unique (U : Domain) (f g : emptyDomain ⟶ U) : f=g := by
  apply OpenFunctions.Map.ext
  intro x
  exact (x.property rfl).elim

theorem no_point_to_empty : IsEmpty (full 0 ⟶ emptyDomain) := by
  refine ⟨fun h => ?_⟩
  exact (((show Map (full 0) emptyDomain from h) ((fullPoints 0).symm Fin.elim0)).property rfl)

/-- Full faithfulness preserves the empty-domain boundary on actual sheaf arrows. -/
theorem no_model_point_to_empty : IsEmpty (embedding.obj (full 0) ⟶ embedding.obj emptyDomain) :=
  ⟨fun h => no_point_to_empty.false ((homEquiv (full 0) emptyDomain).symm h)⟩

end Examples.EuclideanOpenEmbedding
