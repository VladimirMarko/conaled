import SquareKit.SmoothOpenSheafDescent
import Mathlib.Analysis.Calculus.BumpFunction.FiniteDimension

/-! Experimental principal refinements of arbitrary ordinary inverse-image
opens. Smooth characteristic functions are proved to exist, rather than imposed
as a restriction on chart overlaps. -/
noncomputable section
open scoped ContDiff Topology
namespace SquareKit.EuclideanOpen
open CategoryTheory SmoothAlgebra

theorem map_continuous {U V : Domain} (f : U ⟶ V) : Continuous (show Map U V from f) := by
  apply Continuous.subtype_mk
  have h := (show Map U V from f).smooth_representative.continuousOn.domRestrict
  exact h.congr (fun x => OpenFunctions.Map.representative_mem _ x)

/-- Every ambient open subset has a globally smooth defining function. -/
def openDefining {n : ℕ} (s : Set (Fin n → ℝ)) (hs : IsOpen s) : Free n :=
  ⟨(hs.exists_contDiff_support_eq (n := ⊤)).choose,
    (hs.exists_contDiff_support_eq (n := ⊤)).choose_spec.2.1⟩

theorem openDefining_locus {n : ℕ} (s : Set (Fin n → ℝ)) (hs : IsOpen s) :
    Localization.locus (openDefining s hs) = s :=
  (hs.exists_contDiff_support_eq (n := ⊤)).choose_spec.1

variable {U V : Domain} (f : U ⟶ V) (q : Free V.dimension)

def inverseOpen : Set (Fin U.dimension → ℝ) :=
  Subtype.val '' {x : Points U | q.val ((show Map U V from f) x).val ≠ 0}

theorem inverseOpen_open : IsOpen (inverseOpen f q) :=
  (domain_open U).isOpenMap_subtype_val _
    (isOpen_ne_fun ((show ContDiff ℝ ∞ q.val from q.property).continuous.comp (continuous_subtype_val.comp (map_continuous f))) continuous_const)

def inverseDefining : Free U.dimension := openDefining (inverseOpen f q) (inverseOpen_open f q)

theorem inverseDefining_iff (x : Points U) :
    (inverseDefining f q).val x.val ≠ 0 ↔ q.val ((show Map U V from f) x).val ≠ 0 := by
  change x.val ∈ Localization.locus (openDefining _ _) ↔ _
  rw [openDefining_locus]
  constructor
  · rintro ⟨y,hy,he⟩
    have he' : y=x := Subtype.ext he
    cases he'
    exact hy
  · intro hx
    exact ⟨x,hx,rfl⟩

/-- The actual inverse-image restriction is smooth even for nonextendable maps. -/
def inverseRestriction : subdomain U (inverseDefining f q) ⟶ subdomain V q :=
  {toFun x := ⟨((show Map U V from f) ⟨x.val,Localization.locus_product_subset _ _ x.property⟩).val,
      mul_ne_zero ((show Map U V from f) _).property
        ((inverseDefining_iff f q _).mp (right_ne_zero_of_mul x.property))⟩
   smooth i := by
     apply (OpenFunctions.representative_iff _
       (OpenFunctions.extendZero (Points U) (fun x => ((show Map U V from f) x).val i))
       (fun x => OpenFunctions.extendZero_mem _ ⟨x.val,Localization.locus_product_subset _ _ x.property⟩)).mpr
     exact ((show Map U V from f).smooth i).mono (Localization.locus_product_subset _ _)}

theorem inverseRestriction_square :
    inverseRestriction f q ≫ subInclusion V q = subInclusion U (inverseDefining f q) ≫ f :=
  OpenFunctions.Map.ext (fun _ => rfl)

theorem inverse_covers {ι : Type*} (g : ι → Free V.dimension) (hg : Covers V g) :
    Covers U (fun i => inverseDefining f (g i)) := by
  intro x
  obtain ⟨i,hi⟩ := hg ((show Map U V from f) x)
  exact ⟨i,(inverseDefining_iff f (g i) x).mpr hi⟩

end SquareKit.EuclideanOpen
