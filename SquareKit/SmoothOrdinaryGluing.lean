import SquareKit.SmoothOpenOverlap

/-! Experimental gluing of arbitrary ordinary smooth maps on principal-open
covers. Smoothness and target membership are local; no boundedness or ambient
extension condition is imposed on the maps. -/
noncomputable section
open scoped ContDiff Topology
namespace SquareKit.EuclideanOpen
open CategoryTheory SmoothAlgebra
open OpenFunctions
variable (U V : Domain) {ι : Type*} (g : ι → Free U.dimension)

abbrev localPoint (x : Points U) {i : ι} (hi : (g i).val x.val ≠ 0) : Points (subdomain U (g i)) :=
  ⟨x.val,mul_ne_zero x.property hi⟩

def Compatible (a : ∀ i, subdomain U (g i) ⟶ V) : Prop :=
  ∀ i j, overlapLeft U (g i) (g j) ≫ a i = overlapRight U (g i) (g j) ≫ a j

theorem compatible_value {a : ∀ i, subdomain U (g i) ⟶ V} (ha : Compatible U V g a)
    (x : Points U) (i j : ι) (hi : (g i).val x.val ≠ 0) (hj : (g j).val x.val ≠ 0) :
    (show Map (subdomain U (g i)) V from a i) (localPoint U g x hi) =
      (show Map (subdomain U (g j)) V from a j) (localPoint U g x hj) := by
  exact congrArg (fun k : Map (overlap U (g i) (g j)) V =>
    k ⟨x.val,mul_ne_zero (mul_ne_zero x.property hi) hj⟩) (ha i j)

private def glueValue (hc : Covers U g) (a : ∀ i, subdomain U (g i) ⟶ V) (x : Points U) : Points V :=
  (show Map (subdomain U (g (hc x).choose)) V from a (hc x).choose)
    (localPoint U g x (hc x).choose_spec)

private theorem glueValue_on (hc : Covers U g) (a : ∀ i, subdomain U (g i) ⟶ V)
    (ha : Compatible U V g a) (x : Points U) (i : ι) (hi : (g i).val x.val ≠ 0) :
    glueValue U V g hc a x = (show Map (subdomain U (g i)) V from a i) (localPoint U g x hi) :=
  compatible_value U V g ha x (hc x).choose i (hc x).choose_spec hi

/-- The chosen pointwise value is smooth near each point because it agrees with a local map. -/
def glue (hc : Covers U g) (a : ∀ i, subdomain U (g i) ⟶ V) (ha : Compatible U V g a) : U ⟶ V :=
  {toFun := glueValue U V g hc a
   smooth k := by
     intro x hx
     obtain ⟨i,hi⟩ := hc ⟨x,hx⟩
     let ai : Map (subdomain U (g i)) V := a i
     have hlocal := (ai.smooth k).contDiffAt ((domain_open (subdomain U (g i))).mem_nhds (mul_ne_zero hx hi))
     apply (hlocal.congr_of_eventuallyEq ?_).contDiffWithinAt
     filter_upwards [(domain_open (subdomain U (g i))).mem_nhds (mul_ne_zero hx hi)] with y hy
     have hyU : y ∈ Points U := left_ne_zero_of_mul hy
     have hyi : (g i).val y ≠ 0 := right_ne_zero_of_mul hy
     simp only [OpenFunctions.extendZero, dite_eq_left hy, dite_eq_left hyU]
     exact congrArg (fun z : Points V => z.val k) (glueValue_on U V g hc a ha ⟨y,hyU⟩ i hyi)}

theorem glue_restrict (hc : Covers U g) (a : ∀ i, subdomain U (g i) ⟶ V)
    (ha : Compatible U V g a) (i : ι) : subInclusion U (g i) ≫ glue U V g hc a ha = a i := by
  apply OpenFunctions.Map.ext
  intro x
  exact glueValue_on U V g hc a ha ⟨x.val,left_ne_zero_of_mul x.property⟩ i (right_ne_zero_of_mul x.property)

theorem glue_unique (hc : Covers U g) (a : ∀ i, subdomain U (g i) ⟶ V)
    (ha : Compatible U V g a) (b : U ⟶ V) (hb : ∀ i, subInclusion U (g i) ≫ b = a i) :
    b = glue U V g hc a ha := by
  apply OpenFunctions.Map.ext
  intro x
  obtain ⟨i,hi⟩ := hc x
  exact (congrArg (fun k : Map (subdomain U (g i)) V => k (localPoint U g x hi)) (hb i)).trans
    (glueValue_on U V g hc a ha x i hi).symm

theorem exists_unique (hc : Covers U g) (a : ∀ i, subdomain U (g i) ⟶ V)
    (ha : Compatible U V g a) : ∃! b : U ⟶ V, ∀ i, subInclusion U (g i) ≫ b = a i :=
  ⟨glue U V g hc a ha,glue_restrict U V g hc a ha,fun b hb => glue_unique U V g hc a ha b hb⟩

/-- Restrictions of any ordinary map form a compatible family. -/
theorem restriction_compatible (b : U ⟶ V) :
    Compatible U V g (fun i => subInclusion U (g i) ≫ b) := by
  intro i j
  rw [← Category.assoc,← Category.assoc,overlap_square]

end SquareKit.EuclideanOpen
