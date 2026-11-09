import Applications.Orbifold.LocalDisplacement.Division

noncomputable section
open scoped ComplexConjugate
namespace Examples.LocalDisplacement
open Orbifold Orbifold.LocalDisplacement

def a : ℂ := 1/10
def b : ℂ := Complex.I/10

def leftTree : Bracketing.Tree ℂ := .fork (.fork (.leaf a) (.leaf b)) (.leaf a)
def rightTree : Bracketing.Tree ℂ := .fork (.leaf a) (.fork (.leaf b) (.leaf a))

theorem pair_value : gyroAdd a b = (1010/10001 : ℂ) + (990/10001 : ℂ)*Complex.I := by
  apply Complex.ext <;> norm_num [a,b,gyroAdd,Complex.div_re,Complex.div_im,Complex.normSq_apply]

theorem reversed_value : gyroAdd b a = (990/10001 : ℂ) + (1010/10001 : ℂ)*Complex.I := by
  apply Complex.ext <;> norm_num [a,b,gyroAdd,Complex.div_re,Complex.div_im,Complex.normSq_apply]

theorem left_value : leftTree.eval gyroAdd =
    (101040101/510301025 : ℂ) + (101999799/1020602050 : ℂ)*Complex.I := by
  change gyroAdd (gyroAdd a b) a = _
  rw [pair_value]
  apply Complex.ext <;> norm_num [a,gyroAdd,Complex.div_re,Complex.div_im,Complex.normSq_apply]

theorem right_value : rightTree.eval gyroAdd = (20/101 : ℂ) + (99/1010 : ℂ)*Complex.I := by
  change gyroAdd a (gyroAdd b a) = _
  rw [reversed_value]
  apply Complex.ext <;> norm_num [a,gyroAdd,Complex.div_re,Complex.div_im,Complex.normSq_apply]

theorem a_mem : a ∈ U := by norm_num [a,U,Complex.normSq_apply]
theorem b_mem : b ∈ U := by norm_num [b,U,Complex.normSq_apply]

theorem pair_admissible : Admissible a b := by
  refine ⟨a_mem,b_mem,?_⟩
  rw [pair_value]
  norm_num [U,Complex.normSq_apply]

theorem reversed_admissible : Admissible b a := by
  refine ⟨b_mem,a_mem,?_⟩
  rw [reversed_value]
  norm_num [U,Complex.normSq_apply]

theorem left_valid : leftTree.Valid U gyroAdd := by
  refine ⟨⟨a_mem,b_mem,pair_admissible.2.2⟩,a_mem,?_⟩
  change leftTree.eval gyroAdd ∈ U
  rw [left_value]
  norm_num [U,Complex.normSq_apply]

theorem right_valid : rightTree.Valid U gyroAdd := by
  refine ⟨a_mem,⟨b_mem,a_mem,reversed_admissible.2.2⟩,?_⟩
  change rightTree.eval gyroAdd ∈ U
  rw [right_value]
  norm_num [U,Complex.normSq_apply]

theorem nonassociative : leftTree.eval gyroAdd ≠ rightTree.eval gyroAdd := by
  rw [left_value,right_value]
  intro h
  have hr := congrArg Complex.re h
  norm_num at hr

theorem noncollinear : a.re * b.im - a.im * b.re ≠ 0 := by norm_num [a,b]

theorem intermediate_exit : (2/5 : ℂ) ∈ U ∧ ¬ Admissible (2/5) (2/5) := by
  constructor
  · norm_num [U,Complex.normSq_apply]
  · intro h
    norm_num [Admissible,gyroAdd,U,Complex.normSq_apply,map_ofNat,Complex.div_re,Complex.div_im] at h

example : Bracketing.fringeSpec leftTree = Bracketing.fringeSpec rightTree := rfl

example : ¬ (Bracketing.Tree.fork (.leaf (2/5 : ℂ)) (.leaf (2/5))).Valid U gyroAdd :=
  fun h => intermediate_exit.2 h

end Examples.LocalDisplacement
