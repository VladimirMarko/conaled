import TaskSetup462
namespace AssistedH2
open Tasks462.H2
theorem product_zero : productWeight 0 = 0 := rfl
theorem product_add (a b : Nat) : productWeight (a+b) = productWeight a + productWeight b := by
  apply Prod.ext
  · rfl
  · change 2*(a+b) = 2*a+2*b
    omega
theorem final_zero : finalWeight 0 = 0 := rfl
theorem final_add (a b : Nat × Nat) : finalWeight (a+b) = finalWeight a + finalWeight b := by
  change (a.1+b.1)+3*(a.2+b.2) = (a.1+3*a.2)+(b.1+3*b.2)
  omega
end AssistedH2
