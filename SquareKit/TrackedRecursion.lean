import SquareKit.AssemblyFunction
import SquareKit.DiagonalCoverage

/-! Experimental bounded multivalued recursion (#500) for uniformly represented partial computations.
The diagonal family is jointly partial recursive. No enumeration of all native
function families or unrestricted multivalued choice is assumed. -/

namespace Realizability.TrackedRecursion
open Encodable Denumerable
open Nat.Partrec (Code)

/-- Extensional partial computations with a partial-recursiveness witness. -/
abbrev Computation := {f : Nat →. Nat // Nat.Partrec f}

def represented (c : Code) : Computation :=
  ⟨c.eval, Code.exists_code.mpr ⟨c, rfl⟩⟩

theorem represented_surjective : Function.Surjective represented := by
  rintro ⟨f, hf⟩
  obtain ⟨c, hc⟩ := Code.exists_code.mp hf
  exact ⟨c, Subtype.ext hc⟩

/-- Joint recursion, rather than a separate program for each family member. -/
def Uniform (a : Nat → Computation) : Prop :=
  Nat.Partrec (fun z => (a z.unpair.1).val z.unpair.2)

def row (n i : Nat) : Computation := represented ((ofNat Code n).curry i)

@[simp] theorem row_apply (n i x : Nat) :
    (row n i).val x = (ofNat Code n).eval (Nat.pair i x) := Code.eval_curry _ _ _

theorem row_uniform (n : Nat) : Uniform (row n) := by
  simpa [Uniform, row, represented, Code.eval_curry] using
    (Code.exists_code.mpr ⟨ofNat Code n, rfl⟩ : Nat.Partrec (ofNat Code n).eval)

/-- Every jointly recursive family is a represented row. -/
theorem uniform_coverage {a : Nat → Computation} (ha : Uniform a) :
    ∃ k, row k = a := by
  obtain ⟨c, hc⟩ := Code.exists_code.mp ha
  refine ⟨encode c, funext fun i => Subtype.ext (funext fun x => ?_)⟩
  simpa [row, represented, Code.eval_curry] using congrFun hc (Nat.pair i x)

/-- Bauer's diagonal step with the selected family's uniformity made explicit. -/
theorem selected_diagonal (R : Computation → Computation → Prop)
    (g : Nat → Computation) (hg : Uniform g) (hR : ∀ n, R (row n n) (g n)) :
    ∃ p, R p p := by
  obtain ⟨k, hk⟩ := uniform_coverage hg
  exact ⟨row k k, by simpa only [← hk] using hR k⟩

/-- A computable code generator supplies a jointly recursive semantic family. -/
theorem uniform_of_generator (f : Nat → Code) (hf : Computable f) :
    Uniform (fun n => represented (f n)) := by
  exact Partrec.nat_iff.mp (Code.eval_part.comp
    (hf.comp (Computable.fst.comp Primrec.unpair.to_comp))
    (Computable.snd.comp Primrec.unpair.to_comp))

def diagonalCode (n : Nat) : Code := (ofNat Code n).curry n

theorem diagonalCode_computable : Computable diagonalCode :=
  (Code.primrec₂_curry.comp (Primrec.ofNat Code) Primrec.id).to_comp

/-- The transformer may inspect codes. Only its related outputs are extensional. -/
theorem realized_recursion (R : Computation → Computation → Prop)
    (F : Code → Code) (hF : Computable F)
    (hR : ∀ c, R (represented c) (represented (F c))) : ∃ p, R p p :=
  selected_diagonal R (fun n => represented (F (diagonalCode n)))
    (uniform_of_generator _ (hF.comp diagonalCode_computable))
    (fun n => hR (diagonalCode n))

/-- Coverage proves inhabited fibers for every code-realized relation. -/
theorem realized_serial (R : Computation → Computation → Prop)
    (F : Code → Code) (hR : ∀ c, R (represented c) (represented (F c)))
    (p : Computation) : ∃ q, R p q := by
  obtain ⟨c, rfl⟩ := represented_surjective p
  exact ⟨represented (F c), hR c⟩

/-- Existence of a code follows; no executable selection of that code is asserted. -/
theorem realized_code_exists (R : Computation → Computation → Prop)
    (F : Code → Code) (hF : Computable F)
    (hR : ∀ c, R (represented c) (represented (F c))) :
    ∃ c, R (represented c) (represented c) := by
  obtain ⟨p, hp⟩ := realized_recursion R F hF hR
  obtain ⟨c, rfl⟩ := represented_surjective p
  exact ⟨c, hp⟩

/-- Independent comparison with Mathlib's recursion theorem. -/
theorem realized_recursion_mathlib (R : Computation → Computation → Prop)
    (F : Code → Code) (hF : Computable F)
    (hR : ∀ c, R (represented c) (represented (F c))) : ∃ p, R p p := by
  obtain ⟨c, hc⟩ := Code.fixed_point hF
  have he : represented (F c) = represented c := Subtype.ext hc
  exact ⟨represented c, by simpa only [he] using hR c⟩

/-- For single-valued semantic steps the existing selected-diagonal API applies. -/
theorem selected_endomap (h : Computation → Computation)
    (hh : Uniform (fun n => h (row n n))) :
    Nonempty (SquareKit.DiagonalConstruction.Selected row h) := by
  obtain ⟨k, hk⟩ := uniform_coverage hh
  exact ⟨⟨k, fun n => congrFun hk n⟩⟩

end Realizability.TrackedRecursion
