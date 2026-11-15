import SquareKit.AssemblyLift
import Examples.VaryingPartialCertificates

/-! Checked assembly prerequisites for the independently specified certificate
client. The displayed selected records are the specification, not a solution
derived from SDT completeness. See `docs/research/internal-sdt-prerequisites.md`.
-/

namespace AssemblyCertificates
open Realizability Realizability.Assembly VaryingPartialCertificates

/-- Every bounded value remains valid; its canonical trace is retained as data. -/
def certificates (n k : Nat) : Assembly where
  Carrier := Cert n k
  realizes r c := r = c.value.val
  inhabited c := ⟨c.value.val, rfl⟩

/-- The same proper certificate embeddings now have actual recursive trackers. -/
def changeCapacity {n m : Nat} (d : Nat) (h : n+d ≤ m) (k : Nat) :
    Hom (certificates n k) (certificates m k) where
  toFun := embed d h
  tracked := by
    have ht : Computable (fun r : Nat => r+d) :=
      (Primrec.nat_add.comp Primrec.id (Primrec.const d)).to_comp
    refine ⟨_, Partrec.nat_iff.mp ht, ?_⟩
    intro c r hr
    exact ⟨r+d, by simp, by change r+d = c.value.val+d; exact congrArg (·+d) hr⟩

theorem changes_comp {n m r : Nat} (d e : Nat) (h : n+d ≤ m) (h' : m+e ≤ r)
    (k : Nat) :
    (changeCapacity d h k).comp (changeCapacity e h' k) =
      changeCapacity (d+e) (by omega) k := by
  apply Hom.ext
  intro c
  apply Cert.ext
  apply Fin.ext
  change (c.value.val+d)+e = c.value.val+(d+e)
  omega

/-- This equality is at the full selected-record observation, including the trace. -/
theorem selected_changes (n j k : Nat) (hj : j ≤ n) :
    (programLiftMap (changeCapacity 1 (show n+1+1 ≤ n+3 by omega) k)).toFun
      ((programLiftMap (changeCapacity 0 (show n+0 ≤ n+1 by omega) k)).toFun
        (some (selected n j k hj))) = some (selected (n+3) (j+1) k (by omega)) := by
  change some (embed 1 (show n+1+1 ≤ n+3 by omega)
    (embed 0 (show n+0 ≤ n+1 by omega) (selected n j k hj))) = _
  rw [embed_selected, embed_selected]

example :
    (programLiftMap (changeCapacity 1 (show 2+1 ≤ 4 by omega) 2)).toFun
      ((programLiftMap (changeCapacity 0 (show 1+0 ≤ 2 by omega) 2)).toFun
        (some (selected 1 0 2 (by omega)))) =
      some (⟨⟨3, by decide⟩, [2,1,0], rfl⟩ : Cert 4 2) := by
  rw [selected_changes]
  rfl

example : (programLiftMap (changeCapacity 1 (show 2+1 ≤ 4 by omega) 2)).toFun none = none := rfl

theorem first_proper (n k : Nat) :
    ¬ Function.Surjective (changeCapacity 0 (show n+0 ≤ n+1 by omega) k).toFun :=
  first_not_surjective n k

theorem second_proper (n k : Nat) :
    ¬ Function.Surjective (changeCapacity 1 (show n+1+1 ≤ n+3 by omega) k).toFun :=
  second_not_surjective n k

/-- Definedness erases the selected bounded value, even on this constructed object. -/
theorem erasure_not_injective :
    ¬ Function.Injective (fun x : (programLift (certificates 1 2)).Carrier => x.isSome) := by
  intro hi
  have h := hi (a₁ := some (selected 1 0 2 (by omega)))
    (a₂ := some (selected 1 1 2 (by omega))) rfl
  have hv := congrArg (fun c : Cert 1 2 => c.value.val) (Option.some.inj h)
  contradiction

def negate : Hom (encoded Bool) (encoded Bool) :=
  ofComputable Bool.not Primrec.not.to_comp

/-- Admitting Boolean negation cannot imply total fixed points for every arrow. -/
theorem negate_no_fixed_point : ¬ ∃ b, negate.toFun b = b := by
  rintro ⟨b, hb⟩
  cases b <;> contradiction

/-- The lifted endomap has bottom as a fixed point, without producing a Boolean. -/
theorem lifted_negate_bottom : (programLiftMap negate).toFun none = none := rfl

/-- A zero evaluation bound does not establish semantic undefinedness. -/
example : Nat.Partrec.Code.evaln 0 (Nat.Partrec.Code.const 3) 0 = none ∧
    (programLift (encoded Nat)).realizes (Encodable.encode (Nat.Partrec.Code.const 3))
      (some (3 : Nat)) := by
  constructor
  · simp [Nat.Partrec.Code.evaln]
  · exact ⟨3, by simp [Nat.Partrec.Code.eval_const], rfl⟩

/-- Product equations apply to actual independently constructed computable arrows. -/
example : (pair (ofComputable (fun n : Nat => n+1)
    (Primrec.nat_add.comp Primrec.id (Primrec.const 1)).to_comp)
    (Hom.id (encoded Nat))).toFun (3 : Nat) = ((4 : Nat),(3 : Nat)) := rfl

end AssemblyCertificates
