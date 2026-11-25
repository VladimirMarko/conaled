import Applications.Resources.TuringSimulation.TapeReflection
import Applications.Resources.TuringSimulation.FiniteStackToTape

/-!
# Complete singleton tapes and supported package halts

The full native TrCfg relation supplies the entire marked singleton tape. The existing finite support includes literal package halt controls and preserves their stopped transitions.
-/

set_option autoImplicit false
set_option warningAsError true


namespace Resources.TuringSimulation.SingletonOutput

open Turing Turing.TM2to1

variable {K : Type*} {Γ : K → Type*} {Λ σ : Type*}

/-- A complete related tape is one marked row when every source stack is the
empty or singleton list represented by that row. No remote tape contents are
discarded by this theorem. -/
theorem related_singleton_tape
    (source : TM2.Cfg Γ Λ σ)
    (target : TM1.Cfg (Γ' K Γ) (Λ' K Γ Λ σ) σ)
    (row : ∀ k, Option (Γ k))
    (related : TrCfg source target)
    (slots : ∀ k, source.stk k = (row k).toList) :
    target.Tape = Tape.mk₁ [(true, row)] := by
  cases related with
  | @mk q v S L hL =>
    have cells : L = ListBlank.mk [row] := by
      apply ListBlank.ext
      intro n
      funext k
      have observed := stk_nth_val n (hL k)
      have slot_eq : S k = (row k).toList := slots k
      rw [slot_eq] at observed
      cases n with
      | zero =>
        have atZero : ((row k).toList).reverse[0]? = row k := by
          cases row k <;> rfl
        simpa only [atZero, ListBlank.nth_mk, List.getI_cons_zero] using observed
      | succ n =>
        have beyond : ((row k).toList).reverse[n + 1]? = none := by
          cases row k <;> rfl
        have blank_slot : (default : ∀ j, Option (Γ j)) k = none := rfl
        simpa only [beyond, ListBlank.nth_mk, List.getI_cons_succ,
          List.getI_nil, blank_slot] using observed
    change Tape.mk' ∅ (addBottom L) = Tape.mk₁ [(true, row)]
    rw [cells]
    rfl

/-- Reflection fixes the entire singleton tape, including both infinite blank
tails. A later emitter can use the ordinary right-facing output convention. -/
theorem reflection_singleton {A : Type*} [Inhabited A] (a : A) :
    TapeReflection.tape (Tape.mk₁ [a]) = Tape.mk₁ [a] := rfl

/-- One nonempty output stack and all other stacks empty, as a literal row. -/
def haltRow (tm : FinTM2) (a : tm.Γ tm.k₁) : ∀ k, Option (tm.Γ k) :=
  Function.update (fun _ => none) tm.k₁ (some a)

theorem haltList_singleton_slots (tm : FinTM2) (a : tm.Γ tm.k₁) (k : tm.K) :
    (Turing.haltList tm [a]).stk k = (haltRow tm a k).toList := by
  by_cases same : k = tm.k₁
  · subst k
    simp only [Turing.haltList, haltRow, Function.update_self]
    rfl
  · simp only [Turing.haltList, haltRow, dite_eq_right same,
      Function.update_of_ne same]
    rfl

/-- A native related literal package halt carrying one output letter has one
complete marked tape cell. This works with distinct input and output stores. -/
theorem haltList_singleton_tape (tm : FinTM2) (a : tm.Γ tm.k₁)
    (target : TM1.Cfg (Γ' tm.K tm.Γ) (Λ' tm.K tm.Γ tm.Λ tm.σ) tm.σ)
    (related : TrCfg (Turing.haltList tm [a]) target) :
    target.Tape = Tape.mk₁ [(true, haltRow tm a)] :=
  related_singleton_tape (Turing.haltList tm [a]) target (haltRow tm a)
    related (haltList_singleton_slots tm a)

end Resources.TuringSimulation.SingletonOutput

namespace Resources.TuringSimulation.SingletonOutput

open Turing
open Resources.TuringSimulation.StackToTape

/-- Native translation support contains every halted register state, directly
from the existing insertNone construction, independently of the input. -/
theorem package_halt_supported (tm : FinTM2) (v : tm.σ) :
    (none, v) ∈ Package.controlSupport tm := by
  let : Fintype tm.Λ := tm.ΛFin
  let : Fintype tm.σ := tm.σFin
  classical
  change (none, v) ∈ TM1to0.trStmts (TM2to1.tr tm.m)
    (TM2to1.trSupp tm.m (Finset.univ : Finset tm.Λ))
  change (none, v) ∈
    (TM1.stmts (TM2to1.tr tm.m) (TM2to1.trSupp tm.m (Finset.univ : Finset tm.Λ))) ×ˢ
      (Finset.univ : Finset tm.σ)
  exact Finset.mk_mem_product Finset.none_mem_insertNone (Finset.mem_univ v)

/-- The actual support-closed finite transition stops at the actual translated
literal source halt. The supported map uses the real halt control. -/
theorem related_package_halt_stopped (tm : FinTM2) (out : List (tm.Γ tm.k₁))
    (target : TM1.Cfg (TM2to1.Γ' tm.K tm.Γ)
      (TM2to1.Λ' tm.K tm.Γ tm.Λ tm.σ) tm.σ)
    (related : TM2to1.TrCfg (Turing.haltList tm out) target)
    (a : Package.Alphabet tm) :
    Package.closedMachine tm
      (Package.mapCfg tm (TM1to0.trCfg (TM2to1.tr tm.m) target)).q a = none := by
  cases related with
  | mk L hL =>
    rw [Package.mapCfg_supported tm _ (package_halt_supported tm tm.initialState)]
    rfl

end Resources.TuringSimulation.SingletonOutput
