import Applications.Resources.Measured
import SquareKit.ListFusion

/-! Execute actual measured state transitions in order. Potential bounds are
separate from this observation-polymorphic executor.
Provenance and statement review: `docs/research/adwh-potential-accounting.md`. -/
namespace Resources
universe u v w z
variable {ι : Type u} {σ : Type v} {C : Type w} {D : Type z}

def run [Zero C] [Add C] (step : ι → σ → Measured σ C) : List ι → σ → Measured σ C
  | [], s => pure s
  | i :: is, s => bind (step i s) (run step is)

@[simp] theorem run_nil [Zero C] [Add C] (step : ι → σ → Measured σ C) (s : σ) :
    run step [] s = (s, 0) := rfl

/-- Exact source recurrence, derived from measured bind. -/
theorem run_cons [Zero C] [Add C] (step : ι → σ → Measured σ C)
    (i : ι) (is : List ι) (s : σ) :
    run step (i :: is) s =
      ((run step is (step i s).1).1, (step i s).2 + (run step is (step i s).1).2) := rfl

theorem run_state [Zero C] [Add C] (step : ι → σ → Measured σ C) (is : List ι) (s : σ) :
    (run step is s).1 = is.foldl (fun t i => (step i t).1) s := by
  induction is generalizing s with
  | nil => rfl
  | cons i is ih => exact ih _

theorem run_append [AddMonoid C] (step : ι → σ → Measured σ C)
    (is js : List ι) (s : σ) :
    run step (is ++ js) s = bind (run step is s) (run step js) := by
  induction is generalizing s with
  | nil => exact (pure_bind _ _).symm
  | cons i is ih => simp [run, bind, ih, add_assoc]

theorem reweight_run [AddMonoid C] [AddMonoid D] (h : C →+ D)
    (step : ι → σ → Measured σ C) (is : List ι) (s : σ) :
    reweight h (run step is s) = run (fun i s => reweight h (step i s)) is s := by
  induction is generalizing s with
  | nil => simp [run, pure, reweight]
  | cons i is ih =>
    simp only [run_cons]
    rw [← ih]
    simp [reweight, map_add]

theorem run_invariant [Zero C] [Add C] (step : ι → σ → Measured σ C)
    (P : σ → Prop) (closed : ∀ i s, P s → P (step i s).1)
    (is : List ι) (s : σ) (hs : P s) : P (run step is s).1 := by
  induction is generalizing s with
  | nil => exact hs
  | cons i is ih => exact ih _ (closed i s hs)

theorem run_value_fusion [Zero C] [Add C] {τ : Type z}
    (step : ι → σ → Measured σ C) (spec : ι → τ → τ) (decode : σ → τ)
    (P : σ → Prop) (closed : ∀ i s, P s → P (step i s).1)
    (law : ∀ i s, P s → decode (step i s).1 = spec i (decode s))
    (is : List ι) (s : σ) (hs : P s) :
    decode (run step is s).1 = is.foldl (fun t i => spec i t) (decode s) := by
  rw [run_state]
  exact SquareKit.ListFusion.foldl_reachable _ _ decode P s hs
    (fun s i h => closed i s h) (fun s i h => law i s h) is

end Resources
