import Applications.Parallel.ScanSearch
import Applications.Optimization.Choice.Evidence

/-! Policy choice at a site in a known finite scan context. Admission and ranking
observe the completed context. Empirical policies use the declared unpruned
catalog; circuit dominance is not a theorem about elapsed runtime. -/
namespace Applications.Parallel
namespace Shape
variable {M : Type*} [Monoid M]

/-- Common-input adapter. It materializes each plan's own product shape. -/
def load : (s : Shape) → List M → s.Data M
  | .empty, _ => PUnit.unit
  | .leaf, xs => xs.headD 1
  | .prod s t, xs => (load s xs, load t (xs.drop s.size))

theorem flatten_load (s : Shape) (xs : List M) (h : s.size ≤ xs.length) :
    s.flatten (s.load xs) = xs.take s.size := by
  induction s generalizing xs with
  | empty => simp [flatten, size]
  | leaf => cases xs <;> simp_all [load, flatten, size]
  | prod s t ih it =>
    simp only [size] at h
    change s.flatten (s.load xs) ++ t.flatten (t.load (xs.drop s.size)) = xs.take (s.size + t.size)
    rw [ih xs (by omega), it (xs.drop s.size) (by simp; omega)]
    exact List.take_add.symm
end Shape

namespace PolicyChoice
open Optimization.Choice ScanSearch
variable {M : Type*} [Monoid M]

/-- The result is specified on exactly matching inputs; admission enforces size.
Ordinary shaped clients can continue using `Scanner.run` without conversion. -/
def run (p : ScanPlan) (xs : List M) : List M × M :=
  let result := p.scanner.run (p.shape.load xs)
  (p.shape.flatten result.1, result.2)

theorem run_correct (p : ScanPlan) (xs : List M) (h : p.shape.size = xs.length) :
    run p xs = sequential 1 xs := by
  unfold run
  rw [p.correct, Shape.flatten_load _ _ (by omega), List.take_of_length_le (by omega)]

def admitted (frames : List Frame) (size : Nat) (depthLimit : Option Nat) (p : ScanPlan) : Prop :=
  (plug frames p).shape.size = size ∧ ∀ limit ∈ depthLimit, (plug frames p).depth ≤ limit
instance (frames : List Frame) (size : Nat) (depthLimit : Option Nat) (p : ScanPlan) :
    Decidable (admitted frames size depthLimit p) :=
  inferInstanceAs (Decidable (_ ∧ _))

/-- Candidate identity retains the recipe, rather than just size/work/depth. -/
def identify : ScanPlan → String
  | .empty => "e"
  | .leaf => "l"
  | .prod p q => "p(" ++ identify p ++ "," ++ identify q ++ ")"
  | .comp p q => "c(" ++ identify p ++ "," ++ identify q ++ ")"

def frameID : Frame → String
  | .prodLeft p => "pl:" ++ identify p
  | .prodRight p => "pr:" ++ identify p
  | .compOuter p => "co:" ++ identify p
  | .compInner p => "ci:" ++ identify p

def scope (frames : List Frame) (size : Nat) (depthLimit : Option Nat)
    (context : Context) : Context :=
  { context with
    site := context.site ++ ":" ++ String.intercalate ";" (frames.map frameID)
    requirements := size :: depthLimit.toList }

def choose (catalog : List ScanPlan) (frames : List Frame) (size : Nat)
    (depthLimit : Option Nat) (context : Context) (repetitions : Nat)
    (fixed : ScanPlan → Nat) (evidence : Option Epoch) : Option ScanPlan :=
  Optimization.Choice.choose catalog (admitted frames size depthLimit) identify (scope frames size depthLimit context) repetitions
    (fun p => fixed (plug frames p)) evidence

theorem chosen_correct {catalog : List ScanPlan} {frames : List Frame} {size : Nat}
    {depthLimit : Option Nat} {context : Context} {repetitions : Nat}
    {fixed : ScanPlan → Nat} {evidence : Option Epoch} {p : ScanPlan}
    (h : choose catalog frames size depthLimit context repetitions fixed evidence = some p)
    (xs : List M) (hx : xs.length = size) :
    run (plug frames p) xs = sequential 1 xs := by
  have hp := Optimization.Choice.choose_admitted h
  exact run_correct _ _ (hp.2.1.trans hx.symm)

theorem chosen_depth {catalog : List ScanPlan} {frames : List Frame} {size limit : Nat}
    {context : Context} {repetitions : Nat} {fixed : ScanPlan → Nat}
    {evidence : Option Epoch} {p : ScanPlan}
    (h : choose catalog frames size (some limit) context repetitions fixed evidence = some p) :
    (plug frames p).depth ≤ limit :=
  (Optimization.Choice.choose_admitted h).2.2 limit (by simp)

end PolicyChoice
end Applications.Parallel
