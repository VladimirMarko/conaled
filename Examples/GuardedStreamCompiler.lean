import SquareKit.GuardedStreamCompiler
import Examples.GuardedStreams

/-! Checked compiler clients retain independent coordinate meanings and exercise
references, parameters, causal contexts and a lossy coefficient interpretation. -/
namespace SquareKit.GuardedStreamCompiler.Examples
open GuardedStreams

abbrev Program := Body Bool Unit Unit Unit Unit

def model [AddMonoidWithOne R] (p r : Stream R) : Meaning Bool Unit Unit Unit Unit R where
  constant b := if b then 1 else 0
  parameter _ := p
  reference _ := r
  operation _ := addLeft p
  causal _ := addLeft_causal p
  binary _ := (· + ·)

def run [AddMonoidWithOne R] (p r : Stream R) (t : Program)
    (h : guarded t = true) : Stream R :=
  solution (functionTarget (model p r)) (model p r) (functionSound _) t h 0

theorem run_meaning [AddMonoidWithOne R] (p r : Stream R) (t : Program)
    (h : guarded t = true) (expected : Stream R)
    (equation : expected = denote (model p r) t expected) : run p r t h = expected :=
  solution_meaning _ _ _ t h 0 expected equation

def onesBody : Program := .delay true .recur
def compiledOnes [AddMonoidWithOne R] : Stream R := run (fun _ => 0) (fun _ => 0) onesBody rfl

theorem compiledOnes_eq [AddMonoidWithOne R] : (compiledOnes : Stream R) = fun _ => 1 := by
  apply run_meaning
  funext n
  cases n <;> rfl

theorem compiledOnes_direct [AddMonoidWithOne R] : (compiledOnes : Stream R) = ones := by
  rw [compiledOnes_eq]
  exact (constantStream_eq 1).symm

def sumsSource : Program := .delay true (.zip () (.ref ()) .recur)
def compiledSums [AddMonoidWithOne R] : Stream R := run (fun _ => 0) compiledOnes sumsSource rfl

/-- Recovery of the old direct API passes through the public compiler theorem. -/
theorem compiledSums_direct [AddMonoidWithOne R] : (compiledSums : Stream R) = sums := by
  apply run_meaning
  change (sums : Stream R) = cons 1 (fun n => compiledOnes n + sums n)
  calc
    (sums : Stream R) = cons 1 (addLeft ones sums) := sums_fixed
    _ = _ := by
      congr 1
      funext n
      change (ones : Stream R) n + sums n = compiledOnes n + sums n
      rw [compiledOnes_eq, ones_eq]

theorem compiledSums_eq [AddMonoidWithOne R] (n : Nat) :
    (compiledSums : Stream R) n = (n + 1 : Nat) := by
  rw [compiledSums_direct, sums_eq]

example : (compiledOnes : Stream Nat) 0 = 1 := congrFun compiledOnes_eq 0
example (n : Nat) : (compiledOnes : Stream Nat) n = 1 := congrFun compiledOnes_eq n
example : (compiledSums : Stream Nat) 0 = 1 := compiledSums_eq 0
example : (compiledSums : Stream Nat) 4 = 5 := compiledSums_eq 4

/-- Independent finite summation specification, with no compiler or solver. -/
def triangular : Nat → Nat
  | 0 => 0
  | n + 1 => (n + 1) + triangular n

def triangularBody : Program := .delay false (.zip () (.ref ()) .recur)
def compiledTriangular : Stream Nat := run (fun _ => 0) compiledSums triangularBody rfl

theorem compiledTriangular_eq : compiledTriangular = triangular := by
  apply run_meaning
  funext n
  cases n with
  | zero => rfl
  | succ n =>
    change (n + 1) + triangular n = compiledSums n + triangular n
    rw [compiledSums_eq]
    rfl

example : compiledTriangular 4 = 10 := by rw [compiledTriangular_eq]; rfl

/-- A stream parameter may enter a guarded binary context directly. -/
def parameterBody : Program := .delay false (.zip () (.param ()) .recur)
theorem parameter_triangular :
    run (fun n => n + 1) (fun _ => 0) parameterBody rfl = triangular := by
  apply run_meaning
  funext n
  cases n <;> rfl

/-- The admitted causal operation can occur outside the guard. -/
def outerBody : Program := .app () (.delay false .recur)
theorem outer_meaning : run (fun _ => 1) (fun _ => 0) outerBody rfl = fun n => n + 1 := by
  apply run_meaning
  funext n
  cases n with
  | zero => rfl
  | succ n => change n + 1 + 1 = 1 + (n + 1); omega

theorem model_interpretation [AddMonoidWithOne R] [AddMonoidWithOne S]
    (f : R →+ S) (h1 : f 1 = 1) (p r : Stream R) (q s : Stream S)
    (hp : f ∘ p = q) (hr : f ∘ r = s) :
    Interpretation (model p r) (model q s) f where
  constant b := by cases b <;> simp [model, h1]
  parameter _ := hp
  reference _ := hr
  operation _ x := by
    funext n
    change f (p n + x n) = q n + f (x n)
    rw [map_add]
    exact congrArg (fun y => y + f (x n)) (congrFun hp n)
  binary _ a b := map_add f a b

theorem run_interpretation [AddMonoidWithOne R] [AddMonoidWithOne S]
    (f : R →+ S) (h1 : f 1 = 1) (p r : Stream R) (q s : Stream S)
    (hp : f ∘ p = q) (hr : f ∘ r = s) (t : Program) (h : guarded t = true) :
    f ∘ run p r t h = run q s t h :=
  solution_interpretation _ _ _ _ _ _ f (model_interpretation f h1 p r q s hp hr) t h 0 0

open GuardedStreams.Examples (parity)
theorem compiledOnes_parity : parity ∘ (compiledOnes : Stream Nat) = compiledOnes := by
  apply run_interpretation parity (by simp [parity])
  all_goals funext n; exact map_zero parity

theorem compiledSums_parity : parity ∘ (compiledSums : Stream Nat) = compiledSums := by
  apply run_interpretation parity (by simp [parity])
  · funext n; exact map_zero parity
  · exact compiledOnes_parity

example : (compiledSums : Stream (ZMod 2)) 4 = 1 := by
  rw [← congrFun compiledSums_parity 4]
  change parity ((compiledSums : Stream Nat) 4) = 1
  rw [compiledSums_eq]
  rfl

example : ¬ Function.Injective parity := GuardedStreams.Examples.parity_not_injective
example : guarded (.recur : Program) = false := rfl
example : ¬ Guarded (denote (model (fun _ => 0) (fun _ => 0) :
    Meaning Bool Unit Unit Unit Unit Nat) (.recur : Program)) := identity_not_guarded

/-- The failed obligation is the delay-one constructor law at coordinate zero. -/
theorem zero_map_rejected : ¬ Interpretation
    (model (fun _ => (0 : Nat)) (fun _ => 0))
    (model (fun _ => (0 : Nat)) (fun _ => 0)) (fun _ => 0) := by
  intro h
  have bad := h.constant true
  change (0 : Nat) = 1 at bad
  contradiction

theorem zero_map_body_square_fails : ¬ (∀ s : Stream Nat,
    (fun _ : Nat => 0) ∘ denote (model (fun _ => 0) (fun _ => 0)) onesBody s =
      denote (model (fun _ => 0) (fun _ => 0)) onesBody ((fun _ => 0) ∘ s)) := by
  intro h
  have bad := congrFun (h (fun _ => 0)) 0
  change (0 : Nat) = 1 at bad
  contradiction

end SquareKit.GuardedStreamCompiler.Examples
