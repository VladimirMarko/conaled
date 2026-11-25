import Applications.Resources.RotationCertificate.Encoding
import Applications.Trees.Rotations.Distance

/-!
# Attained-minimum encoded rotation witnesses

Every legal positioned move fits within the node count of its current tree.
Successful prefixes preserve that count, so a complete encoded trace has at
most the node count times its number of moves. Choosing the attained minimum,
rather than a prescribed normalization route, yields a quadratic word bound.
These are mathematical existence and encoding results; a verifier must still
consume the actual word and establish its own semantic and work contracts.
-/
set_option autoImplicit false
set_option warningAsError true

namespace Resources.RotationCertificate
open Trees.Rotations (RotationMove Shape applyMoves?)
open Resources.BinaryCounter (Bits value)

/-- The bound follows the actual intermediate tree after every successful move. -/
theorem certCode_length_le_of_applyMoves (moves : List RotationMove)
    (s t : BinaryTree Unit) (run : applyMoves? moves s = some t) :
    (certCode moves).length ≤ moves.length * s.numNodes := by
  induction moves generalizing s with
  | nil => simp [certCode]
  | cons move moves ih =>
      cases first : Trees.Rotations.applyMove? move s with
      | none => simp [first] at run
      | some next =>
          simp only [Trees.Rotations.applyMoves?_cons, first, Option.bind_some] at run
          have depth := applyMove_depth_le move s next first
          have same := applyMoveRun_numNodes move s next (by
            simpa only [applyMoveRun_value] using first)
          have tail := ih next run
          rw [same] at tail
          simp only [certCode, List.length_append, moveCode_length, List.length_cons]
          nlinarith

/-- The minimum simultaneously fits the threshold and the universal distance bound. -/
theorem minimum_certificate_bound {n : Nat} (s t : Shape n) :
    ∃ moves : List RotationMove,
      applyMoves? moves s.val = some t.val ∧
      moves.length = Shape.distance s t ∧
      (certCode moves).length ≤ n * (2 * n - 2) := by
  obtain ⟨moves, run, length⟩ := Shape.distance_spec s t
  refine ⟨moves, run, length, ?_⟩
  have encoded := certCode_length_le_of_applyMoves moves s.val t.val run
  rw [s.property, length] at encoded
  calc
    (certCode moves).length ≤ Shape.distance s t * n := encoded
    _ ≤ (2 * n - 2) * n :=
      Nat.mul_le_mul_right n (Shape.distance_le_two_mul_sub_two s t)
    _ = n * (2 * n - 2) := Nat.mul_comm _ _

/-- Explicit input language, using common-size shapes and the attained distance. -/
def Yes (input : Word) : Prop :=
  ∃ (n : Nat) (s t : Shape n) (bs : Bits),
    input = inputCode s.val t.val bs ∧ Shape.distance s t ≤ value bs

/-- The language has exactly the encoded successful traces within its threshold. -/
theorem yes_iff_trace (input : Word) :
    Yes input ↔ ∃ (s t : BinaryTree Unit) (bs : Bits) (moves : List RotationMove),
      input = inputCode s t bs ∧ applyMoves? moves s = some t ∧
      moves.length ≤ value bs := by
  constructor
  · rintro ⟨n, s, t, bs, encoded, bound⟩
    obtain ⟨moves, run, length⟩ := (Shape.distance_le_iff s t (value bs)).mp bound
    exact ⟨s.val, t.val, bs, moves, encoded, run, length⟩
  · rintro ⟨s, t, bs, moves, encoded, run, bound⟩
    have same := Trees.Rotations.applyMoves?_numNodes moves run
    let source : Shape s.numNodes := ⟨s, rfl⟩
    let target : Shape s.numNodes := ⟨t, same⟩
    refine ⟨s.numNodes, source, target, bs, encoded, ?_⟩
    exact (Shape.distance_le_length source target run).trans bound

/-- Every yes input has an attained-minimum trace with a quadratic encoded size. -/
theorem yes_small_trace (input : Word) (accepted : Yes input) :
    ∃ (s t : BinaryTree Unit) (bs : Bits) (moves : List RotationMove),
      input = inputCode s t bs ∧ applyMoves? moves s = some t ∧
      moves.length ≤ value bs ∧ (certCode moves).length ≤ 2 * input.length ^ 2 := by
  obtain ⟨n, s, t, bs, encoded, threshold⟩ := accepted
  obtain ⟨moves, run, length, bound⟩ := minimum_certificate_bound s t
  refine ⟨s.val, t.val, bs, moves, encoded, run, length ▸ threshold, ?_⟩
  have nodes : n ≤ input.length := by
    rw [encoded, inputCode_length, s.property, t.property]
    omega
  have squared := Nat.mul_le_mul nodes nodes
  have distance_bound := Nat.mul_le_mul_left n (Nat.sub_le (2 * n) 2)
  simp only [pow_two]
  nlinarith

end Resources.RotationCertificate
