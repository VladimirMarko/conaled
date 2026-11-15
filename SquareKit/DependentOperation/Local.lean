import SquareKit.DependentOperation.Syntax

/-! Local contracts derive whole-program boundaries for indexed operations. -/
namespace SquareKit.DependentOperation
open DependentBranchTheoryMaps

theorem eval_subst {O : Signature} {V W : Nat → Type} {A : Nat → Type}
    (operate : ∀ {n m}, O n m → A n → A m) (ρ : ∀ n, W n → A n)
    (σ : Substitution O V W) {n} (t : Term O V n) :
    eval @operate ρ (t.graft σ) = eval @operate (fun n v => eval @operate ρ (σ n v)) t :=
  t.interpret_graft (model A @operate) ρ σ

theorem compile_meaning {O P : Signature} (F : Compiler O P)
    {A B : Nat → Type} (a : ∀ {n m}, O n m → A n → A m)
    (b : ∀ {n m}, P n m → B n → B m) (meaning : ∀ n, A n → B n)
    (localLaw : F.LocalMeaning (model A @a) (model B @b) meaning)
    {V : Nat → Type} (ρ : ∀ n, V n → A n) {n} (t : Term O V n) :
    eval @b (fun n v => meaning n (ρ n v)) (compile F t) = meaning n (eval @a ρ t) :=
  F.interpret_transport (model A @a) (model B @b) meaning localLaw
    (fun _ => id) ρ (fun n v => meaning n (ρ n v)) (fun _ _ => rfl) t

/-- Arbitrary two typed substitutions preserve the selected interpretation. -/
theorem eval_twice {O : Signature} {V W X : Nat → Type} {A : Nat → Type}
    (a : ∀ {n m}, O n m → A n → A m) (ρ : ∀ n, X n → A n)
    (σ : Substitution O V W) (τ : Substitution O W X) {n} (t : Term O V n) :
    eval @a ρ ((t.graft σ).graft τ) =
      eval @a (fun n v => eval @a (fun k w => eval @a ρ (τ k w)) (σ n v)) t := by
  rw [eval_subst, eval_subst]

/-- Only a primitive emitted word's behavior is supplied. Global execution,
including the output index and selected payload, follows by induction. -/
theorem emit_sound {O : Signature} {V : Nat → Type} {I R : Type} {A : Nat → Type}
    (a : ∀ {n m}, O n m → A n → A m)
    (instruction : ∀ {n m}, O n m → List I) (execute : I → R → R)
    (erase : ∀ n, A n → R)
    (localLaw : ∀ {n m} (o : O n m) (x : A n),
      (instruction o).foldl (fun s i => execute i s) (erase n x) = erase m (a o x))
    (ρ : ∀ n, V n → A n) {n} (t : Term O V n) :
    (emit instruction t).run execute (fun n v => erase n (ρ n v)) = erase n (eval @a ρ t) := by
  induction t with
  | hyp v => rfl
  | rule r ts ih =>
    simp only [emit, Code.run, eval, Derivation.interpret, model]
    rw [List.foldl_append]
    change (instruction r.op).foldl _ ((emit instruction (ts ())).run execute (fun k v => erase k (ρ k v))) = _
    rw [ih ()]
    exact localLaw r.op _

theorem emit_lower {O : Signature} {V : Nat → Type} {I J : Type}
    (instruction : ∀ {n m}, O n m → List I) (f : I → List J) {n} (t : Term O V n) :
    (emit instruction t).lower f = emit (fun o => (instruction o).flatMap f) t := by
  induction t with
  | hyp v => rfl
  | rule r ts ih =>
    simp only [emit, Code.lower, List.flatMap_append]
    have h := ih ()
    have hl := congrArg Code.load h
    have hi := congrArg Code.instructions h
    simp only [Code.lower] at hl hi
    rw [hl, hi]

end SquareKit.DependentOperation
