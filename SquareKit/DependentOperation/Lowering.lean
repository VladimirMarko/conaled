import SquareKit.DependentOperation.Selector

/-! Typed lowering expands symmetric padding into two distinct operations.
Quotation relates that compiled derivation to the independent instruction list. -/
namespace SquareKit.DependentOperation.Selector
open DependentBranchTheoryMaps
set_option backward.isDefEq.respectTransparency false

inductive LowOp : Signature where
  | mirror (n) : LowOp n n
  | left (n) : LowOp n (n+1)
  | right (n) : LowOp n (n+1)
  | origin (n) : LowOp n n

def lowOperate : ∀ {n m}, LowOp n m → Position n → Position m
  | _, _, .mirror _, i => Fin.rev i
  | _, _, .left _, i => ⟨i.val+1, by omega⟩
  | _, _, .right _, i => ⟨i.val, by omega⟩
  | _, _, .origin _, _ => 0

def lowInstructions : ∀ {n m}, LowOp n m → List Low
  | _, _, .mirror _ => [.mirror]
  | _, _, .left _ => [.left]
  | _, _, .right _ => [.right]
  | _, _, .origin _ => [.origin]

def lowering : Compiler Op LowOp where
  certificate r := match r with
    | ⟨n,_,.reflect _⟩ => app (.mirror n) (.hyp ⟨(),rfl⟩)
    | ⟨n,_,.insert _⟩ => app (.left n) (.hyp ⟨(),rfl⟩)
    | ⟨n,_,.pad _⟩ => app (.right (n+1)) (app (.left n) (.hyp ⟨(),rfl⟩))
    | ⟨n,_,.reset _⟩ => app (.origin n) (.hyp ⟨(),rfl⟩)

theorem lowering_local : lowering.LocalMeaning
    (model Position @operate) (model Position @lowOperate) (fun _ => id) := by
  intro r xs
  rcases r with ⟨n,m,o⟩
  cases o <;> rfl

theorem lowering_meaning {V : Nat → Type} (ρ : ∀ n, V n → Position n)
    {n} (t : Term Op V n) : eval @lowOperate ρ (compile lowering t) = eval @operate ρ t :=
  compile_meaning lowering @operate @lowOperate (fun _ => id) lowering_local ρ t

/-- Both routes produce the same actual word. Padding expands into left then
right; this is stronger than equality of program results. -/
theorem lowering_quote {V : Nat → Type} {n} (t : Term Op V n) :
    emit @lowInstructions (compile lowering t) = bytecode t := by
  rw [quotation]
  induction t with
  | hyp v => rfl
  | rule r ts ih =>
    rcases r with ⟨n,m,o⟩
    have h := ih ()
    cases o <;>
      change _ = Code.mk (emit (fun o => (instructions o).flatMap lower) (ts ())).load
        ((emit (fun o => (instructions o).flatMap lower) (ts ())).instructions ++ _)
    all_goals rw [← h]
    all_goals try rfl
    change Code.mk _ ((_ ++ [Low.left]) ++ [Low.right]) = Code.mk _ (_ ++ [Low.left,Low.right])
    simp only [List.append_assoc, List.cons_append, List.nil_append]
    rfl

/-- Interpretation of a lowered term after two arbitrary typed context
substitutions keeps the selected value. No whole-client obligation is supplied. -/
theorem lowering_twice {V W X : Nat → Type} (ρ : ∀ n, X n → Position n)
    (σ : Substitution Op V W) (τ : Substitution Op W X) {n} (t : Term Op V n) :
    eval @lowOperate ρ (compile lowering ((t.graft σ).graft τ)) =
      eval @operate (fun n v => eval @operate
        (fun k w => eval @operate ρ (τ k w)) (σ n v)) t := by
  rw [lowering_meaning, eval_twice]

end SquareKit.DependentOperation.Selector
