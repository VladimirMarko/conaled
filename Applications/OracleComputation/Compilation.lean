import Applications.OracleComputation.Coding
import Mathlib.Computability.PartrecCode

/-! Symbolic interpretation and executable code transformations with explicit oracle witnesses. -/

namespace OracleComputation

/-- The artifact acts on partial functions, with its query interpretation supplied separately. -/
def semanticAlgebra (oracle : Nat →. Nat) : Algebra (Nat →. Nat) where
  zero := fun _ => .some 0
  succ := fun n => .some (n + 1)
  left := fun n => .some n.unpair.1
  right := fun n => .some n.unpair.2
  query := oracle
  pair f g := fun n => Nat.pair <$> f n <*> g n
  comp f g := fun n => g n >>= f
  prec := recur
  rfind := search

@[simp] theorem interpret_semantics (oracle : Nat →. Nat) (c : Code) :
    interpret (semanticAlgebra oracle) c = eval oracle c := by
  induction c <;> simp_all [interpret, semanticAlgebra, eval] <;> rfl

/-- A malformed artifact has no denotation, independently of whether a valid program halts. -/
def artifact (oracle : Nat →. Nat) (xs : List Nat) : Option (Nat →. Nat) :=
  match run (semanticAlgebra oracle) xs [] with
  | some [f] => some f
  | _ => none

/-- The symbolic artifact retains the complete partial denotation. -/
theorem artifact_emit (oracle : Nat →. Nat) (c : Code) :
    artifact oracle (emit c) = some (eval oracle c) := by
  simp [artifact, run_emit]

/-- Result preservation after admitting the actual emitted artifact. -/
theorem artifact_result {oracle : Nat →. Nat} {c : Code} {f : Nat →. Nat}
    (h : artifact oracle (emit c) = some f) (n v : Nat) :
    v ∈ f n ↔ v ∈ eval oracle c n := by
  rw [artifact_emit] at h
  cases Option.some.inj h
  rfl

theorem artifact_termination {oracle : Nat →. Nat} {c : Code} {f : Nat →. Nat}
    (h : artifact oracle (emit c) = some f) (n : Nat) :
    (f n).Dom ↔ (eval oracle c n).Dom := by
  rw [artifact_emit] at h
  cases Option.some.inj h
  rfl

/-- Replace every query by an actual program, leaving code generation executable. -/
def substitute (q : Code) : Code → Code
  | .zero => .zero
  | .succ => .succ
  | .left => .left
  | .right => .right
  | .query => q
  | .pair f g => .pair (substitute q f) (substitute q g)
  | .comp f g => .comp (substitute q f) (substitute q g)
  | .prec f g => .prec (substitute q f) (substitute q g)
  | .rfind f => .rfind (substitute q f)

/-- Query realization preserves the full partial behavior, not only terminating examples. -/
theorem eval_substitute (target : Nat →. Nat) (q c : Code) :
    eval target (substitute q c) = eval (eval target q) c := by
  induction c <;> simp_all [substitute, eval] <;> rfl

/-- Composition of realizations is a concrete source transformation. -/
theorem substitute_comp (r q c : Code) :
    substitute r (substitute q c) = substitute (substitute r q) c := by
  induction c <;> simp_all [substitute]

/-- Preservation requires a witness implementing the requested oracle. -/
theorem substitute_realizes {source target : Nat →. Nat} {q : Code}
    (hq : eval target q = source) (c : Code) :
    eval target (substitute q c) = eval source c := by
  rw [eval_substitute, hq]

/-- Compile to actual ordinary Code when the oracle has a supplied ordinary implementation. -/
def toOrdinary (q : Nat.Partrec.Code) : Code → Nat.Partrec.Code
  | .zero => .zero
  | .succ => .succ
  | .left => .left
  | .right => .right
  | .query => q
  | .pair f g => .pair (toOrdinary q f) (toOrdinary q g)
  | .comp f g => .comp (toOrdinary q f) (toOrdinary q g)
  | .prec f g => .prec (toOrdinary q f) (toOrdinary q g)
  | .rfind f => .comp (.rfind' (toOrdinary q f)) (.pair .id .zero)

/-- The minimization macro matches Mathlib's different `rfind'` argument convention. -/
theorem toOrdinary_correct (q : Nat.Partrec.Code) (c : Code) :
    Nat.Partrec.Code.eval (toOrdinary q c) = eval (Nat.Partrec.Code.eval q) c := by
  induction c with
  | zero | succ | left | right | query => rfl
  | pair f g hf hg => simp [toOrdinary, Nat.Partrec.Code.eval, eval, hf, hg]; rfl
  | comp f g hf hg => simp [toOrdinary, Nat.Partrec.Code.eval, eval, hf, hg]; rfl
  | prec f g hf hg => simp [toOrdinary, Nat.Partrec.Code.eval, eval, hf, hg]; rfl
  | rfind f hf =>
    funext n
    simp [toOrdinary, Nat.Partrec.Code.eval, eval, search, hf,
      Seq.seq, pure, PFun.pure, Part.map_id']

/-- A hypothesis of computability gives existence; `toOrdinary` needs the selected witness. -/
theorem ordinary_code_exists {oracle : Nat →. Nat} (h : Nat.Partrec oracle) (c : Code) :
    ∃ q : Nat.Partrec.Code, Nat.Partrec.Code.eval q = eval oracle c :=
  Nat.Partrec.Code.exists_code.mp (eval_partrec h c)

end OracleComputation
