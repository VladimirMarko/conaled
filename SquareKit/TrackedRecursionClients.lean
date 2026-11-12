import SquareKit.TrackedRecursion

/-! Actual code constructors for the two branches of a multivalued prepend relation. -/
set_option backward.isDefEq.respectTransparency false

namespace Realizability.TrackedRecursion
open Encodable Denumerable
open Nat.Partrec (Code)

@[simp] theorem code_comp_eval (c d : Code) (n : Nat) :
    (Code.comp c d).eval n = (d.eval n).bind c.eval := rfl

@[simp] theorem code_pair_eval (c d : Code) (n : Nat) :
    (Code.pair c d).eval n = (c.eval n).bind
      (fun a => (d.eval n).bind (fun b => Part.some (Nat.pair a b))) := by
  simp [Code.eval, Seq.seq, Part.bind_map, Part.bind_some_eq_map]

@[simp] theorem code_zero_eval (n : Nat) : Code.zero.eval n = Part.some 0 := rfl
@[simp] theorem code_left_eval (n : Nat) : Code.left.eval n = Part.some n.unpair.1 := rfl
@[simp] theorem code_right_eval (n : Nat) : Code.right.eval n = Part.some n.unpair.2 := rfl

/-- A closed predecessor program, built from the native code constructors. -/
def predecessorCode : Code :=
  .comp (.prec .zero (.comp .left .right)) (.pair .zero Code.id)

@[simp] theorem predecessorCode_eval (n : Nat) :
    predecessorCode.eval n = Part.some n.pred := by
  have h : ∀ k, (Code.prec .zero (.comp .left .right)).eval (Nat.pair 0 k) =
      Part.some k.pred := by
    intro k
    induction k with
    | zero => simp
    | succ k ih => simp only [Code.eval_prec_succ, Part.bind_eq_bind, ih, code_comp_eval, code_left_eval,
        code_right_eval, Part.bind_some, Nat.unpair_pair, Nat.pred_succ]
  simpa only [predecessorCode, code_comp_eval, code_pair_eval, code_zero_eval,
    Code.eval_id, Part.bind_some] using h n

/-- Repeat the same partial computation; a positive repetition has exactly its domain. -/
theorem repeat_bind_self (p : Part Nat) : p.bind (fun _ => p) = p := by
  apply Part.ext
  intro v
  simp only [Part.mem_bind_iff]
  exact ⟨fun ⟨_, _, hv⟩ => hv, fun hv => ⟨v, hv, hv⟩⟩

/-- At zero return b; at n+1 run c on n. No choice of a compiler template is used. -/
def prefixCode (b : Nat) (c : Code) : Code :=
  .comp (.prec (Code.const b) (.comp c .left)) (.pair predecessorCode Code.id)

theorem prefixCode_computable (b : Nat) : Computable (prefixCode b) := by
  have h₁ : Primrec (fun c : Code => Code.comp c Code.left) :=
    Code.primrec₂_comp.comp Primrec.id (Primrec.const Code.left)
  have h₂ : Primrec (fun c : Code => Code.prec (Code.const b) (Code.comp c Code.left)) :=
    Code.primrec₂_prec.comp (Primrec.const (Code.const b)) h₁
  exact (Code.primrec₂_comp.comp h₂
    (Primrec.const (Code.pair predecessorCode Code.id))).to_comp

@[simp] theorem prefixCode_zero (b : Nat) (c : Code) :
    (prefixCode b c).eval 0 = Part.some b := by
  simp [prefixCode, Code.eval_id, Code.eval_const]

@[simp] theorem prefixCode_succ (b : Nat) (c : Code) (n : Nat) :
    (prefixCode b c).eval (n+1) = c.eval n := by
  have h : ∀ k, (Code.prec (Code.const b) (.comp c .left)).eval
      (Nat.pair n (k+1)) = c.eval n := by
    intro k
    induction k with
    | zero => simp [Code.eval_prec_succ, Part.bind_eq_bind, Code.eval_const]
    | succ k ih =>
      simp only [Code.eval_prec_succ, ih]
      simpa only [Part.bind_eq_bind, code_comp_eval, code_left_eval, Nat.unpair_pair, Part.bind_some]
        using repeat_bind_self (c.eval n)
  simpa only [prefixCode, code_comp_eval, code_pair_eval, predecessorCode_eval,
    Code.eval_id, Part.bind_some, Nat.pred_succ] using h n

/-- Prefixing a represented partial sequence preserves partial recursiveness. -/
def prepend (b : Nat) (p : Computation) : Computation :=
  ⟨fun n => n.casesOn (Part.some b) p.val, by
    obtain ⟨c, hc⟩ := represented_surjective p
    apply Code.exists_code.mpr
    refine ⟨prefixCode b c, funext fun n => ?_⟩
    cases n with
    | zero => exact prefixCode_zero b c
    | succ n => simp [← hc, represented]⟩

@[simp] theorem prefix_zero (b : Nat) (p : Computation) :
    (prepend b p).val 0 = Part.some b := rfl

@[simp] theorem prefix_succ (b : Nat) (p : Computation) (n : Nat) :
    (prepend b p).val (n+1) = p.val n := rfl

theorem represented_prefixCode (b : Nat) (c : Code) :
    represented (prefixCode b c) = prepend b (represented c) := by
  apply Subtype.ext
  funext n
  cases n <;> simp [represented]

def constant (b : Nat) : Computation := represented (Code.const b)

@[simp] theorem constant_apply (b n : Nat) :
    (constant b).val n = Part.some b := Code.eval_const b n

theorem constant_injective : Function.Injective constant := by
  intro a b h
  have he := congrArg (fun p : Computation => p.val 0) h
  simpa using he

/-- A fixed prepend computation is total, with its selected constant value. -/
theorem prefix_fixed_total (b : Nat) (p : Computation) (hp : p = prepend b p)
    (n : Nat) : p.val n = Part.some b := by
  induction n with
  | zero => exact congrArg (fun p : Computation => p.val 0) hp
  | succ n ih =>
    calc p.val (n+1) = (prepend b p).val (n+1) := congrArg (fun p : Computation => p.val (n+1)) hp
         _ = Part.some b := ih

/-- Both branches have actual nonbottom fixed computations through the diagonal theorem. -/
theorem prefix_fixed_exists (b : Nat) :
    ∃ p : Computation, p = prepend b p ∧ ∀ n, p.val n = Part.some b := by
  obtain ⟨p, hp⟩ := realized_recursion (fun p q => q = prepend b p)
    (prefixCode b) (prefixCode_computable b) (represented_prefixCode b)
  exact ⟨p, hp, prefix_fixed_total b p hp⟩

/-- One relation, with two genuinely different outputs for every input. -/
def PrefixRelation (p q : Computation) : Prop := q = prepend 0 p ∨ q = prepend 1 p

theorem prefix_outputs_distinct (p : Computation) : prepend 0 p ≠ prepend 1 p := by
  intro h
  have he := congrArg (fun p : Computation => p.val 0) h
  simp at he

theorem prefixRelation_serial (p : Computation) : ∃ q, PrefixRelation p q :=
  ⟨prepend 0 p, Or.inl rfl⟩

theorem prefixRelation_zero_realizes (c : Code) :
    PrefixRelation (represented c) (represented (prefixCode 0 c)) :=
  Or.inl (represented_prefixCode 0 c)

theorem prefixRelation_one_realizes (c : Code) :
    PrefixRelation (represented c) (represented (prefixCode 1 c)) :=
  Or.inr (represented_prefixCode 1 c)

theorem prefixRelation_two_fixed : ∃ p q : Computation,
    PrefixRelation p p ∧ PrefixRelation q q ∧ p ≠ q ∧
    (∀ n, p.val n = Part.some 0) ∧ (∀ n, q.val n = Part.some 1) := by
  obtain ⟨p, hp, ht⟩ := prefix_fixed_exists 0
  obtain ⟨q, hq, hu⟩ := prefix_fixed_exists 1
  refine ⟨p, q, Or.inl hp, Or.inr hq, ?_, ht, hu⟩
  intro he
  have hv := congrArg (fun p : Computation => p.val 0) he
  simp [ht, hu] at hv

/-- Prefixing is not the identity transformer on semantic computations. -/
theorem prefix_changes (a b : Nat) (hab : a ≠ b) : prepend a (constant b) ≠ constant b := by
  intro h
  have he := congrArg (fun p : Computation => p.val 0) h
  exact hab (by simpa using he)

/-- Companion client of Mathlib's second recursion theorem, not the diagonal proof above. -/
theorem exists_self_code : ∃ c : Code, ∀ n, c.eval n = Part.some (encode c) := by
  obtain ⟨c, hc⟩ := Code.fixed_point₂
    ((Computable.encode.comp Computable.fst).partrec.to₂ :
      Partrec₂ (fun c : Code => fun _ : Nat => Part.some (encode c)))
  exact ⟨c, fun n => congrFun hc n⟩

end Realizability.TrackedRecursion
