import SquareKit.IndexedCompositional
import Applications.Languages.WitnessTrie

/-! Finite parser constructors and depth restriction through the indexed compatibility law.
Both native parser and finite trie interpretations retain exact selected decisions.
Retained operands are restricted without consuming an input character. -/
namespace LanguageWitnesses.IndexedCompositional
open SquareKit.IndexedCompositional
universe u
variable {α : Type u}

abbrev Index (α : Type u) := Language α × Nat
inductive Op (α : Type u) : Index α → Type (u+1)
  | union (P Q : Language α) (n : Nat) : Op α (fun w => P w ⊕ Q w, n)
  | transport (P Q : Language α) (n : Nat) (e : ∀ w, Iso (P w) (Q w)) : Op α (Q,n)
  | cut (P : Language α) (n : Nat) : Op α (P,n)
  | scale (P : Language α) (n : Nat) {A : Type u} (d : Decision A) : Op α (fun w => A × P w,n)
  | intersection (P Q : Language α) (n : Nat) : Op α (fun w => P w × Q w,n)
  | concat (P Q : Language α) (n : Nat) : Op α (Concat P Q,n)
  | star (P : Language α) (n : Nat) : Op α (Star P,n)

abbrev signature : Signature (Index α) where
  Op := Op α
  arity
    | .union _ _ _ | .intersection _ _ _ | .concat _ _ _ => 2
    | .transport _ _ _ _ | .cut _ _ | .scale _ _ _ | .star _ _ => 1
  child
    | .union P Q n, k | .intersection P Q n, k | .concat P Q n, k => (Fin.cases P (fun _ => Q) k,n)
    | .transport P _ n _, _ | .scale P n _, _ | .star P n, _ => (P,n)
    | .cut P n, _ => (P,n+1)

abbrev behavior : Behavior (Index α) where
  Output j := Decision (j.1 [])
  Request j := match j.2 with | 0 => PEmpty | _+1 => α
  next j a := match j with
    | (_,0) => nomatch a
    | (P,n+1) => (derivative P a,n)

abbrev Source (j : Index α) := Parser j.1
abbrev Target (j : Index α) := WitnessTrie j.1 j.2

def source [DecidableEq α] : behavior.Coalgebra (Source (α := α))
  | (_,0), p => (p.nullable, fun a => nomatch a)
  | (_,_n+1), p => (p.nullable, fun a => p.derive a)

def target : behavior.Coalgebra (Target (α := α))
  | (_,0), .leaf d => (d, fun a => nomatch a)
  | (_,_n+1), .node d ts => (d,ts)

def sourceAlgebra : {j : Index α} → (op : signature.Op j) →
    (∀ k, Source (signature.child op k)) → Source j
  | _, .union _ _ _, xs => .union (xs 0) (xs 1)
  | _, .transport _ _ _ e, xs => .transport e (xs 0)
  | _, .cut _ _, xs => xs 0
  | _, .scale _ _ d, xs => .scale d (xs 0)
  | _, .intersection _ _ _, xs => .intersection (xs 0) (xs 1)
  | _, .concat _ _ _, xs => .concat (xs 0) (xs 1)
  | _, .star _ _, xs => .star (xs 0)

def targetAlgebra : {j : Index α} → (op : signature.Op j) →
    (∀ k, Target (signature.child op k)) → Target j
  | _, .union _ _ _, xs => WitnessTrie.union (xs 0) (xs 1)
  | _, .transport _ _ _ e, xs => WitnessTrie.transport e (xs 0)
  | _, .cut _ n, xs => WitnessTrie.truncate n (Nat.le_succ n) (xs 0)
  | _, .scale _ _ d, xs => WitnessTrie.scale d (xs 0)
  | _, .intersection _ _ _, xs => WitnessTrie.intersection (xs 0) (xs 1)
  | _, .concat _ _ n, xs => WitnessTrie.concat n (xs 0) (xs 1)
  | _, .star _ n, xs => WitnessTrie.star n (xs 0)

def step : {j : Index α} → (op : signature.Op j) →
    (∀ k, behavior.Output (signature.child op k)) →
    (a : behavior.Request j) → Term signature (Slot signature behavior op) (behavior.next j a)
  | _, .union _ _ 0, _, a => nomatch a
  | _, .union P Q (n+1), _, a => by
    let left : Slot signature behavior (.union P Q (n+1)) (derivative P a,n) := by
      exact @Slot.succ (Index α) signature behavior _ (.union P Q (n+1)) ⟨0, by exact Nat.zero_lt_succ 1⟩ a
    let right : Slot signature behavior (.union P Q (n+1)) (derivative Q a,n) := by
      exact @Slot.succ (Index α) signature behavior _ (.union P Q (n+1)) ⟨1, by exact Nat.lt_succ_self 1⟩ a
    exact .node (.union (derivative P a) (derivative Q a) n)
      (fun k => Fin.cases (.leaf left) (fun _ => .leaf right) k)
  | _, .transport _ _ 0 _, _, a => nomatch a
  | _, .transport P Q (n+1) e, _, a =>
    .node (.transport (derivative P a) (derivative Q a) n (fun w => e (a::w)))
      (fun _ => .leaf (Slot.succ (S := signature) (B := behavior) (op := Op.transport P Q (n+1) e) 0 a))
  | _, .cut _ 0, _, a => nomatch a
  | _, .cut P (n+1), _, a =>
    .node (.cut (derivative P a) n) (fun _ => .leaf (Slot.succ (S := signature) (B := behavior) (op := Op.cut P (n+1)) 0 a))
  | _, .scale _ 0 _, _, a => nomatch a
  | _, .scale P (n+1) d, _, a =>
    .node (.scale (derivative P a) n d) (fun _ => .leaf (Slot.succ (S := signature) (B := behavior) (op := Op.scale P (n+1) d) 0 a))
  | _, .intersection _ _ 0, _, a => nomatch a
  | _, .intersection P Q (n+1), _, a =>
    .node (.intersection (derivative P a) (derivative Q a) n)
      (fun k => Fin.cases
        (.leaf (by exact @Slot.succ (Index α) signature behavior _ (Op.intersection P Q (n+1)) ⟨0, by exact Nat.zero_lt_succ 1⟩ a))
        (fun _ => .leaf (by exact @Slot.succ (Index α) signature behavior _ (Op.intersection P Q (n+1)) ⟨1, by exact Nat.lt_succ_self 1⟩ a)) k)
  | _, .concat _ _ 0, _, a => nomatch a
  | _, .concat P Q (n+1), xs, a =>
    .node (.transport _ _ n (fun w => (derivativeConcatIso P Q a w).symm)) (fun _ =>
      .node (.union _ _ n) (fun k => Fin.cases
        (.node (.scale _ n (xs 0)) (fun _ => .leaf (by exact @Slot.succ (Index α) signature behavior _ (Op.concat P Q (n+1)) ⟨1, by exact Nat.lt_succ_self 1⟩ a)))
        (fun _ => .node (.concat _ _ n) (fun k => Fin.cases
          (.leaf (by exact @Slot.succ (Index α) signature behavior _ (Op.concat P Q (n+1)) ⟨0, by exact Nat.zero_lt_succ 1⟩ a))
          (fun _ => .node (.cut Q n) (fun _ => .leaf (Slot.ret (S := signature) (B := behavior) (op := Op.concat P Q (n+1)) 1))) k)) k))
  | _, .star _ 0, _, a => nomatch a
  | _, .star P (n+1), _, a =>
    .node (.transport _ _ n (fun w => (derivativeStarIso P a w).symm)) (fun _ =>
      .node (.scale _ n (.yes [])) (fun _ =>
        .node (.concat _ _ n) (fun k => Fin.cases
          (.leaf (by exact @Slot.succ (Index α) signature behavior _ (Op.star P (n+1)) ⟨0, by exact Nat.zero_lt_succ 0⟩ a))
          (fun _ => .node (.star P n) (fun _ =>
            .node (.cut P n) (fun _ => .leaf (Slot.ret (S := signature) (B := behavior) (op := Op.star P (n+1)) 0)))) k)))

def rule : Rule (signature (α := α)) behavior where
  out op xs := match op with
    | .union _ _ _ => (xs 0).sum (xs 1)
    | .transport _ _ _ e => (xs 0).map (e [])
    | .cut _ _ => xs 0
    | .scale _ _ d => d.prod (xs 0)
    | .intersection _ _ _ => (xs 0).prod (xs 1)
    | .concat P Q _ => ((xs 0).prod (xs 1)).map (nullableConcatIso P Q).symm
    | .star _ _ => .yes ⟨[], rfl⟩
  step := step

theorem sourceCompatible [DecidableEq α] :
    (rule (α := α)).Compatible sourceAlgebra source where
  output j op xs := by
    cases op with
    | union P Q n => cases n <;> rfl
    | transport P Q n e => cases n <;> rfl
    | cut P n => cases n <;> rfl
    | scale P n d => cases n <;> rfl
    | intersection P Q n => cases n <;> rfl
    | concat P Q n => cases n <;> rfl
    | star P n => cases n <;> rfl
  next j op xs a := by
    cases op with
    | union P Q n => cases n with
      | zero => exact nomatch a
      | succ n => rfl
    | transport P Q n e => cases n with
      | zero => exact nomatch a
      | succ n => rfl
    | cut P n => cases n with
      | zero => exact nomatch a
      | succ n => rfl
    | scale P n d => cases n with
      | zero => exact nomatch a
      | succ n => rfl
    | intersection P Q n => cases n with
      | zero => exact nomatch a
      | succ n => rfl
    | concat P Q n => cases n with
      | zero => exact nomatch a
      | succ n => rfl
    | star P n => cases n with
      | zero => exact nomatch a
      | succ n => rfl

theorem targetCompatible : (rule (α := α)).Compatible targetAlgebra target where
  output j op xs := by
    cases op with
    | union P Q n =>
      change (target (fun w => P w ⊕ Q w,n) (WitnessTrie.union (xs 0) (xs 1))).1 =
        ((target _ (xs 0)).1).sum ((target _ (xs 1)).1)
      cases n with
      | zero => cases xs 0; cases xs 1; rfl
      | succ n => cases xs 0; cases xs 1; rfl
    | transport P Q n e =>
      change (target (Q,n) (WitnessTrie.transport e (xs 0))).1 = ((target _ (xs 0)).1).map (e [])
      cases n with
      | zero => cases xs 0; rfl
      | succ n => cases xs 0; rfl
    | cut P n =>
      simp only [targetAlgebra, rule]
      cases n <;> cases xs 0 <;> rfl
    | scale P n d =>
      simp only [targetAlgebra, rule]
      cases n <;> cases xs 0 <;> rfl
    | intersection P Q n =>
      simp only [targetAlgebra, rule]
      cases n <;> cases xs 0 <;> cases xs 1 <;> rfl
    | concat P Q n =>
      simp only [targetAlgebra, rule]
      cases n <;> cases xs 0 <;> cases xs 1 <;> rfl
    | star P n =>
      simp only [targetAlgebra, rule]
      cases n <;> cases xs 0 <;> rfl
  next j op xs a := by
    cases op with
    | union P Q n => cases n with
      | zero => exact nomatch a
      | succ n =>
        change (target _ (WitnessTrie.union (xs 0) (xs 1))).2 a =
          WitnessTrie.union ((target _ (xs 0)).2 a) ((target _ (xs 1)).2 a)
        cases xs 0; cases xs 1; rfl
    | transport P Q n e => cases n with
      | zero => exact nomatch a
      | succ n =>
        change (target _ (WitnessTrie.transport e (xs 0))).2 a =
          WitnessTrie.transport (fun w => e (a::w)) ((target _ (xs 0)).2 a)
        cases xs 0; rfl
    | cut P n => cases n with
      | zero => exact nomatch a
      | succ n =>
        simp only [targetAlgebra, rule, step, Term.fold, Rule.slots]
        cases xs 0; rfl
    | scale P n d => cases n with
      | zero => exact nomatch a
      | succ n =>
        simp only [targetAlgebra, rule, step, Term.fold, Rule.slots]
        cases xs 0; rfl
    | intersection P Q n => cases n with
      | zero => exact nomatch a
      | succ n =>
        change (target _ (WitnessTrie.intersection (xs 0) (xs 1))).2 a =
          WitnessTrie.intersection ((target _ (xs 0)).2 a) ((target _ (xs 1)).2 a)
        cases xs 0; cases xs 1; rfl
    | concat P Q n => cases n with
      | zero => exact nomatch a
      | succ n =>
        change (target _ (WitnessTrie.concat (n+1) (xs 0) (xs 1))).2 a =
          WitnessTrie.transport (fun w => (derivativeConcatIso P Q a w).symm)
            (WitnessTrie.union (WitnessTrie.scale ((target _ (xs 0)).1) ((target _ (xs 1)).2 a))
              (WitnessTrie.concat n ((target _ (xs 0)).2 a)
                (WitnessTrie.truncate n (Nat.le_succ n) (xs 1))))
        cases xs 0; cases xs 1; rfl
    | star P n => cases n with
      | zero => exact nomatch a
      | succ n =>
        change (target _ (WitnessTrie.star (n+1) (xs 0))).2 a =
          WitnessTrie.transport (fun w => (derivativeStarIso P a w).symm)
            (WitnessTrie.scale (.yes []) (WitnessTrie.concat n ((target _ (xs 0)).2 a)
              (WitnessTrie.star n (WitnessTrie.truncate n (Nat.le_succ n) (xs 0)))))
        cases xs 0; rfl

def unfold [DecidableEq α] (j : Index α) : Source j → Target j := fun p => WitnessTrie.unfold p j.2

theorem unfold_morphism [DecidableEq α] :
    behavior.Morphism (source (α := α)) target unfold where
  output j p := by rcases j with ⟨P,n⟩; cases n <;> rfl
  next j p a := by rcases j with ⟨P,n⟩; cases n with
    | zero => exact nomatch a
    | succ n => rfl

/-- Direct word observations keep the word-indexed result visible to callers. -/
def read {X : Index α → Type v} (c : behavior.Coalgebra X) :
    {P : Language α} → {n : Nat} → X (P,n) → (w : List α) → w.length ≤ n → Decision (P w)
  | _, _, x, [], _ => (c _ x).1
  | _, 0, _, _::_, h => False.elim (Nat.not_succ_le_zero _ h)
  | _, _n+1, x, a::w, h => read c ((c _ x).2 a) w (Nat.le_of_succ_le_succ h)

theorem read_morphism {X : Index α → Type v} {Y : Index α → Type w}
    (c : behavior.Coalgebra X) (d : behavior.Coalgebra Y)
    (f : ∀ j, X j → Y j) (h : behavior.Morphism c d f)
    {P : Language α} {n} (x : X (P,n)) (word : List α) (bound : word.length ≤ n) :
    read d (f _ x) word bound = read c x word bound := by
  induction word generalizing P n with
  | nil => cases n <;> exact h.output _ x
  | cons a word ih =>
    cases n with
    | zero => exact False.elim (Nat.not_succ_le_zero _ bound)
    | succ n =>
      change read d ((d _ (f _ x)).2 a) word _ = read c ((c _ x).2 a) word _
      rw [h.next]; exact ih _ _

theorem read_source [DecidableEq α] {P : Language α} {n} (p : Parser P)
    (word : List α) (bound : word.length ≤ n) : read source (n := n) p word bound = p.parse word := by
  induction word generalizing P n with
  | nil => cases n <;> rfl
  | cons a word ih =>
    cases n with
    | zero => exact False.elim (Nat.not_succ_le_zero _ bound)
    | succ n => exact ih _ _

theorem read_target {P : Language α} {n} (t : WitnessTrie P n)
    (word : List α) (bound : word.length ≤ n) : read target t word bound = t.lookup word bound := by
  induction word generalizing P n with
  | nil => cases t <;> rfl
  | cons a word ih =>
    cases t with
    | leaf => exact False.elim (Nat.not_succ_le_zero _ bound)
    | node d ts => exact ih _ _

/-- Both native interpretations are compared through the shared all-term theorem. -/
theorem recovered [DecidableEq α] {P : Language α} {n}
    (t : Term signature Source (P,n)) (word : List α) (bound : word.length ≤ n) :
    (Term.fold targetAlgebra unfold t).lookup word bound =
      (Term.fold sourceAlgebra (fun _ x => x) t).parse word := by
  have ht := (rule (α := α)).fold_morphism targetAlgebra target targetCompatible source unfold unfold_morphism
  have hs := (rule (α := α)).fold_morphism sourceAlgebra source sourceCompatible source (fun _ x => x)
    ⟨fun _ _ => rfl, fun _ _ _ => rfl⟩
  rw [← read_target, read_morphism _ _ _ ht]
  rw [← read_morphism _ _ _ hs, read_source]

/-- The all-term observation theorem recovers the whole native finite trie. -/
theorem recovered_tree [DecidableEq α] {P : Language α} {n}
    (t : Term signature Source (P,n)) :
    Term.fold targetAlgebra unfold t =
      WitnessTrie.unfold (Term.fold sourceAlgebra (fun _ x => x) t) n := by
  apply WitnessTrie.ext_lookup
  intro word bound
  rw [WitnessTrie.lookup_unfold]
  exact recovered t word bound

/-- Recovery of the direct concatenation result through the shared theorem. -/
theorem recovered_concat [DecidableEq α] {P Q : Language α}
    (p : Parser P) (q : Parser Q) (n : Nat) :
    WitnessTrie.concat n (WitnessTrie.unfold p n) (WitnessTrie.unfold q n) =
      WitnessTrie.unfold (.concat p q) n := by
  let t : Term signature Source (Concat P Q,n) := .node (.concat P Q n)
    (fun k => Fin.cases (.leaf p) (fun _ => .leaf q) k)
  exact recovered_tree t

theorem recovered_star [DecidableEq α] {P : Language α} (p : Parser P) (n : Nat) :
    WitnessTrie.star n (WitnessTrie.unfold p n) = WitnessTrie.unfold (.star p) n :=
  recovered_tree (.node (.star P n) (fun _ => .leaf p))

/-- One-step restriction is the new signature operation, not a derivative. -/
def cutTerm {X : Index α → Type v} {P : Language α} {n}
    (t : Term signature X (P,n+1)) : Term signature X (P,n) :=
  .node (.cut P n) (fun _ => t)

theorem fold_cut {X : Index α → Type v} (f : ∀ j, X j → Target j)
    {P : Language α} {n} (t : Term signature X (P,n+1)) :
    Term.fold targetAlgebra f (cutTerm t) =
      WitnessTrie.truncate n (Nat.le_succ n) (Term.fold targetAlgebra f t) := rfl

theorem fold_cut_twice {X : Index α → Type v} (f : ∀ j, X j → Target j)
    {P : Language α} {n} (t : Term signature X (P,n+2)) :
    Term.fold targetAlgebra f (cutTerm (cutTerm t)) =
      WitnessTrie.truncate n (Nat.le_trans (Nat.le_succ n) (Nat.le_succ (n+1)))
        (Term.fold targetAlgebra f t) := by
  rw [fold_cut, fold_cut, WitnessTrie.truncate_comp]

/-- Trie leaves may retain choices not produced by the standard symbolic parser. -/
theorem recovered_trie {P : Language α} {n} (t : Term signature Target (P,n))
    (word : List α) (bound : word.length ≤ n) :
    read (rule.lift target) t word bound =
      (Term.fold targetAlgebra (fun _ x => x) t).lookup word bound := by
  have ht := (rule (α := α)).fold_morphism targetAlgebra target targetCompatible target (fun _ x => x)
    ⟨fun _ _ => rfl, fun _ _ _ => rfl⟩
  rw [← read_morphism _ _ _ ht, read_target]
end LanguageWitnesses.IndexedCompositional
