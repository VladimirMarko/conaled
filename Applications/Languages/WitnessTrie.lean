import Applications.Languages.Parser

/-! Bounded automatic observations retain a selected witness or its refutation.
All recursive combinators decrease the observation depth. -/
namespace LanguageWitnesses
universe u
variable {α : Type u}

inductive WitnessTrie : Language α → Nat → Type (u+1)
  | leaf {P} : Decision (P []) → WitnessTrie P 0
  | node {P n} : Decision (P []) → ((a : α) → WitnessTrie (derivative P a) n) → WitnessTrie P (n+1)

namespace WitnessTrie
variable {P Q : Language α}

def head : {n : Nat} → WitnessTrie P n → Decision (P [])
  | _, .leaf d => d
  | _, .node d _ => d

def lookup {P : Language α} : {n : Nat} → WitnessTrie P n → (w : List α) → w.length ≤ n → Decision (P w)
  | _, .leaf d, [], _ => d
  | _, .leaf _, _ :: _, h => False.elim (Nat.not_succ_le_zero _ h)
  | _, .node d _, [], _ => d
  | _, .node _ ts, a :: w, h => (ts a).lookup w (Nat.le_of_succ_le_succ h)

theorem observation {n : Nat} (t : WitnessTrie P n) (w : List α) (h : w.length ≤ n) :
    (t.lookup w h).test = true ↔ Nonempty (P w) := Decision.test_correct _

def truncate {P : Language α} : (n : Nat) → {m : Nat} → n ≤ m → WitnessTrie P m → WitnessTrie P n
  | 0, _, _, t => .leaf t.head
  | _+1, 0, h, _ => False.elim (Nat.not_succ_le_zero _ h)
  | n+1, _+1, h, .node d ts => .node d (fun a => truncate n (Nat.le_of_succ_le_succ h) (ts a))

theorem lookup_truncate (n : Nat) {m : Nat} (h : n ≤ m) (t : WitnessTrie P m)
    (w : List α) (hw : w.length ≤ n) :
    (truncate n h t).lookup w hw = t.lookup w (Nat.le_trans hw h) := by
  induction n generalizing m P w with
  | zero =>
    cases w with
    | nil => cases t <;> rfl
    | cons a w => exact False.elim (Nat.not_succ_le_zero _ hw)
  | succ n ih =>
    cases t with
    | leaf d => exact False.elim (Nat.not_succ_le_zero _ h)
    | node d ts =>
      cases w with
      | nil => rfl
      | cons a w => exact ih _ _ _ _

/-- Exact bounded decisions determine the entire finite trie. -/
theorem ext_lookup {n} (s t : WitnessTrie P n)
    (h : ∀ w hw, s.lookup w hw = t.lookup w hw) : s = t := by
  induction n generalizing P with
  | zero =>
    cases s; cases t
    exact congrArg WitnessTrie.leaf (h [] (Nat.zero_le _))
  | succ n ih =>
    cases s with
    | node d ss => cases t with
      | node e ts =>
        have hd : d = e := h [] (Nat.zero_le _)
        have hs : ss = ts := by
          funext a
          apply ih
          intro w hw
          exact h (a::w) (Nat.succ_le_succ hw)
        cases hd; cases hs; rfl

theorem truncate_self {n} (t : WitnessTrie P n) : truncate n (Nat.le_refl n) t = t := by
  apply ext_lookup
  intro w hw
  exact lookup_truncate _ _ _ _ _

theorem truncate_comp (l n : Nat) {m} (hln : l ≤ n) (hnm : n ≤ m) (t : WitnessTrie P m) :
    truncate l hln (truncate n hnm t) = truncate l (Nat.le_trans hln hnm) t := by
  apply ext_lookup
  intro w hw
  rw [lookup_truncate, lookup_truncate, lookup_truncate]

def unfold [DecidableEq α] {P : Language α} (p : Parser P) : (n : Nat) → WitnessTrie P n
  | 0 => .leaf p.nullable
  | n+1 => .node p.nullable (fun a => unfold (p.derive a) n)

theorem lookup_unfold [DecidableEq α] (p : Parser P) (n : Nat) (w : List α) (h : w.length ≤ n) :
    (unfold p n).lookup w h = p.parse w := by
  induction w generalizing P n with
  | nil => cases n <;> rfl
  | cons a w ih =>
    cases n with
    | zero => exact False.elim (Nat.not_succ_le_zero _ h)
    | succ n => exact ih _ _ _

theorem truncate_unfold [DecidableEq α] (p : Parser P) (n m : Nat) (h : n ≤ m) :
    truncate n h (unfold p m) = unfold p n := by
  induction n generalizing P m with
  | zero => cases m <;> rfl
  | succ n ih =>
    cases m with
    | zero => exact False.elim (Nat.not_succ_le_zero _ h)
    | succ m =>
      simp only [unfold, truncate]
      congr 1
      funext a
      exact ih _ _ _

def transport {P Q : Language α} (e : ∀ w, Iso (P w) (Q w)) : {n : Nat} → WitnessTrie P n → WitnessTrie Q n
  | _, .leaf d => .leaf (d.map (e []))
  | _, .node d ts => .node (d.map (e [])) (fun a => transport (fun w => e (a :: w)) (ts a))

def union {P Q : Language α} : {n : Nat} → WitnessTrie P n → WitnessTrie Q n → WitnessTrie (fun w => P w ⊕ Q w) n
  | _, .leaf p, .leaf q => .leaf (p.sum q)
  | _, .node p ps, .node q qs => .node (p.sum q) (fun a => union (ps a) (qs a))

def intersection {P Q : Language α} : {n : Nat} → WitnessTrie P n → WitnessTrie Q n → WitnessTrie (fun w => P w × Q w) n
  | _, .leaf p, .leaf q => .leaf (p.prod q)
  | _, .node p ps, .node q qs => .node (p.prod q) (fun a => intersection (ps a) (qs a))

def scale {P : Language α} {A : Type u} (d : Decision A) : {n : Nat} → WitnessTrie P n → WitnessTrie (fun w => A × P w) n
  | _, .leaf p => .leaf (d.prod p)
  | _, .node p ps => .node (d.prod p) (fun a => scale d (ps a))

/-- Retain the original right operand, truncated to the smaller depth. -/
def concat {P Q : Language α} : (n : Nat) → WitnessTrie P n → WitnessTrie Q n → WitnessTrie (Concat P Q) n
  | 0, .leaf p, .leaf q => .leaf ((p.prod q).map (nullableConcatIso P Q).symm)
  | n+1, .node p ps, q@(.node qh qs) =>
    .node ((p.prod qh).map (nullableConcatIso P Q).symm) (fun a =>
      transport (fun w => (derivativeConcatIso P Q a w).symm)
        (union (scale p (qs a)) (concat n (ps a) (truncate n (Nat.le_succ n) q))))

/-- Empty nullable-parse lists are a selection policy, not an erasure of the index. -/
def star {P : Language α} : (n : Nat) → WitnessTrie P n → WitnessTrie (Star P) n
  | 0, _ => .leaf (.yes ⟨[], rfl⟩)
  | n+1, p@(.node _ ps) => .node (.yes ⟨[], rfl⟩) (fun a =>
      transport (fun w => (derivativeStarIso P a w).symm)
        (scale (.yes []) (concat n (ps a) (star n (truncate n (Nat.le_succ n) p)))))
theorem unfold_transport [DecidableEq α] (e : ∀ w, Iso (P w) (Q w))
    (p : Parser P) (n : Nat) :
    unfold (.transport e p) n = transport e (unfold p n) := by
  induction n generalizing P Q with
  | zero => rfl
  | succ n ih =>
    simp only [unfold, Parser.nullable, Parser.derive, transport]
    congr 1
    funext a
    exact ih _ _

theorem unfold_union [DecidableEq α] (p : Parser P) (q : Parser Q) (n : Nat) :
    unfold (.union p q) n = union (unfold p n) (unfold q n) := by
  induction n generalizing P Q with
  | zero => rfl
  | succ n ih =>
    simp only [unfold, Parser.nullable, Parser.derive, union]
    congr 1
    funext a
    exact ih _ _

theorem unfold_intersection [DecidableEq α] (p : Parser P) (q : Parser Q) (n : Nat) :
    unfold (.intersection p q) n = intersection (unfold p n) (unfold q n) := by
  induction n generalizing P Q with
  | zero => rfl
  | succ n ih =>
    simp only [unfold, Parser.nullable, Parser.derive, intersection]
    congr 1
    funext a
    exact ih _ _

theorem unfold_scale [DecidableEq α] {A : Type u} (d : Decision A) (p : Parser P) (n : Nat) :
    unfold (.scale d p) n = scale d (unfold p n) := by
  induction n generalizing P with
  | zero => rfl
  | succ n ih =>
    simp only [unfold, Parser.nullable, Parser.derive, scale]
    congr 1
    funext a
    exact ih _

theorem unfold_concat [DecidableEq α] (p : Parser P) (q : Parser Q) (n : Nat) :
    unfold (.concat p q) n = concat n (unfold p n) (unfold q n) := by
  induction n generalizing P Q with
  | zero => rfl
  | succ n ih =>
    simp only [unfold, Parser.nullable, Parser.derive, concat]
    congr 1
    funext a
    erw [unfold_transport, unfold_union, unfold_scale, ih]
    erw [truncate_unfold]
    rfl

theorem unfold_star [DecidableEq α] (p : Parser P) (n : Nat) :
    unfold (.star p) n = star n (unfold p n) := by
  induction n generalizing P with
  | zero => rfl
  | succ n ih =>
    simp only [unfold, Parser.nullable, Parser.derive, star]
    congr 1
    funext a
    erw [unfold_transport, unfold_scale, unfold_concat, ih, truncate_unfold]
    rfl
end WitnessTrie
end LanguageWitnesses
