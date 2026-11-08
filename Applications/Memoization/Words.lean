import Applications.Memoization.Representation
import Applications.Memoization.Client

namespace Applications.Memoization
namespace Words

def Key : Nat → Type
  | 0 => Unit
  | d + 1 => Unit ⊕ (Bool × Key d)

def representation : (d : Nat) → Representation (Key d)
  | 0 => .unit
  | d + 1 => .sum .unit (.prod .bool (representation d))

abbrev Table (d : Nat) (V : Type) := (representation d).Carrier V

def cells : Nat → Nat
  | 0 => 1
  | d+1 => 1 + 2 * cells d

def storedEntries : {d : Nat} → Table d V → Nat
  | 0, _ => 1
  | _+1, t => 1 + storedEntries t.2.1 + storedEntries t.2.2

theorem storedEntries_cells {d : Nat} (t : Table d V) : storedEntries t = cells d := by
  induction d with
  | zero => rfl
  | succ d ih => simp only [storedEntries, cells, ih]; omega

def word : {d : Nat} → Key d → List Bool
  | 0, _ => []
  | _ + 1, .inl _ => []
  | _ + 1, .inr (b,k) => b :: word k

theorem word_length {d : Nat} (k : Key d) : (word k).length ≤ d := by
  induction d with
  | zero => simp [word]
  | succ d ih => cases k with
    | inl u => simp [word]
    | inr p => simpa [word] using ih p.2

def key : (d : Nat) → (w : List Bool) → w.length ≤ d → Key d
  | 0, [], _ => ()
  | 0, _ :: _, h => False.elim (by simp at h)
  | _ + 1, [], _ => .inl ()
  | d + 1, b :: w, h => .inr (b, key d w (by simpa using h))

@[simp] theorem word_key (d : Nat) (w : List Bool) (h : w.length ≤ d) :
    word (key d w h) = w := by
  induction d generalizing w with
  | zero => cases w with
    | nil => rfl
    | cons b w => simp only [List.length_cons] at h; omega
  | succ d ih => cases w <;> simp [key, word, ih]

@[simp] theorem key_word {d : Nat} (k : Key d) : key d (word k) (word_length k) = k := by
  induction d with
  | zero => cases k; rfl
  | succ d ih => cases k with
    | inl u => cases u; rfl
    | inr p => cases p with
      | mk b k => simp [word, key, ih]; rfl

def boundedEquiv (d : Nat) : Key d ≃ {w : List Bool // w.length ≤ d} where
  toFun k := ⟨word k, word_length k⟩
  invFun w := key d w.val w.property
  left_inv := key_word
  right_inv w := Subtype.ext (word_key d w.val w.property)

def observe {d : Nat} (t : Table d V) (w : List Bool) : Option V :=
  if h : w.length ≤ d then some ((representation d).lookup t (key d w h)) else none

@[simp] theorem observe_tabulate (d : Nat) (f : List Bool → V) (w : List Bool) :
    observe ((representation d).tabulate (fun k => f (word k))) w =
      if w.length ≤ d then some (f w) else none := by
  unfold observe
  split <;> simp_all

/-- Physical truncation copies only the requested prefix tree. -/
def restrict : {m n : Nat} → m ≤ n → Table n V → Table m V
  | 0, 0, _, t => t
  | 0, _ + 1, _, t => t.1
  | _ + 1, 0, h, _ => False.elim (by omega)
  | m + 1, n + 1, h, t =>
    (t.1, (restrict (Nat.le_of_succ_le_succ h) t.2.1,
      restrict (Nat.le_of_succ_le_succ h) t.2.2))

theorem lookup_restrict {m n : Nat} (h : m ≤ n) (t : Table n V) (k : Key m) :
    (representation m).lookup (restrict h t) k =
      (representation n).lookup t (key n (word k) ((word_length k).trans h)) := by
  induction m generalizing n with
  | zero => cases n <;> cases k <;> rfl
  | succ m ih => cases n with
    | zero => omega
    | succ n => cases k with
      | inl u => cases u; rfl
      | inr p => rcases p with ⟨b,k⟩; cases b <;> exact ih _ _ k

theorem observe_restrict {m n : Nat} (h : m ≤ n) (t : Table n V)
    (w : List Bool) (hw : w.length ≤ m) : observe (restrict h t) w = observe t w := by
  simp only [observe, dite_eq_left hw, dite_eq_left (hw.trans h)]
  rw [lookup_restrict]
  simp

theorem restrict_restrict {l m n : Nat} (h : l ≤ m) (h' : m ≤ n) (t : Table n V) :
    restrict h (restrict h' t) = restrict (h.trans h') t := by
  apply (representation l).ext
  intro k
  simp only [lookup_restrict, word_key]

example : observe ((representation 3).tabulate (fun k => Client.wordMeaning (word k)))
    [true,false,true] = some ([true,false,true],5) := by rw [observe_tabulate]; rfl
example : observe ((representation 0).tabulate (fun k => Client.wordMeaning (word k)))
    [] = some ([],0) := by rw [observe_tabulate]; rfl
example : observe ((representation 1).tabulate (fun k => Client.wordMeaning (word k)))
    [true,false] = none := by rw [observe_tabulate]; rfl

end Words
end Applications.Memoization
