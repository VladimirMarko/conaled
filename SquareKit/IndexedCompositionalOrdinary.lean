import SquareKit.IndexedCompositional

/-! The ordinary derivative-template calculus embeds at the singleton sort.
Original slots retain children; successor slots use the current parent letter.
The old fold contract is recovered through the indexed fold theorem. -/
namespace SquareKit.IndexedCompositional.Ordinary
universe u v w d a o b
variable {Op : Type u} {arity : Op → Nat} {X : Type v} {Y : Type w}
  {D : Type d} {A : Type a} {O : Type o}

abbrev signature (Op : Type u) (arity : Op → Nat) : Signature Unit where
  Op _ := Op
  arity := arity
  child _ _ := ()

abbrev behavior (A : Type a) (O : Type o) : Behavior Unit where
  Output _ := O
  Request _ := A
  next _ _ := ()

abbrev coalgebra (c : WordCoalgebra.Coalgebra A O X) : (behavior A O).Coalgebra (fun _ => X) :=
  fun _ => c

/-- Replace ordinary leaves by indexed terms, at the sole sort. -/
def expand {F : Unit → Type w} (f : X → Term (signature Op arity) F ()) :
    CompositionalCoalgebra.Term Op arity X → Term (signature Op arity) F ()
  | .leaf x => f x
  | .node op ts => .node op (fun k => expand f (ts k))

def embed (t : CompositionalCoalgebra.Term Op arity X) : Term (signature Op arity) (fun _ => X) () :=
  expand Term.leaf t

@[simp] theorem embed_leaf (x : X) : embed (CompositionalCoalgebra.Term.leaf (Op := Op) (arity := arity) x) =
    Term.leaf x := rfl
@[simp] theorem embed_node (op : Op) (ts : Fin (arity op) → CompositionalCoalgebra.Term Op arity X) :
    embed (.node op ts) = .node op (fun k => embed (ts k)) := rfl

theorem bind_expand {F : Unit → Type b} {G : Unit → Type w}
    (g : ∀ j, F j → Term (signature Op arity) G j)
    (f : X → Term (signature Op arity) F ()) (t : CompositionalCoalgebra.Term Op arity X) :
    Term.bind g (expand f t) = expand (fun x => Term.bind g (f x)) t := by
  induction t with
  | leaf => rfl
  | node op ts ih => simp only [expand, Term.bind]; congr 1; funext k; exact ih k

theorem expand_bind {F : Unit → Type d} (g : Y → Term (signature Op arity) F ())
    (f : X → CompositionalCoalgebra.Term Op arity Y) (t : CompositionalCoalgebra.Term Op arity X) :
    expand g (CompositionalCoalgebra.Term.bind f t) = expand (fun x => expand g (f x)) t := by
  induction t with
  | leaf => rfl
  | node op ts ih => simp only [CompositionalCoalgebra.Term.bind, FinitaryTerm.bind, expand]; congr 1; funext k; exact ih k

/-- Substitution retains the old variable and constructor structure. -/
theorem embed_bind (f : X → CompositionalCoalgebra.Term Op arity Y) (t : CompositionalCoalgebra.Term Op arity X) :
    embed (CompositionalCoalgebra.Term.bind f t) =
      Term.bind (fun j x => match j with | () => embed (f x)) (embed t) := by
  simp only [embed, expand_bind, bind_expand, Term.bind]

/-- Fold arbitrary indexed algebras through the ordinary tree embedding. -/
theorem fold_expand {F : Unit → Type b} {G : Unit → Type d}
    (alg : ∀ {j} (op : (signature Op arity).Op j),
      (∀ k, G ((signature Op arity).child op k)) → G j)
    (g : ∀ j, F j → G j) (f : X → Term (signature Op arity) F ())
    (t : CompositionalCoalgebra.Term Op arity X) :
    Term.fold alg g (expand f t) =
      CompositionalCoalgebra.Term.fold (fun op xs => alg op xs) (fun x => Term.fold alg g (f x)) t := by
  induction t with
  | leaf => rfl
  | node op ts ih => simp only [expand, Term.fold, CompositionalCoalgebra.Term.fold]; congr 1; funext k; exact ih k

abbrev algebra (alg : (op : Op) → (Fin (arity op) → D) → D) :
    ∀ {j} (op : (signature Op arity).Op j),
      (∀ k, (fun _ : Unit => D) ((signature Op arity).child op k)) → D :=
  fun op xs => alg op xs

theorem fold_embed (alg : (op : Op) → (Fin (arity op) → D) → D)
    (f : X → D) (t : CompositionalCoalgebra.Term Op arity X) :
    Term.fold (algebra alg) (fun _ => f) (embed t) = CompositionalCoalgebra.Term.fold alg f t := by
  exact fold_expand (algebra alg) (fun _ => f) Term.leaf t

/-- A right slot queries precisely the current letter, not an arbitrary child request. -/
def slot {j : Unit} (op : Op) (letter : A) : Fin (arity op) ⊕ Fin (arity op) →
    Slot (signature Op arity) (behavior A O) (j := j) op ()
  | .inl k => .ret k
  | .inr k => .succ k letter

def rule (r : CompositionalCoalgebra.Rule Op arity A O) : Rule (signature Op arity) (behavior A O) where
  out op xs := r.out op xs
  step {j} op xs letter := expand (fun s => .leaf (slot (j := j) op letter s)) (r.step op xs letter)

theorem output_embed (r : CompositionalCoalgebra.Rule Op arity A O) (c : WordCoalgebra.Coalgebra A O X)
    (t : CompositionalCoalgebra.Term Op arity X) :
    (rule r).output (coalgebra c) (embed t) = r.output c t := by
  induction t with
  | leaf => rfl
  | node op ts ih => simp only [embed_node, Rule.output, CompositionalCoalgebra.Rule.output, rule];
                     congr 1; funext k; exact ih k

theorem next_embed (r : CompositionalCoalgebra.Rule Op arity A O) (c : WordCoalgebra.Coalgebra A O X)
    (t : CompositionalCoalgebra.Term Op arity X) (letter : A) :
    (rule r).next (coalgebra c) (embed t) letter = embed (r.next c t letter) := by
  induction t with
  | leaf => rfl
  | node op ts ih =>
    simp only [embed_node, Rule.next, CompositionalCoalgebra.Rule.next, output_embed]
    simp only [rule, bind_expand, embed, expand_bind]
    congr 1
    funext s
    cases s with
    | inl k => rfl
    | inr k => exact ih k

/-- Constructor-local compatibility translates without adding composite premises. -/
theorem compatible (r : CompositionalCoalgebra.Rule Op arity A O)
    (alg : (op : Op) → (Fin (arity op) → D) → D) (d : WordCoalgebra.Coalgebra A O D)
    (h : r.Compatible alg d) : (rule r).Compatible (algebra alg) (coalgebra d) where
  output _ op xs := h.output op xs
  next j op xs letter := by
    cases j
    simp only [coalgebra, algebra, rule]
    rw [fold_expand]
    rw [h.next]
    congr 1
    funext s
    cases s <;> rfl

/-- The ordinary #268 fold-morphism contract, obtained from the new indexed theorem. -/
theorem fold_morphism (r : CompositionalCoalgebra.Rule Op arity A O)
    (alg : (op : Op) → (Fin (arity op) → D) → D) (d : WordCoalgebra.Coalgebra A O D)
    (hc : r.Compatible alg d) (c : WordCoalgebra.Coalgebra A O X)
    (f : X → D) (hf : WordCoalgebra.Morphism c d f) :
    WordCoalgebra.Morphism (r.lift c) d (CompositionalCoalgebra.Term.fold alg f) := by
  have indexed := (rule r).fold_morphism (algebra alg) (coalgebra d)
    (compatible r alg d hc) (coalgebra c) (fun _ => f)
    ⟨fun _ x => hf.output x, fun _ x letter => hf.next x letter⟩
  constructor
  · intro t
    have h := indexed.output () (embed t)
    simpa only [fold_embed, coalgebra, Rule.lift, output_embed, CompositionalCoalgebra.Rule.lift, behavior] using h
  · intro t letter
    have h := indexed.next () (embed t) letter
    simpa only [fold_embed, coalgebra, Rule.lift, next_embed, CompositionalCoalgebra.Rule.lift, behavior] using h
namespace Example

/-- A two-child operation retains its first child and advances only its second. -/
def mixed : CompositionalCoalgebra.Rule Unit (fun _ => 2) Bool Nat where
  out _ xs := xs 0 + xs 1
  step _ _ _ := .node () (fun k =>
    if k = 0 then .leaf (.inl 0) else .leaf (.inr 1))

def counter : WordCoalgebra.Coalgebra Bool Nat Nat :=
  fun n => (n, fun letter => n + if letter then 1 else 2)

def add (_ : Unit) (xs : Fin 2 → Nat) : Nat := xs 0 + xs 1

theorem mixed_compatible : mixed.Compatible add counter where
  output _ _ := rfl
  next _ xs letter := by
    simp [counter, add, mixed, CompositionalCoalgebra.Term.fold, Nat.add_assoc]

def pair : CompositionalCoalgebra.Term Unit (fun _ => 2) Nat :=
  .node () (fun k => if k = 0 then .leaf 7 else .leaf 11)

/-- The current letter selects +1 or +2; advancing both children would be wrong. -/
theorem mixed_current_letter :
    (rule mixed).output (coalgebra counter)
      ((rule mixed).next (coalgebra counter) (embed pair) true) = 19 ∧
    (rule mixed).output (coalgebra counter)
      ((rule mixed).next (coalgebra counter) (embed pair) false) = 20 := by
  rw [next_embed, next_embed, output_embed, output_embed]
  constructor <;> rfl

/-- The existing ordinary contract is obtained through the indexed fold theorem. -/
theorem mixed_fold : WordCoalgebra.Morphism (mixed.lift counter) counter
    (CompositionalCoalgebra.Term.fold add id) :=
  fold_morphism mixed add counter mixed_compatible counter id
    ⟨fun _ => rfl, fun _ _ => rfl⟩

example : CompositionalCoalgebra.Term.fold add id (mixed.next counter pair true) = 19 := by
  have h := mixed_fold.next pair true
  exact h.symm.trans rfl
end Example
end SquareKit.IndexedCompositional.Ordinary
