import Mathlib.Data.Tree.Basic

/-!
Dense binomial queues with the literal recursions of VFA's `Binom` chapter.
The Boolean comparator is executable data; no order law or rank cache is part
of the raw operations. Empty slots and the source's malformed-tree fallbacks
are retained. Correctness predicates and finite observations are separate.
-/
set_option autoImplicit false
set_option warningAsError true

namespace Search.BinomialQueue

universe u
variable {K : Type u}

/-- The position in this ordinary list is the rank slot, including empty slots. -/
abbrev Queue (K : Type u) := List (BinaryTree K)

def empty : Queue K := []

/-- The Nat specialization of the source's strict greater-than comparison. -/
def natGreater (x y : Nat) : Bool := decide (y < x)

/-- Link proper outer roots, choosing the second root on a comparison tie.
The source returns nil for either malformed outer tree. -/
def smash (greater : K → K → Bool) : BinaryTree K → BinaryTree K → BinaryTree K
  | .node x a .nil, .node y b .nil =>
      if greater x y then .node x (.node y b a) .nil
      else .node y (.node x a b) .nil
  | _, _ => .nil

/-- Place a carry into the first available dense rank slot. -/
def carry (greater : K → K → Bool) : Queue K → BinaryTree K → Queue K
  | [], .nil => []
  | [], t => [t]
  | .nil :: q, t => t :: q
  | u :: q, .nil => u :: q
  | u :: q, t => .nil :: carry greater q (smash greater t u)

def insert (greater : K → K → Bool) (x : K) (q : Queue K) : Queue K :=
  carry greater q (.node x .nil .nil)

/-- Source full-adder recursion. With three occupied inputs, emit the incoming
carry and link the two operand heads, preserving their argument order. -/
def join (greater : K → K → Bool) : Queue K → Queue K → BinaryTree K → Queue K
  | [], q, c => carry greater q c
  | p, [], c => carry greater p c
  | .nil :: p, .nil :: q, c => c :: join greater p q .nil
  | .nil :: p, q₀ :: q, .nil => q₀ :: join greater p q .nil
  | .nil :: p, q₀ :: q, c => .nil :: join greater p q (smash greater c q₀)
  | p₀ :: p, .nil :: q, .nil => p₀ :: join greater p q .nil
  | p₀ :: p, .nil :: q, c => .nil :: join greater p q (smash greater c p₀)
  | p₀ :: p, q₀ :: q, c => c :: join greater p q (smash greater p₀ q₀)

/-- Literal continuation recursion down the right/sibling spine. -/
def unzip : BinaryTree K → (Queue K → Queue K) → Queue K
  | .nil, cont => cont []
  | .node x a b, cont => unzip b (fun q => .node x a .nil :: cont q)

def heapDeleteMax : BinaryTree K → Queue K
  | .node _ a .nil => unzip a id
  | _ => []

/-- Scan root keys, replacing the candidate only on strict improvement. -/
def findMaxAux (greater : K → K → Bool) (current : K) : Queue K → K
  | [] => current
  | .nil :: q => findMaxAux greater current q
  | .node x _ _ :: q => findMaxAux greater (if greater x current then x else current) q

def findMax (greater : K → K → Bool) : Queue K → Option K
  | [] => none
  | .nil :: q => findMax greater q
  | .node x _ _ :: q => some (findMaxAux greater x q)

/-- Stop at the first proper root not strictly smaller than the threshold.
The bogus branch remains observable on malformed raw forests. -/
def deleteMaxAux (greater : K → K → Bool) (m : K) : Queue K → Queue K × Queue K
  | .nil :: p =>
      let result := deleteMaxAux greater m p
      (.nil :: result.1, result.2)
  | .node x a .nil :: p =>
      if greater m x then
        let result := deleteMaxAux greater m p
        (.node x a .nil :: result.1, result.2)
      else (.nil :: p, heapDeleteMax (.node x a .nil))
  | _ => ([], [])

def deleteMax (greater : K → K → Bool) (q : Queue K) : Option (K × Queue K) :=
  match findMax greater q with
  | none => none
  | some m =>
      let result := deleteMaxAux greater m q
      some (m, join greater result.1 result.2 .nil)

def merge (greater : K → K → Bool) (p q : Queue K) : Queue K :=
  join greater p q .nil

@[simp] theorem empty_eq : (empty : Queue K) = [] := rfl

@[simp] theorem natGreater_eq (x y : Nat) : natGreater x y = true ↔ ¬ x ≤ y := by
  simp [natGreater, Nat.not_le]

theorem smash_nodes (greater : K → K → Bool) (x y : K) (a b : BinaryTree K) :
    smash greater (.node x a .nil) (.node y b .nil) =
      if greater x y then .node x (.node y b a) .nil
      else .node y (.node x a b) .nil := rfl

@[simp] theorem smash_nil_left (greater : K → K → Bool) (t : BinaryTree K) :
    smash greater .nil t = .nil := by cases t <;> rfl

@[simp] theorem smash_nil_right (greater : K → K → Bool) (t : BinaryTree K) :
    smash greater t .nil = .nil := by
  cases t with
  | nil => rfl
  | node _ _ r => cases r <;> rfl

theorem smash_bad_left (greater : K → K → Bool) (x y : K)
    (a b c t : BinaryTree K) :
    smash greater (.node x a (.node y b c)) t = .nil := by cases t <;> rfl

theorem smash_bad_right (greater : K → K → Bool) (x y : K)
    (a b c t : BinaryTree K) :
    smash greater t (.node x a (.node y b c)) = .nil := by
  cases t with
  | nil => rfl
  | node _ _ r => cases r <;> rfl

@[simp] theorem carry_nil_nil (greater : K → K → Bool) :
    carry greater ([] : Queue K) .nil = [] := rfl

theorem carry_nil_node (greater : K → K → Bool) (x : K) (a b : BinaryTree K) :
    carry greater [] (.node x a b) = [.node x a b] := rfl

theorem carry_hole (greater : K → K → Bool) (q : Queue K) (t : BinaryTree K) :
    carry greater (.nil :: q) t = t :: q := by cases t <;> rfl

@[simp] theorem carry_leaf (greater : K → K → Bool) (q : Queue K) :
    carry greater q .nil = q := by cases q with
  | nil => rfl
  | cons t q => cases t <;> rfl

theorem carry_occupied (greater : K → K → Bool) (x y : K)
    (a b c d : BinaryTree K) (q : Queue K) :
    carry greater (.node x a b :: q) (.node y c d) =
      .nil :: carry greater q (smash greater (.node y c d) (.node x a b)) := rfl

theorem insert_eq (greater : K → K → Bool) (x : K) (q : Queue K) :
    insert greater x q = carry greater q (.node x .nil .nil) := rfl

@[simp] theorem join_nil_left (greater : K → K → Bool) (q : Queue K) (c : BinaryTree K) :
    join greater [] q c = carry greater q c := rfl

@[simp] theorem join_nil_right (greater : K → K → Bool) (p : Queue K) (c : BinaryTree K) :
    join greater p [] c = carry greater p c := by cases p <;> rfl

theorem join_holes (greater : K → K → Bool) (p q : Queue K) (c : BinaryTree K) :
    join greater (.nil :: p) (.nil :: q) c = c :: join greater p q .nil := by
  cases c <;> rfl

theorem join_hole_node_leaf (greater : K → K → Bool) (p q : Queue K)
    (x : K) (a b : BinaryTree K) :
    join greater (.nil :: p) (.node x a b :: q) .nil =
      .node x a b :: join greater p q .nil := rfl

theorem join_hole_node_node (greater : K → K → Bool) (p q : Queue K)
    (x y : K) (a b c d : BinaryTree K) :
    join greater (.nil :: p) (.node x a b :: q) (.node y c d) =
      .nil :: join greater p q (smash greater (.node y c d) (.node x a b)) := rfl

theorem join_node_hole_leaf (greater : K → K → Bool) (p q : Queue K)
    (x : K) (a b : BinaryTree K) :
    join greater (.node x a b :: p) (.nil :: q) .nil =
      .node x a b :: join greater p q .nil := rfl

theorem join_node_hole_node (greater : K → K → Bool) (p q : Queue K)
    (x y : K) (a b c d : BinaryTree K) :
    join greater (.node x a b :: p) (.nil :: q) (.node y c d) =
      .nil :: join greater p q (smash greater (.node y c d) (.node x a b)) := rfl

theorem join_nodes (greater : K → K → Bool) (p q : Queue K)
    (x y : K) (a b c d carryTree : BinaryTree K) :
    join greater (.node x a b :: p) (.node y c d :: q) carryTree =
      carryTree :: join greater p q (smash greater (.node x a b) (.node y c d)) := by
  cases carryTree <;> rfl

@[simp] theorem unzip_nil (cont : Queue K → Queue K) : unzip .nil cont = cont [] := rfl

theorem unzip_node (x : K) (a b : BinaryTree K) (cont : Queue K → Queue K) :
    unzip (.node x a b) cont = unzip b (fun q => .node x a .nil :: cont q) := rfl

@[simp] theorem heapDeleteMax_nil : heapDeleteMax (.nil : BinaryTree K) = [] := rfl

theorem heapDeleteMax_node (x : K) (a : BinaryTree K) :
    heapDeleteMax (.node x a .nil) = unzip a id := rfl

theorem heapDeleteMax_bad (x y : K) (a b c : BinaryTree K) :
    heapDeleteMax (.node x a (.node y b c)) = [] := rfl

@[simp] theorem findMaxAux_nil (greater : K → K → Bool) (x : K) :
    findMaxAux greater x [] = x := rfl

theorem findMaxAux_hole (greater : K → K → Bool) (x : K) (q : Queue K) :
    findMaxAux greater x (.nil :: q) = findMaxAux greater x q := rfl

theorem findMaxAux_node (greater : K → K → Bool) (x y : K)
    (a b : BinaryTree K) (q : Queue K) :
    findMaxAux greater x (.node y a b :: q) =
      findMaxAux greater (if greater y x then y else x) q := rfl

@[simp] theorem findMax_nil (greater : K → K → Bool) :
    findMax greater ([] : Queue K) = none := rfl

theorem findMax_hole (greater : K → K → Bool) (q : Queue K) :
    findMax greater (.nil :: q) = findMax greater q := rfl

theorem findMax_node (greater : K → K → Bool) (x : K)
    (a b : BinaryTree K) (q : Queue K) :
    findMax greater (.node x a b :: q) = some (findMaxAux greater x q) := rfl

@[simp] theorem deleteMaxAux_nil (greater : K → K → Bool) (m : K) :
    deleteMaxAux greater m [] = ([], []) := rfl

theorem deleteMaxAux_hole (greater : K → K → Bool) (m : K) (p : Queue K) :
    deleteMaxAux greater m (.nil :: p) =
      (.nil :: (deleteMaxAux greater m p).1, (deleteMaxAux greater m p).2) := rfl

theorem deleteMaxAux_node (greater : K → K → Bool) (m x : K)
    (a : BinaryTree K) (p : Queue K) :
    deleteMaxAux greater m (.node x a .nil :: p) =
      if greater m x then
        (.node x a .nil :: (deleteMaxAux greater m p).1, (deleteMaxAux greater m p).2)
      else (.nil :: p, heapDeleteMax (.node x a .nil)) := rfl

theorem deleteMaxAux_bad (greater : K → K → Bool) (m x y : K)
    (a b c : BinaryTree K) (p : Queue K) :
    deleteMaxAux greater m (.node x a (.node y b c) :: p) = ([], []) := rfl

theorem deleteMax_eq (greater : K → K → Bool) (q : Queue K) :
    deleteMax greater q = (findMax greater q).map (fun m =>
      (m, join greater (deleteMaxAux greater m q).1 (deleteMaxAux greater m q).2 .nil)) := by
  cases h : findMax greater q <;> simp [deleteMax, h]

theorem merge_eq (greater : K → K → Bool) (p q : Queue K) :
    merge greater p q = join greater p q .nil := rfl

end Search.BinomialQueue
