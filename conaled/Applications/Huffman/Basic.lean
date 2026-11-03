import Applications.Bracketing.Basic
import Mathlib.Data.List.Perm.Basic

/-!
# Huffman trees: independent weighted-path specification and cached constructors

The source `Elem = (Char, Weight)` is the specialization `α = Char × Nat`,
`w = Prod.snd`. Keeping the weight function explicit also permits whole existing
subtrees to serve as atoms in the greedy exchange proof. Feasibility fixes the
multiset of leaf occurrences, not their order or merely their total weight.
-/
set_option autoImplicit false
set_option warningAsError true

namespace Huffman
open Bracketing
open Tree
universe u v
variable {α : Type u} {β : Type v}

def height : Tree α → Nat
  | .leaf _ => 0
  | .fork l r => 1 + max (height l) (height r)

theorem height_lt_size (t : Tree α) : height t < size t := by
  induction t with
  | leaf => simp [height, size]
  | fork l r ihl ihr =>
    have hl := size_pos l
    have hr := size_pos r
    simp only [height, size]
    omega

theorem fringe_singleton_iff (t : Tree α) (x : α) :
    fringeSpec t = [x] ↔ t = Tree.leaf x := by
  constructor
  · intro h
    cases t with
    | leaf y =>
      have hy : y = x := by simpa only [fringeSpec, List.cons.injEq, and_true] using h
      exact congrArg Tree.leaf hy
    | fork l r =>
      have hl := size_pos l
      have hr := size_pos r
      have hn := congrArg List.length h
      simp only [fringeSpec, List.length_append, fringeSpec_length, List.length_cons,
        List.length_nil] at hn
      omega
  · rintro rfl
    rfl

def weight (w : α → Nat) : Tree α → Nat
  | leaf a => w a
  | fork l r => weight w l + weight w r

def cost (w : α → Nat) : Tree α → Nat
  | leaf _ => 0
  | fork l r => cost w l + cost w r + weight w l + weight w r

def depthsFrom (d : Nat) : Tree α → List Nat
  | leaf _ => [d]
  | fork l r => depthsFrom (d+1) l ++ depthsFrom (d+1) r

def depths (t : Tree α) : List Nat := depthsFrom 0 t

/-- The independent printed sum of leaf weight times depth. -/
def pathCost (w : α → Nat) (d : Nat) (t : Tree α) : Nat :=
  ((fringeSpec t).zip (depthsFrom d t)).map (fun p => w p.1*p.2) |>.sum

def Feasible (xs : List α) (t : Tree α) : Prop := (fringeSpec t).Perm xs

def Optimal (w : α → Nat) (xs : List α) (t : Tree α) : Prop :=
  Feasible xs t ∧ ∀ u, Feasible xs u → pathCost w 0 t ≤ pathCost w 0 u

theorem depthsFrom_length (d : Nat) (t : Tree α) :
    (depthsFrom d t).length = (fringeSpec t).length := by
  induction t generalizing d with
  | leaf => rfl
  | fork l r ihl ihr => simp [depthsFrom,fringeSpec,ihl,ihr]

theorem weight_fringe (w : α → Nat) (t : Tree α) :
    weight w t = ((fringeSpec t).map w).sum := by
  induction t with
  | leaf => simp [weight,fringeSpec]
  | fork l r ihl ihr => simp [weight,fringeSpec,ihl,ihr]

theorem pathCost_eq (w : α → Nat) (d : Nat) (t : Tree α) :
    pathCost w d t = cost w t + d*weight w t := by
  induction t generalizing d with
  | leaf a => simp [pathCost,cost,fringeSpec,depthsFrom,weight,Nat.mul_comm]
  | fork l r ihl ihr =>
      simp only [pathCost,fringeSpec,depthsFrom,
        List.zip_append (depthsFrom_length (d+1) l).symm,List.map_append,List.sum_append]
      rw [← pathCost,← pathCost,ihl,ihr]
      simp only [cost,weight,Nat.mul_add,Nat.add_mul,Nat.one_mul]
      omega

theorem cost_eq_source (w : α → Nat) (t : Tree α) :
    cost w t = (((fringeSpec t).zip (depths t)).map (fun p => w p.1*p.2)).sum := by
  have h := pathCost_eq w 0 t
  simpa [pathCost,depths] using h.symm

theorem optimal_iff (w : α → Nat) (xs : List α) (t : Tree α) :
    Optimal w xs t ↔ Feasible xs t ∧ ∀ u, Feasible xs u → cost w t ≤ cost w u := by
  simp only [Optimal,pathCost_eq,Nat.zero_mul,Nat.add_zero]

theorem feasible_weight (w : α → Nat) {xs : List α} {t : Tree α}
    (h : Feasible xs t) : weight w t = (xs.map w).sum := by
  rw [weight_fringe]
  exact (h.map w).sum_nat

theorem feasible_size {xs : List α} {t : Tree α} (h : Feasible xs t) :
    size t = xs.length := by
  rw [← fringeSpec_length]
  exact h.length_eq

theorem feasible_nonempty {xs : List α} {t : Tree α} (h : Feasible xs t) :
    xs ≠ [] := by
  have hs := size_pos t
  have he := feasible_size h
  intro hx
  simp [hx] at he
  omega

abbrev Pair (α : Type u) := Tree α × Nat

def ValidPair (w : α → Nat) (p : Pair α) : Prop := p.2 = weight w p.1

def cachedLeaf (w : α → Nat) (a : α) : Pair α := (Tree.leaf a,w a)

def node (p q : Pair α) : Pair α := (Tree.fork p.1 q.1,p.2+q.2)

theorem leaf_valid (w : α → Nat) (a : α) : ValidPair w (cachedLeaf w a) := rfl

theorem node_valid (w : α → Nat) (p q : Pair α)
    (hp : ValidPair w p) (hq : ValidPair w q) : ValidPair w (node p q) := by
  change p.2+q.2=weight w p.1+weight w q.1
  rw [hp,hq]

def mapTree (f : α → β) : Tree α → Tree β
  | leaf a => Tree.leaf (f a)
  | fork l r => Tree.fork (mapTree f l) (mapTree f r)

theorem fringe_mapTree (f : α → β) (t : Tree α) :
    fringeSpec (mapTree f t) = (fringeSpec t).map f := by
  induction t <;> simp_all [mapTree,fringeSpec]

theorem weight_mapTree (w : β → Nat) (f : α → β) (t : Tree α) :
    weight w (mapTree f t) = weight (w ∘ f) t := by
  induction t <;> simp_all [mapTree,weight]

theorem cost_mapTree (w : β → Nat) (f : α → β) (t : Tree α) :
    cost w (mapTree f t) = cost (w ∘ f) t := by
  induction t <;> simp_all [mapTree,cost,weight_mapTree]

def flatten : Tree (Tree α) → Tree α
  | leaf t => t
  | fork l r => Tree.fork (flatten l) (flatten r)

theorem fringe_flatten (t : Tree (Tree α)) :
    fringeSpec (flatten t) = (fringeSpec t).flatMap fringeSpec := by
  induction t <;> simp_all [flatten,fringeSpec]

theorem weight_flatten (w : α → Nat) (t : Tree (Tree α)) :
    weight w (flatten t) = weight (weight w) t := by
  induction t <;> simp_all [flatten,weight]

theorem cost_flatten (w : α → Nat) (t : Tree (Tree α)) :
    cost w (flatten t) = cost (weight w) t + ((fringeSpec t).map (cost w)).sum := by
  induction t with
  | leaf t => simp [flatten,cost,fringeSpec]
  | fork l r ihl ihr =>
      simp only [flatten,cost,ihl,ihr,weight_flatten,fringeSpec,List.map_append,List.sum_append]
      omega

/-- All full binary ways to combine a multiset of existing trees. -/
def ForestFeasible (ts : List (Tree α)) (t : Tree α) : Prop :=
  ∃ shape : Tree (Tree α), (fringeSpec shape).Perm ts ∧ flatten shape=t

def ForestOptimal (w : α → Nat) (ts : List (Tree α)) (t : Tree α) : Prop :=
  ForestFeasible ts t ∧ ∀ u, ForestFeasible ts u → cost w t≤cost w u

theorem forestFeasible_fringe {ts : List (Tree α)} {t : Tree α}
    (h : ForestFeasible ts t) : (fringeSpec t).Perm (ts.flatMap fringeSpec) := by
  obtain ⟨shape,hp,rfl⟩ := h
  rw [fringe_flatten]
  exact hp.flatMap_right fringeSpec

theorem forestOptimal_of_atomOptimal (w : α → Nat) (ts : List (Tree α))
    (shape : Tree (Tree α)) (h : Optimal (weight w) ts shape) :
    ForestOptimal w ts (flatten shape) := by
  obtain ⟨hf,hm⟩ := (optimal_iff _ _ _).mp h
  refine ⟨⟨shape,hf,rfl⟩,?_⟩
  rintro t ⟨other,ho,rfl⟩
  have hc := hm other ho
  have hs : ((fringeSpec shape).map (cost w)).sum = ((fringeSpec other).map (cost w)).sum :=
    ((hf.trans ho.symm).map (cost w)).sum_nat
  rw [cost_flatten,cost_flatten,hs]
  omega

end Huffman
