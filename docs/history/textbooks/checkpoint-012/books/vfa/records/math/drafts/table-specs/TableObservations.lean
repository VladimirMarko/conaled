import Mathlib.Logic.Function.Basic
import Mathlib.Data.List.Basic

/-!
Cross-cutting preparation only. This file is outside the integrated library.
It investigates the common observation seam of VFA Maps/Table/ETableAbs/Trie;
it does not implement or claim completion of those chapters.
-/
set_option autoImplicit false
set_option warningAsError true

namespace TablePreparation
universe u v w z
variable {K : Type u} {V : Type v} {T : Type w} {U : Type z}

/-- The three ordinary Table operations. No invariant or equality is an operation. -/
structure Ops (K : Type u) (V : Type v) (T : Type w) where
  empty : T
  get : K → T → V
  set : K → V → T → T

/-- Laws are separate; representation validity is a justified input condition. -/
structure Laws (ops : Ops K V T) (d : V) (Valid : T → Prop) : Prop where
  empty_valid : Valid ops.empty
  set_valid : ∀ k v t, Valid t → Valid (ops.set k v t)
  get_empty : ∀ k, ops.get k ops.empty = d
  get_set_same : ∀ k v t, Valid t → ops.get k (ops.set k v t) = v
  get_set_other : ∀ k q v t, k ≠ q → Valid t →
    ops.get q (ops.set k v t) = ops.get q t

/-- Equality only of total lookup observations, not of raw representations. -/
def ObservedEq (a : Ops K V T) (b : Ops K V U) (t : T) (u : U) : Prop :=
  ∀ q, a.get q t = b.get q u

def observe (ops : Ops K V T) (t : T) : K → V := fun q => ops.get q t

theorem Laws.observe_set [DecidableEq K] {ops : Ops K V T} {d : V}
    {Valid : T → Prop} (h : Laws ops d Valid) (k : K) (v : V) (t : T)
    (ht : Valid t) :
    observe ops (ops.set k v t) = Function.update (observe ops t) k v := by
  funext q
  by_cases hq : q = k
  · subst q
    simpa only [Function.update_self, observe] using h.get_set_same k v t ht
  · simpa only [Function.update_of_ne hq, observe] using
      h.get_set_other k q v t (Ne.symm hq) ht

theorem Laws.empty_observed {a : Ops K V T} {b : Ops K V U} {d : V}
    {ValidA : T → Prop} {ValidB : U → Prop}
    (ha : Laws a d ValidA) (hb : Laws b d ValidB) :
    ObservedEq a b a.empty b.empty := fun q => (ha.get_empty q).trans (hb.get_empty q).symm

theorem Laws.set_observed {a : Ops K V T} {b : Ops K V U} {d : V}
    {ValidA : T → Prop} {ValidB : U → Prop}
    (ha : Laws a d ValidA) (hb : Laws b d ValidB) (k : K) (v : V)
    {t : T} {u : U} (ht : ValidA t) (hu : ValidB u) (rel : ObservedEq a b t u) :
    ObservedEq a b (a.set k v t) (b.set k v u) := by
  classical
  intro q
  by_cases hq : k = q
  · subst q
    exact (ha.get_set_same k v t ht).trans (hb.get_set_same k v u hu).symm
  · exact (ha.get_set_other k q v t hq ht).trans
      ((rel q).trans (hb.get_set_other k q v u hq hu).symm)

/-- A concrete source-style client: write twice in order, then query. -/
def twoWrites (ops : Ops K V T) (k₁ : K) (v₁ : V) (k₂ : K) (v₂ : V) (q : K) : V :=
  ops.get q (ops.set k₂ v₂ (ops.set k₁ v₁ ops.empty))

theorem twoWrites_equivalent {a : Ops K V T} {b : Ops K V U} {d : V}
    {ValidA : T → Prop} {ValidB : U → Prop}
    (ha : Laws a d ValidA) (hb : Laws b d ValidB)
    (k₁ : K) (v₁ : V) (k₂ : K) (v₂ : V) (q : K) :
    twoWrites a k₁ v₁ k₂ v₂ q = twoWrites b k₁ v₁ k₂ v₂ q :=
  ha.set_observed hb k₂ v₂ (ha.set_valid k₁ v₁ _ ha.empty_valid)
    (hb.set_valid k₁ v₁ _ hb.empty_valid)
    (ha.set_observed hb k₁ v₁ ha.empty_valid hb.empty_valid (ha.empty_observed hb)) q

theorem twoWrites_latest {ops : Ops K V T} {d : V} {Valid : T → Prop}
    (h : Laws ops d Valid) (k₁ : K) (v₁ : V) (k₂ : K) (v₂ : V) :
    twoWrites ops k₁ v₁ k₂ v₂ k₂ = v₂ :=
  h.get_set_same k₂ v₂ _ (h.set_valid k₁ v₁ _ h.empty_valid)

theorem twoWrites_first {ops : Ops K V T} {d : V} {Valid : T → Prop}
    (h : Laws ops d Valid) (k₁ : K) (v₁ : V) (k₂ : K) (v₂ : V)
    (hne : k₂ ≠ k₁) : twoWrites ops k₁ v₁ k₂ v₂ k₁ = v₁ :=
  (h.get_set_other k₂ k₁ v₂ _ hne (h.set_valid k₁ v₁ _ h.empty_valid)).trans
    (h.get_set_same k₁ v₁ _ h.empty_valid)

theorem twoWrites_other {ops : Ops K V T} {d : V} {Valid : T → Prop}
    (h : Laws ops d Valid) (k₁ : K) (v₁ : V) (k₂ : K) (v₂ : V) (q : K)
    (h₁ : k₁ ≠ q) (h₂ : k₂ ≠ q) : twoWrites ops k₁ v₁ k₂ v₂ q = d :=
  (h.get_set_other k₂ q v₂ _ h₂ (h.set_valid k₁ v₁ _ h.empty_valid)).trans
    ((h.get_set_other k₁ q v₁ _ h₁ h.empty_valid).trans (h.get_empty q))

def functionOps [DecidableEq K] (d : V) : Ops K V (K → V) where
  empty := fun _ => d
  get q t := t q
  set k v t := Function.update t k v

theorem functionLaws [DecidableEq K] (d : V) :
    Laws (functionOps (K := K) d) d (fun _ => True) where
  empty_valid := trivial
  set_valid _ _ _ _ := trivial
  get_empty _ := rfl
  get_set_same _ _ _ _ := by simp [functionOps]
  get_set_other _ _ _ _ h _ := by simp [functionOps, Ne.symm h]

/-- First matching binding wins; duplicates are allowed and shadowed. -/
def lookup? [DecidableEq K] (q : K) : List (K × V) → Option V
  | [] => none
  | (k, v) :: rest => if q = k then some v else lookup? q rest

def associationOps [DecidableEq K] (d : V) : Ops K V (List (K × V)) where
  empty := []
  get q t := (lookup? q t).getD d
  set k v t := (k, v) :: t

theorem associationLaws [DecidableEq K] (d : V) :
    Laws (associationOps (K := K) d) d (fun _ => True) where
  empty_valid := trivial
  set_valid _ _ _ _ := trivial
  get_empty _ := rfl
  get_set_same _ _ _ _ := by simp [associationOps, lookup?]
  get_set_other _ _ _ _ h _ := by simp [associationOps, lookup?, Ne.symm h]

/-- Partial observations retain explicit binding, including binding to the default. -/
def withDefault (d : V) (m : K → Option V) : K → V := fun q => (m q).getD d

def hasBinding (m : K → Option V) (q : K) : Bool := (m q).isSome

theorem withDefault_update [DecidableEq K] (d : V) (m : K → Option V) (k : K) (v : V) :
    withDefault d (Function.update m k (some v)) = Function.update (withDefault d m) k v := by
  funext q
  by_cases h : q = k <;> simp [withDefault, h]

theorem lookup_cons_update [DecidableEq K] (k : K) (v : V) (xs : List (K × V)) :
    (fun q => lookup? q ((k, v) :: xs)) =
      Function.update (fun q => lookup? q xs) k (some v) := by
  funext q
  simp [lookup?, Function.update_apply]

/-- A bound bit and default-valued lookup together recover an actual binding. -/
theorem binding_iff (d : V) (m : K → Option V) (q : K) (v : V) :
    m q = some v ↔ hasBinding m q = true ∧ withDefault d m q = v := by
  cases h : m q <;> simp [hasBinding, withDefault, h]

/-- Forgetting absence cannot reflect equality, even for one written binding. -/
theorem forget_default_not_injective [DecidableEq K] (k : K) (d : V) :
    ∃ m n : K → Option V, m ≠ n ∧ withDefault d m = withDefault d n := by
  let m : K → Option V := fun _ => none
  let n := Function.update m k (some d)
  refine ⟨m, n, ?_, ?_⟩
  · intro eq
    have h := congrFun eq k
    simp [m, n] at h
  · change withDefault d m = withDefault d (Function.update m k (some d))
    rw [withDefault_update]
    exact (Function.update_eq_self k (withDefault d m)).symm

section CheckedCases

/-- The concrete Maps client assigns false at 1, true at 3, default false. -/
example :
    twoWrites (associationOps false) (1 : Nat) false 3 true 0 = false ∧
    twoWrites (associationOps false) (1 : Nat) false 3 true 1 = false ∧
    twoWrites (associationOps false) (1 : Nat) false 3 true 2 = false ∧
    twoWrites (associationOps false) (1 : Nat) false 3 true 3 = true :=
  ⟨twoWrites_other (associationLaws false) 1 false 3 true 0 (by decide) (by decide),
   twoWrites_first (associationLaws false) 1 false 3 true (by decide),
   twoWrites_other (associationLaws false) 1 false 3 true 2 (by decide) (by decide),
   twoWrites_latest (associationLaws false) 1 false 3 true⟩

/-- The independently expected later write wins at a repeated key. -/
example : twoWrites (associationOps (K := Nat) "") 0 "A" 0 "B" 0 = "B" :=
  twoWrites_latest (associationLaws "") 0 "A" 0 "B"

/-- Same client proof, function realization. -/
example : twoWrites (functionOps (K := Nat) "") 0 "A" 0 "B" 0 = "B" :=
  twoWrites_latest (functionLaws "") 0 "A" 0 "B"

/-- Absence remains the supplied default, through the public theorem. -/
example : twoWrites (associationOps (K := Nat) "") 0 "A" 2 "B" 1 = "" :=
  twoWrites_other (associationLaws "") 0 "A" 2 "B" 1 (by decide) (by decide)

/-- Keys need equality, not an order; arbitrary query and payloads are retained. -/
example (v₁ v₂ : V) (q : Bool) (d : V) :
    twoWrites (associationOps d) false v₁ true v₂ q =
      twoWrites (functionOps d) false v₁ true v₂ q :=
  twoWrites_equivalent (associationLaws d) (functionLaws d) false v₁ true v₂ q

/-- An explicitly stored false and absence have equal total observations. -/
example :
    withDefault false (fun q => lookup? q ([(3, false)] : List (Nat × Bool))) =
      withDefault false (fun q => lookup? q ([] : List (Nat × Bool))) ∧
    hasBinding (fun q => lookup? q ([(3, false)] : List (Nat × Bool))) 3 = true ∧
    hasBinding (fun q => lookup? q ([] : List (Nat × Bool))) 3 = false := by
  refine ⟨?_, by decide, by decide⟩
  rw [lookup_cons_update, withDefault_update]
  exact Function.update_eq_self 3 _

/-- A shadowed raw list member is not evidence of the observed binding. -/
example : (0, "old") ∈ ([(0, "new"), (0, "old")] : List (Nat × String)) ∧
    lookup? 0 ([(0, "new"), (0, "old")] : List (Nat × String)) ≠ some "old" := by
  decide

end CheckedCases
end TablePreparation
