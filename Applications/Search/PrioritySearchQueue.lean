import Applications.Search.PriorityInterface

/-!
# The book's keyed priority-queue interface

The book explicitly leaves PSQ implementation details outside its scope (p415).
This is a total executable reference model of that interface, including replacement
on equal priority and the right-fold batch order. Its linear list representation
is not assigned the logarithmic costs of an abstract balanced PSQ. Separate cost
contracts state the implementation assumptions used by the source clients.
-/
set_option autoImplicit false
set_option warningAsError true
namespace Search.PrioritySearchQueue
universe u v w
variable {α : Type u} {κ : Type v} {π : Type w}

section Insert
variable [DecidableEq κ] [LE π] [DecidableLE π]

def insert (key : α → κ) (e : α × π) : List (α × π) → List (α × π)
  | [] => [e]
  | a :: as => if key e.1 = key a.1 then
      if e.2 ≤ a.2 then e :: as else a :: as
    else a :: insert key e as

def add (key : α → κ) (es q : List (α × π)) : List (α × π) :=
  es.foldr (insert key) q

def Unique (key : α → κ) (q : List (α × π)) : Prop :=
  (q.map (fun e => key e.1)).Nodup

theorem insert_origin (key : α → κ) (e a : α × π) (q : List (α × π))
    (h : a ∈ insert key e q) : a = e ∨ a ∈ q := by
  induction q with
  | nil => simpa [insert] using h
  | cons b bs ih =>
    simp only [insert] at h
    split at h
    · split at h <;> simp only [List.mem_cons] at h
      · rcases h with rfl | h
        · exact Or.inl rfl
        · exact Or.inr (by simp [h])
      · exact Or.inr (List.mem_cons.mpr h)
    · simp only [List.mem_cons] at h
      rcases h with rfl | h
      · exact Or.inr (by simp)
      · rcases ih h with rfl | h
        · exact Or.inl rfl
        · exact Or.inr (by simp [h])

theorem insert_length (key : α → κ) (e : α × π) (q : List (α × π)) :
    (insert key e q).length ≤ q.length + 1 := by
  induction q with
  | nil => simp [insert]
  | cons b bs ih =>
    simp only [insert]
    split
    · split <;> simp
    · simp only [List.length_cons]; omega

theorem insert_unique (key : α → κ) (e : α × π) (q : List (α × π))
    (h : Unique key q) : Unique key (insert key e q) := by
  induction q with
  | nil => simp [Unique, insert]
  | cons a as ih =>
    have hh : key a.1 ∉ as.map (fun z => key z.1) ∧ Unique key as := by
      simpa [Unique] using h
    simp only [insert]
    split
    next he =>
      split
      · simpa [Unique, he] using h
      · exact h
    next he =>
      simp only [Unique, List.map_cons, List.nodup_cons]
      refine ⟨?_, ih hh.2⟩
      intro hm
      obtain ⟨z,hz,hze⟩ := List.mem_map.mp hm
      rcases insert_origin key e z as hz with rfl | hz
      · exact he hze
      · exact hh.1 (List.mem_map.mpr ⟨z,hz,hze⟩)

theorem add_origin (key : α → κ) (es q : List (α × π)) (e : α × π)
    (h : e ∈ add key es q) : e ∈ es ++ q := by
  induction es with
  | nil => simpa [add] using h
  | cons a as ih =>
    rcases insert_origin key a e (add key as q) h with rfl | h
    · simp
    · simpa using List.mem_cons_of_mem a (ih h)

theorem add_length (key : α → κ) (es q : List (α × π)) :
    (add key es q).length ≤ es.length + q.length := by
  induction es with
  | nil => simp [add]
  | cons a as ih =>
    have h := insert_length key a (add key as q)
    change (insert key a (add key as q)).length ≤ _
    simp only [List.length_cons]; omega

theorem add_unique (key : α → κ) (es q : List (α × π))
    (h : Unique key q) : Unique key (add key es q) := by
  induction es with
  | nil => exact h
  | cons e es ih => exact insert_unique key e _ ih

theorem equal_priority_replaces (key : α → κ) (e a : α × π)
    (as : List (α × π)) (hk : key e.1 = key a.1) (hp : e.2 ≤ a.2) :
    insert key e (a :: as) = e :: as := by simp [insert,hk,hp]

theorem larger_priority_retains (key : α → κ) (e a : α × π)
    (as : List (α × π)) (hk : key e.1 = key a.1) (hp : ¬e.2 ≤ a.2) :
    insert key e (a :: as) = a :: as := by simp [insert,hk,hp]

variable [Std.IsLinearPreorder π]

theorem insert_covers (key : α → κ) (e a : α × π) (q : List (α × π))
    (h : a = e ∨ a ∈ q) :
    ∃ b ∈ insert key e q, key b.1 = key a.1 ∧ b.2 ≤ a.2 := by
  induction q with
  | nil =>
    have he : a = e := by simpa using h
    subst a
    exact ⟨e,by simp [insert],rfl,Std.le_refl _⟩
  | cons b bs ih =>
    by_cases hk : key e.1 = key b.1
    · by_cases hp : e.2 ≤ b.2
      · rcases h with rfl | h
        · exact ⟨a,by simp [insert,hk,hp],rfl,Std.le_refl _⟩
        · rcases List.mem_cons.mp h with rfl | h
          · exact ⟨e,by simp [insert,hk,hp],hk,hp⟩
          · exact ⟨a,by simp [insert,hk,hp,h],rfl,Std.le_refl _⟩
      · rcases h with rfl | h
        · exact ⟨b,by simp [insert,hk,hp],hk.symm,Std.le_total.resolve_left hp⟩
        · exact ⟨a,by simpa [insert,hk,hp] using h,rfl,Std.le_refl _⟩
    · rcases h with rfl | h
      · obtain ⟨a,ha,hka,hpa⟩ := ih (Or.inl rfl)
        exact ⟨a,by simp [insert,hk,ha],hka,hpa⟩
      · rcases List.mem_cons.mp h with rfl | h
        · exact ⟨a,by simp [insert,hk],rfl,Std.le_refl _⟩
        · obtain ⟨c,hc,hkc,hpc⟩ := ih (Or.inr h)
          exact ⟨c,by simp [insert,hk,hc],hkc,hpc⟩

theorem add_covers (key : α → κ) (es q : List (α × π)) (e : α × π)
    (h : e ∈ es ++ q) :
    ∃ b ∈ add key es q, key b.1 = key e.1 ∧ b.2 ≤ e.2 := by
  induction es with
  | nil => exact ⟨e,by simpa [add] using h,rfl,Std.le_refl _⟩
  | cons a as ih =>
    rcases List.mem_cons.mp h with rfl | h
    · exact insert_covers key e e (add key as q) (Or.inl rfl)
    · obtain ⟨b,hb,hkb,hpb⟩ := ih h
      obtain ⟨c,hc,hkc,hpc⟩ := insert_covers key a b (add key as q) (Or.inr hb)
      exact ⟨c,hc,hkc.trans hkb,Std.le_trans hpc hpb⟩
end Insert

section Delete
variable [LE π] [DecidableLE π]

/-- Leftmost minimum with exactly one occurrence removed. -/
def takeMin (e : α × π) : List (α × π) → (α × π) × List (α × π)
  | [] => (e,[])
  | a :: as =>
      let r := takeMin a as
      if e.2 ≤ r.1.2 then (e,a :: as) else (r.1,e :: r.2)

theorem takeMin_perm (e : α × π) (q : List (α × π)) :
    (e :: q).Perm ((takeMin e q).1 :: (takeMin e q).2) := by
  induction q generalizing e with
  | nil => exact .refl _
  | cons a as ih =>
    simp only [takeMin]
    split
    · exact .refl _
    · exact (List.Perm.cons e (ih a)).trans (List.Perm.swap _ _ _)

variable [Std.IsLinearPreorder π]

theorem takeMin_le (e : α × π) (q : List (α × π)) :
    ∀ a ∈ e :: q, (takeMin e q).1.2 ≤ a.2 := by
  induction q generalizing e with
  | nil => simp [takeMin]
  | cons b bs ih =>
    intro a ha
    by_cases h : e.2 ≤ (takeMin b bs).1.2
    · simp only [takeMin,ite_eq_left h]
      rcases List.mem_cons.mp ha with rfl | ha
      · exact Std.le_refl _
      · exact Std.le_trans h (ih b a ha)
    · simp only [takeMin,ite_eq_right h]
      rcases List.mem_cons.mp ha with rfl | ha
      · exact Std.le_total.resolve_left h
      · exact ih b a ha

end Delete

section Model
variable [DecidableEq κ] [LE κ] [DecidableLE κ]
  [LE π] [DecidableLE π] [Std.IsLinearPreorder π]

/-- Key order makes equal-priority removal choose the least key. Sorting is part
of this reference observer, not a claimed logarithmic implementation. -/
def putOrdered (key : α → κ) (e : α × π) : List (α × π) → List (α × π)
  | [] => [e]
  | a :: as => if key e.1 ≤ key a.1 then e :: a :: as else a :: putOrdered key e as

def ordered (key : α → κ) : List (α × π) → List (α × π)
  | [] => []
  | e :: es => putOrdered key e (ordered key es)

def remove (key : α → κ) (q : List (α × π)) :
    Option ((α × π) × List (α × π)) :=
  match ordered key q with
  | [] => none
  | e :: es => some (takeMin e es)

omit [DecidableEq κ] [LE π] [DecidableLE π] [Std.IsLinearPreorder π] in
theorem putOrdered_perm (key : α → κ) (e : α × π) (q : List (α × π)) :
    (putOrdered key e q).Perm (e :: q) := by
  induction q with
  | nil => exact .refl _
  | cons a as ih =>
    simp only [putOrdered]
    split
    · exact .refl _
    · exact (List.Perm.cons a ih).trans (List.Perm.swap _ _ _)

omit [DecidableEq κ] [LE π] [DecidableLE π] [Std.IsLinearPreorder π] in
theorem ordered_perm (key : α → κ) (q : List (α × π)) :
    (ordered key q).Perm q := by
  induction q with
  | nil => exact .refl _
  | cons e es ih =>
    exact (putOrdered_perm key e _).trans (List.Perm.cons e ih)

omit [DecidableEq κ] [Std.IsLinearPreorder π] in
theorem remove_none (key : α → κ) (q : List (α × π)) :
    remove key q = none ↔ q = [] := by
  have h := (ordered_perm key q).length_eq
  simp only [remove]
  split
  next he =>
    have hz : q = [] := by
      have hh : q.length = 0 := by simpa [he] using h.symm
      cases q <;> simp_all
    simp [hz]
  next e es he =>
    have hn : q ≠ [] := by
      intro hq
      have hz : ordered key q = [] := by simp [hq,ordered]
      rw [hz] at he
      contradiction
    simp [hn]

omit [DecidableEq κ] in
theorem remove_spec (key : α → κ) (q : List (α × π)) (e : α × π)
    (r : List (α × π)) (hq : Unique key q) (hd : remove key q = some (e,r)) :
    Unique key r ∧ q.Perm (e :: r) ∧ ∀ a ∈ q, e.2 ≤ a.2 := by
  unfold remove at hd
  split at hd
  next he => simp at hd
  next a as he =>
    have hp := (ordered_perm key q).symm
    rw [he] at hp
    have ht := takeMin_perm a as
    have hz : takeMin a as = (e,r) := Option.some.inj hd
    rw [hz] at ht
    have perm := hp.trans ht
    refine ⟨?_,perm,?_⟩
    · have hn := (perm.map (fun z : α × π => key z.1)).nodup_iff.mp hq
      exact (List.nodup_cons.mp hn).2
    · intro b hb
      have hl := takeMin_le a as b (hp.mem_iff.mp hb)
      simpa only [hz] using hl

def keyed (key : α → κ) : PriorityInterface.Queue α κ π key where
  Carrier := List (α × π)
  entries := id
  empty := []
  add := add key
  remove := remove key
  Valid := Unique key
  lawful := {
    empty_entries := rfl
    empty_valid := List.nodup_nil
    add_valid := add_unique key
    add_origin := add_origin key
    add_covers := add_covers key
    add_length := add_length key
    remove_none := remove_none key
    remove_spec := remove_spec key
  }

omit [LE κ] [DecidableLE κ] [Std.IsLinearPreorder π] in
theorem batch_order (key : α → κ) (es q : List (α × π)) :
    add key es q = es.foldr (insert key) q := rfl

theorem exact_same_key_tie :
    add (fun x : Nat × Nat => x.1) [((3,10),7),((3,20),7)] [] = [((3,10),7)] := by decide

theorem exact_priority_then_key_tie :
    remove id ([(4,8),(3,5),(1,5),(2,7)] : List (Nat × Nat)) =
      some ((1,5),[(2,7),(3,5),(4,8)]) := by
  decide +kernel

end Model
end Search.PrioritySearchQueue
