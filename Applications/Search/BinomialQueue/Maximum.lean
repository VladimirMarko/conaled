import Applications.Search.BinomialQueue.Ranked
import Mathlib.Order.Defs.Unbundled
import Mathlib.Order.Basic
import Mathlib.Data.List.Perm.Basic

/-!
The source continuation, literal first-maximum scan and deletion correctness.
The raw observations retain all empty slots and malformed fallback branches.
Order arguments use a total preorder and the executable strict comparison law;
comparator-equivalent keys are never identified as equal.
-/
set_option autoImplicit false
set_option warningAsError true

namespace Search.BinomialQueue

universe u
variable {K : Type u}

/-- The source continuation is applied to the empty list, after the detached
right-spine roots. It is not applied to the already reconstructed forest. -/
theorem unzip_eq_append (t : BinaryTree K) (cont : Queue K → Queue K) :
    unzip t cont = unzip t id ++ cont [] := by
  induction t generalizing cont with
  | nil => rfl
  | node x a b _ ih =>
      calc
        unzip (.node x a b) cont = unzip b id ++ .node x a .nil :: cont [] :=
          ih (fun q => .node x a .nil :: cont q)
        _ = (unzip b id ++ [.node x a .nil]) ++ cont [] := by
          simp only [List.append_assoc, List.cons_append, List.nil_append]
        _ = unzip (.node x a b) id ++ cont [] := by
          congr 1
          exact (ih (fun q => .node x a .nil :: q)).symm

/-- Right siblings appear first, so the physical descending-rank spine becomes
an ascending-rank forest without changing any left subtree. -/
theorem unzip_node_id (x : K) (a b : BinaryTree K) :
    unzip (.node x a b) id = unzip b id ++ [.node x a .nil] :=
  unzip_eq_append b (fun q => .node x a .nil :: q)

/-- Raw semantic emptiness permits any number of empty slots. -/
theorem findMax_eq_none_iff (greater : K → K → Bool) (q : Queue K) :
    findMax greater q = none ↔ ∀ t ∈ q, t = .nil := by
  induction q with
  | nil => simp [findMax]
  | cons t q ih =>
      cases t with
      | nil => simpa only [findMax, List.mem_cons, forall_eq_or_imp, true_and] using ih
      | node x a b => simp [findMax]

theorem deleteMax_eq_none_iff (greater : K → K → Bool) (q : Queue K) :
    deleteMax greater q = none ↔ ∀ t ∈ q, t = .nil := by
  rw [deleteMax_eq, Option.map_eq_none_iff, findMax_eq_none_iff]

/-- The scan always returns either its literal seed or a literal occupied root,
even when the comparator is unlawful or a tree is malformed. -/
theorem findMaxAux_eq_or_mem (greater : K → K → Bool) (current : K) (q : Queue K) :
    findMaxAux greater current q = current ∨
      ∃ a b, .node (findMaxAux greater current q) a b ∈ q := by
  induction q generalizing current with
  | nil => exact Or.inl rfl
  | cons t q ih =>
      cases t with
      | nil =>
          rcases ih current with h | ⟨a, b, h⟩
          · exact Or.inl h
          · exact Or.inr ⟨a, b, List.mem_cons_of_mem _ h⟩
      | node x a b =>
          by_cases hg : greater x current = true
          · simp only [findMaxAux_node, ite_eq_left hg]
            rcases ih x with h | ⟨c, d, h⟩
            · exact Or.inr ⟨a, b, by rw [h]; exact List.mem_cons_self⟩
            · exact Or.inr ⟨c, d, List.mem_cons_of_mem _ h⟩
          · simp only [findMaxAux_node, ite_eq_right hg]
            rcases ih current with h | ⟨c, d, h⟩
            · exact Or.inl h
            · exact Or.inr ⟨c, d, List.mem_cons_of_mem _ h⟩

theorem findMax_some_mem (greater : K → K → Bool) (q : Queue K) (m : K)
    (hm : findMax greater q = some m) : ∃ a b, .node m a b ∈ q := by
  induction q with
  | nil => simp [findMax] at hm
  | cons t q ih =>
      cases t with
      | nil =>
          obtain ⟨a, b, h⟩ := ih hm
          exact ⟨a, b, List.mem_cons_of_mem _ h⟩
      | node x a b =>
          have he : findMaxAux greater x q = m := Option.some.inj hm
          rcases findMaxAux_eq_or_mem greater x q with h | ⟨c, d, h⟩
          · exact ⟨a, b, by rw [← he, h]; exact List.mem_cons_self⟩
          · exact ⟨c, d, List.mem_cons_of_mem _ (by simpa only [he] using h)⟩

section Ordered
variable [Preorder K] [Std.Total (fun x y : K => x ≤ y)]
variable {greater : K → K → Bool}
variable (hgreater : ∀ x y, greater x y = true ↔ ¬ x ≤ y)
include hgreater

/-- Accumulator provenance records a literal root, not merely its order class.
If the seed loses, every earlier root is strictly smaller than the result. -/
theorem findMaxAux_first (current : K) (q : Queue K) (m : K)
    (hm : findMaxAux greater current q = m) :
    (m = current ∧ ∀ x a b, .node x a b ∈ q → x ≤ current) ∨
      ∃ before a b after,
        q = before ++ .node m a b :: after ∧
        greater m current = true ∧
        (∀ x l r, .node x l r ∈ before → greater m x = true) ∧
        (∀ x l r, .node x l r ∈ after → x ≤ m) := by
  classical
  induction q generalizing current m with
  | nil =>
      exact Or.inl ⟨hm.symm, by simp⟩
  | cons t q ih =>
      cases t with
      | nil =>
          rcases ih current m hm with ⟨he, hb⟩ | ⟨before, a, b, after, he, hc, hp, hs⟩
          · refine Or.inl ⟨he, ?_⟩
            intro x a b hx
            exact hb x a b (by simpa using hx)
          · refine Or.inr ⟨.nil :: before, a, b, after, by simp only [List.cons_append, he], hc, ?_, hs⟩
            intro x l r hx
            exact hp x l r (by simpa using hx)
      | node x a b =>
          by_cases hg : greater x current = true
          · have hm' : findMaxAux greater x q = m := by
              simpa [findMaxAux, hg] using hm
            rcases ih x m hm' with ⟨he, hb⟩ | ⟨before, c, d, after, he, hc, hp, hs⟩
            · rw [he]
              exact Or.inr ⟨[], a, b, q, rfl, hg, by simp, hb⟩
            · have hcx : current ≤ x :=
                (total_of (fun a b : K => a ≤ b) current x).resolve_right ((hgreater x current).mp hg)
              have hmc : greater m current = true :=
                (hgreater m current).mpr (fun h => (hgreater m x).mp hc (le_trans h hcx))
              refine Or.inr ⟨.node x a b :: before, c, d, after,
                by simp only [List.cons_append, he], hmc, ?_, hs⟩
              intro y l r hy
              rcases List.mem_cons.mp hy with hy | hy
              · cases hy
                exact hc
              · exact hp y l r hy
          · have hxc : x ≤ current := by
              by_contra hn
              exact hg ((hgreater x current).mpr hn)
            have hm' : findMaxAux greater current q = m := by
              simpa [findMaxAux, hg] using hm
            rcases ih current m hm' with ⟨he, hb⟩ | ⟨before, c, d, after, he, hc, hp, hs⟩
            · refine Or.inl ⟨he, ?_⟩
              intro y l r hy
              rcases List.mem_cons.mp hy with hy | hy
              · cases hy
                exact hxc
              · exact hb y l r hy
            · have hmx : greater m x = true :=
                (hgreater m x).mpr (fun h => (hgreater m current).mp hc (le_trans h hxc))
              refine Or.inr ⟨.node x a b :: before, c, d, after,
                by simp only [List.cons_append, he], hc, ?_, hs⟩
              intro y l r hy
              rcases List.mem_cons.mp hy with hy | hy
              · cases hy
                exact hmx
              · exact hp y l r hy

/-- The source scan selects the first literal root of the maximal preorder class.
No validity assumption is needed until descendant contents are considered. -/
theorem findMax_some_split (q : Queue K) (m : K)
    (hm : findMax greater q = some m) :
    ∃ before a b after,
      q = before ++ .node m a b :: after ∧
      (∀ x l r, .node x l r ∈ before → greater m x = true) ∧
      (∀ x l r, .node x l r ∈ after → x ≤ m) := by
  induction q with
  | nil => simp [findMax] at hm
  | cons t q ih =>
      cases t with
      | nil =>
          obtain ⟨before, a, b, after, he, hp, hs⟩ := ih hm
          refine ⟨.nil :: before, a, b, after, by simp only [List.cons_append, he], ?_, hs⟩
          intro x l r hx
          exact hp x l r (by simpa using hx)
      | node x a b =>
          have he : findMaxAux greater x q = m := Option.some.inj hm
          rcases findMaxAux_first hgreater x q m he with ⟨he, hb⟩ |
              ⟨before, c, d, after, hq, hc, hp, hs⟩
          · rw [he]
            exact ⟨[], a, b, q, rfl, by simp, hb⟩
          · refine ⟨.node x a b :: before, c, d, after,
              by simp only [List.cons_append, hq], ?_, hs⟩
            intro y l r hy
            rcases List.mem_cons.mp hy with hy | hy
            · cases hy
              exact hc
            · exact hp y l r hy

/-- Every root, including the selected one, lies below the returned maximum. -/
theorem findMax_some_roots_le (q : Queue K) (m : K)
    (hm : findMax greater q = some m) :
    ∀ x a b, .node x a b ∈ q → x ≤ m := by
  obtain ⟨before, a, b, after, he, hp, hs⟩ := findMax_some_split hgreater q m hm
  intro x l r hx
  rw [he, List.mem_append, List.mem_cons] at hx
  rcases hx with hx | hx | hx
  · exact (total_of (fun a b : K => a ≤ b) x m).resolve_right ((hgreater m x).mp (hp x l r hx))
  · cases hx
    exact le_refl _
  · exact hs x l r hx

end Ordered

/-- Detaching the sibling roots preserves every occurrence of the raw tree. -/
theorem unzip_contents (t : BinaryTree K) :
    (contents (unzip t id)).Perm (treeContents t) := by
  induction t with
  | nil => exact List.Perm.refl _
  | node x a b _ ih =>
      simpa only [unzip_node_id, contents_append, contents_cons, contents_nil,
        treeContents, Trees.preorder_node, Trees.preorder_nil, List.append_nil, List.cons_append] using
        (ih.append_right (x :: treeContents a)).trans List.perm_append_comm

theorem unzip_proper (t : BinaryTree K) : ∀ s ∈ unzip t id, Proper s := by
  induction t with
  | nil => simp [unzip]
  | node x a b _ ih =>
      intro s hs
      rw [unzip_node_id, List.mem_append, List.mem_singleton] at hs
      rcases hs with hs | hs
      · exact ih s hs
      · subst s
        exact rfl

theorem unzip_occupied (t : BinaryTree K) : ∀ s ∈ unzip t id, occupied s = true := by
  induction t with
  | nil => simp [unzip]
  | node x a b _ ih =>
      intro s hs
      rw [unzip_node_id, List.mem_append, List.mem_singleton] at hs
      rcases hs with hs | hs
      · exact ih s hs
      · subst s
        exact rfl

/-- The detached children omit just the proper outer root, even without ranks. -/
theorem heapDeleteMax_contents (x : K) (a : BinaryTree K) :
    (treeContents (.node x a .nil)).Perm
      (x :: contents (heapDeleteMax (.node x a .nil))) := by
  simpa only [heapDeleteMax_node, treeContents, Trees.preorder_node,
    Trees.preorder_nil, List.append_nil] using (unzip_contents a).symm.cons x

/-- Exact prefix reconstruction for the actual second scan. Proper shape and
strictness on the prefix are essential; the suffix is untouched. -/
theorem deleteMaxAux_of_split (greater : K → K → Bool) (m : K)
    (before : Queue K) (a : BinaryTree K) (after : Queue K)
    (hproper : ∀ t ∈ before, Proper t)
    (hsmall : ∀ x l r, .node x l r ∈ before → greater m x = true)
    (hself : greater m m = false) :
    deleteMaxAux greater m (before ++ .node m a .nil :: after) =
      (before ++ .nil :: after, heapDeleteMax (.node m a .nil)) := by
  induction before with
  | nil => simp [deleteMaxAux_node, hself]
  | cons t before ih =>
      have hpt : ∀ s ∈ before, Proper s := fun s hs =>
        hproper s (List.mem_cons_of_mem _ hs)
      have hst : ∀ x l r, .node x l r ∈ before → greater m x = true :=
        fun x l r hx => hsmall x l r (List.mem_cons_of_mem _ hx)
      cases t with
      | nil => simp only [List.cons_append, deleteMaxAux_hole, ih hpt hst]
      | node x l r =>
          have hr : r = .nil := hproper _ List.mem_cons_self
          subst r
          have hg := hsmall x l .nil List.mem_cons_self
          simp only [List.cons_append, deleteMaxAux_node, hg, ↓reduceIte, ih hpt hst]

/-- Both auxiliary outputs together retain every occurrence except the chosen
literal root. The result is valid for arbitrary proper prefix shapes. -/
theorem deleteMaxAux_split_contents (greater : K → K → Bool) (m : K)
    (before : Queue K) (a : BinaryTree K) (after : Queue K)
    (hproper : ∀ t ∈ before, Proper t)
    (hsmall : ∀ x l r, .node x l r ∈ before → greater m x = true)
    (hself : greater m m = false) :
    (contents (before ++ .node m a .nil :: after)).Perm
      (m :: (contents (deleteMaxAux greater m (before ++ .node m a .nil :: after)).1 ++
        contents (deleteMaxAux greater m (before ++ .node m a .nil :: after)).2)) := by
  rw [deleteMaxAux_of_split greater m before a after hproper hsmall hself]
  have h := Multiset.coe_eq_coe.mpr (unzip_contents a)
  apply Multiset.coe_eq_coe.mp
  simp only [contents_append, contents_cons, treeContents, Trees.preorder_node,
    Trees.preorder_nil, List.nil_append, List.append_nil, heapDeleteMax_node,
    ← Multiset.coe_add, ← Multiset.cons_coe, ← Multiset.singleton_add]
  rw [h]
  ac_rfl

/-- Separate the actual first scan and final join from the returned pair. -/
theorem deleteMax_some_iff (greater : K → K → Bool) (q : Queue K) (m : K)
    (rest : Queue K) :
    deleteMax greater q = some (m, rest) ↔
      findMax greater q = some m ∧
        join greater (deleteMaxAux greater m q).1 (deleteMaxAux greater m q).2 .nil = rest := by
  cases h : findMax greater q with
  | none => simp [deleteMax, h]
  | some selected =>
      simp only [deleteMax, h, Option.some.injEq, Prod.mk.injEq]
      constructor
      · rintro ⟨rfl, hr⟩
        exact ⟨rfl, hr⟩
      · rintro ⟨rfl, hr⟩
        exact ⟨rfl, hr⟩

theorem deleteMax_none_relate_raw (greater : K → K → Bool) (q : Queue K) :
    Abs q [] ↔ deleteMax greater q = none := by
  rw [abs_nil_iff, deleteMax_eq_none_iff]

section ProperDeletion
variable [Preorder K] [Std.Total (fun x y : K => x ≤ y)]
variable {greater : K → K → Bool}
variable (hgreater : ∀ x y, greater x y = true ↔ ¬ x ≤ y)
include hgreater

/-- Rank is not needed for occurrence preservation: literal first-maximum
provenance and proper outer shapes already rule out the lossy fallback. -/
theorem deleteMax_some_contents_of_proper (q rest : Queue K) (m : K)
    (hq : ∀ t ∈ q, Proper t) (hd : deleteMax greater q = some (m, rest)) :
    (contents q).Perm (m :: contents rest) := by
  obtain ⟨hf, hj⟩ := (deleteMax_some_iff greater q m rest).mp hd
  obtain ⟨before, a, b, after, he, hp, _⟩ := findMax_some_split hgreater q m hf
  have hb : b = .nil := hq (.node m a b) (by rw [he]; simp)
  subst b
  have hbefore : ∀ t ∈ before, Proper t := fun t ht =>
    hq t (by rw [he]; exact List.mem_append_left _ ht)
  have hafter : ∀ t ∈ after, Proper t := fun t ht =>
    hq t (by rw [he]; exact List.mem_append_right _ (List.mem_cons_of_mem _ ht))
  have hself : greater m m = false := by
    cases h : greater m m with
    | false => rfl
    | true => exact False.elim ((hgreater m m).mp h (le_refl m))
  have haux := deleteMaxAux_of_split greater m before a after hbefore hp hself
  rw [he, haux] at hj
  have hfirst : ∀ t ∈ before ++ .nil :: after, Proper t := by
    intro t ht
    rcases List.mem_append.mp ht with ht | ht
    · exact hbefore t ht
    · rcases List.mem_cons.mp ht with ht | ht
      · subst t
        exact proper_nil
      · exact hafter t ht
  have hjoin := join_contents greater (before ++ .nil :: after)
    (heapDeleteMax (.node m a .nil)) .nil hfirst (unzip_proper a) proper_nil
  have hout : (contents rest).Perm
      (contents (before ++ .nil :: after) ++ contents (heapDeleteMax (.node m a .nil))) := by
    simpa only [hj, treeContents, Trees.preorder_nil, List.nil_append] using hjoin
  have hperm := deleteMaxAux_split_contents greater m before a after hbefore hp hself
  rw [haux] at hperm
  rw [he]
  exact hperm.trans (hout.symm.cons m)

end ProperDeletion

section ChildRanks
variable [LE K]

/-- The descending sibling spine is returned as exactly n increasing-rank slots. -/
theorem unzip_length {n : Nat} {m : K} {t : BinaryTree K}
    (h : pow2heapAux n m t) : (unzip t id).length = n := by
  induction n generalizing m t with
  | zero =>
      have ht := (pow2heapAux_zero _ _).mp h
      subst t
      rfl
  | succ n ih =>
      cases t with
      | nil => exact False.elim h
      | node k l r => simp only [unzip_node_id, List.length_append,
          List.length_singleton, ih h.2.2]

/-- The detached child forest always starts at rank zero. -/
theorem unzip_valid {n : Nat} {m : K} {t : BinaryTree K}
    (h : pow2heapAux n m t) : priq (unzip t id) := by
  induction n generalizing m t with
  | zero =>
      have ht := (pow2heapAux_zero _ _).mp h
      subst t
      trivial
  | succ n ih =>
      cases t with
      | nil => exact False.elim h
      | node k l r =>
          rw [unzip_node_id]
          change priqFrom 0 (unzip r id ++ [.node k l .nil])
          rw [priqFrom_append]
          refine ⟨ih h.2.2, ?_⟩
          rw [unzip_length h.2.2, Nat.zero_add]
          exact ⟨Or.inr h.2.1, trivial⟩

theorem heapDeleteMax_valid {n : Nat} {t : BinaryTree K}
    (h : pow2heap n t) : priq (heapDeleteMax t) := by
  obtain ⟨m, a, rfl, ha⟩ := (pow2heap_iff _ _).mp h
  exact unzip_valid ha

theorem heapDeleteMax_length {n : Nat} {t : BinaryTree K}
    (h : pow2heap n t) : (heapDeleteMax t).length = n := by
  obtain ⟨m, a, rfl, ha⟩ := (pow2heap_iff _ _).mp h
  exact unzip_length ha

theorem heapDeleteMax_occupied {n : Nat} {t : BinaryTree K}
    (h : pow2heap n t) : ∀ s ∈ heapDeleteMax t, occupied s = true := by
  obtain ⟨m, a, rfl, _⟩ := (pow2heap_iff _ _).mp h
  exact unzip_occupied a

theorem heapDeleteMax_mass_add_one {n : Nat} {t : BinaryTree K}
    (h : pow2heap n t) : mass (heapDeleteMax t) + 1 = 2 ^ n := by
  obtain ⟨m, a, rfl, ha⟩ := (pow2heap_iff _ _).mp h
  have hp := (heapDeleteMax_contents m a).length_eq
  have hn := pow2heapAux_numNodes ha
  simp only [treeContents, Trees.preorder_length, List.length_cons, contents_length,
    BinaryTree.numNodes] at hp
  omega

theorem heapDeleteMax_mass {n : Nat} {t : BinaryTree K}
    (h : pow2heap n t) : mass (heapDeleteMax t) = 2 ^ n - 1 := by
  have he := heapDeleteMax_mass_add_one h
  omega

/-- The source None wrapper retains its validity premise and orientation. -/
theorem deleteMax_none_relate (greater : K → K → Bool) (q : Queue K) (_hq : priq q) :
    Abs q [] ↔ deleteMax greater q = none := deleteMax_none_relate_raw greater q

end ChildRanks

/-- Every detached descendant remains bounded by its removed root. -/
theorem heapDeleteMax_bound [Preorder K] {n : Nat} {m : K} {a : BinaryTree K}
    (h : pow2heap n (.node m a .nil)) :
    ∀ x ∈ contents (heapDeleteMax (.node m a .nil)), x ≤ m := by
  intro x hx
  exact pow2heapAux_bound h x ((unzip_contents a).mem_iff.mp hx)

section RankedDeletion
variable [Preorder K] [Std.Total (fun x y : K => x ≤ y)]
variable {greater : K → K → Bool}
variable (hgreater : ∀ x y, greater x y = true ↔ ¬ x ≤ y)
include hgreater

/-- Successful provenance identifies the literal root and its absolute rank. -/
theorem findMax_some_valid_split (i : Nat) (q : Queue K) (m : K)
    (hq : priqFrom i q) (hm : findMax greater q = some m) :
    ∃ before a after, q = before ++ .node m a .nil :: after ∧
      pow2heap (i + before.length) (.node m a .nil) ∧
      (∀ x l r, .node x l r ∈ before → greater m x = true) ∧
      (∀ x l r, .node x l r ∈ after → x ≤ m) := by
  obtain ⟨before, a, b, after, he, hp, hs⟩ := findMax_some_split hgreater q m hm
  have hv := (priqFrom_append i before (.node m a b :: after)).mp (he ▸ hq)
  have ht := hv.2.1.resolve_left (by simp)
  have hb : b = .nil := pow2heap_proper ht
  subst b
  exact ⟨before, a, after, he, ht, hp, hs⟩

/-- Both auxiliary outputs have their actual bases: i for the replaced forest,
zero for the child forest. -/
theorem deleteMaxAux_valid (i : Nat) (q : Queue K) (m : K)
    (hq : priqFrom i q) (hm : findMax greater q = some m) :
    priqFrom i (deleteMaxAux greater m q).1 ∧ priq (deleteMaxAux greater m q).2 := by
  obtain ⟨before, a, after, he, ht, hp, _⟩ := findMax_some_valid_split hgreater i q m hq hm
  have hv := (priqFrom_append i before (.node m a .nil :: after)).mp (he ▸ hq)
  have hself : greater m m = false := by
    cases h : greater m m with
    | false => rfl
    | true => exact False.elim ((hgreater m m).mp h le_rfl)
  rw [he, deleteMaxAux_of_split greater m before a after (priqFrom_proper hv.1) hp hself]
  constructor
  · exact (priqFrom_append i before (.nil :: after)).mpr ⟨hv.1, Or.inl rfl, hv.2.2⟩
  · exact heapDeleteMax_valid ht

/-- Replacing the selected root by a hole preserves every stored slot. -/
theorem deleteMaxAux_fst_length (i : Nat) (q : Queue K) (m : K)
    (hq : priqFrom i q) (hm : findMax greater q = some m) :
    (deleteMaxAux greater m q).1.length = q.length := by
  obtain ⟨before, a, after, he, _, hp, _⟩ := findMax_some_valid_split hgreater i q m hq hm
  have hv := (priqFrom_append i before (.node m a .nil :: after)).mp (he ▸ hq)
  have hself : greater m m = false := by
    cases h : greater m m with
    | false => rfl
    | true => exact False.elim ((hgreater m m).mp h le_rfl)
  rw [he, deleteMaxAux_of_split greater m before a after (priqFrom_proper hv.1) hp hself]
  simp only [List.length_append, List.length_cons]

/-- The selected rank is strictly before the end of the generalized forest. -/
theorem deleteMaxAux_snd_length_lt (i : Nat) (q : Queue K) (m : K)
    (hq : priqFrom i q) (hm : findMax greater q = some m) :
    (deleteMaxAux greater m q).2.length < i + q.length := by
  obtain ⟨before, a, after, he, ht, hp, _⟩ := findMax_some_valid_split hgreater i q m hq hm
  have hv := (priqFrom_append i before (.node m a .nil :: after)).mp (he ▸ hq)
  have hself : greater m m = false := by
    cases h : greater m m with
    | false => rfl
    | true => exact False.elim ((hgreater m m).mp h le_rfl)
  rw [he, deleteMaxAux_of_split greater m before a after (priqFrom_proper hv.1) hp hself]
  simp only [heapDeleteMax_length ht, List.length_append, List.length_cons]
  omega

theorem deleteMaxAux_contents (i : Nat) (q : Queue K) (m : K)
    (hq : priqFrom i q) (hm : findMax greater q = some m) :
    (contents q).Perm
      (m :: (contents (deleteMaxAux greater m q).1 ++ contents (deleteMaxAux greater m q).2)) := by
  obtain ⟨before, a, after, he, _, hp, _⟩ := findMax_some_valid_split hgreater i q m hq hm
  have hv := (priqFrom_append i before (.node m a .nil :: after)).mp (he ▸ hq)
  have hself : greater m m = false := by
    cases h : greater m m with
    | false => rfl
    | true => exact False.elim ((hgreater m m).mp h le_rfl)
  rw [he]
  exact deleteMaxAux_split_contents greater m before a after (priqFrom_proper hv.1) hp hself

/-- The full source chain preserves rank validity after an actual success. -/
theorem deleteMax_some_priq (q rest : Queue K) (m : K)
    (hq : priq q) (hd : deleteMax greater q = some (m, rest)) : priq rest := by
  obtain ⟨hf, hj⟩ := (deleteMax_some_iff greater q m rest).mp hd
  have hv := deleteMaxAux_valid hgreater 0 q m hq hf
  rw [← hj]
  exact join_valid greater hgreater 0 _ _ .nil hv.1 hv.2 (Or.inl rfl)

theorem deleteMax_some_contents (q rest : Queue K) (m : K)
    (hq : priq q) (hd : deleteMax greater q = some (m, rest)) :
    (contents q).Perm (m :: contents rest) :=
  deleteMax_some_contents_of_proper hgreater q rest m (priqFrom_proper hq) hd

omit [Std.Total (fun x y : K => x ≤ y)] hgreater in
/-- A rank-valid forest is bounded once all occupied roots are bounded. -/
theorem priqFrom_contents_le (i : Nat) (q : Queue K) (m : K)
    (hq : priqFrom i q)
    (hroots : ∀ x a b, .node x a b ∈ q → x ≤ m) :
    ∀ x ∈ contents q, x ≤ m := by
  induction q generalizing i with
  | nil => simp
  | cons t q ih =>
      have ht := hq.1
      have htail := ih (i + 1) hq.2 (fun x a b hx => hroots x a b (List.mem_cons_of_mem _ hx))
      intro x hx
      rcases List.mem_append.mp hx with hx | hx
      · cases t with
        | nil => simp [treeContents] at hx
        | node k a b =>
            have hv := ht.resolve_left (by simp)
            have hb : b = .nil := pow2heap_proper hv
            subst b
            exact (pow2heap_bound hv x hx).trans (hroots k a .nil List.mem_cons_self)
      · exact htail x hx

theorem findMax_some_bound (i : Nat) (q : Queue K) (m : K)
    (hq : priqFrom i q) (hm : findMax greater q = some m) :
    ∀ x ∈ contents q, x ≤ m :=
  priqFrom_contents_le i q m hq (findMax_some_roots_le hgreater q m hm)

/-- The source relational success law applies to every abstraction witness. -/
theorem deleteMax_some_relate (q rest : Queue K) (m : K) (xs ys : List K)
    (hq : priq q) (hxs : Abs q xs) (hd : deleteMax greater q = some (m, rest))
    (hys : Abs rest ys) : xs.Perm (m :: ys) ∧ ∀ x ∈ ys, x ≤ m := by
  have hp := deleteMax_some_contents hgreater q rest m hq hd
  have hx := (queue_elems_iff q xs).mp hxs
  have hy := (queue_elems_iff rest ys).mp hys
  constructor
  · exact hx.trans (hp.trans (hy.symm.cons m))
  · intro x hxy
    have hf := (deleteMax_some_iff greater q m rest).mp hd |>.1
    exact findMax_some_bound hgreater 0 q m hq hf x
      (hp.mem_iff.mpr (List.mem_cons_of_mem _ (hy.mem_iff.mp hxy)))

theorem deleteMax_some_mem (q rest : Queue K) (m : K)
    (hq : priq q) (hd : deleteMax greater q = some (m, rest)) : m ∈ contents q :=
  (deleteMax_some_contents hgreater q rest m hq hd).mem_iff.mpr List.mem_cons_self

theorem deleteMax_some_mass (q rest : Queue K) (m : K)
    (hq : priq q) (hd : deleteMax greater q = some (m, rest)) :
    mass rest + 1 = mass q := by
  simpa only [List.length_cons, contents_length] using
    (deleteMax_some_contents hgreater q rest m hq hd).length_eq.symm

/-- An occurrence equation, not a set equation: exactly one selected key is removed. -/
theorem deleteMax_some_count [DecidableEq K] (q rest : Queue K) (m query : K)
    (hq : priq q) (hd : deleteMax greater q = some (m, rest)) :
    (contents q).count query = (contents rest).count query + if query = m then 1 else 0 := by
  have hp := deleteMax_some_contents hgreater q rest m hq hd
  have hc := congrFun (Sequences.Multiplicity.perm_contents hp) query
  by_cases he : query = m
  · subst query
    simpa [Sequences.Multiplicity.contents, List.count_cons] using hc
  · simpa [Sequences.Multiplicity.contents, List.count_cons, he, Ne.symm he] using hc

/-- Source deletion never trims padding and never grows the stored forest. -/
theorem deleteMax_length (q rest : Queue K) (m : K)
    (hq : priq q) (hd : deleteMax greater q = some (m, rest)) :
    rest.length = q.length := by
  obtain ⟨hf, hj⟩ := (deleteMax_some_iff greater q m rest).mp hd
  have hfst := deleteMaxAux_fst_length hgreater 0 q m hq hf
  have hsnd : (deleteMaxAux greater m q).2.length < q.length := by
    simpa only [Nat.zero_add] using deleteMaxAux_snd_length_lt hgreater 0 q m hq hf
  have hmax : max (deleteMaxAux greater m q).1.length
      (deleteMaxAux greater m q).2.length = q.length := by rw [hfst]; omega
  have hlo := (join_length_bounds greater (deleteMaxAux greater m q).1
    (deleteMaxAux greater m q).2 .nil).1
  rw [hmax, hj] at hlo
  apply Nat.le_antisymm ?_ hlo
  by_contra hn
  have hgrow : q.length < rest.length := by omega
  have hc : Canonical rest := by
    rw [← hj]
    apply join_growth_canonical greater
    rw [hmax, hj]
    exact hgrow
  have hv := deleteMax_some_priq hgreater q rest m hq hd
  have hlen := canonical_length hv hc
  have hm := deleteMax_some_mass hgreater q rest m hq hd
  have hs := Nat.size_le_size (show mass rest ≤ mass q by omega)
  have hbound := size_mass_le_length hq
  omega

end RankedDeletion

end Search.BinomialQueue
