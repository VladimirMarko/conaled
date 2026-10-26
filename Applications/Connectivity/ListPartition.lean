import Std

set_option autoImplicit false
set_option warningAsError true

/-! Concrete ListPartition proofs adapted from adwh-checkpoint-233.
Source members and declaration dispositions: docs/research/adwh-connectivity-provenance.tsv.
Operations retain the source failure and representative-selection behavior. -/

namespace Connectivity.ListPartition

abbrev Vertex := Int
abbrev Name := Vertex
abbrev DS := List (Name × List Vertex)

/-- Finite signed-bound interpretation of the source ascending range [1..n]. -/
def vertices (n : Int) : List Vertex :=
  (List.range n.toNat).map (fun k => Int.ofNat (k + 1))

def startDS (n : Int) : DS := (vertices n).map (fun v => (v, [v]))

/-- Source justLookup without its partial fromJust.  Lookup keeps the first key. -/
def lookupDS (ds : DS) (name : Name) : Option (List Vertex) :=
  List.lookup name ds

/-- Retain the actual filter/head executor, including its first-match behavior. -/
def findDS (ds : DS) (v : Vertex) : Option Name :=
  ((ds.filter (fun block => block.2.contains v)).head?).map Prod.fst

/-- The actual two-lookups, append and filtering body, with no validity repair. -/
def unionDS (n1 n2 : Name) (ds : DS) : Option DS :=
  match lookupDS ds n1, lookupDS ds n2 with
  | some xs, some ys =>
      some ((n1, xs ++ ys) :: ds.filter (fun block => !([n1, n2].contains block.1)))
  | _, _ => none

def carrier (ds : DS) : List Vertex := (ds.map Prod.snd).flatten

/-- Independent named partition: multiplicities, universe and head names. -/
def IsPartitionOf (vs : List Vertex) (ds : DS) : Prop :=
  vs.Nodup ∧ (carrier ds).Perm vs ∧
    ∀ name xs, (name, xs) ∈ ds → xs.head? = some name

def SameBlock (ds : DS) (u v : Vertex) : Prop :=
  ∃ name xs, (name, xs) ∈ ds ∧ u ∈ xs ∧ v ∈ xs

def IsName (ds : DS) (name : Name) : Prop := name ∈ ds.map Prod.fst

def FirstAssoc (ds : DS) (name : Name) (xs : List Vertex) : Prop :=
  ∃ before after, ds = before ++ (name, xs) :: after ∧
    ∀ block ∈ before, block.1 ≠ name

def FirstContaining (ds : DS) (v : Vertex) (name : Name) : Prop :=
  ∃ before xs after, ds = before ++ (name, xs) :: after ∧ v ∈ xs ∧
    ∀ block ∈ before, v ∉ block.2

/-- Independent undirected equivalence closure, bounded by the vertex universe. -/
inductive Connected (vs : List Vertex) (links : List (Vertex × Vertex)) :
    Vertex → Vertex → Prop
  | refl {v : Vertex} : v ∈ vs → Connected vs links v v
  | edge {u v : Vertex} : u ∈ vs → v ∈ vs → (u, v) ∈ links → Connected vs links u v
  | symm {u v : Vertex} : Connected vs links u v → Connected vs links v u
  | trans {u v w : Vertex} : Connected vs links u v → Connected vs links v w →
      Connected vs links u w

/-- Actual successful distinct-name calls; no post-invariant is assumed. -/
inductive MergeHistory (n : Int) : List (Name × Name) → DS → Prop
  | start : MergeHistory n [] (startDS n)
  | snoc {links : List (Name × Name)} {ds out : DS} {a b : Name} :
      MergeHistory n links ds → IsName ds a → IsName ds b → a ≠ b →
      unionDS a b ds = some out → MergeHistory n (links ++ [(a, b)]) out

private theorem carrier_cons (b : Name × List Vertex) (ds : DS) :
    carrier (b :: ds) = b.2 ++ carrier ds := by
  simp [carrier]

private theorem mem_carrier_iff (ds : DS) (v : Vertex) :
    v ∈ carrier ds ↔ ∃ name xs, (name, xs) ∈ ds ∧ v ∈ xs := by
  rw [carrier, List.mem_flatten]
  constructor
  · rintro ⟨xs, hm, hv⟩
    obtain ⟨⟨name, ys⟩, hy, he⟩ := List.mem_map.mp hm
    cases he
    exact ⟨name, ys, hy, hv⟩
  · rintro ⟨name, xs, hx, hv⟩
    exact ⟨xs, List.mem_map.mpr ⟨(name, xs), hx, rfl⟩, hv⟩

theorem head_member {xs : List Vertex} {name : Name}
    (h : xs.head? = some name) : name ∈ xs := by
  obtain ⟨ys, rfl⟩ := List.head?_eq_some_iff.mp h
  simp

private theorem carrier_nodup {vs : List Vertex} {ds : DS}
    (h : IsPartitionOf vs ds) : (carrier ds).Nodup := h.2.1.symm.nodup h.1

private theorem carrier_mem_universe {vs : List Vertex} {ds : DS}
    (h : IsPartitionOf vs ds) (v : Vertex) : v ∈ carrier ds ↔ v ∈ vs :=
  h.2.1.mem_iff

private theorem same_member_block_eq {ds : DS} {b c : Name × List Vertex} {v : Vertex}
    (h : (carrier ds).Nodup) (hb : b ∈ ds) (hc : c ∈ ds)
    (hv : v ∈ b.2) (hw : v ∈ c.2) : b = c := by
  induction ds with
  | nil => simp at hb
  | cons a ds ih =>
      have hn := List.nodup_append.mp (by simpa [carrier_cons] using h)
      rcases List.mem_cons.mp hb with hba | hbt
      · subst b
        rcases List.mem_cons.mp hc with hca | hct
        · exact hca.symm
        · have ht : v ∈ carrier ds := (mem_carrier_iff ds v).mpr ⟨c.1, c.2, hct, hw⟩
          exact False.elim (hn.2.2 v hv v ht rfl)
      · rcases List.mem_cons.mp hc with hca | hct
        · subst c
          have ht : v ∈ carrier ds := (mem_carrier_iff ds v).mpr ⟨b.1, b.2, hbt, hv⟩
          exact False.elim (hn.2.2 v hw v ht rfl)
        · exact ih hn.2.1 hbt hct

private theorem same_name_block_eq {vs : List Vertex} {ds : DS}
    (h : IsPartitionOf vs ds) {b c : Name × List Vertex}
    (hb : b ∈ ds) (hc : c ∈ ds) (hn : b.1 = c.1) : b = c := by
  have hbm := head_member (h.2.2 b.1 b.2 hb)
  have hcm := head_member (h.2.2 c.1 c.2 hc)
  apply same_member_block_eq (carrier_nodup h) hb hc hbm
  simpa [hn] using hcm

private theorem name_in_universe {vs : List Vertex} {ds : DS}
    (h : IsPartitionOf vs ds) {name : Name} (hn : IsName ds name) : name ∈ vs := by
  obtain ⟨b, hb, he⟩ := List.mem_map.mp hn
  have hm := head_member (h.2.2 b.1 b.2 hb)
  apply (carrier_mem_universe h name).mp
  apply (mem_carrier_iff ds name).mpr
  exact ⟨b.1, b.2, hb, by simpa [he] using hm⟩

theorem mem_vertices_iff (n v : Int) : v ∈ vertices n ↔ 1 ≤ v ∧ v ≤ n := by
  constructor
  · rintro h
    obtain ⟨k, hk, rfl⟩ := List.mem_map.mp h
    have hk' := List.mem_range.mp hk
    change 1 ≤ (k : Int) + 1 ∧ (k : Int) + 1 ≤ n
    omega
  · rintro ⟨hv, hn⟩
    apply List.mem_map.mpr
    refine ⟨(v - 1).toNat, List.mem_range.mpr ?_, ?_⟩
    · omega
    · change ((v - 1).toNat : Int) + 1 = v
      omega

theorem startDS_nonpositive (n : Int) (hn : n ≤ 0) : startDS n = [] := by
  have hz : n.toNat = 0 := by omega
  simp [startDS, vertices, hz]

theorem startDS_length (n : Int) : (startDS n).length = n.toNat := by
  simp [startDS, vertices]

theorem lookupDS_first_iff (ds : DS) (name : Name) (xs : List Vertex) :
    lookupDS ds name = some xs ↔ FirstAssoc ds name xs := by
  simpa [lookupDS, FirstAssoc, ne_comm] using
    (List.lookup_eq_some_iff (l := ds) (k := name) (b := xs))

private theorem lookupDS_member {ds : DS} {name : Name} {xs : List Vertex}
    (h : lookupDS ds name = some xs) : (name, xs) ∈ ds := by
  obtain ⟨before, after, rfl, _⟩ := (lookupDS_first_iff ds name xs).mp h
  simp

private theorem lookupDS_defined_iff (ds : DS) (name : Name) :
    (∃ xs, lookupDS ds name = some xs) ↔ IsName ds name := by
  constructor
  · rintro ⟨xs, hx⟩
    exact List.mem_map.mpr ⟨(name, xs), lookupDS_member hx, rfl⟩
  · intro hn
    obtain ⟨b, hb, he⟩ := List.mem_map.mp hn
    apply Option.isSome_iff_exists.mp
    apply List.lookup_isSome_iff.mpr
    exact ⟨b, hb, by simp [he]⟩

private theorem findDS_cons (name : Name) (xs : List Vertex) (ds : DS) (v : Vertex) :
    findDS ((name, xs) :: ds) v = if v ∈ xs then some name else findDS ds v := by
  by_cases h : v ∈ xs <;> simp [findDS, h]

private theorem lookupDS_cons (key : Name) (xs : List Vertex) (ds : DS) (name : Name) :
    lookupDS ((key, xs) :: ds) name = if name = key then some xs else lookupDS ds name := by
  unfold lookupDS
  rw [List.lookup_cons]
  by_cases h : name = key
  · subst key
    simp
  · rw [beq_eq_false_iff_ne.mpr h, ite_eq_right h]

theorem findDS_first_iff (ds : DS) (v : Vertex) (name : Name) :
    findDS ds v = some name ↔ FirstContaining ds v name := by
  rw [findDS, Option.map_eq_some_iff]
  constructor
  · rintro ⟨⟨key, xs⟩, hh, he⟩
    change key = name at he
    subst key
    obtain ⟨tail, ht⟩ := List.head?_eq_some_iff.mp hh
    obtain ⟨before, after, hd, hb, hv, _⟩ := List.filter_eq_cons_iff.mp ht
    exact ⟨before, xs, after, hd, by simpa using hv, by simpa using hb⟩
  · rintro ⟨before, xs, after, rfl, hv, hb⟩
    refine ⟨(name, xs), ?_, rfl⟩
    apply List.head?_eq_some_iff.mpr
    refine ⟨after.filter (fun block => block.2.contains v), List.filter_eq_cons_iff.mpr ?_⟩
    exact ⟨before, after, rfl, by simpa using hb, by simpa using hv, rfl⟩

theorem findDS_defined_iff (ds : DS) (v : Vertex) :
    (∃ name, findDS ds v = some name) ↔ v ∈ carrier ds := by
  induction ds with
  | nil => simp [findDS, carrier]
  | cons b ds ih =>
      rcases b with ⟨name, xs⟩
      by_cases h : v ∈ xs <;> simp [findDS_cons, carrier_cons, h, ih]

theorem unionDS_eq_some_iff (n1 n2 : Name) (ds out : DS) :
    unionDS n1 n2 ds = some out ↔
      ∃ xs ys, FirstAssoc ds n1 xs ∧ FirstAssoc ds n2 ys ∧
        out = (n1, xs ++ ys) :: ds.filter (fun b => !([n1, n2].contains b.1)) := by
  simp only [← lookupDS_first_iff]
  cases h1 : lookupDS ds n1 <;> cases h2 : lookupDS ds n2 <;>
    simp [unionDS, h1, h2, eq_comm]

theorem unionDS_defined_iff (n1 n2 : Name) (ds : DS) :
    (∃ out, unionDS n1 n2 ds = some out) ↔ IsName ds n1 ∧ IsName ds n2 := by
  simp only [unionDS_eq_some_iff, ← lookupDS_first_iff]
  constructor
  · rintro ⟨_, xs, ys, hx, hy, _⟩
    exact ⟨(lookupDS_defined_iff ds n1).mp ⟨xs, hx⟩,
      (lookupDS_defined_iff ds n2).mp ⟨ys, hy⟩⟩
  · rintro ⟨h1, h2⟩
    obtain ⟨xs, hx⟩ := (lookupDS_defined_iff ds n1).mpr h1
    obtain ⟨ys, hy⟩ := (lookupDS_defined_iff ds n2).mpr h2
    exact ⟨_, xs, ys, hx, hy, rfl⟩

theorem partition_blocks_nonempty {vs : List Vertex} {ds : DS}
    (h : IsPartitionOf vs ds) (name : Name) (xs : List Vertex) (hm : (name, xs) ∈ ds) :
    xs ≠ [] := by
  intro he
  have hh := h.2.2 name xs hm
  simp [he] at hh

private theorem partition_block_properties {vs : List Vertex} {ds : DS}
    (h : IsPartitionOf vs ds) :
    (∀ b ∈ ds, b.2.Nodup) ∧
      ds.Pairwise (fun b c => ∀ u ∈ b.2, ∀ v ∈ c.2, u ≠ v) := by
  have hc := carrier_nodup h
  change (ds.map Prod.snd).flatten.Pairwise (· ≠ ·) at hc
  have hp := List.pairwise_flatten.mp hc
  constructor
  · intro b hb
    exact hp.1 b.2 (List.mem_map.mpr ⟨b, hb, rfl⟩)
  · exact List.pairwise_map.mp hp.2

theorem partition_names_nodup {vs : List Vertex} {ds : DS}
    (h : IsPartitionOf vs ds) : (ds.map Prod.fst).Nodup := by
  change (ds.map Prod.fst).Pairwise (· ≠ ·)
  apply List.pairwise_map.mpr
  apply List.Pairwise.imp_of_mem ?_ (partition_block_properties h).2
  intro b c hb hc hd he
  exact hd b.1 (head_member (h.2.2 b.1 b.2 hb)) c.1
    (head_member (h.2.2 c.1 c.2 hc)) he

theorem partition_block_nodup {vs : List Vertex} {ds : DS}
    (h : IsPartitionOf vs ds) (name : Name) (xs : List Vertex) (hm : (name, xs) ∈ ds) :
    xs.Nodup := (partition_block_properties h).1 (name, xs) hm

theorem partition_distinct_blocks_disjoint {vs : List Vertex} {ds : DS}
    (h : IsPartitionOf vs ds) {n1 n2 : Name} {xs ys : List Vertex}
    (hx : (n1, xs) ∈ ds) (hy : (n2, ys) ∈ ds) (hne : n1 ≠ n2)
    (v : Vertex) (hv : v ∈ xs) : v ∉ ys := by
  intro hw
  have he := same_member_block_eq (carrier_nodup h) hx hy hv hw
  exact hne (congrArg Prod.fst he)

theorem carrier_singletons (vs : List Vertex) :
    carrier (vs.map (fun v => (v, [v]))) = vs := by
  induction vs with
  | nil => rfl
  | cons v vs ih => simp [carrier_cons, ih]

theorem startDS_partition (n : Int) : IsPartitionOf (vertices n) (startDS n) := by
  refine ⟨?_, ?_, ?_⟩
  · apply List.Pairwise.map (fun k : Nat => Int.ofNat (k + 1)) ?_ List.nodup_range
    intro a b hab he
    apply hab
    exact Nat.add_right_cancel (Int.ofNat.inj he)
  · change (carrier ((vertices n).map (fun v => (v, [v])))).Perm (vertices n)
    rw [carrier_singletons]
  · intro name xs hm
    obtain ⟨v, _, he⟩ := List.mem_map.mp hm
    cases he
    rfl

theorem findDS_partition_iff {vs : List Vertex} {ds : DS}
    (h : IsPartitionOf vs ds) (v : Vertex) (name : Name) :
    findDS ds v = some name ↔ ∃ xs, (name, xs) ∈ ds ∧ v ∈ xs := by
  constructor
  · intro hf
    obtain ⟨before, xs, after, he, hv, _⟩ := (findDS_first_iff ds v name).mp hf
    exact ⟨xs, by simp [he], hv⟩
  · rintro ⟨xs, hx, hv⟩
    obtain ⟨key, hk⟩ := (findDS_defined_iff ds v).mpr
      ((mem_carrier_iff ds v).mpr ⟨name, xs, hx, hv⟩)
    obtain ⟨before, ys, after, he, hw, _⟩ := (findDS_first_iff ds v key).mp hk
    have hy : (key, ys) ∈ ds := by simp [he]
    have hn := congrArg Prod.fst (same_member_block_eq (carrier_nodup h) hx hy hv hw)
    change name = key at hn
    rw [← hn] at hk
    exact hk

theorem findDS_startDS (n v : Int) :
    findDS (startDS n) v = if 1 ≤ v ∧ v ≤ n then some v else none := by
  by_cases hv : 1 ≤ v ∧ v ≤ n
  · rw [ite_eq_left hv]
    apply (findDS_partition_iff (startDS_partition n) v v).mpr
    exact ⟨[v], List.mem_map.mpr ⟨v, (mem_vertices_iff n v).mpr hv, rfl⟩, by simp⟩
  · rw [ite_eq_right hv]
    cases he : findDS (startDS n) v with
    | none => rfl
    | some name =>
        have hm := (findDS_defined_iff (startDS n) v).mp ⟨name, he⟩
        have hu := (carrier_mem_universe (startDS_partition n) v).mp hm
        exact False.elim (hv ((mem_vertices_iff n v).mp hu))

theorem findDS_representative {vs : List Vertex} {ds : DS}
    (h : IsPartitionOf vs ds) {v : Vertex} {name : Name}
    (hf : findDS ds v = some name) : name ∈ vs ∧ findDS ds name = some name := by
  obtain ⟨xs, hx, _⟩ := (findDS_partition_iff h v name).mp hf
  have hn := head_member (h.2.2 name xs hx)
  exact ⟨(carrier_mem_universe h name).mp ((mem_carrier_iff ds name).mpr ⟨name, xs, hx, hn⟩),
    (findDS_partition_iff h name name).mpr ⟨xs, hx, hn⟩⟩

theorem sameBlock_symm {ds : DS} {u v : Vertex} (h : SameBlock ds u v) :
    SameBlock ds v u := by
  obtain ⟨name, xs, hx, hu, hv⟩ := h
  exact ⟨name, xs, hx, hv, hu⟩

theorem sameBlock_equivalence_on {vs : List Vertex} {ds : DS}
    (h : IsPartitionOf vs ds) :
    (∀ v ∈ vs, SameBlock ds v v) ∧
    (∀ u v, SameBlock ds u v → SameBlock ds v u) ∧
    (∀ u v w, SameBlock ds u v → SameBlock ds v w → SameBlock ds u w) ∧
    (∀ u v, SameBlock ds u v → u ∈ vs ∧ v ∈ vs) := by
  refine ⟨?_, fun _ _ => sameBlock_symm, ?_, ?_⟩
  · intro v hv
    obtain ⟨name, xs, hx, hm⟩ := (mem_carrier_iff ds v).mp ((carrier_mem_universe h v).mpr hv)
    exact ⟨name, xs, hx, hm, hm⟩
  · rintro u v w ⟨n1, xs, hx, hu, hv⟩ ⟨n2, ys, hy, hv', hw⟩
    have he := same_member_block_eq (carrier_nodup h) hx hy hv hv'
    cases he
    exact ⟨n1, xs, hx, hu, hw⟩
  · rintro u v ⟨name, xs, hx, hu, hv⟩
    exact ⟨(carrier_mem_universe h u).mp ((mem_carrier_iff ds u).mpr ⟨name, xs, hx, hu⟩),
      (carrier_mem_universe h v).mp ((mem_carrier_iff ds v).mpr ⟨name, xs, hx, hv⟩)⟩

theorem findDS_equal_iff_sameBlock {vs : List Vertex} {ds : DS}
    (h : IsPartitionOf vs ds) {u v : Vertex} (hu : u ∈ vs) (_hv : v ∈ vs) :
    findDS ds u = findDS ds v ↔ SameBlock ds u v := by
  constructor
  · intro he
    obtain ⟨name, hf⟩ := (findDS_defined_iff ds u).mpr ((carrier_mem_universe h u).mpr hu)
    obtain ⟨xs, hx, hux⟩ := (findDS_partition_iff h u name).mp hf
    obtain ⟨ys, hy, hvy⟩ := (findDS_partition_iff h v name).mp (he.symm.trans hf)
    have hs := same_name_block_eq h hx hy rfl
    cases hs
    exact ⟨name, xs, hx, hux, hvy⟩
  · rintro ⟨name, xs, hx, hux, hvx⟩
    rw [(findDS_partition_iff h u name).mpr ⟨xs, hx, hux⟩,
      (findDS_partition_iff h v name).mpr ⟨xs, hx, hvx⟩]

theorem lookupDS_of_member {vs : List Vertex} {ds : DS}
    (h : IsPartitionOf vs ds) {name : Name} {xs : List Vertex} (hm : (name, xs) ∈ ds) :
    lookupDS ds name = some xs := by
  obtain ⟨ys, hy⟩ := (lookupDS_defined_iff ds name).mpr (List.mem_map.mpr ⟨(name, xs), hm, rfl⟩)
  have he := same_name_block_eq h hm (lookupDS_member hy) rfl
  cases he
  exact hy

private theorem split_names_perm {vs : List Vertex} {ds : DS}
    (h : IsPartitionOf vs ds) {n1 n2 : Name} {xs ys : List Vertex}
    (hx : (n1, xs) ∈ ds) (hy : (n2, ys) ∈ ds) (hne : n1 ≠ n2) :
    ((n1, xs) :: (n2, ys) :: ds.filter (fun b => !([n1, n2].contains b.1))).Perm ds := by
  let selected := fun b : Name × List Vertex => [n1, n2].contains b.1
  have hds : ds.Nodup := by
    apply List.Pairwise.of_map Prod.fst ?_ (partition_names_nodup h)
    intro a b hn he
    exact hn (congrArg Prod.fst he)
  have hf : (ds.filter selected).Nodup := List.Pairwise.filter selected hds
  have hp : (ds.filter selected).Perm [(n1, xs), (n2, ys)] := by
    apply (List.perm_ext_iff_of_nodup hf (by simp [hne])).mpr
    intro b
    constructor
    · intro hm
      obtain ⟨hb, hs⟩ := List.mem_filter.mp hm
      have hn : b.1 = n1 ∨ b.1 = n2 := by simpa [selected] using hs
      rcases hn with hn | hn
      · have he := same_name_block_eq h hb hx hn
        simp [he]
      · have he := same_name_block_eq h hb hy hn
        simp [he]
    · intro hm
      rcases List.mem_cons.mp hm with he | hm
      · subst b
        simp [selected, hx]
      · have he := List.mem_singleton.mp hm
        subst b
        simp [selected, hy]
  have hs := List.filter_append_perm selected ds
  have he := (hp.append_right (ds.filter (fun b => !selected b))).symm.trans hs
  simpa [selected] using he

private theorem unionDS_components {n1 n2 : Name} {ds out : DS}
    (hu : unionDS n1 n2 ds = some out) :
    ∃ xs ys, lookupDS ds n1 = some xs ∧ lookupDS ds n2 = some ys ∧
      out = (n1, xs ++ ys) :: ds.filter (fun b => !([n1, n2].contains b.1)) := by
  simpa only [← lookupDS_first_iff] using (unionDS_eq_some_iff n1 n2 ds out).mp hu

theorem unionDS_partition {vs : List Vertex} {ds out : DS} {n1 n2 : Name}
    (h : IsPartitionOf vs ds) (_h1 : IsName ds n1) (_h2 : IsName ds n2)
    (hne : n1 ≠ n2) (hu : unionDS n1 n2 ds = some out) : IsPartitionOf vs out := by
  obtain ⟨xs, ys, hx, hy, rfl⟩ := unionDS_components hu
  have hxm := lookupDS_member hx
  have hym := lookupDS_member hy
  have hp := split_names_perm h hxm hym hne
  have hc := (hp.map Prod.snd).flatten
  refine ⟨h.1, ?_, ?_⟩
  · apply List.Perm.trans ?_ h.2.1
    simpa [carrier, List.append_assoc] using hc
  · intro name zs hz
    rcases List.mem_cons.mp hz with he | hz
    · cases he
      obtain ⟨tail, he⟩ := List.head?_eq_some_iff.mp (h.2.2 n1 xs hxm)
      simp [he]
    · exact h.2.2 name zs (List.mem_filter.mp hz).1

theorem unionDS_block_count {vs : List Vertex} {ds out : DS} {n1 n2 : Name}
    (h : IsPartitionOf vs ds) (_h1 : IsName ds n1) (_h2 : IsName ds n2)
    (hne : n1 ≠ n2) (hu : unionDS n1 n2 ds = some out) : out.length + 1 = ds.length := by
  obtain ⟨xs, ys, hx, hy, rfl⟩ := unionDS_components hu
  have hp := (split_names_perm h (lookupDS_member hx) (lookupDS_member hy) hne).length_eq
  simpa [Nat.add_assoc, Nat.add_comm, Nat.add_left_comm] using hp

theorem unionDS_names {ds out : DS} {n1 n2 : Name}
    (hu : unionDS n1 n2 ds = some out) :
    out.map Prod.fst = n1 :: (ds.map Prod.fst).filter (fun n => !([n1, n2].contains n)) := by
  obtain ⟨xs, ys, _, _, rfl⟩ := unionDS_components hu
  simp only [List.map_cons]
  congr 1
  exact (List.filter_map (f := Prod.fst)
    (p := fun n : Name => !([n1, n2].contains n)) (l := ds)).symm

private theorem lookup_filtered_other (ds : DS) (n1 n2 name : Name)
    (h1 : name ≠ n1) (h2 : name ≠ n2) :
    lookupDS (ds.filter (fun b => !([n1, n2].contains b.1))) name = lookupDS ds name := by
  induction ds with
  | nil => rfl
  | cons b ds ih =>
      rcases b with ⟨key, xs⟩
      by_cases hk : name = key
      · subst key
        have hcontains : ([n1, n2].contains name : Bool) = false := by simp [h1, h2]
        simp only [List.filter_cons, hcontains, Bool.not_false, ↓reduceIte,
          lookupDS_cons]
      · rw [List.filter_cons]
        split
        · simp only [lookupDS_cons, ite_eq_right hk, ih]
        · rw [lookupDS_cons, ite_eq_right hk]
          exact ih

theorem unionDS_other_lookup {ds out : DS} {n1 n2 name : Name}
    (hu : unionDS n1 n2 ds = some out) (h1 : name ≠ n1) (h2 : name ≠ n2) :
    lookupDS out name = lookupDS ds name := by
  obtain ⟨xs, ys, _, _, rfl⟩ := unionDS_components hu
  rw [lookupDS_cons, ite_eq_right h1]
  exact lookup_filtered_other ds n1 n2 name h1 h2

private theorem sameBlock_named_iff {vs : List Vertex} {ds : DS}
    (h : IsPartitionOf vs ds) {name : Name} {xs : List Vertex}
    (hx : (name, xs) ∈ ds) (v : Vertex) : SameBlock ds v name ↔ v ∈ xs := by
  constructor
  · rintro ⟨key, ys, hy, hv, hn⟩
    have he := same_member_block_eq (carrier_nodup h) hy hx hn
      (head_member (h.2.2 name xs hx))
    cases he
    exact hv
  · intro hv
    exact ⟨name, xs, hx, hv, head_member (h.2.2 name xs hx)⟩

theorem unionDS_sameBlock_iff {vs : List Vertex} {ds out : DS} {n1 n2 : Name}
    (h : IsPartitionOf vs ds) (_h1 : IsName ds n1) (_h2 : IsName ds n2)
    (_hne : n1 ≠ n2) (hu : unionDS n1 n2 ds = some out) (u v : Vertex) :
    SameBlock out u v ↔ SameBlock ds u v ∨
      (SameBlock ds u n1 ∧ SameBlock ds n2 v) ∨
      (SameBlock ds u n2 ∧ SameBlock ds n1 v) := by
  obtain ⟨xs, ys, hx, hy, rfl⟩ := unionDS_components hu
  have hxm := lookupDS_member hx
  have hym := lookupDS_member hy
  constructor
  · rintro ⟨name, zs, hz, huz, hvz⟩
    rcases List.mem_cons.mp hz with he | hz
    · cases he
      rcases List.mem_append.mp huz with hux | huy <;>
        rcases List.mem_append.mp hvz with hvx | hvy
      · exact Or.inl ⟨n1, xs, hxm, hux, hvx⟩
      · exact Or.inr (Or.inl ⟨(sameBlock_named_iff h hxm u).mpr hux,
          sameBlock_symm ((sameBlock_named_iff h hym v).mpr hvy)⟩)
      · exact Or.inr (Or.inr ⟨(sameBlock_named_iff h hym u).mpr huy,
          sameBlock_symm ((sameBlock_named_iff h hxm v).mpr hvx)⟩)
      · exact Or.inl ⟨n2, ys, hym, huy, hvy⟩
    · exact Or.inl ⟨name, zs, (List.mem_filter.mp hz).1, huz, hvz⟩
  · rintro (hold | hcross | hcross)
    · obtain ⟨name, zs, hz, huz, hvz⟩ := hold
      by_cases hn1 : name = n1
      · have he := same_name_block_eq h hz hxm hn1
        cases he
        exact ⟨n1, xs ++ ys, by simp, List.mem_append_left _ huz, List.mem_append_left _ hvz⟩
      · by_cases hn2 : name = n2
        · have he := same_name_block_eq h hz hym hn2
          cases he
          exact ⟨n1, xs ++ ys, by simp, List.mem_append_right _ huz, List.mem_append_right _ hvz⟩
        · refine ⟨name, zs, List.mem_cons_of_mem _ (List.mem_filter.mpr ⟨hz, ?_⟩), huz, hvz⟩
          simp [hn1, hn2]
    · have hux := (sameBlock_named_iff h hxm u).mp hcross.1
      have hvy := (sameBlock_named_iff h hym v).mp (sameBlock_symm hcross.2)
      exact ⟨n1, xs ++ ys, by simp, List.mem_append_left _ hux, List.mem_append_right _ hvy⟩
    · have huy := (sameBlock_named_iff h hym u).mp hcross.1
      have hvx := (sameBlock_named_iff h hxm v).mp (sameBlock_symm hcross.2)
      exact ⟨n1, xs ++ ys, by simp, List.mem_append_right _ huy, List.mem_append_left _ hvx⟩

theorem unionDS_find {vs : List Vertex} {ds out : DS} {n1 n2 : Name}
    (h : IsPartitionOf vs ds) (h1 : IsName ds n1) (h2 : IsName ds n2)
    (hne : n1 ≠ n2) (hu : unionDS n1 n2 ds = some out)
    (v : Vertex) (hv : v ∈ vs) :
    findDS out v = if findDS ds v = some n2 then some n1 else findDS ds v := by
  have hout := unionDS_partition h h1 h2 hne hu
  obtain ⟨xs, ys, hx, hy, he⟩ := unionDS_components hu
  have hxm := lookupDS_member hx
  have hym := lookupDS_member hy
  obtain ⟨name, hf⟩ := (findDS_defined_iff ds v).mpr ((carrier_mem_universe h v).mpr hv)
  obtain ⟨zs, hz, hvz⟩ := (findDS_partition_iff h v name).mp hf
  by_cases hn2 : name = n2
  · subst name
    have hzys := same_name_block_eq h hz hym rfl
    cases hzys
    rw [hf, ite_eq_left rfl]
    apply (findDS_partition_iff hout v n1).mpr
    exact ⟨xs ++ ys, by simp [he], List.mem_append_right _ hvz⟩
  · rw [hf, ite_eq_right (by simpa using hn2)]
    by_cases hn1 : name = n1
    · subst name
      have hzxs := same_name_block_eq h hz hxm rfl
      cases hzxs
      apply (findDS_partition_iff hout v n1).mpr
      exact ⟨xs ++ ys, by simp [he], List.mem_append_left _ hvz⟩
    · apply (findDS_partition_iff hout v name).mpr
      exact ⟨zs, by simp [he, hz, hn1, hn2], hvz⟩

theorem unionDS_commute_components {vs : List Vertex} {ds out12 out21 : DS} {n1 n2 : Name}
    (h : IsPartitionOf vs ds) (h1 : IsName ds n1) (h2 : IsName ds n2)
    (hne : n1 ≠ n2) (h12 : unionDS n1 n2 ds = some out12)
    (h21 : unionDS n2 n1 ds = some out21) :
    ∀ u v, SameBlock out12 u v ↔ SameBlock out21 u v := by
  intro u v
  rw [unionDS_sameBlock_iff h h1 h2 hne h12,
    unionDS_sameBlock_iff h h2 h1 (Ne.symm hne) h21]
  constructor <;> rintro (ha | hb | hc)
  · exact Or.inl ha
  · exact Or.inr (Or.inr hb)
  · exact Or.inr (Or.inl hc)
  · exact Or.inl ha
  · exact Or.inr (Or.inr hb)
  · exact Or.inr (Or.inl hc)

theorem unionDS_least_equivalence {vs : List Vertex} {ds out : DS} {n1 n2 : Name}
    (h : IsPartitionOf vs ds) (h1 : IsName ds n1) (h2 : IsName ds n2)
    (hne : n1 ≠ n2) (hu : unionDS n1 n2 ds = some out) :
    (∀ u v, SameBlock ds u v → SameBlock out u v) ∧ SameBlock out n1 n2 ∧
    ∀ R : Vertex → Vertex → Prop,
      (∀ v ∈ vs, R v v) → (∀ u v, R u v → R v u) →
      (∀ u v w, R u v → R v w → R u w) →
      (∀ u v, SameBlock ds u v → R u v) → R n1 n2 →
      ∀ u v, SameBlock out u v → R u v := by
  have hr := (sameBlock_equivalence_on h).1
  refine ⟨fun u v hh => (unionDS_sameBlock_iff h h1 h2 hne hu u v).mpr (Or.inl hh), ?_, ?_⟩
  · apply (unionDS_sameBlock_iff h h1 h2 hne hu n1 n2).mpr
    exact Or.inr (Or.inl ⟨hr n1 (name_in_universe h h1), hr n2 (name_in_universe h h2)⟩)
  · intro R _hrefl hsym htrans hold hlink u v huv
    rcases (unionDS_sameBlock_iff h h1 h2 hne hu u v).mp huv with ho | hc | hc
    · exact hold u v ho
    · exact htrans u n2 v (htrans u n1 n2 (hold u n1 hc.1) hlink) (hold n2 v hc.2)
    · exact htrans u n1 v (htrans u n2 n1 (hold u n2 hc.1) (hsym n1 n2 hlink)) (hold n1 v hc.2)

theorem connected_mono {vs : List Vertex} {old new : List (Vertex × Vertex)}
    (hsub : ∀ e ∈ old, e ∈ new) {u v : Vertex} (h : Connected vs old u v) :
    Connected vs new u v := by
  induction h with
  | refl hv => exact Connected.refl hv
  | edge hu hv he => exact Connected.edge hu hv (hsub _ he)
  | symm _ ih => exact Connected.symm ih
  | trans _ _ ih1 ih2 => exact Connected.trans ih1 ih2

theorem connected_nil_iff (vs : List Vertex) (u v : Vertex) :
    Connected vs [] u v ↔ u = v ∧ u ∈ vs := by
  constructor
  · intro h
    induction h with
    | refl hv => exact ⟨rfl, hv⟩
    | edge _ _ he => simp at he
    | symm _ ih => exact ⟨ih.1.symm, by simpa [ih.1] using ih.2⟩
    | trans _ _ ih1 ih2 => exact ⟨ih1.1.trans ih2.1, ih1.2⟩
  · rintro ⟨rfl, hu⟩
    exact Connected.refl hu

theorem sameBlock_start_iff (n u v : Int) :
    SameBlock (startDS n) u v ↔ u = v ∧ u ∈ vertices n := by
  constructor
  · rintro ⟨name, xs, hm, hu, hv⟩
    obtain ⟨w, hw, he⟩ := List.mem_map.mp hm
    cases he
    have hu' := List.mem_singleton.mp hu
    have hv' := List.mem_singleton.mp hv
    exact ⟨hu'.trans hv'.symm, by simpa [hu'] using hw⟩
  · rintro ⟨rfl, hu⟩
    exact ⟨u, [u], List.mem_map.mpr ⟨u, hu, rfl⟩, by simp, by simp⟩

theorem mergeHistory_partition {n : Int} {links : List (Name × Name)} {ds : DS}
    (h : MergeHistory n links ds) : IsPartitionOf (vertices n) ds := by
  induction h with
  | start => exact startDS_partition n
  | snoc _ h1 h2 hne hu ih => exact unionDS_partition ih h1 h2 hne hu

theorem mergeHistory_connectivity_iff {n : Int} {links : List (Name × Name)} {ds : DS}
    (h : MergeHistory n links ds) :
    ∀ u v, SameBlock ds u v ↔ Connected (vertices n) links u v := by
  induction h with
  | start =>
      intro u v
      rw [sameBlock_start_iff, connected_nil_iff]
  | @snoc links ds out a b hh ha hb hab hu ih =>
      have hp := mergeHistory_partition hh
      have ho := unionDS_partition hp ha hb hab hu
      have hc := sameBlock_equivalence_on ho
      have hleast := unionDS_least_equivalence hp ha hb hab hu
      have hlink : Connected (vertices n) (links ++ [(a, b)]) a b :=
        Connected.edge (name_in_universe hp ha) (name_in_universe hp hb) (by simp)
      have hmono {u v : Vertex} (hc : Connected (vertices n) links u v) :
          Connected (vertices n) (links ++ [(a, b)]) u v :=
        connected_mono (fun _ he => List.mem_append_left _ he) hc
      intro u v
      constructor
      · intro hs
        rcases (unionDS_sameBlock_iff hp ha hb hab hu u v).mp hs with old | cross | cross
        · exact hmono ((ih u v).mp old)
        · exact Connected.trans (Connected.trans (hmono ((ih u a).mp cross.1)) hlink)
            (hmono ((ih b v).mp cross.2))
        · exact Connected.trans (Connected.trans (hmono ((ih u b).mp cross.1)) (Connected.symm hlink))
            (hmono ((ih a v).mp cross.2))
      · intro hs
        induction hs with
        | refl hv => exact hc.1 _ hv
        | edge hv hw he =>
            rcases List.mem_append.mp he with he | he
            · exact hleast.1 _ _ ((ih _ _).mpr (Connected.edge hv hw he))
            · have he' := List.mem_singleton.mp he
              cases he'
              exact hleast.2.1
        | symm _ ihs => exact hc.2.1 _ _ ihs
        | trans _ _ ih1 ih2 => exact hc.2.2.1 _ _ _ ih1 ih2

theorem mergeHistory_find_iff_connected {n : Int} {links : List (Name × Name)} {ds : DS}
    (h : MergeHistory n links ds) {u v : Vertex} (hu : u ∈ vertices n) (hv : v ∈ vertices n) :
    findDS ds u = findDS ds v ↔ Connected (vertices n) links u v := by
  rw [findDS_equal_iff_sameBlock (mergeHistory_partition h) hu hv,
    mergeHistory_connectivity_iff h]

theorem mergeHistory_block_count {n : Int} {links : List (Name × Name)} {ds : DS}
    (h : MergeHistory n links ds) : ds.length + links.length = n.toNat := by
  induction h with
  | start => simpa using startDS_length n
  | snoc hh ha hb hab hu ih =>
      have hc := unionDS_block_count (mergeHistory_partition hh) ha hb hab hu
      simp only [List.length_append, List.length_singleton]
      omega

theorem mergeHistory_link_bound {n : Int} {links : List (Name × Name)} {ds : DS}
    (h : MergeHistory n links ds) : links.length ≤ n.toNat := by
  have hc := mergeHistory_block_count h
  omega

/-! Ten diagnostic groups. These are statements about these actual executors,
not tests of the array variant and not evidence of an operation/runtime bound. -/

-- D1: the printed positive domain and explicit empty signed-bound extensions.
example : startDS 0 = [] ∧ startDS (-3) = [] ∧ startDS 1 = [(1, [1])] ∧
    IsPartitionOf [1] (startDS 1) := by
  exact ⟨rfl, rfl, rfl, startDS_partition 1⟩

-- D2: genuine merge, representative lookup, and independent output validity.
example : unionDS 1 2 (startDS 3) = some [(1, [1, 2]), (3, [3])] ∧
    findDS [(1, [1, 2]), (3, [3])] 2 = some 1 ∧
    IsPartitionOf [1, 2, 3] [(1, [1, 2]), (3, [3])] := by
  exact ⟨rfl, rfl, unionDS_partition (n1 := 1) (n2 := 2) (startDS_partition 3)
    (by unfold IsName; decide) (by unfold IsName; decide) (by decide) rfl⟩

-- D3: component equality does not mean equal names or equal returned lists.
example : unionDS 2 1 (startDS 3) = some [(2, [2, 1]), (3, [3])] ∧
    unionDS 2 1 (startDS 3) ≠ unionDS 1 2 (startDS 3) ∧
    ∀ u v, SameBlock [(1, [1, 2]), (3, [3])] u v ↔
      SameBlock [(2, [2, 1]), (3, [3])] u v := by
  exact ⟨rfl, by decide, unionDS_commute_components (n1 := 1) (n2 := 2) (startDS_partition 3)
    (by unfold IsName; decide) (by unfold IsName; decide) (by decide) rfl rfl⟩

-- D4: merged block first; untouched blocks retain their exact source order.
example : unionDS 4 2 (startDS 5) =
    some [(4, [4, 2]), (1, [1]), (3, [3]), (5, [5])] := rfl

-- D5: same-name union really duplicates a block, despite successful lookups.
example : unionDS 1 1 (startDS 2) = some [(1, [1, 1]), (2, [2])] ∧
    ¬ IsPartitionOf [1, 2] [(1, [1, 1]), (2, [2])] := by
  refine ⟨rfl, ?_⟩
  intro h
  have hc := h.2.1.length_eq
  simp [carrier] at hc

-- D6: absent names and vertices do not acquire a shared represented component.
example : lookupDS (startDS 2) 3 = none ∧ unionDS 1 3 (startDS 2) = none ∧
    findDS (startDS 2) 0 = findDS (startDS 2) 3 ∧ ¬ SameBlock (startDS 2) 0 3 := by
  refine ⟨rfl, rfl, rfl, ?_⟩
  intro hs
  have hm := (sameBlock_equivalence_on (startDS_partition 2)).2.2.2 0 3 hs
  have hv := (mem_vertices_iff 2 0).mp hm.1
  omega

-- D7: literal first matches and removal of every matching key on malformed data.
example : findDS [(1, [1, 2]), (2, [2, 3])] 2 = some 1 ∧
    unionDS 1 2 [(1, [1]), (1, [4]), (2, [2])] = some [(1, [1, 2])] ∧
    4 ∉ carrier [(1, [1, 2])] := by
  exact ⟨rfl, rfl, by decide⟩

-- D8: a stored key need not itself be a represented member on malformed inputs.
example : findDS [(7, [1]), (2, [2])] 1 = some 7 ∧
    findDS [(7, [1]), (2, [2])] 7 = none := by
  exact ⟨rfl, rfl⟩

-- D9: the source list union keeps the first name even when its set is smaller.
example : unionDS 1 2 [(1, [1]), (2, [2, 3])] = some [(1, [1, 2, 3])] := rfl

private def figureList1 : DS := [(1, [1, 2]), (3, [3]), (4, [4]), (5, [5]), (6, [6]), (7, [7])]
private def figureList2 : DS := [(6, [6, 7]), (1, [1, 2]), (3, [3]), (4, [4]), (5, [5])]
private def figureList3 : DS := [(3, [3, 6, 7]), (1, [1, 2]), (4, [4]), (5, [5])]
private def figureList4 : DS := [(1, [1, 2, 3, 6, 7]), (4, [4]), (5, [5])]

-- D10: Figure9.1's array name schedule is not the list schedule. The fourth
-- list call is explicitly adapted from (1,6) to (1,3); the array example remains open.
example : unionDS 1 2 (startDS 7) = some figureList1 ∧
    unionDS 6 7 figureList1 = some figureList2 ∧
    unionDS 3 6 figureList2 = some figureList3 ∧
    unionDS 1 6 figureList3 = none ∧ unionDS 1 3 figureList3 = some figureList4 ∧
    MergeHistory 7 [(1, 2), (6, 7), (3, 6), (1, 3)] figureList4 ∧
    ∀ u v, SameBlock figureList4 u v ↔
      Connected (vertices 7) [(1, 2), (6, 7), (3, 6), (1, 3)] u v := by
  have h1 : MergeHistory 7 [(1, 2)] figureList1 :=
    MergeHistory.snoc MergeHistory.start (by unfold IsName; decide) (by unfold IsName; decide) (by decide) rfl
  have h2 : MergeHistory 7 [(1, 2), (6, 7)] figureList2 :=
    MergeHistory.snoc h1 (by unfold IsName; decide) (by unfold IsName; decide) (by decide) rfl
  have h3 : MergeHistory 7 [(1, 2), (6, 7), (3, 6)] figureList3 :=
    MergeHistory.snoc h2 (by unfold IsName; decide) (by unfold IsName; decide) (by decide) rfl
  have h4 : MergeHistory 7 [(1, 2), (6, 7), (3, 6), (1, 3)] figureList4 :=
    MergeHistory.snoc h3 (by unfold IsName; decide) (by unfold IsName; decide) (by decide) rfl
  exact ⟨rfl, rfl, rfl, rfl, rfl, h4, mergeHistory_connectivity_iff h4⟩

end Connectivity.ListPartition
