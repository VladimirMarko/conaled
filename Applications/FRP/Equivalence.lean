import Mathlib

/-!
# The two event denotations in Elliott's 2015 talks

Adapted from the untypechecked historical draft in docs/history/frp/.
Checked with the repository toolchain; included in the project proof audit.
There are no `sorry`s, new axioms, or assumed equivalence theorems in this file.
Classical choice is used only to construct mathematical denotations.

`CoList` represents total finite or omega-long lists.  It does not represent
Haskell bottom, partial spines, or partial elements.

The main equivalence is `eventEquiv`.  Its right side has precisely the
finite-predecessor condition, NOT the stronger finite-history condition.
-/

noncomputable section
open Classical

namespace FRP

attribute [local instance] Classical.propDecidable

/-- An initial segment of the natural numbers, with a value at every live index.
This admits finite lists, the empty list, and infinite lists. -/
structure CoList (A : Type) where
  live : ℕ → Prop
  initial : ∀ {i j : ℕ}, i ≤ j → live j → live i
  value : {i : ℕ // live i} → A

namespace CoList
abbrev Pos {A : Type} (s : CoList A) := {i : ℕ // s.live i}

/-- An extensional observation. `none` means END, not unknown or divergence. -/
def get? {A : Type} (s : CoList A) (n : ℕ) : Option A :=
  if h : s.live n then some (s.value ⟨n, h⟩) else none

def nil {A : Type} : CoList A where
  live := fun _ => False
  initial := by intros; assumption
  value := fun i => False.elim i.property

def ofStream {A : Type} (f : ℕ → A) : CoList A where
  live := fun _ => True
  initial := by intros; trivial
  value := fun i => f i.val

def map {A B : Type} (f : A → B) (s : CoList A) : CoList B where
  live := s.live
  initial := s.initial
  value := f ∘ s.value

/-- No coinductive primitive is required: equality is equality at all indices. -/
theorem ext {A : Type} (s t : CoList A)
    (hdom : ∀ n, s.live n ↔ t.live n)
    (hval : ∀ n (hs : s.live n) (ht : t.live n),
      s.value ⟨n, hs⟩ = t.value ⟨n, ht⟩) : s = t := by
  cases s with
  | mk p hp f =>
    cases t with
    | mk q hq g =>
      dsimp at hdom hval
      have hpq : p = q := funext (fun n => propext (hdom n))
      subst q
      have hfg : f = g := by
        funext i
        exact hval i.val i.property i.property
      subst g
      rfl

@[simp] theorem map_id {A : Type} (s : CoList A) : map id s = s := by
  cases s
  rfl

@[simp] theorem map_comp {A B C : Type} (f : A → B) (g : B → C)
    (s : CoList A) : map g (map f s) = map (g ∘ f) s := by
  rfl
end CoList

/-! ## An order-theoretic enumeration lemma

A linearly ordered set is a finite or omega-long list of positions precisely
when every element has finitely many strict predecessors.  The enumeration
number of x is the number of its predecessors.
-/

def FinitePred (X : Type) [LinearOrder X] : Prop :=
  ∀ x : X, (Set.Iio x).Finite

namespace Numbering
variable {X Y : Type} [LinearOrder X] [LinearOrder Y]

def pred (h : FinitePred X) (x : X) : Finset X := (h x).toFinset

def rank (h : FinitePred X) (x : X) : ℕ := (pred h x).card

@[simp] theorem mem_pred (h : FinitePred X) (x y : X) :
    y ∈ pred h x ↔ y < x := by
  simp [pred]

theorem rank_strictMono (h : FinitePred X) : StrictMono (rank h) := by
  intro x y hxy
  apply Finset.card_lt_card
  apply Finset.ssubset_iff_subset_ne.mpr
  constructor
  · intro z hz
    exact (mem_pred h y z).mpr (lt_trans ((mem_pred h x z).mp hz) hxy)
  · intro heq
    have hx : x ∈ pred h y := (mem_pred h y x).mpr hxy
    rw [← heq] at hx
    exact (lt_irrefl x) ((mem_pred h x x).mp hx)

/-- No gaps in the range of rank.  Proof: use the largest predecessor, then
strong induction on the number of predecessors. -/
theorem rank_initial_lt (h : FinitePred X) (y : X) (n : ℕ)
    (hn : n < rank h y) : ∃ x : X, rank h x = n := by
  have aux : ∀ m : ℕ, ∀ y : X, rank h y = m →
      ∀ n : ℕ, n < m → ∃ x : X, rank h x = n := by
    intro m
    induction m using Nat.strong_induction_on with
    | h m ih =>
      intro y hym n hn
      have hpos : 0 < (pred h y).card := by
        change 0 < rank h y
        omega
      have hne : (pred h y).Nonempty := Finset.card_pos.mp hpos
      let x : X := (pred h y).max' hne
      have hxm : x ∈ pred h y := Finset.max'_mem _ _
      have hxy : x < y := (mem_pred h y x).mp hxm
      have hset : pred h y = insert x (pred h x) := by
        ext z
        constructor
        · intro hz
          have hzx : z ≤ x := Finset.le_max' _ _ hz
          rcases lt_or_eq_of_le hzx with hzlt | hzeq
          · exact Finset.mem_insert.mpr (Or.inr ((mem_pred h x z).mpr hzlt))
          · exact Finset.mem_insert.mpr (Or.inl hzeq)
        · intro hz
          rcases Finset.mem_insert.mp hz with hzx | hzlt
          · simpa [hzx] using hxm
          · exact (mem_pred h y z).mpr
              (lt_trans ((mem_pred h x z).mp hzlt) hxy)
      have hnot : x ∉ pred h x := by simp
      have hr : rank h y = rank h x + 1 := by
        unfold rank
        rw [hset, Finset.card_insert_of_notMem hnot]
      by_cases heq : n = rank h x
      · exact ⟨x, heq.symm⟩
      · have hnx : n < rank h x := by omega
        have hxm' : rank h x < m := by omega
        exact ih (rank h x) hxm' x rfl n hnx
  exact aux (rank h y) y rfl n hn

theorem rank_initial (h : FinitePred X) (y : X) (n : ℕ)
    (hn : n ≤ rank h y) : ∃ x : X, rank h x = n := by
  rcases lt_or_eq_of_le hn with hlt | heq
  · exact rank_initial_lt h y n hlt
  · exact ⟨y, heq.symm⟩

/-- Pull back finite predecessor sets through a strictly increasing map. -/
theorem finitePred_of_strictMono (hY : FinitePred Y) (f : X → Y)
    (hf : StrictMono f) : FinitePred X := by
  intro x
  have hp : (f ⁻¹' Set.Iio (f x)).Finite :=
    Set.Finite.preimage hf.injective.injOn (hY (f x))
  have heq : f ⁻¹' Set.Iio (f x) = Set.Iio x := by
    ext z
    exact hf.lt_iff_lt
  rwa [heq] at hp

/-- Rank is invariant under order isomorphism. -/
theorem rank_iso (hX : FinitePred X) (hY : FinitePred Y)
    (e : X ≃o Y) (x : X) : rank hX x = rank hY (e x) := by
  unfold rank
  apply Finset.card_bij (fun z _ => e z)
  · intro z hz
    exact (mem_pred hY (e x) (e z)).mpr
      (e.strictMono ((mem_pred hX x z).mp hz))
  · intro a ha b hb hab
    exact e.injective hab
  · intro y hy
    refine ⟨e.symm y, ?_, e.apply_symm_apply y⟩
    apply (mem_pred hX x (e.symm y)).mpr
    have hylt := (mem_pred hY (e x) y).mp hy
    have hh := e.symm.strictMono hylt
    simpa using hh

/-- Canonically turn a labelled finite-predecessor order into a co-list. -/
def linearize {A : Type} (h : FinitePred X) (v : X → A) : CoList A where
  live := fun n => ∃ x : X, rank h x = n
  initial := by
    intro i j hij hj
    rcases hj with ⟨y, hy⟩
    exact rank_initial h y i (by omega)
  value := fun i => v (Classical.choose i.property)

/-- The canonical increasing bijection from the original positions to indices. -/
def indexIso {A : Type} (h : FinitePred X) (v : X → A) :
    X ≃o (linearize h v).Pos where
  toFun := fun x => ⟨rank h x, ⟨x, rfl⟩⟩
  invFun := fun i => Classical.choose i.property
  left_inv := by
    intro x
    apply (rank_strictMono h).injective
    exact Classical.choose_spec (show ∃ y, rank h y = rank h x from ⟨x, rfl⟩)
  right_inv := by
    intro i
    apply Subtype.ext
    exact Classical.choose_spec i.property
  map_rel_iff' := by
    intro x y
    change rank h x ≤ rank h y ↔ x ≤ y
    exact (rank_strictMono h).le_iff_le

@[simp] theorem linearize_value {A : Type} (h : FinitePred X)
    (v : X → A) (x : X) :
    (linearize h v).value (indexIso h v x) = v x := by
  change v ((indexIso h v).symm (indexIso h v x)) = v x
  rw [OrderIso.symm_apply_apply]

end Numbering

namespace CoList
variable {A B : Type}

theorem finitePred (s : CoList A) : FinitePred s.Pos := by
  apply Numbering.finitePred_of_strictMono
    (X := s.Pos) (Y := ℕ) (fun n => Set.finite_Iio n)
    (fun i => i.val)
  intro i j hij
  exact hij

/-- In an initial segment of naturals, rank is the index itself. -/
theorem rank_pos (s : CoList A) (i : s.Pos) :
    Numbering.rank s.finitePred i = i.val := by
  unfold Numbering.rank
  have hc : (Numbering.pred s.finitePred i).card = (Finset.range i.val).card := by
    apply Finset.card_bij (fun j _ => j.val)
    · intro j hj
      exact Finset.mem_range.mpr ((Numbering.mem_pred s.finitePred i j).mp hj)
    · intro j hj k hk h
      exact Subtype.ext h
    · intro n hn
      have hni : n < i.val := Finset.mem_range.mp hn
      let j : s.Pos := ⟨n, s.initial (Nat.le_of_lt hni) i.property⟩
      refine ⟨j, ?_, rfl⟩
      exact (Numbering.mem_pred _ _ _).mpr hni
  simpa using hc

/-- Order isomorphisms between initial segments preserve the literal indices. -/
theorem iso_index (s : CoList A) (t : CoList B)
    (e : s.Pos ≃o t.Pos) (i : s.Pos) : (e i).val = i.val := by
  have h := Numbering.rank_iso s.finitePred t.finitePred e i
  simpa only [rank_pos] using h.symm

/-- Two co-lists with order-isomorphic, equally-labelled positions are equal. -/
theorem eq_of_iso (s t : CoList A) (e : s.Pos ≃o t.Pos)
    (hv : ∀ i, t.value (e i) = s.value i) : s = t := by
  have hd : ∀ n, s.live n ↔ t.live n := by
    intro n
    constructor
    · intro hn
      have h := (e ⟨n, hn⟩).property
      simpa only [iso_index s t e ⟨n, hn⟩] using h
    · intro hn
      have h := (e.symm ⟨n, hn⟩).property
      simpa only [iso_index t s e.symm ⟨n, hn⟩] using h
  apply ext s t hd
  intro n hs ht
  have he : e ⟨n, hs⟩ = (⟨n, ht⟩ : t.Pos) :=
    Subtype.ext (iso_index s t e ⟨n, hs⟩)
  have h := hv ⟨n, hs⟩
  rw [he] at h
  exact h.symm
end CoList

/-! ## Old and new event carriers -/

abbrev Behavior (T A : Type) := T → A

/-- Literally the total-spine reading of [(T,A)] with non-decreasing times. -/
structure OldEvent (T A : Type) [LinearOrder T] where
  seq : CoList (T × A)
  ordered : Monotone (fun i : seq.Pos => (seq.value i).1)

namespace OldEvent
variable {T A : Type} [LinearOrder T]
abbrev Pos (e : OldEvent T A) := e.seq.Pos

def time (e : OldEvent T A) (i : e.Pos) : T := (e.seq.value i).1
def value (e : OldEvent T A) (i : e.Pos) : A := (e.seq.value i).2

/-- This is EXTRA structure; it is not part of `OldEvent`. -/
def FiniteHistory (e : OldEvent T A) : Prop :=
  ∀ t : T, {i : e.Pos | e.time i < t}.Finite

abbrev Fiber (e : OldEvent T A) (t : T) := {i : e.Pos // e.time i = t}

theorem fiber_finitePred (e : OldEvent T A) (t : T) :
    FinitePred (e.Fiber t) := by
  apply Numbering.finitePred_of_strictMono e.seq.finitePred (fun i => i.val)
  intro i j hij
  exact hij

/-- Group the occurrences at each timestamp, preserving their original order.
The result's batches can still be infinite. -/
def group (e : OldEvent T A) : T → CoList A := fun t =>
  Numbering.linearize (e.fiber_finitePred t) (fun i => e.value i.val)

end OldEvent

abbrev Batch (T A : Type) := T → CoList A

namespace Batch
variable {T A : Type} [LinearOrder T]

/-- The occurrences, not just the support times.  Lexicographic order retains
both temporal order and the order of simultaneous occurrences. -/
abbrev Occ (b : Batch T A) :=
  {p : T ×ₗ ℕ // (b (ofLex p).1).live (ofLex p).2}

namespace Occ
omit [LinearOrder T] in
section

def time {b : Batch T A} (p : b.Occ) : T := (ofLex p.val).1
def index {b : Batch T A} (p : b.Occ) : ℕ := (ofLex p.val).2

def localPos {b : Batch T A} (p : b.Occ) : (b p.time).Pos :=
  ⟨p.index, p.property⟩

def value {b : Batch T A} (p : b.Occ) : A := (b p.time).value p.localPos

def mk (b : Batch T A) (t : T) (i : (b t).Pos) : b.Occ :=
  ⟨toLex (t, i.val), i.property⟩

@[simp] theorem time_mk (b : Batch T A) (t : T) (i : (b t).Pos) :
    (mk b t i).time = t := rfl
@[simp] theorem index_mk (b : Batch T A) (t : T) (i : (b t).Pos) :
    (mk b t i).index = i.val := rfl
@[simp] theorem value_mk (b : Batch T A) (t : T) (i : (b t).Pos) :
    (mk b t i).value = (b t).value i := rfl

@[simp] theorem mk_localPos (b : Batch T A) (p : b.Occ) :
    mk b p.time p.localPos = p := by
  apply Subtype.ext
  rfl

end

theorem le_iff {b : Batch T A} (p q : b.Occ) :
    p ≤ q ↔ p.time < q.time ∨ p.time = q.time ∧ p.index ≤ q.index := by
  exact Prod.Lex.le_iff

theorem lt_iff {b : Batch T A} (p q : b.Occ) :
    p < q ↔ p.time < q.time ∨ p.time = q.time ∧ p.index < q.index := by
  exact Prod.Lex.lt_iff

theorem same_time_le {b : Batch T A} {t : T} (i j : (b t).Pos) :
    mk b t i ≤ mk b t j ↔ i ≤ j := by
  rw [le_iff]
  simp

end Occ

/-- THE EXACT image condition for total sorted co-lists. -/
def Admissible (b : Batch T A) : Prop := FinitePred b.Occ

/-- The stronger, separately named total-finite-history condition. -/
def FiniteHistory (b : Batch T A) : Prop :=
  ∀ t : T, {p : b.Occ | p.time < t}.Finite

/-- Flatten an admissible batch function by chronological rank. -/
def flatten (b : Batch T A) (h : b.Admissible) : OldEvent T A where
  seq := Numbering.linearize h (fun p => (p.time, p.value))
  ordered := by
    intro i j hij
    let r := Numbering.indexIso h (fun p : b.Occ => (p.time, p.value))
    have hpq : r.symm i ≤ r.symm j := r.symm.monotone hij
    have ht := (Occ.le_iff (r.symm i) (r.symm j)).mp hpq
    change (r.symm i).time ≤ (r.symm j).time
    rcases ht with ht | ⟨ht, _⟩
    · exact le_of_lt ht
    · exact le_of_eq ht
end Batch

/-! ## A timestamp- and value-preserving order isomorphism

This is a relational characterization of grouping.  Neither direction of the
main theorem is assumed by this definition.
-/

structure Realization {T A : Type} [LinearOrder T]
    (e : OldEvent T A) (b : Batch T A) where
  iso : e.Pos ≃o b.Occ
  time_eq : ∀ i, (iso i).time = e.time i
  value_eq : ∀ i, (iso i).value = e.value i

namespace Realization
variable {T A : Type} [LinearOrder T]

/-- Canonical flattening is a realization. -/
def flatten (b : Batch T A) (h : b.Admissible) :
    Realization (b.flatten h) b where
  iso := (Numbering.indexIso h (fun p : b.Occ => (p.time, p.value))).symm
  time_eq := by intro i; rfl
  value_eq := by intro i; rfl

/-- A realization makes the target admissible. -/
theorem admissible {e : OldEvent T A} {b : Batch T A}
    (r : Realization e b) : b.Admissible :=
  Numbering.finitePred_of_strictMono e.seq.finitePred r.iso.symm r.iso.symm.strictMono

/-- For fixed batches there is only one old event realization. -/
theorem old_unique {e f : OldEvent T A} {b : Batch T A}
    (r : Realization e b) (s : Realization f b) : e = f := by
  have hs : e.seq = f.seq := by
    apply CoList.eq_of_iso e.seq f.seq (r.iso.trans s.iso.symm)
    intro i
    apply Prod.ext
    · change f.time (s.iso.symm (r.iso i)) = e.time i
      have h := s.time_eq (s.iso.symm (r.iso i))
      simp only [OrderIso.apply_symm_apply] at h
      exact h.symm.trans (r.time_eq i)
    · change f.value (s.iso.symm (r.iso i)) = e.value i
      have h := s.value_eq (s.iso.symm (r.iso i))
      simp only [OrderIso.apply_symm_apply] at h
      exact h.symm.trans (r.value_eq i)
  cases e
  cases f
  cases hs
  rfl

/-- Restrict a realization to one timestamp. -/
def fiberIso {e : OldEvent T A} {b : Batch T A}
    (r : Realization e b) (t : T) : e.Fiber t ≃o (b t).Pos where
  toFun := fun i =>
    ⟨(r.iso i.val).index, by
      have ht : (r.iso i.val).time = t := (r.time_eq i.val).trans i.property
      have hp := (r.iso i.val).property
      change (b (r.iso i.val).time).live (r.iso i.val).index at hp
      simpa only [ht] using hp⟩
  invFun := fun j =>
    ⟨r.iso.symm (Batch.Occ.mk b t j), by
      have h := r.time_eq (r.iso.symm (Batch.Occ.mk b t j))
      simpa using h.symm⟩
  left_inv := by
    intro i
    apply Subtype.ext
    apply r.iso.injective
    simp only [OrderIso.apply_symm_apply]
    apply Subtype.ext
    apply Prod.ext
    · exact ((r.time_eq i.val).trans i.property).symm
    · rfl
  right_inv := by
    intro j
    apply Subtype.ext
    simp only [OrderIso.apply_symm_apply, Batch.Occ.index_mk]
  map_rel_iff' := by
    intro i j
    have hti : (r.iso i.val).time = t := (r.time_eq i.val).trans i.property
    have htj : (r.iso j.val).time = t := (r.time_eq j.val).trans j.property
    change (r.iso i.val).index ≤ (r.iso j.val).index ↔ i.val ≤ j.val
    have h := r.iso.le_iff_le (x := i.val) (y := j.val)
    rw [Batch.Occ.le_iff, hti, htj] at h
    simpa using h

theorem fiber_value {e : OldEvent T A} {b : Batch T A}
    (r : Realization e b) (t : T) (i : e.Fiber t) :
    (b t).value (r.fiberIso t i) = e.value i.val := by
  have ht : (r.iso i.val).time = t := (r.time_eq i.val).trans i.property
  have h := r.value_eq i.val
  unfold Batch.Occ.value Batch.Occ.localPos at h
  have transport : ∀ (u v : T) (huv : u = v) (n : ℕ)
      (hu : (b u).live n) (hv : (b v).live n),
      (b v).value ⟨n, hv⟩ = (b u).value ⟨n, hu⟩ := by
    intro u v huv n hu hv
    subst v
    rfl
  exact (transport _ _ ht _ _ _).trans h

/-- For a fixed old event the batches are unique, including order and duplicates. -/
theorem batch_unique {e : OldEvent T A} {b c : Batch T A}
    (r : Realization e b) (s : Realization e c) : b = c := by
  funext t
  let er := r.fiberIso t
  let es := s.fiberIso t
  apply CoList.eq_of_iso (b t) (c t) (er.symm.trans es)
  intro i
  have hs := s.fiber_value t (er.symm i)
  have hr := r.fiber_value t (er.symm i)
  change (b t).value (er (er.symm i)) = e.value (er.symm i).val at hr
  rw [OrderIso.apply_symm_apply] at hr
  exact hs.trans hr.symm

end Realization

namespace OldEvent
variable {T A : Type} [LinearOrder T]

/-- Splitting a position into its timestamp and the corresponding fiber. -/
def splitFiber (e : OldEvent T A) : (Σ t : T, e.Fiber t) ≃ e.Pos where
  toFun := fun p => p.2.val
  invFun := fun i => ⟨e.time i, ⟨i, rfl⟩⟩
  left_inv := by
    rintro ⟨t, i, hi⟩
    cases hi
    rfl
  right_inv := by intro i; rfl

/-- Number all fibers independently. -/
def numberFibers (e : OldEvent T A) :
    (Σ t : T, e.Fiber t) ≃ (Σ t : T, (e.group t).Pos) where
  toFun := fun p => ⟨p.1,
    Numbering.indexIso (e.fiber_finitePred p.1) (fun i => e.value i.val) p.2⟩
  invFun := fun p => ⟨p.1,
    (Numbering.indexIso (e.fiber_finitePred p.1) (fun i => e.value i.val)).symm p.2⟩
  left_inv := by
    rintro ⟨t, i⟩
    simp only [OrderIso.symm_apply_apply]
  right_inv := by
    rintro ⟨t, i⟩
    exact congrArg (fun j => Sigma.mk t j)
      ((Numbering.indexIso (e.fiber_finitePred t) (fun i => e.value i.val)).apply_symm_apply i)

end OldEvent

namespace Batch
variable {T A : Type} [LinearOrder T]

def sigmaOcc (b : Batch T A) : (Σ t : T, (b t).Pos) ≃ b.Occ where
  toFun := fun p => Occ.mk b p.1 p.2
  invFun := fun p => ⟨p.time, p.localPos⟩
  left_inv := by rintro ⟨t, n, hn⟩; rfl
  right_inv := by intro p; exact Occ.mk_localPos b p
end Batch

namespace OldEvent
variable {T A : Type} [LinearOrder T]

/-- Grouping at the level of occurrences, before proving it preserves order. -/
def groupEquiv (e : OldEvent T A) : e.Pos ≃ (Batch.Occ e.group) :=
  e.splitFiber.symm.trans (e.numberFibers.trans (Batch.sigmaOcc e.group))

/-- The inverse equivalence preserves chronological order.  At unequal times
this follows from non-decreasing timestamps; at equal times it follows from
the increasing numbering of a fiber. -/
def ungroupIso (e : OldEvent T A) : (Batch.Occ e.group) ≃o e.Pos where
  toEquiv := e.groupEquiv.symm
  map_rel_iff' := by
    rintro ⟨⟨t, n⟩, hn⟩ ⟨⟨u, m⟩, hm⟩
    let rt := Numbering.indexIso (e.fiber_finitePred t) (fun i => e.value i.val)
    let ru := Numbering.indexIso (e.fiber_finitePred u) (fun i => e.value i.val)
    let i : e.Fiber t := rt.symm ⟨n, hn⟩
    let j : e.Fiber u := ru.symm ⟨m, hm⟩
    change i.val ≤ j.val ↔ toLex (t, n) ≤ toLex (u, m)
    rw [Prod.Lex.toLex_le_toLex]
    constructor
    · intro hij
      have htu : t ≤ u := by
        have h := e.ordered hij
        change e.time i.val ≤ e.time j.val at h
        simpa only [i.property, j.property] using h
      rcases lt_or_eq_of_le htu with hlt | heq
      · exact Or.inl hlt
      · right
        refine ⟨heq, ?_⟩
        subst u
        change (rt.symm ⟨n, hn⟩).val ≤ (rt.symm ⟨m, hm⟩).val at hij
        have h' : rt.symm ⟨n, hn⟩ ≤ rt.symm ⟨m, hm⟩ := hij
        have hh := rt.monotone h'
        have hhval := (show (rt (rt.symm ⟨n, hn⟩)).val ≤
          (rt (rt.symm ⟨m, hm⟩)).val from hh)
        simpa only [OrderIso.apply_symm_apply] using hhval
    · intro hpq
      rcases hpq with htu | ⟨htu, hnm⟩
      · by_contra hij
        have hji : j.val ≤ i.val := le_of_lt (lt_of_not_ge hij)
        have h := e.ordered hji
        change e.time j.val ≤ e.time i.val at h
        have hut : u ≤ t := by simpa only [i.property, j.property] using h
        exact (not_le_of_gt htu) hut
      · change t = u at htu
        subst u
        have h' : (⟨n, hn⟩ : (e.group t).Pos) ≤ ⟨m, hm⟩ := hnm
        exact rt.symm.monotone h'

/-- Grouping itself, now as an order isomorphism. -/
def groupIso (e : OldEvent T A) : e.Pos ≃o (Batch.Occ e.group) := e.ungroupIso.symm

theorem ungroup_time (e : OldEvent T A) (p : (Batch.Occ e.group)) :
    e.time (e.ungroupIso p) = p.time := by
  exact ((Numbering.indexIso (e.fiber_finitePred p.time)
    (fun i => e.value i.val)).symm p.localPos).property

theorem ungroup_value (e : OldEvent T A) (p : (Batch.Occ e.group)) :
    e.value (e.ungroupIso p) = p.value := by
  rfl

def groupRealization (e : OldEvent T A) : Realization e e.group where
  iso := e.groupIso
  time_eq := by
    intro i
    have h := e.ungroup_time (e.groupIso i)
    change e.time (e.ungroupIso (e.ungroupIso.symm i)) = (e.groupIso i).time at h
    simpa using h.symm
  value_eq := by
    intro i
    have h := e.ungroup_value (e.groupIso i)
    change e.value (e.ungroupIso (e.ungroupIso.symm i)) = (e.groupIso i).value at h
    simpa using h.symm

theorem group_admissible (e : OldEvent T A) : Batch.Admissible e.group :=
  e.groupRealization.admissible

end OldEvent

/-! ## The main isomorphism, with both inverse laws -/

variable {T A : Type} [LinearOrder T]

/-- Precise completion of the new representation for the BARE old carrier. -/
def NewEvent (T A : Type) [LinearOrder T] :=
  {b : Batch T A // b.Admissible}

def toNew (e : OldEvent T A) : NewEvent T A :=
  ⟨e.group, e.group_admissible⟩

def toOld (b : NewEvent T A) : OldEvent T A := b.val.flatten b.property

theorem toOld_toNew (e : OldEvent T A) : toOld (toNew e) = e := by
  exact Realization.old_unique
    (Realization.flatten e.group e.group_admissible) e.groupRealization

theorem toNew_toOld (b : NewEvent T A) : toNew (toOld b) = b := by
  apply Subtype.ext
  exact Realization.batch_unique (toOld b).groupRealization
    (Realization.flatten b.val b.property)

/-- The exact representation equivalence.  In particular this theorem does
not discard a Zeno list or an infinite final batch. -/
def eventEquiv : OldEvent T A ≃ NewEvent T A where
  toFun := toNew
  invFun := toOld
  left_inv := toOld_toNew
  right_inv := toNew_toOld

/-! ## Transport of finite histories

These are restrictions of the equivalence, not premises smuggled into it.
-/

namespace Realization

theorem finiteHistory_iff {e : OldEvent T A} {b : Batch T A}
    (r : Realization e b) : e.FiniteHistory ↔ b.FiniteHistory := by
  have hs : ∀ t : T,
      r.iso '' {i : e.Pos | e.time i < t} = {p : b.Occ | p.time < t} := by
    intro t
    ext p
    constructor
    · rintro ⟨i, hi, rfl⟩
      change (r.iso i).time < t
      rw [r.time_eq]
      exact hi
    · intro hp
      refine ⟨r.iso.symm p, ?_, r.iso.apply_symm_apply p⟩
      have h := r.time_eq (r.iso.symm p)
      simp only [OrderIso.apply_symm_apply] at h
      change e.time (r.iso.symm p) < t
      rw [← h]
      exact hp
  constructor
  · intro he t
    rw [← hs t]
    exact (he t).image r.iso
  · intro hb t
    have hf : (r.iso '' {i : e.Pos | e.time i < t}).Finite := by
      rw [hs t]
      exact hb t
    exact hf.of_finite_image r.iso.injective.injOn

end Realization

/-- The restriction of `eventEquiv` to the finite-history fragment. -/
def finiteHistoryEquiv :
    {e : OldEvent T A // e.FiniteHistory} ≃
      {b : NewEvent T A // b.val.FiniteHistory} where
  toFun := fun e => ⟨toNew e.val,
    e.val.groupRealization.finiteHistory_iff.mp e.property⟩
  invFun := fun b => ⟨toOld b.val,
    (Realization.flatten b.val.val b.val.property).finiteHistory_iff.mpr b.property⟩
  left_inv := by
    intro e
    apply Subtype.ext
    exact toOld_toNew e.val
  right_inv := by
    intro b
    apply Subtype.ext
    exact toNew_toOld b.val

/-! ## Behavior equations: the old formulas are the Reader operations -/
namespace Behavior
omit [LinearOrder T] in
section
variable {B C : Type}

def time : Behavior T T := id

def pure (a : A) : Behavior T A := fun _ => a

def map (f : A → B) (x : Behavior T A) : Behavior T B := f ∘ x

def ap (f : Behavior T (A → B)) (x : Behavior T A) : Behavior T B :=
  fun t => f t (x t)

def lift2 (f : A → B → C) (x : Behavior T A) (y : Behavior T B) : Behavior T C :=
  fun t => f (x t) (y t)

def timeTrans (x : Behavior T A) (u : Behavior T T) : Behavior T A := x ∘ u

theorem lift2_eq_ap (f : A → B → C) (x : Behavior T A) (y : Behavior T B) :
    lift2 f x y = ap (map f x) y := rfl

theorem old_lift0 (a : A) : pure (T := T) a = fun _ => a := rfl

theorem old_lift1 (f : A → B) (x : Behavior T A) :
    map f x = fun t => f (x t) := rfl

theorem old_lift2 (f : A → B → C) (x : Behavior T A) (y : Behavior T B) :
    lift2 f x y = fun t => f (x t) (y t) := rfl

theorem old_timeTrans (x : Behavior T A) (u : Behavior T T) :
    timeTrans x u = fun t => x (u t) := rfl
end
end Behavior


/-! ## Preservation of event mapping and snapshot -/
namespace OldEvent
variable {B : Type}

def mapWithTime (f : T → A → B) (e : OldEvent T A) : OldEvent T B where
  seq := e.seq.map (fun (p : T × A) => (p.1, f p.1 p.2))
  ordered := e.ordered

def map (f : A → B) (e : OldEvent T A) : OldEvent T B :=
  mapWithTime (fun _ => f) e

def snapshot (e : OldEvent T A) (b : Behavior T B) : OldEvent T (A × B) :=
  mapWithTime (fun t a => (a, b t)) e
end OldEvent

namespace Batch
variable {B : Type}

def mapWithTime (f : T → A → B) (b : Batch T A) : Batch T B :=
  fun t => CoList.map (f t) (b t)

def map (f : A → B) (b : Batch T A) : Batch T B :=
  mapWithTime (fun _ => f) b

def snapshot (e : Batch T A) (b : Behavior T B) : Batch T (A × B) :=
  mapWithTime (fun t a => (a, b t)) e
end Batch

namespace Realization
variable {B : Type}

def mapWithTime {e : OldEvent T A} {b : Batch T A}
    (r : Realization e b) (f : T → A → B) :
    Realization (e.mapWithTime f) (b.mapWithTime f) where
  iso := r.iso
  time_eq := r.time_eq
  value_eq := by
    intro i
    change f (r.iso i).time (r.iso i).value = f (e.time i) (e.value i)
    exact congrArg₂ f (r.time_eq (show e.Pos from i)) (r.value_eq (show e.Pos from i))
end Realization

namespace OldEvent
variable {B : Type}

theorem group_mapWithTime (e : OldEvent T A) (f : T → A → B) :
    (e.mapWithTime f).group = Batch.mapWithTime f e.group :=
  Realization.batch_unique (e.mapWithTime f).groupRealization
    (e.groupRealization.mapWithTime f)

theorem group_map (e : OldEvent T A) (f : A → B) :
    (e.map f).group = Batch.map f e.group := group_mapWithTime e (fun _ => f)

theorem group_snapshot (e : OldEvent T A) (b : Behavior T B) :
    (e.snapshot b).group = Batch.snapshot e.group b :=
  group_mapWithTime e (fun t a => (a, b t))
end OldEvent

/-! ## Before and switching

`before` is defined mathematically by the ordered subset of qualifying
occurrences.  It is NOT Haskell's unbounded lazy `filter`: see the README.
-/
namespace OldEvent

def before (e : OldEvent T A) (t : T) : CoList A :=
  Numbering.linearize
    (Numbering.finitePred_of_strictMono e.seq.finitePred
      (fun i : {i : e.Pos // e.time i < t} => i.val)
      (by intro i j hij; exact hij))
    (fun i => e.value i.val)
end OldEvent

namespace Batch

def before (b : Batch T A) (h : b.Admissible) (t : T) : CoList A :=
  Numbering.linearize
    (Numbering.finitePred_of_strictMono h
      (fun p : {p : b.Occ // p.time < t} => p.val)
      (by intro p q hpq; exact hpq))
    (fun p => p.val.value)
end Batch

namespace Realization

def beforeIso {e : OldEvent T A} {b : Batch T A}
    (r : Realization e b) (t : T) :
    {i : e.Pos // e.time i < t} ≃o {p : b.Occ // p.time < t} where
  toFun := fun i => ⟨r.iso i.val, by simpa only [r.time_eq] using i.property⟩
  invFun := fun p => ⟨r.iso.symm p.val, by
    have h := r.time_eq (r.iso.symm p.val)
    simp only [OrderIso.apply_symm_apply] at h
    simpa only [← h] using p.property⟩
  left_inv := by intro i; apply Subtype.ext; exact r.iso.symm_apply_apply i.val
  right_inv := by intro p; apply Subtype.ext; exact r.iso.apply_symm_apply p.val
  map_rel_iff' := by intro i j; exact r.iso.le_iff_le

theorem before_eq {e : OldEvent T A} {b : Batch T A}
    (r : Realization e b) (hb : b.Admissible) (t : T) :
    e.before t = b.before hb t := by
  let he : FinitePred {i : e.Pos // e.time i < t} :=
    Numbering.finitePred_of_strictMono e.seq.finitePred
      (fun i => i.val) (by intro i j hij; exact hij)
  let hn : FinitePred {p : b.Occ // p.time < t} :=
    Numbering.finitePred_of_strictMono hb
      (fun p => p.val) (by intro p q hpq; exact hpq)
  let eo := Numbering.indexIso he (fun i => e.value i.val)
  let en := Numbering.indexIso hn (fun p => p.val.value)
  apply CoList.eq_of_iso (e.before t) (b.before hb t)
    (eo.symm.trans ((r.beforeIso t).trans en))
  intro i
  change (Numbering.linearize hn (fun p => p.val.value)).value
      (en (r.beforeIso t (eo.symm i))) =
    (Numbering.linearize he (fun i => e.value i.val)).value i
  rw [Numbering.linearize_value]
  change (r.iso (eo.symm i).val).value = e.value (eo.symm i).val
  exact r.value_eq _
end Realization

/-! An abstract `last` of a finite set of ordered positions. -/
namespace Last
variable {X Y : Type} [LinearOrder X] [LinearOrder Y]

def lastOn (s : Set X) (hs : s.Finite) (v : X → A) (initial : A) : A :=
  if h : hs.toFinset.Nonempty then v (hs.toFinset.max' h) else initial

/-- Last is invariant under an order- and label-preserving reindexing. -/
theorem lastOn_iso (r : X ≃o Y)
    (s : Set X) (hs : s.Finite) (u : Set Y) (hu : u.Finite)
    (hmem : ∀ x, x ∈ s ↔ r x ∈ u)
    (v : X → A) (w : Y → A) (hval : ∀ x, w (r x) = v x) (initial : A) :
    lastOn s hs v initial = lastOn u hu w initial := by
  by_cases hne : hs.toFinset.Nonempty
  · let x := hs.toFinset.max' hne
    have hxs : x ∈ s := hs.mem_toFinset.mp (Finset.max'_mem _ _)
    have hxru : r x ∈ hu.toFinset := hu.mem_toFinset.mpr ((hmem x).mp hxs)
    have hnu : hu.toFinset.Nonempty := ⟨r x, hxru⟩
    let y := hu.toFinset.max' hnu
    have hyu : y ∈ u := hu.mem_toFinset.mp (Finset.max'_mem _ _)
    have hyis : r.symm y ∈ hs.toFinset := hs.mem_toFinset.mpr
      ((hmem (r.symm y)).mpr (by simpa using hyu))
    have hxy : r x ≤ y := Finset.le_max' _ _ hxru
    have hyx : y ≤ r x := by
      have hh : r.symm y ≤ x := Finset.le_max' _ _ hyis
      have hh' := r.monotone hh
      simpa using hh'
    have heq : r x = y := le_antisymm hxy hyx
    simp only [lastOn, dite_eq_left hne, dite_eq_left hnu]
    change v x = w y
    rw [← heq, hval]
  · have hnu : ¬ hu.toFinset.Nonempty := by
      intro hh
      rcases hh with ⟨y, hy⟩
      have hyu : y ∈ u := hu.mem_toFinset.mp hy
      have his : r.symm y ∈ s := (hmem (r.symm y)).mpr (by simpa using hyu)
      exact hne ⟨r.symm y, hs.mem_toFinset.mpr his⟩
    simp only [lastOn, dite_eq_right hne, dite_eq_right hnu]
end Last

namespace OldEvent

def switcher (initial : Behavior T A) (e : OldEvent T (Behavior T A))
    (h : e.FiniteHistory) : Behavior T A := fun t =>
  (Last.lastOn {i : e.Pos | e.time i < t} (h t) e.value initial) t
end OldEvent

namespace Batch

def switcher (initial : Behavior T A) (b : Batch T (Behavior T A))
    (h : b.FiniteHistory) : Behavior T A := fun t =>
  (Last.lastOn {p : b.Occ | p.time < t} (h t) (fun p => p.value) initial) t
end Batch

namespace Realization

theorem switcher_eq {e : OldEvent T (Behavior T A)}
    {b : Batch T (Behavior T A)} (r : Realization e b)
    (he : e.FiniteHistory) (hb : b.FiniteHistory) (initial : Behavior T A) :
    e.switcher initial he = b.switcher initial hb := by
  funext t
  have h := Last.lastOn_iso r.iso
    {i : e.Pos | e.time i < t} (he t)
    {p : b.Occ | p.time < t} (hb t)
    (by intro i; simp only [Set.mem_ofPred_eq, r.time_eq])
    e.value (fun p => p.value) r.value_eq initial
  exact congrFun h t
end Realization

/-! ## Why lossless merge with arbitrary singletons requires finite history

Even allowing the output extra occurrences, timestamp-preserving injection
of e into a sorted output containing an occurrence at t forces e's history
strictly before t to be finite.
-/
namespace OldEvent
variable {B : Type}

theorem finite_before_of_following_occurrence
    (e : OldEvent T A) (out : OldEvent T B) (t : T)
    (j : out.Pos) (hjt : out.time j = t)
    (embed : e.Pos → out.Pos) (hinj : Function.Injective embed)
    (htime : ∀ i, out.time (embed i) = e.time i) :
    {i : e.Pos | e.time i < t}.Finite := by
  have hp : (embed ⁻¹' Set.Iio j).Finite :=
    Set.Finite.preimage hinj.injOn (out.seq.finitePred j)
  apply hp.subset
  intro i hi
  change embed i < j
  by_contra hnot
  have hji : j ≤ embed i := le_of_not_gt hnot
  have hh := out.ordered hji
  change out.time j ≤ out.time (embed i) at hh
  rw [hjt, htime] at hh
  exact (not_le_of_gt hi) hh
end OldEvent

/-! ## Counterexamples: restrictions in the old comment really matter -/
namespace Examples

/-- Infinitely many simultaneous occurrences.  Its support is a singleton. -/
def infiniteBatch : OldEvent ℝ Unit where
  seq := CoList.ofStream (fun _ => (0, ()))
  ordered := by intro i j hij; exact le_rfl

theorem infiniteBatch_not_finiteHistory : ¬ infiniteBatch.FiniteHistory := by
  intro h
  have hf := (h 1).image (fun i => i.val)
  have heq : (fun i : infiniteBatch.Pos => i.val) ''
      {i : infiniteBatch.Pos | infiniteBatch.time i < 1} = Set.univ := by
    ext n
    constructor
    · intro _; trivial
    · intro _
      refine ⟨⟨n, True.intro⟩, ?_, rfl⟩
      change (0 : ℝ) < 1
      norm_num
  rw [heq] at hf
  exact Set.infinite_univ hf

/-- A Zeno event, with one occurrence at each time 1 - 1/(n+2). -/
def zeno : OldEvent ℝ ℕ where
  seq := CoList.ofStream (fun n => (1 - 1 / ((n : ℝ) + 2), n))
  ordered := by
    intro i j hij
    change 1 - 1 / ((i.val : ℝ) + 2) ≤ 1 - 1 / ((j.val : ℝ) + 2)
    have hij' : (i.val : ℝ) ≤ (j.val : ℝ) := by exact_mod_cast hij
    have hi : 0 < (i.val : ℝ) + 2 := by positivity
    have hj : 0 < (j.val : ℝ) + 2 := by positivity
    have hd : 1 / ((j.val : ℝ) + 2) ≤ 1 / ((i.val : ℝ) + 2) :=
      (div_le_div_iff₀ hj hi).mpr (by nlinarith)
    linarith

theorem zeno_before_one (i : zeno.Pos) : zeno.time i < 1 := by
  change 1 - 1 / ((i.val : ℝ) + 2) < 1
  have hp : 0 < 1 / ((i.val : ℝ) + 2) := by positivity
  linarith

theorem zeno_not_finiteHistory : ¬ zeno.FiniteHistory := by
  intro h
  have hf := (h 1).image (fun i => i.val)
  have heq : (fun i : zeno.Pos => i.val) ''
      {i : zeno.Pos | zeno.time i < 1} = Set.univ := by
    ext n
    constructor
    · intro _; trivial
    · intro _
      exact ⟨⟨n, True.intro⟩, zeno_before_one _, rfl⟩
  rw [heq] at hf
  exact Set.infinite_univ hf

/-- Nonetheless the exact representation equivalence applies to both. -/
example : toOld (toNew zeno) = zeno := toOld_toNew zeno
example : toOld (toNew infiniteBatch) = infiniteBatch := toOld_toNew infiniteBatch

end Examples

/-- Intrinsic finite predecessors are necessary and sufficient, rather than
merely a sufficient condition selected for convenience. -/
theorem admissible_iff_representable (b : Batch T A) :
    b.Admissible ↔ ∃ e : OldEvent T A, Nonempty (Realization e b) := by
  constructor
  · intro hb
    exact ⟨b.flatten hb, ⟨Realization.flatten b hb⟩⟩
  · rintro ⟨e, ⟨r⟩⟩
    exact r.admissible

namespace Batch

theorem finiteHistory_admissible [NoMaxOrder T]
    (b : Batch T A) (h : b.FiniteHistory) : b.Admissible := by
  intro p
  obtain ⟨u, hpu⟩ := exists_gt p.time
  apply (h u).subset
  intro q hq
  rcases (Occ.lt_iff q p).mp hq with hqt | ⟨hqt, _⟩
  · exact lt_trans hqt hpu
  · change q.time < u
    rw [hqt]
    exact hpu

/-- Over real time, finite history also forces each individual batch finite. -/
theorem finite_batch_of_finiteHistory [NoMaxOrder T]
    (b : Batch T A) (h : b.FiniteHistory) (t : T) :
    (Set.univ : Set (b t).Pos).Finite := by
  obtain ⟨u, htu⟩ := exists_gt t
  have hinj : Function.Injective (Occ.mk b t) := by
    intro i j hij
    apply Subtype.ext
    exact congrArg Occ.index hij
  have hf : ((Occ.mk b t) ⁻¹' {p : b.Occ | p.time < u}).Finite :=
    Set.Finite.preimage hinj.injOn (h u)
  have heq : (Occ.mk b t) ⁻¹' {p : b.Occ | p.time < u} = Set.univ := by
    ext i
    simp [htu]
  rwa [heq] at hf
end Batch

/-- A direct isomorphism of the total finite-history carriers. -/
def totalEventEquiv [NoMaxOrder T] :
    {e : OldEvent T A // e.FiniteHistory} ≃
      {b : Batch T A // b.FiniteHistory} where
  toFun := fun e => ⟨e.val.group,
    e.val.groupRealization.finiteHistory_iff.mp e.property⟩
  invFun := fun b => ⟨b.val.flatten (b.val.finiteHistory_admissible b.property),
    (Realization.flatten b.val (b.val.finiteHistory_admissible b.property)).finiteHistory_iff.mpr
      b.property⟩
  left_inv := by
    intro e
    apply Subtype.ext
    exact Realization.old_unique
      (Realization.flatten e.val.group
        (Batch.finiteHistory_admissible e.val.group
          (e.val.groupRealization.finiteHistory_iff.mp e.property)))
      e.val.groupRealization
  right_inv := by
    intro b
    apply Subtype.ext
    exact Realization.batch_unique
      (b.val.flatten (b.val.finiteHistory_admissible b.property)).groupRealization
      (Realization.flatten b.val (b.val.finiteHistory_admissible b.property))

namespace OldEvent

/-- A literal mathematical `last` on the chronological prefix exists exactly
when that prefix is finite, including the empty-prefix/default case. -/
theorem finite_before_iff_empty_or_last (e : OldEvent T A) (t : T) :
    {i : e.Pos | e.time i < t}.Finite ↔
      ((∀ i : e.Pos, ¬ e.time i < t) ∨
       ∃ i : e.Pos, e.time i < t ∧ ∀ j : e.Pos, e.time j < t → j ≤ i) := by
  constructor
  · intro h
    by_cases hn : h.toFinset.Nonempty
    · right
      let i := h.toFinset.max' hn
      refine ⟨i, h.mem_toFinset.mp (Finset.max'_mem _ _), ?_⟩
      intro j hj
      exact Finset.le_max' _ _ (h.mem_toFinset.mpr hj)
    · left
      intro i hi
      exact hn ⟨i, h.mem_toFinset.mpr hi⟩
  · rintro (hempty | ⟨i, hi, hlast⟩)
    · have heq : {i : e.Pos | e.time i < t} = ∅ := by
        ext i
        simp [hempty i]
      rw [heq]
      exact Set.finite_empty
    · apply ((e.seq.finitePred i).union (Set.finite_singleton i)).subset
      intro j hj
      rcases lt_or_eq_of_le (hlast j hj) with hlt | heq
      · exact Or.inl hlt
      · exact Or.inr heq
end OldEvent

namespace CoList

/-- This representation has precisely finite and omega-long shapes, not
transfinite lists such as omega+1. -/
theorem finite_or_infinite {A : Type} (s : CoList A) :
    (∃ n : ℕ, ∀ i : ℕ, s.live i ↔ i < n) ∨ (∀ i : ℕ, s.live i) := by
  by_cases hall : ∀ i : ℕ, s.live i
  · exact Or.inr hall
  · left
    have hex : ∃ i : ℕ, ¬ s.live i := by
      by_contra hn
      apply hall
      intro i
      by_contra hi
      exact hn ⟨i, hi⟩
    let n := Nat.find hex
    have hn : ¬ s.live n := Nat.find_spec hex
    refine ⟨n, ?_⟩
    intro i
    constructor
    · intro hi
      by_contra hlt
      exact hn (s.initial (Nat.le_of_not_gt hlt) hi)
    · intro hi
      by_contra hnot
      have hni : n ≤ i := Nat.find_min' hex hnot
      omega
end CoList

end FRP

-- On a successful build, inspect these outputs for any unexpected axioms.
#print axioms FRP.eventEquiv
#print axioms FRP.totalEventEquiv
#print axioms FRP.Realization.switcher_eq
#print axioms FRP.Examples.zeno_not_finiteHistory
