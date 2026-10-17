import Applications.FRP.Spec
import Applications.FRP.Equivalence

/-! Finite batches connect the raw carrier theorem to the native event model. -/
noncomputable section
open Classical
namespace FRP
namespace CoList
variable {A : Type}

def ofList (xs : List A) : CoList A where
  live n := n < xs.length
  initial := fun h hj => lt_of_le_of_lt h hj
  value i := xs[i.val]

theorem ofList_finite (xs : List A) : (Set.univ : Set (ofList xs).Pos).Finite :=
  ((Set.finite_Iio xs.length).preimage Subtype.val_injective.injOn).subset
    (fun i _ => i.property)

theorem ofList_injective : Function.Injective (@ofList A) := by
  intro xs ys h
  have hl : xs.length = ys.length := by
    have hd : ∀ n, n < xs.length ↔ n < ys.length := fun n =>
      Iff.of_eq (congrArg (fun s : CoList A => s.live n) h)
    apply Nat.le_antisymm
    · by_contra hn
      exact (Nat.lt_irrefl _) ((hd ys.length).mp (Nat.lt_of_not_ge hn))
    · by_contra hn
      exact (Nat.lt_irrefl _) ((hd xs.length).mpr (Nat.lt_of_not_ge hn))
  apply List.ext_getElem hl
  intro i hi hj
  exact Option.some.inj (show some xs[i] = some ys[i] from by
    simpa [get?, ofList, hi, hj] using congrArg (fun s => s.get? i) h)

theorem exists_list (s : CoList A) (h : (Set.univ : Set s.Pos).Finite) :
    ∃ xs : List A, ofList xs = s := by
  rcases s.finite_or_infinite with ⟨n, hn⟩ | hall
  · refine ⟨List.ofFn (fun i : Fin n => s.value ⟨i, (hn i).mpr i.isLt⟩), ?_⟩
    apply CoList.ext
    · intro i; simpa [ofList] using (hn i).symm
    · intro i hi hs; simp [ofList]
  · have hf := h.image (fun i => i.val)
    have he : (fun i : s.Pos => i.val) '' Set.univ = Set.univ := by
      ext n; simp only [Set.mem_image, Set.mem_univ, true_and, iff_true]
      exact ⟨⟨n, hall n⟩, rfl⟩
    rw [he] at hf
    exact False.elim (Set.infinite_univ hf)

def toList (s : CoList A) (h : (Set.univ : Set s.Pos).Finite) : List A :=
  (exists_list s h).choose

@[simp] theorem ofList_toList (s : CoList A) (h : (Set.univ : Set s.Pos).Finite) :
    ofList (s.toList h) = s := (exists_list s h).choose_spec

@[simp] theorem ofList_map {B : Type} (f : A → B) (xs : List A) :
    ofList (xs.map f) = (ofList xs).map f := by
  apply CoList.ext
  · simp [ofList, map]
  · intros; simp [ofList, map]
end CoList

namespace Native
variable {A : Type}

def batch (e : FRPSpec.Event A) : Batch ℝ A := fun t => CoList.ofList (e.at t)

theorem finiteHistory (e : FRPSpec.Event A) : (batch e).FiniteHistory := by
  intro t
  let s := e.finite_past t
  have hf : (⋃ u ∈ FRPSpec.PastSupport e.at t,
      (fun n : ℕ => toLex (u, n)) '' Set.Iio (e.at u).length).Finite :=
    s.biUnion (fun u _ => (Set.finite_Iio _).image _)
  apply (hf.preimage Subtype.val_injective.injOn).subset
  intro p hp
  change Batch.Occ.time (b := batch e) p < t at hp
  change p.val ∈ ⋃ u ∈ FRPSpec.PastSupport e.at t,
    (fun n : ℕ => toLex (u, n)) '' Set.Iio (e.at u).length
  refine Set.mem_iUnion.mpr ⟨Batch.Occ.time (b := batch e) p, Set.mem_iUnion.mpr ⟨?_, ?_⟩⟩
  · refine ⟨hp, ?_⟩
    intro he
    have hi : Batch.Occ.index (b := batch e) p < (e.at (Batch.Occ.time (b := batch e) p)).length := p.property
    simp [he] at hi
  · exact ⟨Batch.Occ.index (b := batch e) p, p.property, rfl⟩

def toFiniteBatch (e : FRPSpec.Event A) : {b : Batch ℝ A // b.FiniteHistory} :=
  ⟨batch e, finiteHistory e⟩

def fromFiniteBatch (b : {b : Batch ℝ A // b.FiniteHistory}) : FRPSpec.Event A where
  «at» t := (b.val t).toList (b.val.finite_batch_of_finiteHistory b.property t)
  finite_past t := by
    apply ((b.property t).image Batch.Occ.time).subset
    rintro u ⟨hu, hne⟩
    have hex : ∃ i, (b.val u).live i := by
      by_contra hn
      apply hne
      apply CoList.ofList_injective
      rw [CoList.ofList_toList]
      apply CoList.ext
      · intro i; simp [CoList.ofList] at *; exact hn i
      · intro i hi; exact False.elim (hn ⟨i, hi⟩)
    obtain ⟨i, hi⟩ := hex
    exact ⟨Batch.Occ.mk b.val u ⟨i, hi⟩, hu, rfl⟩

@[simp] theorem batch_fromFiniteBatch (b : {b : Batch ℝ A // b.FiniteHistory}) :
    batch (fromFiniteBatch b) = b.val := by
  funext t
  exact CoList.ofList_toList (b.val t) (b.val.finite_batch_of_finiteHistory b.property t)

/-- Finite occurrence histories are exactly finite past support of finite lists. -/
def equiv : FRPSpec.Event A ≃ {b : Batch ℝ A // b.FiniteHistory} where
  toFun := toFiniteBatch
  invFun := fromFiniteBatch
  left_inv e := by
    apply FRPSpec.Event.ext
    funext t
    apply CoList.ofList_injective
    exact congrFun (batch_fromFiniteBatch (toFiniteBatch e)) t
  right_inv b := Subtype.ext (batch_fromFiniteBatch b)

/-- The missing bridge to the native model, preserving ordered batch values. -/
def oldEquiv : {e : OldEvent ℝ A // e.FiniteHistory} ≃ FRPSpec.Event A :=
  totalEventEquiv.trans equiv.symm

@[simp] theorem batch_oldEquiv (e : {e : OldEvent ℝ A // e.FiniteHistory}) :
    batch (oldEquiv e) = e.val.group := batch_fromFiniteBatch _

@[simp] theorem group_oldEquiv_symm (e : FRPSpec.Event A) :
    (oldEquiv.symm e).val.group = batch e := by
  rw [← batch_oldEquiv, Equiv.apply_symm_apply]

/-- Chronological rank enumerates the concatenated batches. Their indices put
all left occurrences before right occurrences at each timestamp. -/
def merge (l r : {e : OldEvent ℝ A // e.FiniteHistory}) :
    {e : OldEvent ℝ A // e.FiniteHistory} :=
  oldEquiv.symm (FRPSpec.Event.merge (oldEquiv l) (oldEquiv r))

/-- Stable merge preserves the full ordered list, including duplicates. -/
theorem group_merge (l r : {e : OldEvent ℝ A // e.FiniteHistory}) (t : ℝ) :
    (merge l r).val.group t =
      CoList.ofList ((oldEquiv l).at t ++ (oldEquiv r).at t) :=
  congrFun (group_oldEquiv_symm _) t

theorem merge_preserves (l r : {e : OldEvent ℝ A // e.FiniteHistory}) :
    oldEquiv (merge l r) = FRPSpec.Event.merge (oldEquiv l) (oldEquiv r) :=
  oldEquiv.apply_symm_apply _

/-- A left occurrence retains its literal local index. -/
theorem merge_left (l r : {e : OldEvent ℝ A // e.FiniteHistory})
    (t : ℝ) (i : ℕ) (hi : i < ((oldEquiv l).at t).length) :
    ((merge l r).val.group t).get? i = some ((oldEquiv l).at t)[i] := by
  rw [group_merge]
  simp [CoList.get?, CoList.ofList, List.getElem_append_left, hi,
    show i < ((oldEquiv l).at t).length + ((oldEquiv r).at t).length by omega]

/-- A right occurrence follows every simultaneous left occurrence. -/
theorem merge_right (l r : {e : OldEvent ℝ A // e.FiniteHistory})
    (t : ℝ) (i : ℕ) (hi : i < ((oldEquiv r).at t).length) :
    ((merge l r).val.group t).get? (((oldEquiv l).at t).length + i) =
      some ((oldEquiv r).at t)[i] := by
  rw [group_merge]
  simp [CoList.get?, CoList.ofList, List.getElem_append_right,
    show ((oldEquiv l).at t).length + i <
      ((oldEquiv l).at t).length + ((oldEquiv r).at t).length by omega]

end Native
end FRP
