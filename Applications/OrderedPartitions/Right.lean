import Applications.OrderedPartitions.Left
import Mathlib.Data.List.Induction

/-! Right-extending enumeration and prefix-closed pruning reuse left semantics by reversal. -/
set_option autoImplicit false
set_option warningAsError true
namespace OrderedPartitions
universe u
variable {α : Type u}

theorem snoc_induction {β : Type u} {P : List β → Prop}
    (nil : P []) (snoc : ∀ xs x, P xs → P (xs ++ [x])) (xs : List β) : P xs :=
  List.reverseRecOn xs nil snoc

def mirror (p : Partition α) : Partition α := p.reverse.map List.reverse

@[simp] theorem mirror_nil : mirror ([] : Partition α) = [] := rfl

@[simp] theorem mirror_cons (block : List α) (p : Partition α) :
    mirror (block :: p) = mirror p ++ [block.reverse] := by
  simp [mirror]

@[simp] theorem mirror_append_singleton (p : Partition α) (block : List α) :
    mirror (p ++ [block]) = block.reverse :: mirror p := by
  simp [mirror]

@[simp] theorem mirror_mirror (p : Partition α) : mirror (mirror p) = p := by
  simp [mirror, List.map_reverse, List.map_map]

@[simp] theorem mirror_inj (p q : Partition α) : mirror p = mirror q ↔ p = q := by
  constructor
  · intro h
    simpa using congrArg mirror h
  · exact congrArg mirror

@[simp] theorem flatten_mirror (p : Partition α) : (mirror p).flatten = p.flatten.reverse := by
  simpa [mirror, List.map_reverse] using (List.reverse_flatten (L := p)).symm

@[simp] theorem nonemptyBlocks_mirror (p : Partition α) :
    NonemptyBlocks (mirror p) ↔ NonemptyBlocks p := by
  constructor
  · intro h block hb he
    have hm : block.reverse ∈ mirror p :=
      List.mem_map.mpr ⟨block, List.mem_reverse.mpr hb, rfl⟩
    exact h _ hm (by simp [he])
  · intro h block hb he
    obtain ⟨before, hm, rfl⟩ := List.mem_map.mp hb
    exact h before (List.mem_reverse.mp hm) (by simpa using he)

@[simp] theorem isPartition_mirror (xs : List α) (p : Partition α) :
    IsPartition xs.reverse (mirror p) ↔ IsPartition xs p := by
  simp [IsPartition]

def snocBlock (x : α) (p : Partition α) : Partition α := p ++ [[x]]

/-- Actual source `init p ++ [last p ++ [x]]`, with a total default only for p = []. -/
def bindRight (x : α) (p : Partition α) : Partition α :=
  p.dropLast ++ [p.getLastD [] ++ [x]]

def extendRight (x : α) : Partition α → List (Partition α)
  | [] => [snocBlock x []]
  | block :: rest => [snocBlock x (block :: rest), bindRight x (block :: rest)]

def stepRight (x : α) (ps : List (Partition α)) : List (Partition α) :=
  ps.flatMap (extendRight x)

def partsRight (xs : List α) : List (Partition α) :=
  xs.foldl (fun ps x => stepRight x ps) [[]]

@[simp] theorem bindRight_append_singleton (x : α) (p : Partition α) (block : List α) :
    bindRight x (p ++ [block]) = p ++ [block ++ [x]] := by
  simp [bindRight]

theorem extendRight_mirror (x : α) (p : Partition α) :
    extendRight x p = (extendLeft x (mirror p)).map mirror := by
  induction p using snoc_induction with
  | nil => rfl
  | snoc p block ih =>
    have hext : extendRight x (p ++ [block]) =
        [snocBlock x (p ++ [block]), bindRight x (p ++ [block])] := by
      cases p <;> rfl
    rw [hext, mirror_append_singleton]
    simp [extendLeft, consBlock, glueLeft, snocBlock, List.append_assoc]

theorem stepRight_mirror (x : α) (ps : List (Partition α)) :
    stepRight x ps = (stepLeft x (ps.map mirror)).map mirror := by
  simp only [stepRight, stepLeft, List.flatMap_map, List.map_flatMap]
  congr 1
  funext p
  exact extendRight_mirror x p

@[simp] theorem partsRight_nil : partsRight ([] : List α) = [[]] := rfl

@[simp] theorem partsRight_append_singleton (xs : List α) (x : α) :
    partsRight (xs ++ [x]) = stepRight x (partsRight xs) := by
  simp [partsRight]

/-- Reversal here is a proved correspondence; the implemented source fold still uses snoc/bind. -/
theorem partsRight_mirror (xs : List α) :
    partsRight xs = (partsLeft xs.reverse).map mirror := by
  induction xs using snoc_induction with
  | nil => rfl
  | snoc xs x ih =>
    rw [partsRight_append_singleton, ih, stepRight_mirror]
    simp [List.map_map, Function.comp_def]

theorem mem_partsRight (xs : List α) (p : Partition α) :
    p ∈ partsRight xs ↔ IsPartition xs p := by
  rw [partsRight_mirror, List.mem_map]
  constructor
  · rintro ⟨q, hq, rfl⟩
    have h := (mem_partsLeft xs.reverse q).mp hq
    have hm := (isPartition_mirror xs.reverse q).mpr h
    simpa using hm
  · intro hp
    refine ⟨mirror p, (mem_partsLeft xs.reverse (mirror p)).mpr ?_, mirror_mirror p⟩
    exact (isPartition_mirror xs p).mpr hp

theorem partsRight_nodup (xs : List α) : (partsRight xs).Nodup := by
  rw [partsRight_mirror]
  change List.Pairwise (fun p q => p ≠ q) ((partsLeft xs.reverse).map mirror)
  have h := partsLeft_nodup xs.reverse
  change List.Pairwise (fun p q => p ≠ q) (partsLeft xs.reverse) at h
  rw [List.pairwise_map]
  exact h.imp (fun hpq heq => hpq ((mirror_inj _ _).mp heq))

theorem length_partsRight (xs : List α) :
    (partsRight xs).length = if xs.isEmpty then 1 else 2 ^ (xs.length - 1) := by
  simp [partsRight_mirror, length_partsLeft]

/-- The two folds may enumerate in different orders. -/
theorem partsRight_perm_left (xs : List α) : (partsRight xs).Perm (partsLeft xs) := by
  exact (List.perm_ext_iff_of_nodup (partsRight_nodup xs) (partsLeft_nodup xs)).mpr
    (fun p => (mem_partsRight xs p).trans (mem_partsLeft xs p).symm)

def lastOk (ok : List α → Bool) (p : Partition α) : Bool :=
  match p with
  | [] => false
  | _ :: _ => ok (p.getLastD [])

@[simp] theorem lastOk_append_singleton (ok : List α → Bool)
    (p : Partition α) (block : List α) : lastOk ok (p ++ [block]) = ok block := by
  cases p with
  | nil => rfl
  | cons b bs =>
    change ok (((b :: bs) ++ [block]).getLastD []) = ok block
    rw [List.getLastD_concat]

@[simp] theorem allOk_append (ok : List α → Bool) (p q : Partition α) :
    allOk ok (p ++ q) = (allOk ok p && allOk ok q) := by
  simp [allOk]

def prunedStepRight (ok : List α → Bool) (x : α)
    (ps : List (Partition α)) : List (Partition α) :=
  ps.flatMap (fun p => (extendRight x p).filter (lastOk ok))

def prunedPartsRight (ok : List α → Bool) (xs : List α) : List (Partition α) :=
  xs.foldl (fun ps x => prunedStepRight ok x ps) [[]]

theorem filter_extendRight (ok : List α → Bool) (hp : PrefixClosed ok)
    (x : α) (p : Partition α) :
    (extendRight x p).filter (allOk ok) =
      if allOk ok p then (extendRight x p).filter (lastOk ok) else [] := by
  induction p using snoc_induction with
  | nil =>
    cases h : ok [x] <;> simp [extendRight, snocBlock, lastOk, h]
  | snoc p block ih =>
    have hback : ok (block ++ [x]) = true → ok block = true := hp block [x]
    have hext : extendRight x (p ++ [block]) =
        [p ++ [block] ++ [[x]], p ++ [block ++ [x]]] := by
      have hext' : extendRight x (p ++ [block]) =
          [snocBlock x (p ++ [block]), bindRight x (p ++ [block])] := by
        cases p <;> rfl
      rw [hext']
      simp only [snocBlock, bindRight_append_singleton]
    have hlast : lastOk ok (p ++ [block, [x]]) = ok [x] := by
      have h := lastOk_append_singleton ok (p ++ [block]) [x]
      simpa only [List.append_assoc, List.singleton_append] using h
    rw [hext]
    cases hb : ok block <;> cases hr : allOk ok p <;>
      cases hx : ok (block ++ [x]) <;> cases hs : ok [x] <;>
      simp_all

theorem filter_stepRight (ok : List α → Bool) (hp : PrefixClosed ok)
    (x : α) (ps : List (Partition α)) :
    (stepRight x ps).filter (allOk ok) =
      prunedStepRight ok x (ps.filter (allOk ok)) := by
  induction ps with
  | nil => rfl
  | cons p ps ih =>
    simp only [stepRight, List.flatMap_cons, List.filter_append] at ih ⊢
    rw [filter_extendRight ok hp x p, ih]
    cases h : allOk ok p <;> simp [h, prunedStepRight]

/-- Exact list equality for the source right-extending foldl pruning, with the dual closure hypothesis. -/
theorem filter_partsRight (ok : List α → Bool) (hp : PrefixClosed ok) (xs : List α) :
    (partsRight xs).filter (allOk ok) = prunedPartsRight ok xs := by
  exact SquareKit.ListFusion.foldl_reachable (fun ps x => stepRight x ps)
    (fun ps x => prunedStepRight ok x ps) (List.filter (allOk ok))
    (fun _ => True) [[]] trivial (fun _ _ _ => trivial)
    (fun ps x _ => filter_stepRight ok hp x ps) xs

theorem mem_prunedPartsRight (ok : List α → Bool) (hp : PrefixClosed ok)
    (xs : List α) (p : Partition α) :
    p ∈ prunedPartsRight ok xs ↔
      IsPartition xs p ∧ ∀ block ∈ p, ok block = true := by
  rw [← filter_partsRight ok hp]
  simp [mem_partsRight, allOk_eq_true_iff]

theorem prunedPartsRight_nodup (ok : List α → Bool) (hp : PrefixClosed ok)
    (xs : List α) : (prunedPartsRight ok xs).Nodup := by
  rw [← filter_partsRight ok hp]
  exact (partsRight_nodup xs).filter _

theorem prunedPartsRight_sublist (ok : List α → Bool) (hp : PrefixClosed ok)
    (xs : List α) : (prunedPartsRight ok xs).Sublist (partsRight xs) := by
  rw [← filter_partsRight ok hp]
  exact List.filter_sublist

end OrderedPartitions
