import Applications.Resources.KnapsackSemantics
import Applications.Resources.KnapsackSourceCosts

/-! Complete immutable-array workload: initialization, suffix-first rows,
capacity read, and explicit traversal of every returned name. The existing
three primitive counts and full scalar tariff remain separate observations. -/
set_option autoImplicit false
set_option warningAsError true
namespace Resources.Knapsack
open Optimization.KnapsackThinning
variable {α : Type}

def comparisons (capacity : Nat) (items : List (Item α)) : Nat :=
  (items.map (fun i => capacity+1-i.weight)).sum

def rowsMeasured (capacity : Nat) : List (Item α) → Measured (Array (Selection α)) Work
  | [] => (start capacity,(0,0,0,3*(capacity+1)+3))
  | i :: items => bind (rowsMeasured capacity items) fun old =>
      bind (stepMeasured capacity i old) fun row => (row,(0,0,0,1))

/-- Full name observation rebuilds the returned list with the source map tariff. -/
def namesMeasured : List α → Measured (List α) Work
  | [] => ([],(0,0,0,1))
  | x :: xs => bind (namesMeasured xs) fun ys => (x :: ys,(0,0,0,3))

def observeMeasured (s : Selection α) : Measured (Selection α) Work :=
  bind (namesMeasured s.names) fun names => (⟨names,s.value,s.weight⟩,(0,0,0,3))

def runMeasured (capacity : Nat) (items : List (Item α)) : Measured (Selection α) Work :=
  bind (rowsMeasured capacity items) fun row =>
    bind (read row capacity,(0,0,0,3)) observeMeasured

theorem namesMeasured_exact (xs : List α) :
    namesMeasured xs = (xs,(0,0,0,3*xs.length+1)) := by
  induction xs with
  | nil => rfl
  | cons x xs ih => simp [namesMeasured,bind,ih,Nat.mul_add,Nat.add_assoc]

theorem observeMeasured_exact (s : Selection α) :
    observeMeasured s = (s,(0,0,0,3*s.names.length+4)) := by
  cases s
  simp [observeMeasured,namesMeasured_exact,bind,Nat.add_assoc]

theorem rowsMeasured_exact (capacity : Nat) (items : List (Item α)) :
    rowsMeasured capacity items =
      (table capacity items,
       (items.length*(capacity+1),comparisons capacity items,items.length*(capacity+1),
        items.length*(23*(capacity+1)+10)+23*comparisons capacity items+3*(capacity+1)+3)) := by
  induction items with
  | nil => simp [rowsMeasured,table,comparisons]
  | cons i items ih =>
    rw [rowsMeasured,ih]
    simp only [bind,stepMeasured_exact,table_size]
    simp [comparisons,table,Nat.add_mul,Nat.mul_add,
      Nat.add_assoc,Nat.add_comm,Nat.add_left_comm]
    omega

theorem rowsMeasured_value (capacity : Nat) (items : List (Item α)) :
    (rowsMeasured capacity items).1 = table capacity items := by rw [rowsMeasured_exact]

theorem runMeasured_exact (capacity : Nat) (items : List (Item α)) :
    runMeasured capacity items =
      (select capacity items,
       (items.length*(capacity+1),comparisons capacity items,items.length*(capacity+1),
        items.length*(23*(capacity+1)+10)+23*comparisons capacity items+
          3*(capacity+1)+3*(select capacity items).names.length+10)) := by
  simp [runMeasured,rowsMeasured_exact,bind,observeMeasured_exact,table_read,
    Nat.add_assoc]
  omega

theorem runMeasured_value (capacity : Nat) (items : List (Item α)) :
    (runMeasured capacity items).1 = select capacity items := by rw [runMeasured_exact]

theorem runMeasured_optimal (capacity : Nat) (items : List (Item α)) :
    Optimal capacity items (runMeasured capacity items).1 := by
  rw [runMeasured_value]
  exact select_optimal capacity items

/-- Any additive tariff commutes with the actual pipeline, including its
intermediate array and output selection, rather than merely its final counts. -/
theorem runMeasured_reweight (f : Work →+ Nat) (capacity : Nat) (items : List (Item α)) :
    reweight f (runMeasured capacity items) =
      bind (reweight f (rowsMeasured capacity items)) fun row =>
        bind (reweight f (read row capacity,(0,0,0,3)))
          (fun s => reweight f (observeMeasured s)) := by
  simp only [runMeasured,reweight_bind]

theorem runMeasured_tariff (tests comparisons' updates work capacity : Nat)
    (items : List (Item α)) :
    (reweight (tariff tests comparisons' updates work) (runMeasured capacity items)).2 =
      tests*(items.length*(capacity+1)) + comparisons'*comparisons capacity items +
      updates*(items.length*(capacity+1)) +
      work*(items.length*(23*(capacity+1)+10)+23*comparisons capacity items+
        3*(capacity+1)+3*(select capacity items).names.length+10) := by
  rw [runMeasured_exact]
  rfl

theorem comparisons_bound (capacity : Nat) (items : List (Item α)) :
    comparisons capacity items ≤ items.length*(capacity+1) := by
  induction items with
  | nil => simp [comparisons]
  | cons i items ih =>
    simp only [comparisons,List.map_cons,List.sum_cons] at ih ⊢
    simp only [List.length_cons,Nat.add_mul,Nat.one_mul]
    omega

theorem rowsMeasured_bound (capacity : Nat) (items : List (Item α)) :
    (rowsMeasured capacity items).2.2.2.2 ≤
      items.length*(50*(capacity+1)+11)+3*(capacity+1)+3 := by
  have hc := comparisons_bound capacity items
  rw [rowsMeasured_exact]
  simp only [Nat.mul_add,Nat.mul_one] at hc
  simp only [Nat.mul_add,Nat.mul_left_comm]
  omega

theorem runMeasured_bound (capacity : Nat) (items : List (Item α)) :
    (runMeasured capacity items).2.2.2.2 ≤ 80*(items.length+1)*(capacity+1) := by
  have hc := comparisons_bound capacity items
  have hn := select_names_bound capacity items
  rw [runMeasured_exact]
  simp only [Nat.mul_add,Nat.mul_one] at hc
  simp only [Nat.mul_add,Nat.add_mul,Nat.mul_one,Nat.mul_assoc,Nat.mul_left_comm]
  omega

/-- Scalar copies charged at the actual old arrays reached by the row fold. -/
def copyCharges (capacity : Nat) : List (Item α) → List Nat
  | [] => []
  | _ :: items => copyCharges capacity items ++ [(copy (rowsMeasured capacity items).1).2.2.2.2]

theorem copyCharges_exact (capacity : Nat) (items : List (Item α)) :
    copyCharges capacity items = List.replicate items.length (2*(capacity+1)+1) := by
  induction items with
  | nil => rfl
  | cons i items ih =>
    simp [copyCharges,ih,copy,rowsMeasured_value,table_size,List.replicate_succ',List.length_cons]

theorem immutable_copy_contribution (capacity : Nat) (items : List (Item α)) :
    (copyCharges capacity items).sum = items.length*(2*(capacity+1)+1) := by
  rw [copyCharges_exact]
  simp [List.sum_replicate_nat]

/-- The source's slot-copy contribution excludes one administrative unit per
batch; both contributions remain present in the complete scalar execution. -/
theorem immutable_copy_slots (capacity : Nat) (items : List (Item α)) :
    (copyCharges capacity items).sum = 2*items.length*(capacity+1)+items.length := by
  rw [immutable_copy_contribution]
  rw [Nat.mul_add,Nat.mul_one,← Nat.mul_assoc,Nat.mul_comm items.length 2]

/-- Literal source whole-row recurrence, using the already recovered row model. -/
def sourceRowsRun (capacity : Nat) : List (Item α) → Array (Selection α) × Nat
  | [] => (start capacity,3*(capacity+1)+3)
  | i :: items =>
      let r := sourceRowsRun capacity items
      let s := sourceStepRun capacity i r.1
      (s.1,r.2+s.2+1)

def sourceObserve (s : Selection α) : Selection α × Nat :=
  let r := sourceMapRun (fun name => (name,1)) s.names
  (⟨r.1,s.value,s.weight⟩,r.2+3)

def sourceRun (capacity : Nat) (items : List (Item α)) : Selection α × Nat :=
  let r := sourceRowsRun capacity items
  let o := sourceObserve (read r.1 capacity)
  (o.1,r.2+o.2+3)

theorem sourceObserve_exact (s : Selection α) : sourceObserve s = (s,3*s.names.length+4) := by
  have hm (xs : List α) : sourceMapRun (fun name => (name,1)) xs = (xs,3*xs.length+1) := by
    induction xs with
    | nil => rfl
    | cons x xs ih => simp [sourceMapRun,ih,Nat.mul_add]; omega
  cases s
  simp [sourceObserve,hm,Nat.add_assoc]

theorem rowsMeasured_sourceScalar (capacity : Nat) (items : List (Item α)) :
    reweight (fun w : Work => w.2.2.2) (rowsMeasured capacity items) = sourceRowsRun capacity items := by
  induction items with
  | nil => rfl
  | cons i items ih =>
    have hv := congrArg Prod.fst ih
    have hc := congrArg Prod.snd ih
    have hs := stepMeasured_sourceScalar capacity i (rowsMeasured capacity items).1
    have hsv := congrArg Prod.fst hs
    have hsc := congrArg Prod.snd hs
    dsimp [reweight] at hv hc hsv hsc
    simp only [rowsMeasured,sourceRowsRun,bind,reweight,Prod.snd_add]
    rw [hv] at hsv hsc ⊢
    rw [hc,hsv,hsc]
    simp [Nat.add_assoc]

theorem runMeasured_sourceScalar (capacity : Nat) (items : List (Item α)) :
    reweight (fun w : Work => w.2.2.2) (runMeasured capacity items) = sourceRun capacity items := by
  have hr := rowsMeasured_sourceScalar capacity items
  have hv := congrArg Prod.fst hr
  have hc := congrArg Prod.snd hr
  dsimp [reweight] at hv hc
  simp [runMeasured,bind,reweight,observeMeasured_exact,sourceRun,sourceObserve_exact,hv,hc,
    Nat.add_comm,Nat.add_left_comm]

theorem sourceRun_value (capacity : Nat) (items : List (Item α)) :
    (sourceRun capacity items).1 = select capacity items := by
  rw [← runMeasured_sourceScalar]
  exact runMeasured_value capacity items

theorem sourceRun_bound (capacity : Nat) (items : List (Item α)) :
    (sourceRun capacity items).2 ≤ 80*(items.length+1)*(capacity+1) := by
  rw [← runMeasured_sourceScalar]
  exact runMeasured_bound capacity items

theorem sourceRowsRun_value (capacity : Nat) (items : List (Item α)) :
    (sourceRowsRun capacity items).1 = table capacity items := by
  rw [← rowsMeasured_sourceScalar]
  exact rowsMeasured_value capacity items

theorem sourceRowsRun_bound (capacity : Nat) (items : List (Item α)) :
    (sourceRowsRun capacity items).2 ≤
      items.length*(50*(capacity+1)+11)+3*(capacity+1)+3 := by
  rw [← rowsMeasured_sourceScalar]
  exact rowsMeasured_bound capacity items

theorem sourceRun_optimal (capacity : Nat) (items : List (Item α)) :
    Optimal capacity items (sourceRun capacity items).1 := by
  rw [sourceRun_value]
  exact select_optimal capacity items

theorem rowsMeasured_entry (capacity : Nat) (items : List (Item α))
    (j : Nat) (hj : j ≤ capacity) :
    (rowsMeasured capacity items).1[j]? = some (select j items) := by
  rw [rowsMeasured_value,table_entry capacity items j hj]

theorem runMeasured_answer (capacity : Nat) (items : List (Item α)) :
    (runMeasured capacity items).1 = answer capacity items := by
  rw [runMeasured_value,answer_eq_select]

/-- The copy charges are included in the complete scalar work. -/
theorem copies_charged_in_run (capacity : Nat) (items : List (Item α)) :
    (copyCharges capacity items).sum ≤ (runMeasured capacity items).2.2.2.2 := by
  rw [immutable_copy_contribution,runMeasured_exact]
  simp only [Nat.mul_add,Nat.mul_one,Nat.mul_left_comm]
  omega

end Resources.Knapsack
