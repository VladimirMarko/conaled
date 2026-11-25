import Applications.Resources.BinomialQueue.Measured
import Applications.Resources.BinaryCounter
import Applications.Search.BinomialQueue.Contents
import Applications.Search.BinomialQueue.Maximum
import Applications.Search.BinomialQueue.Ranked

/-!
# Exact source counts and explicit tariff bounds

Stored slots, occupied slots and detached sibling roots are different sizes.
The observations below are taken from the actual measured operations. Comparator
work follows their returned Booleans; uniform bounds require an explicit bound
on the supplied comparator. No claim concerns native execution costs.
-/
set_option autoImplicit false
set_option warningAsError true

namespace Resources.BinomialQueue

universe u
variable {K : Type u}

open Search.BinomialQueue
open scoped BigOperators

theorem smashRun_counts (cmp : K → K → Measured Bool Nat) (t v : BinaryTree K) :
    (smashRun cmp t v).2 .smashCalls = 1 ∧
    (smashRun cmp t v).2 .carryCalls = 0 ∧
    (smashRun cmp t v).2 .joinCalls = 0 ∧
    (smashRun cmp t v).2 .comparisons ≤ 1 ∧
    (smashRun cmp t v).2 .cons = 0 ∧
    (smashRun cmp t v).2 .nodes = 2 * (smashRun cmp t v).2 .comparisons := by
  cases t with
  | nil => cases v <;> simp [smashRun, bill, charge]
  | node x a b =>
      cases b <;> cases v with
      | nil => simp [smashRun, bill, charge]
      | node y c d => cases d <;> simp [smashRun, bill, charge]

/-- Every raw carry is bounded by stored slots, including malformed links. -/
theorem carryRun_bounds (cmp : K → K → Measured Bool Nat) (q : Queue K) (t : BinaryTree K) :
    (carryRun cmp q t).2 .carryCalls ≤ q.length + 1 ∧
    (carryRun cmp q t).2 .smashCalls ≤ q.length ∧
    (carryRun cmp q t).2 .comparisons ≤ q.length ∧
    (carryRun cmp q t).2 .cons ≤ q.length + 1 ∧
    (carryRun cmp q t).2 .nodes ≤ 2 * q.length ∧
    (carryRun cmp q t).2 .joinCalls = 0 := by
  induction q generalizing t with
  | nil => cases t <;> simp [carryRun, bill, charge]
  | cons head tail ih =>
      cases head with
      | nil => cases t <;> simp [carryRun, bill, charge]
      | node x a b =>
          cases t with
          | nil => simp [carryRun, bill, charge]
          | node y c d =>
              have hs := smashRun_counts cmp (.node y c d) (.node x a b)
              have ht := ih (smashRun cmp (.node y c d) (.node x a b)).1
              simp only [carryRun, Pi.add_apply, List.length_cons]
              simp only [bill, charge, Pi.add_apply] at *
              simp only [ite_true, ite_false, reduceCtorEq, Nat.add_zero, Nat.zero_add] at *
              omega

/-- Exact work of a proper occupied carry; redundant high nil slots are allowed. -/
theorem carryRun_leading_counts (cmp : K → K → Measured Bool Nat)
    (q : Queue K) (t : BinaryTree K) (proper : ∀ v ∈ q, Proper v)
    (ht : Proper t) (nonempty : t ≠ .nil) :
    let r := BinaryCounter.leadingOnes (occupancy q)
    (carryRun cmp q t).2 .carryCalls = r + 1 ∧
    (carryRun cmp q t).2 .smashCalls = r ∧
    (carryRun cmp q t).2 .comparisons = r ∧
    (carryRun cmp q t).2 .cons = r + 1 ∧
    (carryRun cmp q t).2 .nodes = 2 * r := by
  induction q generalizing t with
  | nil =>
      cases t with
      | nil => exact (nonempty rfl).elim
      | node x a b => simp [carryRun, bill, charge, occupancy, BinaryCounter.leadingOnes]
  | cons head tail ih =>
      have hp := proper head (by simp)
      have htail : ∀ v ∈ tail, Proper v := fun v hv => proper v (by simp [hv])
      cases t with
      | nil => exact (nonempty rfl).elim
      | node y c d =>
          have hd : d = .nil := ht
          subst d
          cases head with
          | nil =>
              simp [carryRun, bill, charge, occupancy, occupied, BinaryCounter.leadingOnes]
          | node x a b =>
              have hb : b = .nil := hp
              subst b
              cases tested : (cmp y x).1 with
              | false =>
                  have hrec := ih (.node x (.node y c a) .nil) htail rfl (by simp)
                  simpa [carryRun, smashRun, tested, bill, charge, occupancy, occupied,
                    BinaryCounter.leadingOnes, Nat.mul_add, Nat.add_assoc, Nat.add_comm,
                    Nat.add_left_comm] using hrec
              | true =>
                  have hrec := ih (.node y (.node x a c) .nil) htail rfl (by simp)
                  simpa [carryRun, smashRun, tested, bill, charge, occupancy, occupied,
                    BinaryCounter.leadingOnes, Nat.mul_add, Nat.add_assoc, Nat.add_comm,
                    Nat.add_left_comm] using hrec

theorem insertRun_leading_counts (cmp : K → K → Measured Bool Nat)
    (key : K) (q : Queue K) (proper : ∀ t ∈ q, Proper t) :
    let r := BinaryCounter.leadingOnes (occupancy q)
    (insertRun cmp key q).2 .comparisons = r ∧
    (insertRun cmp key q).2 .carryCalls = r + 1 ∧
    (insertRun cmp key q).2 .cons = r + 1 ∧
    (insertRun cmp key q).2 .nodes = 2 * r + 1 := by
  have h := carryRun_leading_counts cmp q (.node key .nil .nil) proper rfl (by simp)
  simp only [insertRun, Pi.add_apply, bill, charge] at *
  simp only [ite_true, ite_false, reduceCtorEq, Nat.add_zero, Nat.zero_add] at *
  omega

/-- Paired slots and the final carry suffix are both charged. -/
theorem joinRun_bounds (cmp : K → K → Measured Bool Nat)
    (p q : Queue K) (c : BinaryTree K) :
    (joinRun cmp p q c).2 .joinCalls = min p.length q.length + 1 ∧
    (joinRun cmp p q c).2 .joinCalls + (joinRun cmp p q c).2 .carryCalls ≤
      max p.length q.length + 2 ∧
    (joinRun cmp p q c).2 .comparisons ≤ max p.length q.length ∧
    (joinRun cmp p q c).2 .cons ≤ max p.length q.length + 1 ∧
    (joinRun cmp p q c).2 .nodes ≤ 2 * max p.length q.length := by
  induction p generalizing q c with
  | nil =>
      have h := carryRun_bounds cmp q c
      simp only [joinRun, Pi.add_apply, List.length_nil, Nat.zero_min, Nat.zero_max]
      simp only [bill, charge, Pi.add_apply] at *
      simp only [ite_true, ite_false, reduceCtorEq, Nat.add_zero, Nat.zero_add] at *
      omega
  | cons head tail ih =>
      cases q with
      | nil =>
          have h := carryRun_bounds cmp (head :: tail) c
          simp only [joinRun, Pi.add_apply, List.length_nil, Nat.min_zero, Nat.max_zero]
          simp only [bill, charge, Pi.add_apply] at *
          simp only [ite_true, ite_false, reduceCtorEq, Nat.add_zero, Nat.zero_add] at *
          omega
      | cons other rest =>
          have hn := ih rest (.nil : BinaryTree K)
          have hhc := smashRun_counts cmp c head
          have hoc := smashRun_counts cmp c other
          have hho := smashRun_counts cmp head other
          have hrh := ih rest (smashRun cmp c head).1
          have hro := ih rest (smashRun cmp c other).1
          have hrt := ih rest (smashRun cmp head other).1
          cases head <;> cases other <;> cases c <;>
            simp only [joinRun, Pi.add_apply, List.length_cons] <;>
            simp only [bill, charge, Pi.add_apply] at * <;>
            simp only [ite_true, ite_false, reduceCtorEq, Nat.add_zero, Nat.zero_add] at * <;>
            omega

/-- The source executes every root slot and the final empty case. -/
theorem findMaxAuxRun_counts (cmp : K → K → Measured Bool Nat) (current : K) (q : Queue K) :
    (findMaxAuxRun cmp current q).2 .findMaxAuxCalls = q.length + 1 ∧
    (findMaxAuxRun cmp current q).2 .findMaxCalls = 0 ∧
    (findMaxAuxRun cmp current q).2 .comparisons = BinaryCounter.ones (occupancy q) := by
  induction q generalizing current with
  | nil => simp [findMaxAuxRun, bill, charge, occupancy, BinaryCounter.ones]
  | cons head tail ih =>
      cases head with
      | nil =>
          rcases ih current with ⟨hc, hf, hp⟩
          simp [findMaxAuxRun, bill, charge, hc, hf, hp, occupancy, occupied,
            BinaryCounter.ones, Nat.add_comm]
      | node x a b =>
          rcases ih (if (cmp x current).1 then x else current) with ⟨hc, hf, hp⟩
          simp [findMaxAuxRun, bill, charge, hc, hf, hp, occupancy, occupied,
            BinaryCounter.ones, Nat.add_comm]

theorem findMaxRun_counts (cmp : K → K → Measured Bool Nat) (q : Queue K) :
    (findMaxRun cmp q).2 .findMaxCalls + (findMaxRun cmp q).2 .findMaxAuxCalls =
      q.length + 1 ∧
    (findMaxRun cmp q).2 .comparisons = BinaryCounter.ones (occupancy q) - 1 := by
  induction q with
  | nil => simp [findMaxRun, bill, charge, occupancy, BinaryCounter.ones]
  | cons head tail ih =>
      cases head with
      | nil =>
          simp only [findMaxRun, Pi.add_apply, bill, charge, List.length_cons,
            occupancy_cons, occupied_nil, BinaryCounter.ones]
          simp only [ite_true, ite_false, reduceCtorEq, Nat.add_zero, Nat.zero_add]
          omega
      | node x a b =>
          have h := findMaxAuxRun_counts cmp x tail
          simp only [findMaxRun, Pi.add_apply, bill, charge, List.length_cons,
            occupancy_cons, occupied_node, BinaryCounter.ones]
          simp only [ite_true, ite_false, reduceCtorEq, Nat.add_zero, Nat.zero_add]
          omega

/-- Zero semantic size does not bound the number of stored slots scanned. -/
theorem findMaxRun_padding (cmp : K → K → Measured Bool Nat) (n : Nat) :
    findMaxRun cmp (List.replicate n .nil) =
      (none, charge .findMaxCalls (n + 1)) := by
  induction n with
  | zero =>
      apply Prod.ext
      · rfl
      · funext metric
        cases metric <;> simp [findMaxRun, bill, charge]
  | succ n ih =>
      simp only [List.replicate_succ, findMaxRun, ih]
      apply Prod.ext
      · rfl
      · funext metric
        cases metric <;> simp [bill, charge, Nat.add_comm]

/-- Cost of the closures introduced by unzip, excluding its supplied continuation. -/
def unzipBill (n : Nat) : Cost :=
  charge .unzipCalls (n + 1) + charge .cons n + charge .nodes n +
    charge .closures n + charge .applications n

/-- The arbitrary continuation is called at [], with its own work preserved. -/
theorem unzipRun_cost (t : BinaryTree K) (cont : Queue K → Measured (Queue K) Cost) :
    (unzipRun t cont).2 = unzipBill (unzip t id).length + (cont []).2 := by
  induction t generalizing cont with
  | nil =>
      funext metric
      cases metric <;> simp [unzipRun, unzip, unzipBill, bill, charge]
  | node x a b _ ih =>
      simp only [unzipRun, ih, unzip_node_id, List.length_append, List.length_cons,
        List.length_nil]
      funext metric
      cases metric <;>
        simp [unzipBill, bill, charge, Nat.add_assoc, Nat.add_comm, Nat.add_left_comm]

theorem unzipRun_identity_cost (t : BinaryTree K) :
    (unzipRun t identityRun).2 =
      unzipBill (unzip t id).length + charge .applications 1 :=
  unzipRun_cost t identityRun

theorem heapDeleteMaxRun_proper_cost (key : K) (child : BinaryTree K) :
    (heapDeleteMaxRun (.node key child .nil)).2 =
      charge .heapDeleteMaxCalls 1 + unzipBill (unzip child id).length +
        charge .applications 1 := by
  rw [heapDeleteMaxRun, unzipRun_identity_cost]
  funext metric
  cases metric <;> simp [bill, charge]

/-- Prices include the actual comparator work bound, not an implicit unit cost. -/
def smashPrice (prices : Cost) (comparisonBound : Nat) : Nat :=
  prices .smashCalls + prices .comparisons +
    prices .comparisonWork * comparisonBound + prices .nodes * 2

def carryPrice (prices : Cost) (comparisonBound : Nat) : Nat :=
  prices .carryCalls + prices .cons + smashPrice prices comparisonBound

def insertPrice (prices : Cost) (comparisonBound : Nat) : Nat :=
  prices .insertCalls + prices .nodes + carryPrice prices comparisonBound

def joinPrice (prices : Cost) (comparisonBound : Nat) : Nat :=
  prices .joinCalls + prices .cons + smashPrice prices comparisonBound +
    carryPrice prices comparisonBound

def scanPrice (prices : Cost) (comparisonBound : Nat) : Nat :=
  prices .findMaxCalls + prices .findMaxAuxCalls + prices .comparisons +
    prices .comparisonWork * comparisonBound

theorem smashRun_weighted_le (cmp : K → K → Measured Bool Nat) (prices : Cost) (C : Nat)
    (bound : ∀ x y, (cmp x y).2 ≤ C) (t v : BinaryTree K) :
    weighted prices (smashRun cmp t v).2 ≤ smashPrice prices C := by
  cases t with
  | nil =>
      cases v <;> simp only [smashRun, weighted_bill, Nat.mul_zero, Nat.add_zero]
      all_goals unfold smashPrice; omega
  | node x a b =>
      cases b with
      | node =>
          cases v <;> simp only [smashRun, weighted_bill, Nat.mul_zero, Nat.add_zero]
          all_goals unfold smashPrice; omega
      | nil =>
          cases v with
          | nil =>
              simp only [smashRun, weighted_bill, Nat.mul_zero, Nat.add_zero]
              unfold smashPrice
              omega
          | node y c d =>
              cases d with
              | node =>
                  simp only [smashRun, weighted_bill, Nat.mul_zero, Nat.add_zero]
                  unfold smashPrice
                  omega
              | nil =>
                  have h := Nat.mul_le_mul_left (prices .comparisonWork) (bound x y)
                  simp only [smashRun, weighted_bill, Nat.mul_zero, Nat.mul_one, Nat.add_zero]
                  unfold smashPrice
                  omega

theorem carryRun_weighted_le (cmp : K → K → Measured Bool Nat) (prices : Cost) (C : Nat)
    (bound : ∀ x y, (cmp x y).2 ≤ C) (q : Queue K) (t : BinaryTree K) :
    weighted prices (carryRun cmp q t).2 ≤ (q.length + 1) * carryPrice prices C := by
  induction q generalizing t with
  | nil =>
      cases t <;>
        simp only [carryRun, weighted_bill, Nat.mul_zero, Nat.mul_one, Nat.add_zero,
          List.length_nil, Nat.zero_add, Nat.one_mul]
      all_goals unfold carryPrice; omega
  | cons head tail ih =>
      cases head with
      | nil =>
          cases t <;>
            simp only [carryRun, weighted_bill, Nat.mul_zero, Nat.mul_one, Nat.add_zero]
          all_goals
            have h := Nat.le_mul_of_pos_left (carryPrice prices C)
              (show 0 < (.nil :: tail).length + 1 by simp)
            unfold carryPrice at *
            omega
      | node x a b =>
          cases t with
          | nil =>
              simp only [carryRun, weighted_bill, Nat.mul_zero, Nat.mul_one, Nat.add_zero]
              have h := Nat.le_mul_of_pos_left (carryPrice prices C)
                (show 0 < (.node x a b :: tail).length + 1 by simp)
              unfold carryPrice at *
              omega
          | node y c d =>
              have hs := smashRun_weighted_le cmp prices C bound (.node y c d) (.node x a b)
              have ht := ih (smashRun cmp (.node y c d) (.node x a b)).1
              simp only [carryRun, weighted_add, weighted_bill, Nat.mul_zero,
                Nat.mul_one, Nat.add_zero, List.length_cons]
              simp only [carryPrice, Nat.add_mul, Nat.mul_add, Nat.one_mul] at *
              omega

theorem insertRun_weighted_le (cmp : K → K → Measured Bool Nat) (prices : Cost) (C : Nat)
    (bound : ∀ x y, (cmp x y).2 ≤ C) (key : K) (q : Queue K) :
    weighted prices (insertRun cmp key q).2 ≤ (q.length + 1) * insertPrice prices C := by
  have h := carryRun_weighted_le cmp prices C bound q (.node key .nil .nil)
  have hentry := Nat.le_mul_of_pos_left (prices .insertCalls + prices .nodes)
    (show 0 < q.length + 1 by omega)
  simp only [insertRun, weighted_add, weighted_bill, Nat.mul_zero, Nat.mul_one, Nat.add_zero]
  simp only [insertPrice, Nat.mul_add] at *
  omega

theorem joinRun_weighted_le (cmp : K → K → Measured Bool Nat) (prices : Cost) (C : Nat)
    (bound : ∀ x y, (cmp x y).2 ≤ C) (p q : Queue K) (c : BinaryTree K) :
    weighted prices (joinRun cmp p q c).2 ≤
      (max p.length q.length + 2) * joinPrice prices C := by
  induction p generalizing q c with
  | nil =>
      have h := carryRun_weighted_le cmp prices C bound q c
      have hcarry : carryPrice prices C ≤ joinPrice prices C := by unfold joinPrice; omega
      have hs := Nat.mul_le_mul_left (q.length + 1) hcarry
      simp only [joinRun, weighted_add, weighted_bill, Nat.mul_zero, Nat.add_zero,
        List.length_nil, Nat.zero_max]
      simp only [Nat.add_mul, Nat.one_mul] at *
      unfold joinPrice at *
      omega
  | cons head tail ih =>
      cases q with
      | nil =>
          have h := carryRun_weighted_le cmp prices C bound (head :: tail) c
          have hcarry : carryPrice prices C ≤ joinPrice prices C := by unfold joinPrice; omega
          have hs := Nat.mul_le_mul_left ((head :: tail).length + 1) hcarry
          simp only [joinRun, weighted_add, weighted_bill, Nat.mul_zero, Nat.add_zero,
            List.length_nil, Nat.max_zero]
          simp only [Nat.add_mul, Nat.one_mul] at *
          unfold joinPrice at *
          omega
      | cons other rest =>
          have hn := ih rest (.nil : BinaryTree K)
          have hhc := smashRun_weighted_le cmp prices C bound c head
          have hoc := smashRun_weighted_le cmp prices C bound c other
          have hho := smashRun_weighted_le cmp prices C bound head other
          have hrh := ih rest (smashRun cmp c head).1
          have hro := ih rest (smashRun cmp c other).1
          have hrt := ih rest (smashRun cmp head other).1
          have hmax : max (tail.length + 1) (rest.length + 1) =
              max tail.length rest.length + 1 := by omega
          cases head <;> cases other <;> cases c <;>
            simp only [joinRun, weighted_add, weighted_bill, Nat.mul_zero, Nat.mul_one,
              Nat.add_zero, List.length_cons, hmax] <;>
            simp only [Nat.add_mul, Nat.one_mul] at * <;>
            unfold joinPrice at * <;> omega

theorem findMaxAuxRun_weighted_le (cmp : K → K → Measured Bool Nat)
    (prices : Cost) (C : Nat) (bound : ∀ x y, (cmp x y).2 ≤ C) (current : K) (q : Queue K) :
    weighted prices (findMaxAuxRun cmp current q).2 ≤ (q.length + 1) * scanPrice prices C := by
  induction q generalizing current with
  | nil =>
      simp only [findMaxAuxRun, weighted_bill, Nat.mul_zero, Nat.add_zero,
        List.length_nil, Nat.zero_add, Nat.one_mul]
      unfold scanPrice
      omega
  | cons head tail ih =>
      cases head with
      | nil =>
          have h := ih current
          simp only [findMaxAuxRun, weighted_add, weighted_bill, Nat.mul_zero,
            Nat.add_zero, List.length_cons]
          simp only [scanPrice, Nat.add_mul, Nat.one_mul] at *
          omega
      | node x a b =>
          have h := ih (if (cmp x current).1 then x else current)
          have hc := Nat.mul_le_mul_left (prices .comparisonWork) (bound x current)
          simp only [findMaxAuxRun, weighted_add, weighted_bill, Nat.mul_zero,
            Nat.mul_one, Nat.add_zero, List.length_cons]
          simp only [scanPrice, Nat.add_mul, Nat.one_mul] at *
          omega

theorem findMaxRun_weighted_le (cmp : K → K → Measured Bool Nat)
    (prices : Cost) (C : Nat) (bound : ∀ x y, (cmp x y).2 ≤ C) (q : Queue K) :
    weighted prices (findMaxRun cmp q).2 ≤ (q.length + 1) * scanPrice prices C := by
  induction q with
  | nil =>
      simp only [findMaxRun, weighted_bill, Nat.mul_zero, Nat.add_zero,
        List.length_nil, Nat.zero_add, Nat.one_mul]
      unfold scanPrice
      omega
  | cons head tail ih =>
      cases head with
      | nil =>
          simp only [findMaxRun, weighted_add, weighted_bill, Nat.mul_zero,
            Nat.add_zero, List.length_cons]
          simp only [scanPrice, Nat.add_mul, Nat.one_mul] at *
          omega
      | node x a b =>
          have h := findMaxAuxRun_weighted_le cmp prices C bound x tail
          simp only [findMaxRun, weighted_add, weighted_bill, Nat.mul_zero,
            Nat.add_zero, List.length_cons]
          simp only [scanPrice, Nat.add_mul, Nat.one_mul] at *
          omega

theorem unzipRun_weighted (prices : Cost) (t : BinaryTree K)
    (cont : Queue K → Measured (Queue K) Cost) :
    weighted prices (unzipRun t cont).2 =
      prices .unzipCalls * ((unzip t id).length + 1) +
        prices .cons * (unzip t id).length + prices .nodes * (unzip t id).length +
        prices .closures * (unzip t id).length + prices .applications * (unzip t id).length +
        weighted prices (cont []).2 := by
  simp only [unzipRun_cost, unzipBill, weighted_add, weighted_charge]

/-- The sharper comparator bill uses the actual number of comparisons. -/
theorem smashRun_comparisonWork_le (cmp : K → K → Measured Bool Nat) (C : Nat)
    (bound : ∀ x y, (cmp x y).2 ≤ C) (t v : BinaryTree K) :
    (smashRun cmp t v).2 .comparisonWork ≤ C * (smashRun cmp t v).2 .comparisons := by
  cases t with
  | nil => cases v <;> simp [smashRun, bill, charge]
  | node x a b =>
      cases b <;> cases v with
      | nil => simp [smashRun, bill, charge]
      | node y c d =>
          cases d <;> simp [smashRun, bill, charge, bound]

theorem carryRun_comparisonWork_le (cmp : K → K → Measured Bool Nat) (C : Nat)
    (bound : ∀ x y, (cmp x y).2 ≤ C) (q : Queue K) (t : BinaryTree K) :
    (carryRun cmp q t).2 .comparisonWork ≤ C * (carryRun cmp q t).2 .comparisons := by
  induction q generalizing t with
  | nil => cases t <;> simp [carryRun, bill, charge]
  | cons head tail ih =>
      cases head with
      | nil => cases t <;> simp [carryRun, bill, charge]
      | node x a b =>
          cases t with
          | nil => simp [carryRun, bill, charge]
          | node y c d =>
              have hs := smashRun_comparisonWork_le cmp C bound (.node y c d) (.node x a b)
              have ht := ih (smashRun cmp (.node y c d) (.node x a b)).1
              simpa [carryRun, bill, charge, Nat.mul_add] using Nat.add_le_add hs ht

theorem insertRun_comparisonWork_le (cmp : K → K → Measured Bool Nat) (C : Nat)
    (bound : ∀ x y, (cmp x y).2 ≤ C) (key : K) (q : Queue K) :
    (insertRun cmp key q).2 .comparisonWork ≤ C * (insertRun cmp key q).2 .comparisons := by
  simpa [insertRun, bill, charge] using
    carryRun_comparisonWork_le cmp C bound q (.node key .nil .nil)

theorem joinRun_comparisonWork_le (cmp : K → K → Measured Bool Nat) (C : Nat)
    (bound : ∀ x y, (cmp x y).2 ≤ C) (p q : Queue K) (c : BinaryTree K) :
    (joinRun cmp p q c).2 .comparisonWork ≤ C * (joinRun cmp p q c).2 .comparisons := by
  induction p generalizing q c with
  | nil =>
      simpa [joinRun, bill, charge] using carryRun_comparisonWork_le cmp C bound q c
  | cons head tail ih =>
      cases q with
      | nil =>
          simpa [joinRun, bill, charge] using
            carryRun_comparisonWork_le cmp C bound (head :: tail) c
      | cons other rest =>
          have hn := ih rest (.nil : BinaryTree K)
          have hhc := smashRun_comparisonWork_le cmp C bound c head
          have hoc := smashRun_comparisonWork_le cmp C bound c other
          have hho := smashRun_comparisonWork_le cmp C bound head other
          have hrh := ih rest (smashRun cmp c head).1
          have hro := ih rest (smashRun cmp c other).1
          have hrt := ih rest (smashRun cmp head other).1
          cases head <;> cases other <;> cases c <;>
            simp only [joinRun, Pi.add_apply, bill, charge, Nat.mul_add] <;>
            simp only [ite_true, ite_false, reduceCtorEq, Nat.add_zero, Nat.zero_add,
              Nat.mul_zero] <;> omega

theorem findMaxAuxRun_comparisonWork_le (cmp : K → K → Measured Bool Nat) (C : Nat)
    (bound : ∀ x y, (cmp x y).2 ≤ C) (current : K) (q : Queue K) :
    (findMaxAuxRun cmp current q).2 .comparisonWork ≤
      C * (findMaxAuxRun cmp current q).2 .comparisons := by
  induction q generalizing current with
  | nil => simp [findMaxAuxRun, bill, charge]
  | cons head tail ih =>
      cases head with
      | nil => simpa [findMaxAuxRun, bill, charge] using ih current
      | node x a b =>
          have ht := ih (if (cmp x current).1 then x else current)
          have hc := bound x current
          simpa [findMaxAuxRun, bill, charge, Nat.mul_add, Nat.add_comm] using
            Nat.add_le_add hc ht

theorem findMaxRun_comparisonWork_le (cmp : K → K → Measured Bool Nat) (C : Nat)
    (bound : ∀ x y, (cmp x y).2 ≤ C) (q : Queue K) :
    (findMaxRun cmp q).2 .comparisonWork ≤ C * (findMaxRun cmp q).2 .comparisons := by
  induction q with
  | nil => simp [findMaxRun, bill, charge]
  | cons head tail ih =>
      cases head with
      | nil => simpa [findMaxRun, bill, charge] using ih
      | node x a b =>
          simpa [findMaxRun, bill, charge] using findMaxAuxRun_comparisonWork_le cmp C bound x tail

theorem heapDeleteMaxRun_comparisons (t : BinaryTree K) :
    (heapDeleteMaxRun t).2 .comparisons = 0 ∧
    (heapDeleteMaxRun t).2 .comparisonWork = 0 := by
  cases t with
  | nil => simp [heapDeleteMaxRun, bill, charge]
  | node x a b =>
      cases b <;>
        simp [heapDeleteMaxRun, unzipRun_cost, unzipBill, identityRun, bill, charge]

theorem deleteMaxAuxRun_comparisonWork_le (cmp : K → K → Measured Bool Nat) (C : Nat)
    (bound : ∀ x y, (cmp x y).2 ≤ C) (m : K) (q : Queue K) :
    (deleteMaxAuxRun cmp m q).2 .comparisonWork ≤
      C * (deleteMaxAuxRun cmp m q).2 .comparisons := by
  induction q with
  | nil => simp [deleteMaxAuxRun, bill, charge]
  | cons head tail ih =>
      cases head with
      | nil => simpa [deleteMaxAuxRun, bill, charge] using ih
      | node x a b =>
          cases b with
          | node => simp [deleteMaxAuxRun, bill, charge]
          | nil =>
              have hc := bound m x
              have hh := heapDeleteMaxRun_comparisons (.node x a .nil)
              cases tested : (cmp m x).1 <;>
                simp [deleteMaxAuxRun, tested, bill, charge, hh.1, hh.2,
                  Nat.mul_add] <;> omega

theorem deleteMaxRun_comparisonWork_le (cmp : K → K → Measured Bool Nat) (C : Nat)
    (bound : ∀ x y, (cmp x y).2 ≤ C) (q : Queue K) :
    (deleteMaxRun cmp q).2 .comparisonWork ≤ C * (deleteMaxRun cmp q).2 .comparisons := by
  have hs := findMaxRun_comparisonWork_le cmp C bound q
  cases found : (findMaxRun cmp q).1 with
  | none => simpa [deleteMaxRun, found, bill, charge] using hs
  | some m =>
      have hd := deleteMaxAuxRun_comparisonWork_le cmp C bound m q
      have hj := joinRun_comparisonWork_le cmp C bound
        (deleteMaxAuxRun cmp m q).1.1 (deleteMaxAuxRun cmp m q).1.2 .nil
      simpa [deleteMaxRun, found, bill, charge, Nat.mul_add] using
        Nat.add_le_add (Nat.add_le_add hs hd) hj

theorem mergeRun_comparisonWork_le (cmp : K → K → Measured Bool Nat) (C : Nat)
    (bound : ∀ x y, (cmp x y).2 ≤ C) (p q : Queue K) :
    (mergeRun cmp p q).2 .comparisonWork ≤ C * (mergeRun cmp p q).2 .comparisons := by
  simpa [mergeRun, bill, charge] using joinRun_comparisonWork_le cmp C bound p q .nil

theorem emptyRun_weighted (prices : Cost) :
    weighted prices (emptyRun : Measured (Queue K) Cost).2 = prices .emptyCalls := by
  simp [emptyRun, weighted_bill]

theorem smashRun_proper_cost (cmp : K → K → Measured Bool Nat) (x y : K)
    (a b : BinaryTree K) :
    (smashRun cmp (.node x a .nil) (.node y b .nil)).2 =
      bill .smashCalls 1 (cmp x y).2 0 2 0 0 := rfl

theorem carryRun_leaf (cmp : K → K → Measured Bool Nat) (q : Queue K) :
    carryRun cmp q .nil = (q, bill .carryCalls 0 0 (if q = [] then 0 else 1) 0 0 0) := by
  cases q with
  | nil => rfl
  | cons t q => cases t <;> rfl

theorem mergeRun_weighted_le (cmp : K → K → Measured Bool Nat) (prices : Cost) (C : Nat)
    (bound : ∀ x y, (cmp x y).2 ≤ C) (p q : Queue K) :
    weighted prices (mergeRun cmp p q).2 ≤
      (max p.length q.length + 2) * (prices .mergeCalls + joinPrice prices C) := by
  have h := joinRun_weighted_le cmp prices C bound p q .nil
  have he := Nat.le_mul_of_pos_left (prices .mergeCalls)
    (show 0 < max p.length q.length + 2 by omega)
  simp only [mergeRun, weighted_add, weighted_bill, Nat.mul_zero, Nat.add_zero, Nat.mul_add]
  omega

/-- The measured bill of an inspected proper prefix, in source slot order.
This list sum is an observation, not an alternative deletion executor. -/
def deletePrefixBill (cmp : K → K → Measured Bool Nat) (m : K) (before : Queue K) : Cost :=
  (before.map (fun t => match t with
    | .nil => bill .deleteMaxAuxCalls 0 0 1 0 0 0
    | .node x _ _ => bill .deleteMaxAuxCalls 1 (cmp m x).2 1 1 0 0)).sum

theorem deletePrefixBill_counts (cmp : K → K → Measured Bool Nat) (m : K) (before : Queue K) :
    (deletePrefixBill cmp m before) .deleteMaxAuxCalls = before.length ∧
    (deletePrefixBill cmp m before) .comparisons = BinaryCounter.ones (occupancy before) ∧
    (deletePrefixBill cmp m before) .cons = before.length ∧
    (deletePrefixBill cmp m before) .nodes = BinaryCounter.ones (occupancy before) ∧
    (deletePrefixBill cmp m before) .unzipCalls = 0 ∧
    (deletePrefixBill cmp m before) .heapDeleteMaxCalls = 0 ∧
    (deletePrefixBill cmp m before) .closures = 0 ∧
    (deletePrefixBill cmp m before) .applications = 0 := by
  induction before with
  | nil => simp [deletePrefixBill, occupancy, BinaryCounter.ones]
  | cons t before ih =>
      cases t <;>
        simp only [deletePrefixBill, List.map_cons, List.sum_cons, Pi.add_apply,
          bill, charge, List.length_cons, occupancy_cons, occupied_nil, occupied_node,
          BinaryCounter.ones] at * <;>
        simp only [ite_true, ite_false, reduceCtorEq, Nat.add_zero, Nat.zero_add] at * <;>
        omega

/-- The exact source-selected root gives an exact measured prefix/children split. -/
theorem deleteMaxAuxRun_of_split (cmp : K → K → Measured Bool Nat) (m : K)
    (before : Queue K) (child : BinaryTree K) (after : Queue K)
    (proper : ∀ t ∈ before, Proper t)
    (smaller : ∀ x a b, .node x a b ∈ before → (cmp m x).1 = true)
    (self : (cmp m m).1 = false) :
    deleteMaxAuxRun cmp m (before ++ .node m child .nil :: after) =
      ((before ++ .nil :: after, heapDeleteMax (.node m child .nil)),
        deletePrefixBill cmp m before + bill .deleteMaxAuxCalls 1 (cmp m m).2 1 1 0 0 +
          (heapDeleteMaxRun (.node m child .nil)).2) := by
  induction before with
  | nil =>
      simp [deleteMaxAuxRun, self, deletePrefixBill, heapDeleteMaxRun_value]
  | cons t before ih =>
      have ht := proper t (by simp)
      have hp : ∀ v ∈ before, Proper v := fun v hv => proper v (by simp [hv])
      have hs : ∀ x a b, .node x a b ∈ before → (cmp m x).1 = true :=
        fun x a b h => smaller x a b (by simp [h])
      cases t with
      | nil =>
          simp [deleteMaxAuxRun, ih hp hs, deletePrefixBill, add_assoc]
      | node x a b =>
          have hb : b = .nil := ht
          subst b
          have hx := smaller x a .nil (by simp)
          simp [deleteMaxAuxRun, hx, ih hp hs, deletePrefixBill, add_assoc]

/-- The combined cons/node coordinates include detached children; the prefix bill
separately records exactly j+1 reconstructed first-output cons expressions. -/
theorem deleteMaxAuxRun_split_counts (cmp : K → K → Measured Bool Nat) (m : K)
    (before : Queue K) (child : BinaryTree K) (after : Queue K)
    (proper : ∀ t ∈ before, Proper t)
    (smaller : ∀ x a b, .node x a b ∈ before → (cmp m x).1 = true)
    (self : (cmp m m).1 = false) :
    let work := (deleteMaxAuxRun cmp m (before ++ .node m child .nil :: after)).2
    let j := before.length
    let o := BinaryCounter.ones (occupancy before)
    let r := (unzip child id).length
    work .deleteMaxAuxCalls = j + 1 ∧ work .comparisons = o + 1 ∧
    work .cons = j + 1 + r ∧ work .nodes = o + 1 + r ∧
    work .unzipCalls = r + 1 ∧ work .heapDeleteMaxCalls = 1 ∧
    work .closures = r ∧ work .applications = r + 1 := by
  rw [deleteMaxAuxRun_of_split cmp m before child after proper smaller self]
  have h := deletePrefixBill_counts cmp m before
  simp only [heapDeleteMaxRun_proper_cost, Pi.add_apply, unzipBill, bill, charge]
  simp only [ite_true, ite_false, reduceCtorEq, Nat.add_zero, Nat.zero_add]
  omega

def auxiliaryPrice (prices : Cost) (comparisonBound : Nat) : Nat :=
  prices .deleteMaxAuxCalls + prices .comparisons + prices .comparisonWork * comparisonBound +
    prices .cons + prices .nodes

def heapPrice (prices : Cost) : Nat :=
  prices .heapDeleteMaxCalls + prices .unzipCalls + prices .cons + prices .nodes +
    prices .closures + prices .applications

theorem deletePrefixBill_weighted_le (cmp : K → K → Measured Bool Nat)
    (prices : Cost) (C : Nat) (bound : ∀ x y, (cmp x y).2 ≤ C) (m : K) (before : Queue K) :
    weighted prices (deletePrefixBill cmp m before) ≤ before.length * auxiliaryPrice prices C := by
  induction before with
  | nil => simp [deletePrefixBill, weighted]
  | cons t before ih =>
      simp only [deletePrefixBill] at ih
      cases t with
      | nil =>
          simp only [deletePrefixBill, List.map_cons, List.sum_cons, weighted_add,
            weighted_bill, Nat.mul_zero, Nat.mul_one, Nat.add_zero, List.length_cons]
          simp only [auxiliaryPrice, Nat.add_mul, Nat.one_mul] at *
          omega
      | node x a b =>
          have h := Nat.mul_le_mul_left (prices .comparisonWork) (bound m x)
          simp only [deletePrefixBill, List.map_cons, List.sum_cons, weighted_add,
            weighted_bill, Nat.mul_zero, Nat.mul_one, Nat.add_zero, List.length_cons]
          simp only [auxiliaryPrice, Nat.add_mul, Nat.one_mul] at *
          omega

theorem heapDeleteMaxRun_weighted_le (prices : Cost) (m : K) (child : BinaryTree K) :
    weighted prices (heapDeleteMaxRun (.node m child .nil)).2 ≤
      ((unzip child id).length + 1) * heapPrice prices := by
  simp only [heapDeleteMaxRun_proper_cost, unzipBill, weighted_add, weighted_charge,
    Nat.mul_one]
  rw [Nat.mul_comm ((unzip child id).length + 1)]
  simp only [heapPrice, Nat.mul_add, Nat.add_mul, Nat.mul_one]
  omega

theorem deleteMaxAuxRun_split_weighted_le (cmp : K → K → Measured Bool Nat)
    (prices : Cost) (C : Nat) (bound : ∀ x y, (cmp x y).2 ≤ C) (m : K)
    (before : Queue K) (child : BinaryTree K) (after : Queue K)
    (proper : ∀ t ∈ before, Proper t)
    (smaller : ∀ x a b, .node x a b ∈ before → (cmp m x).1 = true)
    (self : (cmp m m).1 = false) :
    weighted prices (deleteMaxAuxRun cmp m (before ++ .node m child .nil :: after)).2 ≤
      (before.length + 1) * auxiliaryPrice prices C +
        ((unzip child id).length + 1) * heapPrice prices := by
  have hp := deletePrefixBill_weighted_le cmp prices C bound m before
  have hh := heapDeleteMaxRun_weighted_le prices m child
  have hc := Nat.mul_le_mul_left (prices .comparisonWork) (bound m m)
  rw [deleteMaxAuxRun_of_split cmp m before child after proper smaller self]
  simp only [weighted_add, weighted_bill, Nat.mul_zero, Nat.mul_one, Nat.add_zero]
  simp only [auxiliaryPrice, Nat.add_mul, Nat.one_mul] at *
  omega

theorem heapDeleteMaxRun_rank_cost [LE K] {n : Nat} {t : BinaryTree K}
    (valid : Pow2Heap n t) :
    (heapDeleteMaxRun t).2 =
      charge .heapDeleteMaxCalls 1 + unzipBill n + charge .applications 1 := by
  obtain ⟨m, a, rfl, ha⟩ := (pow2Heap_iff n t).mp valid
  rw [heapDeleteMaxRun_proper_cost, unzip_length ha]

theorem heapDeleteMaxRun_rank_weighted_le [LE K] (prices : Cost)
    {n : Nat} {t : BinaryTree K} (valid : Pow2Heap n t) :
    weighted prices (heapDeleteMaxRun t).2 ≤ (n + 1) * heapPrice prices := by
  obtain ⟨m, a, rfl, ha⟩ := (pow2Heap_iff n t).mp valid
  simpa only [unzip_length ha] using heapDeleteMaxRun_weighted_le prices m a

/-- Both join prices are explicit: its bound uses L+2, which is at most 2(L+1). -/
def deletePrice (prices : Cost) (comparisonBound : Nat) : Nat :=
  prices .deleteMaxCalls + scanPrice prices comparisonBound +
    auxiliaryPrice prices comparisonBound + heapPrice prices +
    joinPrice prices comparisonBound + joinPrice prices comparisonBound

section OrderedDeletion
variable [Preorder K] [Std.Total (fun x y : K => x ≤ y)]
variable (cmp : K → K → Measured Bool Nat)
variable (correct : ∀ x y, (cmp x y).1 = true ↔ ¬ x ≤ y)
include correct

/-- The selected slot j has absolute rank i+j; child work retains that offset. -/
theorem deleteMaxAuxRun_selected_counts (i : Nat) (q : Queue K) (m : K)
    (valid : ValidFrom i q) (found : findMax (fun x y => (cmp x y).1) q = some m) :
    ∃ j < q.length,
      (deleteMaxAuxRun cmp m q).2 .deleteMaxAuxCalls = j + 1 ∧
      (deleteMaxAuxRun cmp m q).2 .comparisons ≤ j + 1 ∧
      (deleteMaxAuxRun cmp m q).2 .cons = j + 1 + (i + j) ∧
      (deleteMaxAuxRun cmp m q).2 .nodes ≤ j + 1 + (i + j) ∧
      (deleteMaxAuxRun cmp m q).2 .unzipCalls = i + j + 1 ∧
      (deleteMaxAuxRun cmp m q).2 .closures = i + j ∧
      (deleteMaxAuxRun cmp m q).2 .applications = i + j + 1 := by
  obtain ⟨before, child, after, shape, ranked, smaller, _⟩ :=
    findMax_some_valid_split correct i q m valid found
  have hp := ((validFrom_append i before (.node m child .nil :: after)).mp (shape ▸ valid)).1
  have self : (cmp m m).1 = false := by
    cases h : (cmp m m).1 with
    | false => rfl
    | true => exact False.elim ((correct m m).mp h le_rfl)
  have hc := deleteMaxAuxRun_split_counts cmp m before child after (validFrom_proper hp) smaller self
  have ho := BinaryCounter.ones_le_length (occupancy before)
  have hr := unzip_length ranked
  rw [occupancy_length] at ho
  rw [← shape] at hc
  refine ⟨before.length, ?_, ?_⟩
  · rw [shape, List.length_append, List.length_cons]
    omega
  · dsimp only at hc
    rw [hr] at hc
    omega

theorem deleteMaxAuxRun_weighted_le (prices : Cost) (C : Nat)
    (bound : ∀ x y, (cmp x y).2 ≤ C) (q : Queue K) (m : K)
    (valid : Valid q) (found : findMax (fun x y => (cmp x y).1) q = some m) :
    weighted prices (deleteMaxAuxRun cmp m q).2 ≤
      q.length * (auxiliaryPrice prices C + heapPrice prices) := by
  obtain ⟨before, child, after, shape, ranked, smaller, _⟩ :=
    findMax_some_valid_split correct 0 q m valid found
  have hp := ((validFrom_append 0 before (.node m child .nil :: after)).mp (shape ▸ valid)).1
  have self : (cmp m m).1 = false := by
    cases h : (cmp m m).1 with
    | false => rfl
    | true => exact False.elim ((correct m m).mp h le_rfl)
  have h := deleteMaxAuxRun_split_weighted_le cmp prices C bound m before child after
    (validFrom_proper hp) smaller self
  have hr : (unzip child id).length = before.length := by simpa using unzip_length ranked
  rw [← shape, hr] at h
  have hlen : before.length + 1 ≤ q.length := by
    rw [shape, List.length_append, List.length_cons]
    omega
  have hm := Nat.mul_le_mul_right (auxiliaryPrice prices C + heapPrice prices) hlen
  simp only [Nat.mul_add] at hm ⊢
  omega

/-- All phases are charged, even when no maximum is found. -/
theorem deleteMaxRun_weighted_le (prices : Cost) (C : Nat)
    (bound : ∀ x y, (cmp x y).2 ≤ C) (q : Queue K) (valid : Valid q) :
    weighted prices (deleteMaxRun cmp q).2 ≤ (q.length + 1) * deletePrice prices C := by
  have hs := findMaxRun_weighted_le cmp prices C bound q
  cases found : (findMaxRun cmp q).1 with
  | none =>
      simp only [deleteMaxRun, found, weighted_add, weighted_bill, Nat.mul_zero, Nat.add_zero]
      simp only [deletePrice, Nat.mul_add, Nat.add_mul, Nat.one_mul]
      simp only [Nat.add_mul, Nat.one_mul] at hs
      omega
  | some m =>
      have hf : findMax (fun x y => (cmp x y).1) q = some m := by
        simpa only [findMaxRun_value] using found
      have hd := deleteMaxAuxRun_weighted_le cmp correct prices C bound q m valid hf
      have hfst : (deleteMaxAuxRun cmp m q).1.1.length = q.length := by
        rw [deleteMaxAuxRun_value]
        exact deleteMaxAux_fst_length correct 0 q m valid hf
      have hsnd : (deleteMaxAuxRun cmp m q).1.2.length < q.length := by
        rw [deleteMaxAuxRun_value]
        simpa only [Nat.zero_add] using deleteMaxAux_snd_length_lt correct 0 q m valid hf
      have hm : max (deleteMaxAuxRun cmp m q).1.1.length
          (deleteMaxAuxRun cmp m q).1.2.length = q.length := by omega
      have hj := joinRun_weighted_le cmp prices C bound
        (deleteMaxAuxRun cmp m q).1.1 (deleteMaxAuxRun cmp m q).1.2 .nil
      rw [hm] at hj
      simp only [deleteMaxRun, found, weighted_add, weighted_bill, Nat.mul_zero, Nat.add_zero]
      simp only [deletePrice, Nat.mul_add, Nat.add_mul, Nat.one_mul] at *
      omega

theorem deleteMaxRun_comparisons_le (q : Queue K) (valid : Valid q) :
    (deleteMaxRun cmp q).2 .comparisons ≤ 3 * q.length := by
  have hs := (findMaxRun_counts cmp q).2
  have ho := BinaryCounter.ones_le_length (occupancy q)
  rw [occupancy_length] at ho
  cases found : (findMaxRun cmp q).1 with
  | none =>
      simp only [deleteMaxRun, found, Pi.add_apply, bill, charge]
      simp only [ite_true, ite_false, reduceCtorEq, Nat.add_zero, Nat.zero_add]
      omega
  | some m =>
      have hf : findMax (fun x y => (cmp x y).1) q = some m := by
        simpa only [findMaxRun_value] using found
      obtain ⟨j, hj, _, hd, _⟩ := deleteMaxAuxRun_selected_counts cmp correct 0 q m valid hf
      have hfst : (deleteMaxAuxRun cmp m q).1.1.length = q.length := by
        rw [deleteMaxAuxRun_value]
        exact deleteMaxAux_fst_length correct 0 q m valid hf
      have hsnd : (deleteMaxAuxRun cmp m q).1.2.length < q.length := by
        rw [deleteMaxAuxRun_value]
        simpa only [Nat.zero_add] using deleteMaxAux_snd_length_lt correct 0 q m valid hf
      have hm : max (deleteMaxAuxRun cmp m q).1.1.length
          (deleteMaxAuxRun cmp m q).1.2.length = q.length := by omega
      have hjoin := (joinRun_bounds cmp (deleteMaxAuxRun cmp m q).1.1
        (deleteMaxAuxRun cmp m q).1.2 .nil).2.2.1
      rw [hm] at hjoin
      simp only [deleteMaxRun, found, Pi.add_apply, bill, charge]
      simp only [ite_true, ite_false, reduceCtorEq, Nat.add_zero, Nat.zero_add]
      omega

theorem deleteMaxRun_canonical_bound (prices : Cost) (C : Nat)
    (bound : ∀ x y, (cmp x y).2 ≤ C) (q : Queue K)
    (valid : Valid q) (canonical : Canonical q) :
    weighted prices (deleteMaxRun cmp q).2 ≤ ((mass q).size + 1) * deletePrice prices C := by
  simpa only [canonical_length valid canonical] using
    deleteMaxRun_weighted_le cmp correct prices C bound q valid

theorem deleteMaxRun_log_bound (prices : Cost) (C : Nat)
    (bound : ∀ x y, (cmp x y).2 ≤ C) (q : Queue K)
    (valid : Valid q) (canonical : Canonical q) (nonempty : q ≠ []) :
    weighted prices (deleteMaxRun cmp q).2 ≤ (Nat.log 2 (mass q) + 2) * deletePrice prices C := by
  simpa only [canonical_log_length valid canonical nonempty, Nat.add_assoc] using
    deleteMaxRun_weighted_le cmp correct prices C bound q valid

end OrderedDeletion

theorem insertRun_canonical_bound [LE K] (cmp : K → K → Measured Bool Nat)
    (prices : Cost) (C : Nat) (bound : ∀ x y, (cmp x y).2 ≤ C) (key : K) (q : Queue K)
    (valid : Valid q) (canonical : Canonical q) :
    weighted prices (insertRun cmp key q).2 ≤ ((mass q).size + 1) * insertPrice prices C := by
  simpa only [canonical_length valid canonical] using insertRun_weighted_le cmp prices C bound key q

theorem mergeRun_canonical_bound [LE K] (cmp : K → K → Measured Bool Nat)
    (prices : Cost) (C : Nat) (bound : ∀ x y, (cmp x y).2 ≤ C) (p q : Queue K)
    (vp : Valid p) (vq : Valid q) (cp : Canonical p) (cq : Canonical q) :
    weighted prices (mergeRun cmp p q).2 ≤
      (max (mass p).size (mass q).size + 2) * (prices .mergeCalls + joinPrice prices C) := by
  simpa only [canonical_length vp cp, canonical_length vq cq] using
    mergeRun_weighted_le cmp prices C bound p q

/-- Initial stored padding B remains visible beside the historical mass cap H. -/
def Capacity (B H : Nat) (q : Queue K) : Prop := q.length ≤ max B H.size

theorem insertRun_capacity_bound (cmp : K → K → Measured Bool Nat)
    (prices : Cost) (C : Nat) (bound : ∀ x y, (cmp x y).2 ≤ C)
    (B H : Nat) (key : K) (q : Queue K) (capacity : Capacity B H q) :
    weighted prices (insertRun cmp key q).2 ≤ (max B H.size + 1) * insertPrice prices C :=
  (insertRun_weighted_le cmp prices C bound key q).trans
    (Nat.mul_le_mul_right _ (Nat.add_le_add_right capacity 1))

theorem mergeRun_capacity_bound (cmp : K → K → Measured Bool Nat)
    (prices : Cost) (C : Nat) (bound : ∀ x y, (cmp x y).2 ≤ C)
    (B H : Nat) (p q : Queue K) (hp : Capacity B H p) (hq : Capacity B H q) :
    weighted prices (mergeRun cmp p q).2 ≤
      (max B H.size + 2) * (prices .mergeCalls + joinPrice prices C) := by
  exact (mergeRun_weighted_le cmp prices C bound p q).trans
    (Nat.mul_le_mul_right _ (Nat.add_le_add_right (max_le hp hq) 2))

theorem deleteMaxRun_capacity_bound [Preorder K] [Std.Total (fun x y : K => x ≤ y)]
    (cmp : K → K → Measured Bool Nat) (correct : ∀ x y, (cmp x y).1 = true ↔ ¬ x ≤ y)
    (prices : Cost) (C : Nat) (bound : ∀ x y, (cmp x y).2 ≤ C)
    (B H : Nat) (q : Queue K) (valid : Valid q) (capacity : Capacity B H q) :
    weighted prices (deleteMaxRun cmp q).2 ≤ (max B H.size + 1) * deletePrice prices C :=
  (deleteMaxRun_weighted_le cmp correct prices C bound q valid).trans
    (Nat.mul_le_mul_right _ (Nat.add_le_add_right capacity 1))

/-- Each successful source link executes two node expressions, including raw
forests where a malformed attempted link performs no comparison or construction. -/
theorem carryRun_nodes (cmp : K → K → Measured Bool Nat) (q : Queue K) (t : BinaryTree K) :
    (carryRun cmp q t).2 .nodes = 2 * (carryRun cmp q t).2 .comparisons := by
  induction q generalizing t with
  | nil => cases t <;> simp [carryRun, bill, charge]
  | cons head tail ih =>
      cases head with
      | nil => cases t <;> simp [carryRun, bill, charge]
      | node x a b =>
          cases t with
          | nil => simp [carryRun, bill, charge]
          | node y c d =>
              have hs := (smashRun_counts cmp (.node y c d) (.node x a b)).2.2.2.2.2
              have ht := ih (smashRun cmp (.node y c d) (.node x a b)).1
              simp [carryRun, bill, charge, hs, ht, Nat.mul_add]

theorem insertRun_nodes (cmp : K → K → Measured Bool Nat) (key : K) (q : Queue K) :
    (insertRun cmp key q).2 .nodes = 2 * (insertRun cmp key q).2 .comparisons + 1 := by
  simp [insertRun, bill, charge, carryRun_nodes, Nat.add_comm]

theorem joinRun_nodes (cmp : K → K → Measured Bool Nat) (p q : Queue K) (c : BinaryTree K) :
    (joinRun cmp p q c).2 .nodes = 2 * (joinRun cmp p q c).2 .comparisons := by
  induction p generalizing q c with
  | nil => simpa [joinRun, bill, charge] using carryRun_nodes cmp q c
  | cons head tail ih =>
      cases q with
      | nil => simpa [joinRun, bill, charge] using carryRun_nodes cmp (head :: tail) c
      | cons other rest =>
          have hn := ih rest (.nil : BinaryTree K)
          have hhc := (smashRun_counts cmp c head).2.2.2.2.2
          have hoc := (smashRun_counts cmp c other).2.2.2.2.2
          have hho := (smashRun_counts cmp head other).2.2.2.2.2
          have hrh := ih rest (smashRun cmp c head).1
          have hro := ih rest (smashRun cmp c other).1
          have hrt := ih rest (smashRun cmp head other).1
          cases head <;> cases other <;> cases c <;>
            simp only [joinRun, Pi.add_apply, bill, charge, Nat.mul_add] <;>
            simp only [ite_true, ite_false, reduceCtorEq, Nat.add_zero, Nat.zero_add,
              Nat.mul_zero] <;> omega

theorem mergeRun_nodes (cmp : K → K → Measured Bool Nat) (p q : Queue K) :
    (mergeRun cmp p q).2 .nodes = 2 * (mergeRun cmp p q).2 .comparisons := by
  simpa [mergeRun, bill, charge] using joinRun_nodes cmp p q .nil

/-- A failed deletion still pays its wrapper and the complete maximum scan. -/
theorem deleteMaxRun_none_bill (cmp : K → K → Measured Bool Nat) (q : Queue K)
    (found : findMax (fun x y => (cmp x y).1) q = none) :
    deleteMaxRun cmp q =
      (none, bill .deleteMaxCalls 0 0 0 0 0 0 + (findMaxRun cmp q).2) := by
  simp only [deleteMaxRun, findMaxRun_value, found]

theorem deleteMaxRun_padding (cmp : K → K → Measured Bool Nat) (n : Nat) :
    deleteMaxRun cmp (List.replicate n .nil) =
      (none, charge .deleteMaxCalls 1 + charge .findMaxCalls (n + 1)) := by
  simp only [deleteMaxRun, findMaxRun_padding]
  apply Prod.ext
  · rfl
  · funext metric
    cases metric <;> simp [bill, charge]

theorem deleteMaxRun_empty (cmp : K → K → Measured Bool Nat) :
    deleteMaxRun cmp [] = (none, charge .deleteMaxCalls 1 + charge .findMaxCalls 1) :=
  deleteMaxRun_padding cmp 0

end Resources.BinomialQueue
