import Applications.FRP.RetainedLifecycle

/-! Experimental implementation (#237). See the [retention report](../../docs/research/frp-query-retention.md).

Retained-list accounting for natural timestamps. Entry density includes
empty fragments; payload and timestamp costs are independent assumptions. -/
namespace FRPSpec.Frontier.Retention.Resource
open Trace
variable {α : Type}

def atTime (t : Nat) (xs : Log Nat α) : Nat :=
  (xs.filter fun x => decide (x.1 = t)).length

def Density (D : Nat) (xs : Log Nat α) : Prop := ∀ t, atTime t xs ≤ D

def Window (q W : Nat) (xs : Log Nat α) : Prop :=
  ∀ x ∈ xs, q ≤ x.1 ∧ x.1 < q+W

/-- Counting fragments, not distinct timestamps or nonempty payloads. -/
theorem split_length (q : Nat) (xs : Log Nat α) (h : ∀ x ∈ xs, q ≤ x.1) :
    xs.length = atTime q xs + (cropLog (q+1) xs).length := by
  revert h
  induction xs with
  | nil => intro h; simp [atTime,cropLog]
  | cons x xs ih =>
    intro h
    have hx := h x (by simp)
    have ht : ∀ y ∈ xs, q ≤ y.1 := fun y hy => h y (by simp [hy])
    have hi := ih ht
    by_cases he : x.1 = q
    · simp [atTime,cropLog,he] at *
      omega
    · have hn : q < x.1 := by omega
      simp [atTime,cropLog,he,hn] at *
      omega

theorem density_crop (D q : Nat) (xs : Log Nat α) (h : Density D xs) :
    Density D (cropLog q xs) := by
  intro t
  apply le_trans _ (h t)
  exact ((List.filter_sublist (p := fun x : Nat × List α => decide (q ≤ x.1)) (l := xs)).filter
    (fun x => decide (x.1 = t))).length_le

theorem atTime_zero (t : Nat) (xs : Log Nat α) (h : ∀ x ∈ xs, x.1 ≠ t) :
    atTime t xs = 0 := by
  unfold atTime
  have he : xs.filter (fun x => decide (x.1 = t)) = [] := by
    apply List.filter_eq_nil_iff.mpr
    intro x hx
    simpa using h x hx
  rw [he]
  rfl

/-- Native interval validation prevents old and incoming fragments from sharing
one timestamp. Density still has to hold inside the incoming packet. -/
theorem density_process (D q : Nat) (s : Frontier.State Nat α) (m : Message Nat α)
    (hv : s.Valid) (hs : Density D s.log) (hm : Density D m.packet) :
    Density D (crop q (process s m)).log := by
  apply density_crop
  by_cases hw : windowValid s m.frontier m.packet
  · intro t
    simp only [process,advance,ite_eq_left hw,Option.getD_some]
    have split : atTime t (s.log ++ m.packet) = atTime t s.log + atTime t m.packet := by
      simp [atTime,List.filter_append]
    rw [split]
    by_cases ht : t < s.frontier
    · have hz : atTime t m.packet = 0 := atTime_zero t m.packet (by
        intro x hx he
        have hl := (hw.2 x hx).1
        omega)
      simpa [hz] using hs t
    · have hz : atTime t s.log = 0 := atTime_zero t s.log (by
        intro x hx he
        have hl := hv x hx
        omega)
      simpa [hz] using hm t
  · simpa [process,advance,hw] using hs

/-- A finite timestamp span needs a separate density bound. -/
theorem retained_length (q W D : Nat) (xs : Log Nat α)
    (hw : Window q W xs) (hd : Density D xs) : xs.length ≤ W*D := by
  induction W generalizing q xs with
  | zero =>
    have he : xs = [] := by
      apply List.eq_nil_iff_forall_not_mem.mpr
      intro x hx
      have hh := hw x hx
      omega
    simp [he]
  | succ W ih =>
    have hc : Window (q+1) W (cropLog (q+1) xs) := by
      intro x hx
      obtain ⟨hm,hq⟩ := List.mem_filter.mp hx
      have ho := hw x hm
      have hl : q+1 ≤ x.1 := of_decide_eq_true hq
      constructor
      · exact hl
      · omega
    have hi := ih (q+1) (cropLog (q+1) xs) hc (density_crop D (q+1) xs hd)
    have hs := split_length q xs (fun x hx => (hw x hx).1)
    have hq := hd q
    simp only [Nat.succ_mul]
    omega

theorem crop_window (q W : Nat) (s : Frontier.State Nat α)
    (hv : s.Valid) (hf : s.frontier ≤ q+W) : Window q W (crop q s).log := by
  intro x hx
  refine ⟨crop_lower q s x hx, ?_⟩
  exact (crop_valid q hv x hx).trans_le hf

/-- A native valid source acquires its lower-window premise by actual cropping. -/
theorem source_length (q W D : Nat) (s : Frontier.State Nat α)
    (hv : s.Valid) (hf : s.frontier ≤ q+W) (hd : Density D s.log) :
    (crop q s).log.length ≤ W*D :=
  retained_length q W D _ (crop_window q W s hv hf) (density_crop D q s.log hd)

/-- Encoded cost counts a list cell/header, timestamp and every payload cell.
This does not count a Lean heap or sharing between live snapshots. -/
def entryCost (timestampCost : Nat → Nat) (payloadCost : α → Nat)
    (header cell : Nat) (x : Nat × List α) : Nat :=
  header + timestampCost x.1 + (x.2.map fun a => cell + payloadCost a).sum

def logCost (timestampCost : Nat → Nat) (payloadCost : α → Nat)
    (header cell : Nat) (xs : Log Nat α) : Nat :=
  (xs.map (entryCost timestampCost payloadCost header cell)).sum

theorem payload_cost (payloadCost : α → Nat) (cell B : Nat) (xs : List α)
    (h : ∀ a ∈ xs, payloadCost a ≤ B) :
    (xs.map fun a => cell+payloadCost a).sum ≤ xs.length*(cell+B) := by
  revert h
  induction xs with
  | nil => intro h; simp
  | cons a xs ih =>
    intro h
    have ha := h a (by simp)
    have ht := ih (fun b hb => h b (by simp [hb]))
    simp only [List.map_cons,List.sum_cons,List.length_cons,Nat.add_mul,Nat.one_mul]
    omega

theorem encoded_bound (q W D P BT BA header cell : Nat)
    (timestampCost : Nat → Nat) (payloadCost : α → Nat) (xs : Log Nat α)
    (hw : Window q W xs) (hd : Density D xs)
    (ht : ∀ x ∈ xs, timestampCost x.1 ≤ BT)
    (hp : ∀ x ∈ xs, x.2.length ≤ P)
    (ha : ∀ x ∈ xs, ∀ a ∈ x.2, payloadCost a ≤ BA) :
    logCost timestampCost payloadCost header cell xs ≤
      W*D*(header+BT+P*(cell+BA)) := by
  have point : ∀ x ∈ xs, entryCost timestampCost payloadCost header cell x ≤
      header+BT+P*(cell+BA) := by
    intro x hx
    have hc := payload_cost payloadCost cell BA x.2 (ha x hx)
    have hl := Nat.mul_le_mul_right (cell+BA) (hp x hx)
    have hb := ht x hx
    unfold entryCost
    omega
  have total : ∀ ys : Log Nat α,
      (∀ x ∈ ys, entryCost timestampCost payloadCost header cell x ≤
        header+BT+P*(cell+BA)) →
      logCost timestampCost payloadCost header cell ys ≤
        ys.length*(header+BT+P*(cell+BA)) := by
    intro ys
    induction ys with
    | nil => intro h; simp [logCost]
    | cons x ys ih =>
      intro h
      have hx := h x (by simp)
      have hi := ih (fun y hy => h y (by simp [hy]))
      simp only [logCost,List.map_cons,List.sum_cons,List.length_cons,Nat.add_mul,Nat.one_mul] at *
      omega
  exact (total xs point).trans (Nat.mul_le_mul_right _ (retained_length q W D xs hw hd))

/-- A one-timestamp window admits arbitrarily many fragments without density. -/
theorem unbounded_density (n : Nat) :
    Window 0 1 (List.replicate n (0,([] : List α))) ∧
    (List.replicate n (0,([] : List α))).length = n := by
  constructor
  · intro x hx
    have he := (List.mem_replicate.mp hx).2
    subst x
    simp
  · simp

/-- Even one retained payload needs an encoding-size assumption. -/
theorem growing_payload (n : Nat) :
    logCost (fun _ => 1) id 1 1 [(0,[n])] = n+3 := by
  simp [logCost,entryCost]
  omega

/-- A one-slot window does not bound absolute timestamp encoding. -/
theorem growing_timestamp (q : Nat) :
    Window q 1 [(q,([] : List Nat))] ∧
    logCost id id 1 1 [(q,([] : List Nat))] = q+1 := by
  constructor
  · intro x hx
    simp only [List.mem_singleton] at hx
    subst x
    constructor <;> omega
  · simp [logCost,entryCost,Nat.add_comm]

end FRPSpec.Frontier.Retention.Resource
