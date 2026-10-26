import Applications.Bracketing.Basic

set_option autoImplicit false
set_option warningAsError true

/-! Exercise14.3: child costs may be combined by any coordinatewise monotone h.
No associativity of h is required. The source fork charge depends on child sizes,
which are fixed by the exact input fringes. Parallel child evaluation uses max.
-/
namespace Bracketing.Recursive

open Bracketing
variable {α : Type}

def Monotone2 (h : Nat → Nat → Nat) : Prop :=
  ∀ a b c d, a ≤ c → b ≤ d → h a b ≤ h c d

def costH (h f : Nat → Nat → Nat) : Tree α → Nat
  | .leaf _ => 0
  | .fork l r => h (costH h f l) (costH h f r) + f (size l) (size r)

def mctH (h f : Nat → Nat → Nat) : (ws : List α) → ws ≠ [] → Tree α
  | [], hn => False.elim (hn rfl)
  | [w], _ => .leaf w
  | x :: y :: xs, _ =>
      sourceMinWith (costH h f)
        ((splitsn (x :: y :: xs)).attach.map (fun p =>
          .fork (mctH h f p.val.1 ((mem_splitsn_iff _ _ _).mp p.property).1)
            (mctH h f p.val.2 ((mem_splitsn_iff _ _ _).mp p.property).2.1)))
        (by simpa using splitsn_ne_nil_of_length (x :: y :: xs) (by simp))
termination_by ws => ws.length
decreasing_by
  all_goals simp_wf
  all_goals first
    | exact (splitsn_lengths_lt p.property).1
    | exact (splitsn_lengths_lt p.property).2

def candidates (h f : Nat → Nat → Nat) (ws : List α) : List (Tree α) :=
  (splitsn ws).attach.map fun p =>
    .fork (mctH h f p.val.1 ((mem_splitsn_iff _ _ _).mp p.property).1)
      (mctH h f p.val.2 ((mem_splitsn_iff _ _ _).mp p.property).2.1)

theorem candidates_nonempty (h f : Nat → Nat → Nat) (ws : List α)
    (hl : 2 ≤ ws.length) : candidates h f ws ≠ [] := by
  simpa [candidates] using splitsn_ne_nil_of_length ws hl

theorem mctH_singleton (h f : Nat → Nat → Nat) (w : α) (hn : [w] ≠ []) :
    mctH h f [w] hn = .leaf w := by rw [mctH]

theorem mctH_long (h f : Nat → Nat → Nat) (ws : List α) (hn : ws ≠ [])
    (hl : 2 ≤ ws.length) :
    mctH h f ws hn = sourceMinWith (costH h f) (candidates h f ws)
      (candidates_nonempty h f ws hl) := by
  cases ws with
  | nil => contradiction
  | cons x xs =>
    cases xs with
    | nil => simp at hl
    | cons y ys => rw [mctH]; rfl

theorem mctH_fringe (h f : Nat → Nat → Nat) (ws : List α) (hn : ws ≠ []) :
    fringeSpec (mctH h f ws hn) = ws := by
  induction ws using (measure List.length).wf.induction with
  | h ws ih =>
    cases ws with
    | nil => contradiction
    | cons x xs =>
      cases xs with
      | nil => simp [mctH_singleton, fringeSpec]
      | cons y ys =>
        rw [mctH_long h f _ hn (by simp)]
        have hm := sourceMinWith_mem (costH h f) (candidates h f (x :: y :: ys))
          (candidates_nonempty h f _ (by simp))
        obtain ⟨p, _, he⟩ := List.mem_map.mp hm
        rw [← he, fringeSpec, ih p.val.1 (splitsn_lengths_lt p.property).1,
          ih p.val.2 (splitsn_lengths_lt p.property).2]
        exact ((mem_splitsn_iff _ _ _).mp p.property).2.2

def MinimumH (h f : Nat → Nat → Nat) (ws : List α) (t : Tree α) : Prop :=
  fringeSpec t = ws ∧ ∀ u, fringeSpec u = ws → costH h f t ≤ costH h f u

theorem mctH_minimum (h f : Nat → Nat → Nat) (hm : Monotone2 h)
    (ws : List α) (hn : ws ≠ []) : MinimumH h f ws (mctH h f ws hn) := by
  induction ws using (measure List.length).wf.induction with
  | h ws ih =>
    refine ⟨mctH_fringe h f ws hn, ?_⟩
    intro u hu
    cases u with
    | leaf w =>
      simp only [fringeSpec] at hu
      subst ws
      rw [mctH_singleton]
      exact Nat.le_refl _
    | fork l r =>
      have hs : (fringeSpec l, fringeSpec r) ∈ splitsn ws :=
        (mem_splitsn_iff _ _ _).mpr ⟨fringeSpec_ne_nil l, fringeSpec_ne_nil r, hu⟩
      have hd := (mem_splitsn_iff _ _ _).mp hs
      have hl := ih _ (splitsn_lengths_lt hs).1 hd.1
      have hr := ih _ (splitsn_lengths_lt hs).2 hd.2.1
      have hlen : 2 ≤ ws.length := by
        have he := congrArg List.length hu
        have hpl := size_pos l
        have hpr := size_pos r
        simp only [fringeSpec, List.length_append, fringeSpec_length] at he
        omega
      have hmem : Tree.fork (mctH h f (fringeSpec l) hd.1)
          (mctH h f (fringeSpec r) hd.2.1) ∈ candidates h f ws := by
        exact List.mem_map.mpr ⟨⟨_, hs⟩, List.mem_attach _ _, rfl⟩
      rw [mctH_long h f ws hn hlen]
      apply Nat.le_trans (sourceMinWith_le _ _ _ _ hmem)
      have hsl := congrArg List.length hl.1
      have hsr := congrArg List.length hr.1
      simp only [fringeSpec_length] at hsl hsr
      simp only [costH, hsl, hsr]
      exact Nat.add_le_add_right (hm _ _ _ _ (hl.2 l rfl) (hr.2 r rfl)) _

theorem addition_monotone : Monotone2 (· + ·) := by
  intro a b c d hac hbd
  exact Nat.add_le_add hac hbd

theorem parallel_max_monotone : Monotone2 max := by
  intro a b c d hac hbd
  exact Nat.max_le.mpr ⟨Nat.le_trans hac (Nat.le_max_left _ _),
    Nat.le_trans hbd (Nat.le_max_right _ _)⟩

theorem parallel_optimum (f : Nat → Nat → Nat) (ws : List α) (hn : ws ≠ []) :
    MinimumH max f ws (mctH max f ws hn) := mctH_minimum max f parallel_max_monotone ws hn

/-- A nonmonotone cost combiner can make local child minimization fail globally. -/
def badH (a _ : Nat) : Nat := if a = 0 then 100 else 0

def badCharge (m n : Nat) : Nat := if m+n=4 ∧ m≠3 then 20 else 0

def badCompetitor : Tree Unit :=
  .fork (.fork (.leaf ()) (.fork (.leaf ()) (.leaf ()))) (.leaf ())

theorem nonmonotone_failure :
    costH badH badCharge (mctH badH badCharge [(),(),(),()] (by simp)) = 20 ∧
    fringeSpec badCompetitor = [(),(),(),()] ∧ costH badH badCharge badCompetitor = 0 := by
  decide +kernel

theorem badH_not_monotone : ¬ Monotone2 badH := by
  intro hh
  have he := hh 0 0 100 0 (by omega) (by omega)
  simp [badH] at he

end Bracketing.Recursive
