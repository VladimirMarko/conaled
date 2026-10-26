import Applications.Bracketing.Recursive

set_option autoImplicit false
set_option warningAsError true

/-!
# Exercise14.3: actual cached generalized child-cost recursion

The second cached field is the leaf count required by the displayed exercise.
The child-cost combiner is h; no associativity of h is used. Exact recursive
first-tie behavior is retained. Monotonicity gives independent global minimum,
but a non-strict combiner may mask a nonoptimal child's cost, so no claim about
the first tree in the whole exhaustive generator is made.
-/
namespace Bracketing.Cached

open Bracketing
open Recursive
variable {α : Type}

abbrev Triple (α : Type) := Nat × Nat × Tree α

def costT (t : Triple α) : Nat := t.1
def weightT (t : Triple α) : Nat := t.2.1
def treeT (t : Triple α) : Tree α := t.2.2

def forkT (h f : Nat → Nat → Nat) (l r : Triple α) : Triple α :=
  (h (costT l) (costT r)+f (weightT l) (weightT r),weightT l+weightT r,
    .fork (treeT l) (treeT r))

def pack (h f : Nat → Nat → Nat) (t : Tree α) : Triple α := (costH h f t,size t,t)

theorem forkT_pack (h f : Nat → Nat → Nat) (l r : Tree α) :
    forkT h f (pack h f l) (pack h f r)=pack h f (.fork l r) := rfl

def triple (h f : Nat → Nat → Nat) : (ws : List α) → ws ≠ [] → Triple α
  | [], hn => False.elim (hn rfl)
  | [w], _ => (0,1,.leaf w)
  | x :: y :: xs, _ =>
      sourceMinWith costT
        ((splitsn (x :: y :: xs)).attach.map (fun p =>
          forkT h f
            (triple h f p.val.1 ((mem_splitsn_iff _ _ _).mp p.property).1)
            (triple h f p.val.2 ((mem_splitsn_iff _ _ _).mp p.property).2.1)))
        (by simpa using splitsn_ne_nil_of_length (x :: y :: xs) (by simp))
termination_by ws => ws.length
decreasing_by
  all_goals simp_wf
  all_goals first
    | exact (splitsn_lengths_lt p.property).1
    | exact (splitsn_lengths_lt p.property).2

def tripleCandidates (h f : Nat → Nat → Nat) (ws : List α) : List (Triple α) :=
  (splitsn ws).attach.map (fun p =>
    forkT h f (triple h f p.val.1 ((mem_splitsn_iff _ _ _).mp p.property).1)
      (triple h f p.val.2 ((mem_splitsn_iff _ _ _).mp p.property).2.1))

theorem tripleCandidates_ne_nil (h f : Nat → Nat → Nat) (ws : List α)
    (hl : 2 ≤ ws.length) : tripleCandidates h f ws ≠ [] := by
  simpa [tripleCandidates] using splitsn_ne_nil_of_length ws hl

theorem triple_singleton (h f : Nat → Nat → Nat) (w : α) (hn : [w] ≠ []) :
    triple h f [w] hn=(0,1,.leaf w) := by rw [triple]

theorem triple_long (h f : Nat → Nat → Nat) (ws : List α) (hn : ws ≠ [])
    (hl : 2 ≤ ws.length) : triple h f ws hn =
      sourceMinWith costT (tripleCandidates h f ws) (tripleCandidates_ne_nil h f ws hl) := by
  cases ws with
  | nil => contradiction
  | cons x xs =>
      cases xs with
      | nil => simp at hl
      | cons y ys => rw [triple]; rfl

theorem triple_eq_pack_mct (h f : Nat → Nat → Nat) (ws : List α) (hn : ws ≠ []) :
    triple h f ws hn=pack h f (mctH h f ws hn) := by
  induction ws using (measure List.length).wf.induction with
  | h ws ih =>
      cases ws with
      | nil => contradiction
      | cons x xs =>
          cases xs with
          | nil => rw [triple_singleton,mctH_singleton]; rfl
          | cons y ys =>
              have hl : 2 ≤ (x :: y :: ys).length := by simp
              have hm : tripleCandidates h f (x :: y :: ys) =
                  (candidates h f (x :: y :: ys)).map (pack h f) := by
                simp only [tripleCandidates,candidates,List.map_map]
                apply List.map_congr_left
                intro p _
                rw [ih p.val.1 (splitsn_lengths_lt p.property).1,
                  ih p.val.2 (splitsn_lengths_lt p.property).2,forkT_pack]
                rfl
              rw [triple_long h f _ hn hl,mctH_long h f _ hn hl]
              apply Eq.trans (Bracketing.sourceMinWith_congr costT _ _ _
                (by simpa using candidates_nonempty h f _ hl) hm)
              exact Bracketing.sourceMinWith_map costT (pack h f) _ _ _

def mct2 (h f : Nat → Nat → Nat) (ws : List α) (hn : ws ≠ []) : Tree α :=
  treeT (triple h f ws hn)

theorem mct2_eq_mct (h f : Nat → Nat → Nat) (ws : List α) (hn : ws ≠ []) :
    mct2 h f ws hn=mctH h f ws hn := by
  simp only [mct2,triple_eq_pack_mct,pack,treeT]

def Cached (h f : Nat → Nat → Nat) (t : Triple α) : Prop :=
  costT t=costH h f (treeT t) ∧ weightT t=size (treeT t)

theorem triple_cached (h f : Nat → Nat → Nat) (ws : List α) (hn : ws ≠ []) :
    Cached h f (triple h f ws hn) := by
  rw [triple_eq_pack_mct]
  exact ⟨rfl,rfl⟩

theorem mct2_fringe (h f : Nat → Nat → Nat) (ws : List α) (hn : ws ≠ []) :
    fringeSpec (mct2 h f ws hn)=ws := by rw [mct2_eq_mct]; exact mctH_fringe h f ws hn

theorem mct2_minimum (h f : Nat → Nat → Nat) (hm : Monotone2 h)
    (ws : List α) (hn : ws ≠ []) : MinimumH h f ws (mct2 h f ws hn) := by
  rw [mct2_eq_mct]
  exact mctH_minimum h f hm ws hn

end Bracketing.Cached
