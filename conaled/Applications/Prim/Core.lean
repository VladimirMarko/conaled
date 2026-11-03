import Applications.Kruskal.Correctness
import Applications.Kruskal.Nested
import SquareKit.Iteration

set_option autoImplicit false
set_option warningAsError true

/-!
The literal growing-tree state and list executors of §9.4.  `Option` records
empty initial vertices and exhausted edge searches.  A skipped edge is retained:
it can become a crossing edge after a later vertex is added.  Vertex and edge
orders are the source orders, including the reversed discovery order at output.
The independent graph specification is imported from `Kruskal`; normalizing only
the vertex list permits direct comparison with that specification.
-/

namespace Prim.Core

open Kruskal
open ForestKruskalSource.Occurrences (picks)

abbrev StateP := Tree × List Edge

def visited (s : StateP) : List Vertex := nodes s.1
def chosen (s : StateP) : List Edge := edges s.1
def pending (s : StateP) : List Edge := s.2

def Safe (vs : List Vertex) (e : Edge) : Prop :=
  (source e ∈ vs ∧ target e ∉ vs) ∨ (target e ∈ vs ∧ source e ∉ vs)

def safeEdgeP (e : Edge) (t : Tree) : Bool :=
  decide (source e ∈ nodes t) != decide (target e ∈ nodes t)

def addP (e : Edge) (t : Tree) : Tree :=
  if source e ∈ nodes t then (target e :: nodes t, e :: edges t)
  else (source e :: nodes t, e :: edges t)

def stepsP (s : StateP) : List StateP :=
  (picks s.2).filterMap (fun p => if safeEdgeP p.1 s.1 then
    some (addP p.1 s.1, p.2) else none)

def gstepP : StateP → Option StateP
  | (_, []) => none
  | (t, e :: es) => if safeEdgeP e t then some (addP e t, es)
      else (gstepP (t, es)).map (fun out => (out.1, e :: out.2))

def applyP : Nat → StateP → Option StateP
  | 0, s => some s
  | k + 1, s => (gstepP s).bind (applyP k)

def startP0 (g : Graph) : Option StateP :=
  (nodes g).head?.map (fun v => (([v], []), edges g))

def startP (g : Graph) : Option StateP :=
  (nodes g).head?.map (fun v => (([v], []), sortEdges (edges g)))

def untilP : Nat → Nat → StateP → Option StateP
  | fuel, n, s => if (visited s).length = n then some s else
      match fuel with
      | 0 => none
      | k + 1 => (gstepP s).bind (untilP k n)

def primState (g : Graph) : Option StateP :=
  (startP g).bind (untilP (nodes g).length (nodes g).length)

def prim (g : Graph) : Option Tree := (primState g).map Prod.fst

def prim1State (g : Graph) : Option StateP :=
  (startP g).bind (applyP ((nodes g).length - 1))

def prim1 (g : Graph) : Option Tree := (prim1State g).map Prod.fst

def branchP : Nat → List StateP → List StateP
  | 0, ss => ss
  | k + 1, ss => branchP k (ss.flatMap stepsP)

def untilBranches : Nat → Nat → List StateP → List StateP
  | fuel, n, ss => if ss.all (fun s => decide ((visited s).length = n)) then ss else
      match fuel with
      | 0 => ss
      | k + 1 => untilBranches k n (ss.flatMap stepsP)

def spatsP (g : Graph) : Option (List Tree) :=
  (startP0 g).map (fun s => (untilBranches (nodes g).length
    (nodes g).length [s]).map Prod.fst)

def normalize (g : Graph) (t : Tree) : Tree := (nodes g, edges t)

def SourceSpanningTree (g t : Graph) : Prop :=
  (nodes t).Perm (nodes g) ∧ SpanningTree g (normalize g t)

def SourceMinimum (g t : Graph) : Prop :=
  (nodes t).Perm (nodes g) ∧ MinimumSpanningTree g (normalize g t)

/-- An independent first admissible occurrence with the exact kept residual. -/
def FirstSafe (s out : StateP) : Prop :=
  ∃ pre e post, pending s = pre ++ e :: post ∧
    (∀ f ∈ pre, ¬ Safe (visited s) f) ∧ Safe (visited s) e ∧
    out = (addP e s.1, pre ++ post)

inductive SourceRun : Nat → StateP → StateP → Prop
  | zero (s : StateP) : SourceRun 0 s s
  | succ {k : Nat} {s middle out : StateP} :
      FirstSafe s middle → SourceRun k middle out → SourceRun (k + 1) s out

theorem safeEdgeP_iff (e : Edge) (t : Tree) :
    safeEdgeP e t = true ↔ Safe (nodes t) e := by
  by_cases hs : source e ∈ nodes t <;> by_cases ht : target e ∈ nodes t <;>
    simp [safeEdgeP, Safe, hs, ht]

theorem safeEdgeP_false_iff (e : Edge) (t : Tree) :
    safeEdgeP e t = false ↔ ¬ Safe (nodes t) e := by
  rw [← safeEdgeP_iff]
  cases safeEdgeP e t <;> simp

theorem safe_exactly_one (vs : List Vertex) (e : Edge) :
    Safe vs e ↔ ¬ (source e ∈ vs ↔ target e ∈ vs) := by
  by_cases hs : source e ∈ vs <;> by_cases ht : target e ∈ vs <;>
    simp [Safe, hs, ht]

theorem addP_sizes (e : Edge) (t : Tree) :
    (nodes (addP e t)).length = (nodes t).length + 1 ∧
    edges (addP e t) = e :: edges t := by
  unfold addP
  split <;> simp [nodes, edges]

theorem addP_new_vertex {e : Edge} {t : Tree} (h : Safe (nodes t) e) :
    ∃ v, v ∉ nodes t ∧ nodes (addP e t) = v :: nodes t ∧
      (v = source e ∨ v = target e) := by
  rcases h with ⟨hs, ht⟩ | ⟨ht, hs⟩
  · exact ⟨target e, ht, by rw [addP, ite_eq_left hs]; rfl, Or.inr rfl⟩
  · exact ⟨source e, hs, by rw [addP, ite_eq_right hs]; rfl, Or.inl rfl⟩

theorem stepsP_members (s out : StateP) : out ∈ stepsP s ↔
    ∃ pre e post, pending s = pre ++ e :: post ∧ Safe (visited s) e ∧
      out = (addP e s.1, pre ++ post) := by
  rw [stepsP, List.mem_filterMap]
  constructor
  · rintro ⟨⟨e, rest⟩, hm, hv⟩
    split at hv
    next hs =>
      have he := Option.some.inj hv
      obtain ⟨pre, post, hp, hr⟩ :=
        (ForestKruskalSource.Occurrences.mem_picks_iff _ _ _).mp hm
      exact ⟨pre, e, post, hp, (safeEdgeP_iff _ _).mp hs, by simpa [hr] using he.symm⟩
    next => simp at hv
  · rintro ⟨pre, e, post, hp, hs, rfl⟩
    refine ⟨(e, pre ++ post), ?_, ?_⟩
    · exact (ForestKruskalSource.Occurrences.mem_picks_iff _ _ _).mpr ⟨pre, post, hp, rfl⟩
    · simp [(safeEdgeP_iff _ _).mpr hs]

theorem gstepP_nil (t : Tree) : gstepP (t, []) = none := by rw [gstepP]

theorem gstepP_take {t : Tree} {e : Edge} {es : List Edge}
    (h : Safe (nodes t) e) : gstepP (t, e :: es) = some (addP e t, es) := by
  simp [gstepP, (safeEdgeP_iff _ _).mpr h]

theorem gstepP_skip {t : Tree} {e : Edge} {es : List Edge}
    (h : ¬ Safe (nodes t) e) :
    gstepP (t, e :: es) = (gstepP (t, es)).map (fun out => (out.1, e :: out.2)) := by
  simp [gstepP, (safeEdgeP_false_iff _ _).mpr h]

theorem gstepP_firstSafe (s out : StateP) :
    gstepP s = some out ↔ FirstSafe s out := by
  rcases s with ⟨t, es⟩
  induction es generalizing out with
  | nil => simp [gstepP, FirstSafe, pending]
  | cons e es ih =>
      by_cases hs : Safe (nodes t) e
      · rw [gstepP_take hs]
        constructor
        · intro he
          cases he
          exact ⟨[], e, es, rfl, by simp, hs, rfl⟩
        · rintro ⟨pre, f, post, hp, hpre, hf, hout⟩
          cases pre with
          | nil =>
              have he : e = f ∧ es = post := by simpa [pending] using hp
              rcases he with ⟨rfl, rfl⟩
              exact congrArg some hout.symm
          | cons a pre =>
              have hea : e = a := by simpa [pending] using congrArg List.head? hp
              exact False.elim (hpre e (by simp [hea]) hs)
      · rw [gstepP_skip hs, Option.map_eq_some_iff]
        constructor
        · rintro ⟨middle, hm, ho⟩
          obtain ⟨pre, f, post, hp, hpre, hf, hout⟩ := (ih middle).mp hm
          refine ⟨e :: pre, f, post, ?_, ?_, hf, ?_⟩
          · simpa [pending] using congrArg (List.cons e) hp
          · intro a ha
            rcases List.mem_cons.mp ha with rfl | ha
            · exact hs
            · exact hpre a ha
          · subst middle
            simpa [List.cons_append] using ho.symm
        · rintro ⟨pre, f, post, hp, hpre, hf, hout⟩
          cases pre with
          | nil =>
              have he : e = f := by simpa [pending] using congrArg List.head? hp
              exact False.elim (hs (he ▸ hf))
          | cons a pre =>
              have he : e = a ∧ es = pre ++ f :: post := by simpa [pending] using hp
              rcases he with ⟨rfl, he⟩
              refine ⟨(addP f t, pre ++ post), (ih _).mpr ?_, ?_⟩
              · exact ⟨pre, f, post, he, fun a ha => hpre a (by simp [ha]), hf, rfl⟩
              · simpa [List.cons_append] using hout.symm

theorem gstepP_is_branch {s out : StateP} (h : gstepP s = some out) :
    out ∈ stepsP s := by
  obtain ⟨pre, e, post, hp, _, hs, ho⟩ := (gstepP_firstSafe s out).mp h
  exact (stepsP_members s out).mpr ⟨pre, e, post, hp, hs, ho⟩

theorem step_sizes {s out : StateP} (h : out ∈ stepsP s) :
    (visited out).length = (visited s).length + 1 ∧
    (chosen out).length = (chosen s).length + 1 ∧
    (pending out).length + 1 = (pending s).length := by
  obtain ⟨pre, e, post, hp, _, rfl⟩ := (stepsP_members s out).mp h
  have ha := addP_sizes e s.1
  refine ⟨ha.1, ?_, ?_⟩
  · change (edges (addP e s.1)).length = (edges s.1).length + 1
    rw [ha.2, List.length_cons]
  · change (pre ++ post).length + 1 = (pending s).length
    rw [hp]
    simp only [List.length_append, List.length_cons]
    omega

theorem step_edge_permutation {s out : StateP} (h : out ∈ stepsP s) :
    (chosen out ++ pending out).Perm (chosen s ++ pending s) := by
  obtain ⟨pre, e, post, hp, _, rfl⟩ := (stepsP_members s out).mp h
  simp only [chosen, pending, (addP_sizes e s.1).2]
  change (e :: (edges s.1 ++ (pre ++ post))).Perm (edges s.1 ++ s.2)
  have h : (e :: (pre ++ post)).Perm s.2 := by
    rw [show s.2 = pre ++ e :: post from hp]
    exact List.perm_middle.symm
  exact List.perm_middle.symm.trans ((List.Perm.refl (edges s.1)).append h)

theorem gstepP_least {s out : StateP}
    (hsort : (pending s).Pairwise (fun e f => weight e ≤ weight f))
    (h : gstepP s = some out) :
    ∃ e, chosen out = e :: chosen s ∧ Safe (visited s) e ∧ e ∈ pending s ∧
      (∀ f ∈ pending s, Safe (visited s) f → weight e ≤ weight f) ∧
      (pending out).Pairwise (fun e f => weight e ≤ weight f) := by
  obtain ⟨pre, e, post, hp, hpre, he, rfl⟩ := (gstepP_firstSafe s out).mp h
  have hpw := hsort
  rw [hp, List.pairwise_append, List.pairwise_cons] at hpw
  refine ⟨e, (addP_sizes e s.1).2, he, ?_, ?_, ?_⟩
  · rw [hp]
    simp
  · intro f hf hsafe
    rw [hp, List.mem_append, List.mem_cons] at hf
    rcases hf with hf | rfl | hf
    · exact False.elim (hpre f hf hsafe)
    · exact Int.le_refl _
    · exact hpw.2.1.1 f hf
  · exact List.pairwise_append.mpr
      ⟨hpw.1, hpw.2.1.2, fun a ha b hb => hpw.2.2 a ha b (by simp [hb])⟩

theorem applyP_source_iff (k : Nat) (s out : StateP) :
    applyP k s = some out ↔ SourceRun k s out := by
  induction k generalizing s out with
  | zero =>
      simp only [applyP, Option.some.injEq]
      constructor
      · rintro rfl
        exact SourceRun.zero s
      · intro h
        cases h
        rfl
  | succ k ih =>
      simp only [applyP, Option.bind_eq_some_iff]
      constructor
      · rintro ⟨middle, hm, ho⟩
        exact SourceRun.succ ((gstepP_firstSafe _ _).mp hm) ((ih _ _).mp ho)
      · intro h
        cases h with
        | succ hm ho => exact ⟨_, (gstepP_firstSafe _ _).mpr hm, (ih _ _).mpr ho⟩

theorem applyP_sizes {k : Nat} {s out : StateP} (h : applyP k s = some out) :
    (visited out).length = (visited s).length + k ∧
    (chosen out).length = (chosen s).length + k ∧
    (pending out).length + k = (pending s).length := by
  induction k generalizing s with
  | zero =>
      have he : s = out := Option.some.inj h
      subst out
      simp
  | succ k ih =>
      obtain ⟨middle, hm, ho⟩ := Option.bind_eq_some_iff.mp h
      have hs := step_sizes (gstepP_is_branch hm)
      have hh := ih ho
      omega

theorem branchP_nil (k : Nat) : branchP k [] = [] := by
  induction k <;> simp_all [branchP]

theorem branchP_sizes {k : Nat} {ss : List StateP} {out : StateP} {n : Nat}
    (hs : ∀ s ∈ ss, (visited s).length = n) (ho : out ∈ branchP k ss) :
    (visited out).length = n + k := by
  induction k generalizing ss n with
  | zero => simpa [branchP] using hs out ho
  | succ k ih =>
      have hnext : ∀ s ∈ ss.flatMap stepsP, (visited s).length = n + 1 := by
        intro s hm
        obtain ⟨middle, hmid, hm⟩ := List.mem_flatMap.mp hm
        rw [(step_sizes hm).1, hs middle hmid]
      have hh := ih hnext ho
      omega

theorem untilP_eq_apply {fuel n : Nat} {s : StateP}
    (hle : (visited s).length ≤ n) (hbudget : n - (visited s).length ≤ fuel) :
    untilP fuel n s = applyP (n - (visited s).length) s := by
  induction fuel generalizing s with
  | zero =>
      have he : (visited s).length = n := by omega
      simp [untilP, he, applyP]
  | succ fuel ih =>
      by_cases he : (visited s).length = n
      · simp [untilP, he, applyP]
      · have hd : n - (visited s).length = (n - (visited s).length - 1) + 1 := by omega
        rw [untilP, ite_eq_right he, hd, applyP]
        cases hm : gstepP s with
        | none => rfl
        | some middle =>
            simp only [Option.bind_some]
            have hs := (step_sizes (gstepP_is_branch hm)).1
            rw [ih (by omega) (by omega)]
            congr 1
            omega

theorem untilBranches_eq_branch {fuel n k : Nat} {ss : List StateP}
    (hs : ∀ s ∈ ss, (visited s).length = k) (hle : k ≤ n) (hbudget : n - k ≤ fuel) :
    untilBranches fuel n ss = branchP (n - k) ss := by
  induction fuel generalizing ss k with
  | zero =>
      have he : k = n := by omega
      have hall : ss.all (fun s => decide ((visited s).length = n)) = true := by
        apply List.all_eq_true.mpr
        intro s hm
        simp [hs s hm, he]
      simp [untilBranches, hall, he, branchP]
  | succ fuel ih =>
      by_cases hempty : ss = []
      · subst ss
        simp [untilBranches, branchP_nil]
      · by_cases he : k = n
        · have hall : ss.all (fun s => decide ((visited s).length = n)) = true := by
            apply List.all_eq_true.mpr
            intro s hm
            simp [hs s hm, he]
          simp [untilBranches, hall, he, branchP]
        · have hall : ss.all (fun s => decide ((visited s).length = n)) = false := by
            apply Bool.eq_false_iff.mpr
            intro hall
            obtain ⟨s, hm⟩ := List.exists_mem_of_ne_nil ss hempty
            have hh := List.all_eq_true.mp hall s hm
            simp [hs s hm, he] at hh
          have hd : n - k = (n - (k + 1)) + 1 := by omega
          rw [untilBranches, hall]
          simp only [Bool.false_eq_true, ↓reduceIte]
          rw [hd, branchP]
          apply ih
          · intro s hm
            obtain ⟨middle, hmid, hm⟩ := List.mem_flatMap.mp hm
            rw [(step_sizes hm).1, hs middle hmid]
          · omega
          · omega

/-- The guard tests the actual number of visited vertices, before consuming fuel. -/
def doneP (n : Nat) (s : StateP) : Bool := decide ((visited s).length = n)

def stepTotal (s : StateP) : StateP := (gstepP s).getD s

theorem untilP_first_hit (fuel n : Nat) (s out : StateP)
    (h : untilP fuel n s = some out) :
    Iteration.UntilSpec (doneP n) stepTotal s out := by
  induction fuel generalizing s with
  | zero =>
      simp only [untilP] at h
      split at h
      · cases h
        exact .stop (by simpa only [doneP, decide_eq_true_eq] using ‹(visited out).length = n›)
      · cases h
  | succ k ih =>
      simp only [untilP] at h
      split at h
      · cases h
        exact .stop (by simpa only [doneP, decide_eq_true_eq] using ‹(visited out).length = n›)
      · have hd : doneP n s = false := by simp [doneP, ‹¬ (visited s).length = n›]
        cases hs : gstepP s with
        | none => simp [hs] at h
        | some mid =>
            simp only [hs, Option.bind_some] at h
            apply Iteration.UntilSpec.step hd
            simpa [stepTotal, hs] using ih mid h

theorem primState_first_hit (g : Graph) (out : StateP) (h : primState g = some out) :
    ∃ s, startP g = some s ∧ Iteration.UntilSpec (doneP (nodes g).length) stepTotal s out := by
  obtain ⟨s, hs, hr⟩ := Option.bind_eq_some_iff.mp h
  exact ⟨s, hs, untilP_first_hit _ _ _ _ hr⟩

theorem prim_eq_prim1 (g : Graph) : prim g = prim1 g := by
  have he : primState g = prim1State g := by
    unfold primState prim1State startP
    cases hv : (nodes g).head? with
    | none => rfl
    | some v =>
        simp only [Option.map_some, Option.bind_some]
        apply untilP_eq_apply
        · have hm : v ∈ nodes g := List.mem_of_head? hv
          have hl := List.length_pos_of_mem hm
          change 1 ≤ (nodes g).length
          omega
        · simp [visited, nodes]
  exact congrArg (fun o => o.map Prod.fst) he

theorem spatsP_fixed (g : Graph) :
    spatsP g = (startP0 g).map (fun s =>
      (branchP ((nodes g).length - 1) [s]).map Prod.fst) := by
  unfold spatsP startP0
  cases hv : (nodes g).head? with
  | none => rfl
  | some v =>
      simp only [Option.map_some]
      have hm : v ∈ nodes g := List.mem_of_head? hv
      have hl := List.length_pos_of_mem hm
      rw [untilBranches_eq_branch (k := 1) (by simp [visited, nodes]) hl
        (by omega)]

/-- Keeping an edge outside the current cut is essential: it can become safe. -/
theorem kept_edge_becomes_safe :
    gstepP (([1], []), [(2, 3, 1), (1, 2, 2)]) =
      some (([2, 1], [(1, 2, 2)]), [(2, 3, 1)]) ∧
    gstepP (([2, 1], [(1, 2, 2)]), [(2, 3, 1)]) =
      some (([3, 2, 1], [(2, 3, 1), (1, 2, 2)]), []) := by
  simp [gstepP, safeEdgeP, addP, nodes, edges, source, target]

theorem empty_boundary : prim ([], []) = none ∧ spatsP ([], []) = none := by decide

theorem singleton_boundary (v : Vertex) :
    prim ([v], []) = some ([v], []) ∧ spatsP ([v], []) = some [([v], [])] := by
  simp [prim, primState, startP, nodes, untilP, visited, spatsP, startP0,
    untilBranches, edges]

end Prim.Core
