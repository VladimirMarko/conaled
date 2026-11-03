import Applications.Dijkstra.Paths
import Applications.Search.Interpretation

/-! The matrix and snoc presentations observe the accepted directed walk and
route semantics. Forward path lists are related with their exact order and cost. -/
set_option autoImplicit false
set_option warningAsError true
namespace Dijkstra.Semantics
open Core Paths
variable {n : Nat}

def adjacency (wa : Weights n) : Search.Heuristic.Graph (Fin n) := fun u =>
  (List.finRange n).filterMap (fun v => (wa u v).map (fun d => (v, d)))

theorem mem_adjacency (wa : Weights n) (u v : Fin n) (d : Nat) :
    (v, d) ∈ adjacency wa u ↔ wa u v = some d := by
  simp [adjacency]

theorem adjacency_length (wa : Weights n) (u : Fin n) : (adjacency wa u).length ≤ n := by
  exact (List.length_filterMap_le _ _).trans_eq List.length_finRange

theorem walk_search {wa : Weights n} {root v : Fin n} {d : Nat} (h : Walk wa root v d) :
    Search.Heuristic.Walk (adjacency wa) root v d := by
  induction h with
  | nil => exact .nil _
  | @snoc v u d w _ he ih =>
      exact Search.Heuristic.walk_append ih (by
        simpa using Search.Heuristic.Walk.cons ((mem_adjacency wa v u w).mpr he)
          (Search.Heuristic.Walk.nil u))

private theorem walk_prepend {wa : Weights n} {root u v : Fin n} {w d : Nat}
    (he : wa root u = some w) (h : Walk wa u v d) : Walk wa root v (w + d) := by
  induction h with
  | nil => simpa using Walk.snoc Walk.nil he
  | snoc _ hx ih => simpa [Nat.add_assoc] using Walk.snoc ih hx

theorem walk_iff (wa : Weights n) (root v : Fin n) (d : Nat) :
    Walk wa root v d ↔ Search.Heuristic.Walk (adjacency wa) root v d := by
  refine ⟨walk_search, ?_⟩
  intro h
  induction h with
  | nil => exact .nil
  | cons he _ ih => exact walk_prepend ((mem_adjacency _ _ _ _).mp he) ih

theorem path_route {wa : Weights n} {root v : Fin n} {ps : List (Fin n)} {d : Nat}
    (h : Path wa root ps v d) :
    ∃ p, Search.Heuristic.Route (adjacency wa) root p ∧
      Search.Heuristic.extract p = (ps, d) ∧ p.vertex = v := by
  induction h with
  | nil => exact ⟨Search.Heuristic.root _, .root, rfl, rfl⟩
  | @snoc ps v u d w _ he ih =>
      obtain ⟨p, hp, hx, hv⟩ := ih
      refine ⟨Search.Heuristic.extend p u w, .extend hp ?_, ?_, rfl⟩
      · rw [hv]; exact (mem_adjacency wa v u w).mpr he
      · have hps := congrArg Prod.fst hx
        have hd := congrArg Prod.snd hx
        change (p.vertex :: p.prior).reverse = ps at hps
        change p.cost = d at hd
        change ((u :: p.vertex :: p.prior).reverse, p.cost + w) = (ps ++ [u], d + w)
        rw [List.reverse_cons, hps, hd]

theorem route_path {wa : Weights n} {root : Fin n} {p : Search.Heuristic.Path (Fin n)}
    (h : Search.Heuristic.Route (adjacency wa) root p) :
    Path wa root (Search.Heuristic.extract p).1 p.vertex p.cost := by
  induction h with
  | root => exact .nil
  | @extend p v d _ he ih =>
      simpa [Search.Heuristic.extract, Search.Heuristic.extend, List.reverse_cons] using
        Path.snoc ih ((mem_adjacency wa p.vertex v d).mp he)

theorem path_iff_route (wa : Weights n) (root v : Fin n) (ps : List (Fin n)) (d : Nat) :
    Path wa root ps v d ↔ ∃ p, Search.Heuristic.Route (adjacency wa) root p ∧
      Search.Heuristic.extract p = (ps, d) ∧ p.vertex = v := by
  refine ⟨path_route, ?_⟩
  rintro ⟨p, hp, he, hv⟩
  have hd := congrArg Prod.snd he
  have hs := congrArg Prod.fst he
  simpa only [hs, hv, show p.cost = d from hd] using route_path hp

def goal (target : Fin n) (v : Fin n) : Bool := decide (v = target)

theorem shortest_iff (wa : Weights n) (root target : Fin n) (d : Nat) :
    Shortest wa root target d ↔
      Search.Heuristic.DistanceResult (adjacency wa) (goal target) root (some d) := by
  constructor
  · rintro ⟨hp, hm⟩
    refine ⟨target, walk_search hp, by simp [goal], ?_⟩
    intro u c hc hu
    have he : u = target := by simpa [goal] using hu
    subst u
    exact hm c ((walk_iff _ _ _ _).mpr hc)
  · rintro ⟨v, hv, hg, hm⟩
    have he : v = target := by simpa [goal] using hg
    subst v
    exact ⟨(walk_iff _ _ _ _).mpr hv, fun c hc => hm target c (walk_search hc) (by simp [goal])⟩

theorem no_path_iff (wa : Weights n) (root target : Fin n) :
    (¬ ∃ d, Walk wa root target d) ↔
      Search.Heuristic.DistanceResult (adjacency wa) (goal target) root none := by
  constructor
  · intro hn v c hw
    simp only [goal, decide_eq_false_iff_not]
    intro he
    subst v
    exact hn ⟨c, (walk_iff _ _ _ _).mpr hw⟩
  · intro hn ⟨d, hd⟩
    have hf := hn target d (walk_search hd)
    simp [goal] at hf

end Dijkstra.Semantics
