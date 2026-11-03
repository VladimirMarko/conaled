import Mathlib.Data.List.Basic

/-!
# Exact layered-network path generation

Chapter 10, Section 10.2.  Layers and edges retain their source order and
multiplicities.  The independent specification chooses one edge per supplied
layer and requires adjacent endpoints to meet.  Integer weights may be negative:
the number of layers, not a weight assumption, bounds the finite search.
-/

namespace Optimization.NetworkPaths

structure Edge where
  source : Int
  target : Int
  weight : Int
  deriving DecidableEq, Repr

abbrev Path := List Edge
abbrev Net := List (List Edge)

def linked (e : Edge) : Path → Bool
  | [] => true
  | f :: _ => e.target == f.source

def connected : Path → Bool
  | [] => true
  | e :: p => linked e p && connected p

/-- The cartesian product has the outer edge choice before the suffix choice. -/
def cp {α : Type} : List (List α) → List (List α)
  | [] => [[]]
  | es :: ns => es.flatMap fun e => (cp ns).map (e :: ·)

def paths0 (ns : Net) : List Path := (cp ns).filter connected

def step (es : List Edge) (ps : List Path) : List Path :=
  es.flatMap fun e => (ps.filter (linked e)).map (e :: ·)

def paths (ns : Net) : List Path := ns.foldr step [[]]

def cost (p : Path) : Int := (p.map Edge.weight).sum

/-- Membership in each layer, independent of any enumeration. -/
def Chooses : Net → Path → Prop
  | [], [] => True
  | es :: ns, e :: p => e ∈ es ∧ Chooses ns p
  | _, _ => False

/-- The adjacent-endpoint path condition, independent of `connected`. -/
def Composable : Path → Prop
  | [] => True
  | [_] => True
  | e :: f :: p => e.target = f.source ∧ Composable (f :: p)

def Feasible (ns : Net) (p : Path) : Prop := Chooses ns p ∧ Composable p

theorem cp_eq_foldr {α : Type} (ns : List (List α)) :
    cp ns = ns.foldr (fun es ps => es.flatMap fun e => ps.map (e :: ·)) [[]] := by
  induction ns with
  | nil => rfl
  | cons es ns ih => simp only [cp, List.foldr_cons, ih]

theorem connected_iff (p : Path) : connected p = true ↔ Composable p := by
  induction p with
  | nil => simp [connected, Composable]
  | cons e p ih =>
      cases p with
      | nil => simp [connected, linked, Composable]
      | cons f p =>
          change (((e.target == f.source) && connected (f :: p)) = true) ↔
            e.target = f.source ∧ Composable (f :: p)
          simp only [Bool.and_eq_true, beq_iff_eq, ih]

theorem mem_cp_iff (ns : Net) (p : Path) : p ∈ cp ns ↔ Chooses ns p := by
  induction ns generalizing p with
  | nil => cases p <;> simp [cp, Chooses]
  | cons es ns ih =>
      cases p with
      | nil => simp [cp, Chooses]
      | cons e p =>
          simp only [cp, List.mem_flatMap, List.mem_map, List.cons.injEq]
          constructor
          · rintro ⟨f, hf, q, hq, hfe, hqp⟩
            subst f
            subst q
            exact ⟨hf, (ih p).mp hq⟩
          · rintro ⟨he, hp⟩
            exact ⟨e, he, p, (ih p).mpr hp, rfl, rfl⟩

theorem filter_cons_paths (e : Edge) (ps : List Path) :
    (ps.map (e :: ·)).filter connected =
      ((ps.filter connected).filter (linked e)).map (e :: ·) := by
  induction ps with
  | nil => rfl
  | cons p ps ih =>
      cases hc : connected p <;> cases hl : linked e p <;>
        simp [connected, hc, hl, ih]

theorem filter_cartesian_step (es : List Edge) (ps : List Path) :
    (es.flatMap (fun e => ps.map (e :: ·))).filter connected =
      step es (ps.filter connected) := by
  induction es with
  | nil => rfl
  | cons e es ih =>
      simp only [List.flatMap_cons, List.filter_append, filter_cons_paths, ih]
      rfl

/-- Filter/fold fusion preserves the complete list, including occurrence order. -/
theorem paths_eq_paths0 (ns : Net) : paths ns = paths0 ns := by
  induction ns with
  | nil => rfl
  | cons es ns ih =>
      change step es (paths ns) = (cp (es :: ns)).filter connected
      rw [ih]
      exact (filter_cartesian_step es (cp ns)).symm

theorem paths0_mem_iff (ns : Net) (p : Path) : p ∈ paths0 ns ↔ Feasible ns p := by
  simp only [paths0, List.mem_filter, mem_cp_iff, connected_iff, Feasible]

/-- Soundness and completeness against the independent layered-path predicate. -/
theorem paths_mem_iff (ns : Net) (p : Path) : p ∈ paths ns ↔ Feasible ns p := by
  rw [paths_eq_paths0]
  exact paths0_mem_iff ns p

theorem feasible_cons_iff (es : List Edge) (ns : Net) (e : Edge) (p : Path) :
    Feasible (es :: ns) (e :: p) ↔
      e ∈ es ∧ Feasible ns p ∧ linked e p = true := by
  cases p <;> simp [Feasible, Chooses, Composable, linked, and_assoc, and_left_comm, and_comm]

theorem chooses_length (ns : Net) (p : Path) (h : Chooses ns p) :
    p.length = ns.length := by
  induction ns generalizing p with
  | nil => cases p <;> simp_all [Chooses]
  | cons es ns ih =>
      cases p with
      | nil => simp [Chooses] at h
      | cons e p => simp only [List.length_cons, ih p h.2]

theorem feasible_length (ns : Net) (p : Path) (h : Feasible ns p) :
    p.length = ns.length := chooses_length ns p h.1

theorem paths_length (ns : Net) (p : Path) (hp : p ∈ paths ns) :
    p.length = ns.length := feasible_length ns p ((paths_mem_iff ns p).mp hp)

theorem paths_nil : paths [] = [[]] := rfl

theorem paths_empty_layer (ns : Net) : paths ([] :: ns) = [] := rfl

theorem paths_nonempty_iff (ns : Net) : paths ns ≠ [] ↔ ∃ p, Feasible ns p := by
  constructor
  · intro h
    obtain ⟨p, hp⟩ := List.exists_mem_of_ne_nil _ h
    exact ⟨p, (paths_mem_iff ns p).mp hp⟩
  · rintro ⟨p, hp⟩ he
    have := (paths_mem_iff ns p).mpr hp
    simp [he] at this

theorem cost_nil : cost [] = 0 := rfl

theorem cost_cons (e : Edge) (p : Path) : cost (e :: p) = e.weight + cost p := by
  simp [cost]

theorem cost_append (p q : Path) : cost (p ++ q) = cost p + cost q := by
  simp [cost, List.sum_append]

theorem paths_single_layer (es : List Edge) : paths [es] = es.map (fun e => [e]) := by
  change es.flatMap (fun e => [[e]]) = es.map (fun e => [e])
  induction es with
  | nil => rfl
  | cons e es ih => simp only [List.flatMap_cons, List.singleton_append, List.map_cons, ih]

theorem repeated_edge_occurrences (e : Edge) : paths [[e, e]] = [[e], [e]] := by
  simp [paths_single_layer]

theorem incompatible_layers_empty :
    paths [[⟨1, 2, 7⟩], [⟨3, 4, -8⟩]] = [] := by decide

theorem negative_weight_path :
    Feasible [[⟨1, 2, 7⟩], [⟨2, 3, -8⟩]] [⟨1, 2, 7⟩, ⟨2, 3, -8⟩] ∧
      cost [⟨1, 2, 7⟩, ⟨2, 3, -8⟩] = -1 := by
  simp [Feasible, Chooses, Composable, cost]

end Optimization.NetworkPaths
