import Applications.Search.PriorityInterface

/-!
# Literal heuristic-search transitions and independent paths

Natural edge costs are the mathematical, non-overflowing domain of the source
`Nat = Int`. A nonempty reverse path is represented by its endpoint and tail,
so source `head` has no arbitrary empty-path value. A finite observation returns
`none` only when its budget is exhausted; `some none` is the source's completed
failure. The solved guard precedes the repeated-vertex guard in every variant.
-/
set_option autoImplicit false
set_option warningAsError true
namespace Search.Heuristic
universe u z
variable {V : Type u}

abbrev Graph (V : Type u) := V → List (V × Nat)
abbrev Heuristic (V : Type u) := V → Nat

structure Path (V : Type u) where
  vertex : V
  prior : List V
  cost : Nat
deriving Repr, DecidableEq

def root (s : V) : Path V := ⟨s,[],0⟩
def extend (p : Path V) (v : V) (d : Nat) : Path V :=
  ⟨v,p.vertex :: p.prior,p.cost+d⟩
def extract (p : Path V) : List V × Nat := ((p.vertex :: p.prior).reverse,p.cost)
def estimate (h : Heuristic V) (p : Path V) : Nat := p.cost + h p.vertex

inductive Walk (g : Graph V) : V → V → Nat → Prop where
  | nil (v : V) : Walk g v v 0
  | cons {u v t : V} {d c : Nat} : (v,d) ∈ g u → Walk g v t c → Walk g u t (d+c)

inductive Route (g : Graph V) (s : V) : Path V → Prop where
  | root : Route g s (root s)
  | extend {p : Path V} {v : V} {d : Nat} :
      Route g s p → (v,d) ∈ g p.vertex → Route g s (extend p v d)

theorem walk_append {g : Graph V} {s u v : V} {a b : Nat}
    (ha : Walk g s u a) (hb : Walk g u v b) : Walk g s v (a+b) := by
  induction ha with
  | nil => simpa using hb
  | cons he hw ih => simpa [Nat.add_assoc] using Walk.cons he (ih hb)

theorem route_walk {g : Graph V} {s : V} {p : Path V} (hp : Route g s p) :
    Walk g s p.vertex p.cost := by
  induction hp with
  | root => exact .nil s
  | @extend p v d hp he ih =>
    change Walk g s v (p.cost+d)
    exact walk_append ih (by simpa using Walk.cons he (Walk.nil v))

def Optimistic (g : Graph V) (h : Heuristic V) (goal : V → Bool) : Prop :=
  ∀ u t c, Walk g u t c → goal t = true → h u ≤ c

def Monotonic (g : Graph V) (h : Heuristic V) : Prop :=
  ∀ u v d, (v,d) ∈ g u → h u ≤ d + h v

def Minimum (g : Graph V) (goal : V → Bool) (s : V) (p : Path V) : Prop :=
  Route g s p ∧ goal p.vertex = true ∧
    ∀ t c, Walk g s t c → goal t = true → p.cost ≤ c

theorem monotonic_walk {g : Graph V} {h : Heuristic V} (hm : Monotonic g h)
    {u v : V} {c : Nat} (hw : Walk g u v c) : h u ≤ c + h v := by
  induction hw with
  | nil => omega
  | @cons u v t d c he hw ih => have he' := hm u v d he; omega

theorem monotonic_optimistic {g : Graph V} {h : Heuristic V} {goal : V → Bool}
    (hm : Monotonic g h) (hz : ∀ v, goal v = true → h v = 0) : Optimistic g h goal := by
  intro u t c hw ht
  simpa [hz t ht] using monotonic_walk hm hw

theorem optimistic_goal_zero {g : Graph V} {h : Heuristic V} {goal : V → Bool}
    (ho : Optimistic g h goal) {v : V} (hv : goal v = true) : h v = 0 := by
  have hh := ho v v 0 (.nil v) hv
  omega

theorem estimate_extension {g : Graph V} {h : Heuristic V} (hm : Monotonic g h)
    (p : Path V) {v : V} {d : Nat} (he : (v,d) ∈ g p.vertex) :
    estimate h p ≤ estimate h (extend p v d) := by
  have hh := hm p.vertex v d he
  simp only [estimate,extend]
  omega

theorem zero_monotonic (g : Graph V) : Monotonic g (fun _ => 0) := by
  intro u v d he; exact Nat.zero_le _

theorem zero_optimistic (g : Graph V) (goal : V → Bool) :
    Optimistic g (fun _ => 0) goal := by intro u t c hw ht; exact Nat.zero_le _

abbrev Frontier (V : Type u) := PriorityInterface.Queue (Path V) V Nat Path.vertex
abbrev Store (V : Type u) := List (V × Nat)

def lookup [DecidableEq V] (v : V) : Store V → Option Nat
  | [] => none
  | (u,c) :: xs => if v = u then some c else lookup v xs

def put [DecidableEq V] (v : V) (c : Nat) (st : Store V) : Store V :=
  (v,c) :: st.filter (fun z => decide (z.1 ≠ v))

def seen [DecidableEq V] (v : V) (st : Store V) : Bool := (lookup v st).isSome

def better [DecidableEq V] (p : Path V) (st : Store V) : Bool :=
  match lookup p.vertex st with | none => false | some c => decide (c ≤ p.cost)

inductive Mode where | tree | reopen | closed deriving Repr, DecidableEq

def skip [DecidableEq V] (mode : Mode) (st : Store V) (p : Path V) : Bool :=
  match mode with | .tree => false | .reopen => better p st | .closed => seen p.vertex st

def record [DecidableEq V] (mode : Mode) (st : Store V) (p : Path V) : Store V :=
  match mode with | .tree => st | _ => put p.vertex p.cost st

def succs (g : Graph V) (h : Heuristic V) (p : Path V) : List (Path V × Nat) :=
  (g p.vertex).map (fun (v,d) => (extend p v d,estimate h (extend p v d)))

def children [DecidableEq V] (mode : Mode) (g : Graph V) (h : Heuristic V)
    (st : Store V) (p : Path V) : List (Path V × Nat) :=
  match mode with
  | .closed => (succs g h p).filter (fun e => !seen e.1.vertex st)
  | _ => succs g h p

def start (Q : Frontier.{u,z} V) (h : Heuristic V) (s : V) : Q.Carrier :=
  Q.add [(root s,h s)] Q.empty

def run [DecidableEq V] (Q : Frontier.{u,z} V) (mode : Mode) (g : Graph V)
    (h : Heuristic V) (goal : V → Bool) :
    Nat → Store V → Q.Carrier → Option (Option (Path V))
  | 0,_,_ => none
  | fuel+1,st,q => match Q.remove q with
    | none => some none
    | some (e,r) =>
      if goal e.1.vertex then some (some e.1)
      else if skip mode st e.1 then run Q mode g h goal fuel st r
      else run Q mode g h goal fuel (record mode st e.1)
        (Q.add (children mode g h st e.1) r)

def search [DecidableEq V] (Q : Frontier.{u,z} V) (mode : Mode) (g : Graph V)
    (h : Heuristic V) (goal : V → Bool) (s : V) (fuel : Nat) :
    Option (Option (List V × Nat)) :=
  (run Q mode g h goal fuel [] (start Q h s)).map (Option.map extract)

abbrev tstar [DecidableEq V] := search (PriorityInterface.leftist (π := Nat) (Path.vertex (V := V))) Mode.tree
abbrev astar [DecidableEq V] := search (PriorityInterface.leftist (π := Nat) (Path.vertex (V := V))) Mode.reopen
abbrev mstar [DecidableEq V] := search (PriorityInterface.leftist (π := Nat) (Path.vertex (V := V))) Mode.closed

/-- Every retained queue priority is the source's cost-plus-heuristic value. -/
def Consistent (Q : Frontier.{u,z} V) (h : Heuristic V) (q : Q.Carrier) : Prop :=
  ∀ e ∈ Q.entries q, e.2 = estimate h e.1

def Sound (Q : Frontier.{u,z} V) (g : Graph V) (s : V) (q : Q.Carrier) : Prop :=
  ∀ e ∈ Q.entries q, Route g s e.1

theorem mem_succs {g : Graph V} {h : Heuristic V} {p : Path V} {e : Path V × Nat} :
    e ∈ succs g h p ↔ ∃ v d, (v,d) ∈ g p.vertex ∧
      e = (extend p v d,estimate h (extend p v d)) := by
  simp only [succs,List.mem_map]
  constructor
  · rintro ⟨⟨v,d⟩,he,rfl⟩; exact ⟨v,d,he,rfl⟩
  · rintro ⟨v,d,he,rfl⟩; exact ⟨(v,d),he,rfl⟩

theorem children_subset [DecidableEq V] (mode : Mode) (g : Graph V) (h : Heuristic V)
    (st : Store V) (p : Path V) : ∀ e ∈ children mode g h st p, e ∈ succs g h p := by
  cases mode with
  | tree => exact fun _ he => he
  | reopen => exact fun _ he => he
  | closed => exact fun _ he => (List.mem_filter.mp he).1

theorem children_length [DecidableEq V] (mode : Mode) (g : Graph V) (h : Heuristic V)
    (st : Store V) (p : Path V) : (children mode g h st p).length ≤ (g p.vertex).length := by
  cases mode with
  | tree => simp [children,succs]
  | reopen => simp [children,succs]
  | closed => simpa [children,succs] using List.length_filter_le (fun e : Path V × Nat => !seen e.1.vertex st) (succs g h p)

theorem add_consistent (Q : Frontier.{u,z} V) (h : Heuristic V) (xs : List (Path V × Nat))
    (q : Q.Carrier) (hq : Consistent Q h q) (hx : ∀ e ∈ xs,e.2 = estimate h e.1) :
    Consistent Q h (Q.add xs q) := by
  intro e he
  rcases List.mem_append.mp (Q.add_origin xs q e he) with he | he
  · exact hx e he
  · exact hq e he

theorem remove_consistent (Q : Frontier.{u,z} V) (h : Heuristic V) (q r : Q.Carrier)
    (e : Path V × Nat) (hv : Q.Valid q) (hq : Consistent Q h q)
    (hd : Q.remove q = some (e,r)) : Consistent Q h r := by
  intro a ha
  exact hq a ((Q.remove_spec q e r hv hd).2.1.mem_iff.mpr (by simp [ha]))

theorem start_consistent (Q : Frontier.{u,z} V) (h : Heuristic V) (s : V) :
    Consistent Q h (start Q h s) := by
  apply add_consistent
  · simp [Consistent,Q.empty_entries]
  · simp [estimate,root]

theorem start_sound (Q : Frontier.{u,z} V) (g : Graph V) (h : Heuristic V) (s : V) :
    Sound Q g s (start Q h s) := by
  intro e he
  have hh := Q.add_origin [(root s,h s)] Q.empty e he
  simp only [Q.empty_entries,List.append_nil,List.mem_singleton] at hh
  subst e
  exact .root

theorem start_valid (Q : Frontier.{u,z} V) (h : Heuristic V) (s : V) :
    Q.Valid (start Q h s) := Q.add_valid _ _ Q.empty_valid

theorem run_sound [DecidableEq V] (Q : Frontier.{u,z} V) (mode : Mode) (g : Graph V)
    (h : Heuristic V) (goal : V → Bool) (s : V) (fuel : Nat) (st : Store V)
    (q : Q.Carrier) (hv : Q.Valid q) (hs : Sound Q g s q) {p : Path V}
    (hr : run Q mode g h goal fuel st q = some (some p)) :
    Route g s p ∧ goal p.vertex = true := by
  induction fuel generalizing st q with
  | zero => simp [run] at hr
  | succ fuel ih =>
    cases hd : Q.remove q with
    | none => simp [run,hd] at hr
    | some z =>
      rcases z with ⟨e,r⟩
      have spec := Q.remove_spec q e r hv hd
      have he : e ∈ Q.entries q := spec.2.1.mem_iff.mpr (by simp)
      have hrest : Sound Q g s r := by
        intro a ha
        exact hs a (spec.2.1.mem_iff.mpr (by simp [ha]))
      simp only [run,hd] at hr
      split at hr
      next hg =>
        simp only [Option.some.injEq] at hr
        subst p
        exact ⟨hs e he,hg⟩
      next hg =>
        split at hr
        next hk => exact ih st r spec.1 hrest hr
        next hk =>
          apply ih _ _ (Q.add_valid _ _ spec.1) _ hr
          intro a ha
          rcases List.mem_append.mp (Q.add_origin _ _ a ha) with ha | ha
          · obtain ⟨v,d,hvd,ha⟩ := mem_succs.mp (children_subset mode g h st e.1 a ha)
            subst a
            exact .extend (hs e he) hvd
          · exact hrest a ha

end Search.Heuristic
