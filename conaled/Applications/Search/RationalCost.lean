import Applications.Search.Interpretation
import Mathlib.Data.Rat.Floor
import Mathlib.Order.WithBot
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Linarith

/-! Static rational costs with blocked edges, interpreted through Nat search.
The rational walk specification does not mention the executable encoding. -/
set_option autoImplicit false
set_option warningAsError true
namespace Search.RationalCost
variable {V : Type}

abbrev Graph (V : Type) := V → List (V × WithTop ℚ)

def Edge (g : Graph V) (u v : V) (d : ℚ) : Prop := (v, (d : WithTop ℚ)) ∈ g u

inductive Walk (g : Graph V) : V → V → ℚ → Prop where
  | nil (v : V) : Walk g v v 0
  | cons {u v t : V} {d c : ℚ} : Edge g u v d → Walk g v t c → Walk g u t (d+c)

def Optimistic (g : Graph V) (h : V → ℚ) (goal : V → Bool) : Prop :=
  ∀ u t c, Walk g u t c → goal t = true → h u ≤ c

def Monotonic (g : Graph V) (h : V → ℚ) : Prop :=
  ∀ u v d, Edge g u v d → h u ≤ d + h v

def DistanceResult (g : Graph V) (goal : V → Bool) (s : V) : Option ℚ → Prop
  | none => ∀ t c, Walk g s t c → goal t ≠ true
  | some c => ∃ t, Walk g s t c ∧ goal t = true ∧
      ∀ u d, Walk g s u d → goal u = true → c ≤ d

/-- A positive common scale. Exactness is a separate input obligation. -/
structure Scale where
  denominator : Nat
  positive : 0 < denominator

def Scale.encode (S : Scale) (q : ℚ) : Nat := ⌊q * S.denominator⌋₊
def Scale.decode (S : Scale) (n : Nat) : ℚ := n / (S.denominator : ℚ)
def Scale.Fits (S : Scale) (q : ℚ) : Prop := (S.encode q : ℚ) = q * S.denominator

@[simp] theorem Scale.encode_zero (S : Scale) : S.encode 0 = 0 := by simp [Scale.encode]


theorem Scale.fits_of_integral (S : Scale) (q : ℚ)
    (h : ∃ n : Nat, q * S.denominator = n) : S.Fits q := by
  obtain ⟨n, hn⟩ := h
  simp [Scale.Fits, Scale.encode, hn]

theorem Scale.denominator_pos (S : Scale) : (0 : ℚ) < S.denominator := by
  exact_mod_cast S.positive

@[simp] theorem Scale.decode_zero (S : Scale) : S.decode 0 = 0 := by simp [Scale.decode]
@[simp] theorem Scale.decode_add (S : Scale) (a b : Nat) :
    S.decode (a+b) = S.decode a + S.decode b := by simp [Scale.decode, add_div]

theorem Scale.decode_encode (S : Scale) {q : ℚ} (h : S.Fits q) :
    S.decode (S.encode q) = q := by
  dsimp [Scale.decode]
  rw [h]
  exact mul_div_cancel_right₀ q (ne_of_gt S.denominator_pos)

@[simp] theorem Scale.decode_le_decode (S : Scale) (a b : Nat) :
    S.decode a ≤ S.decode b ↔ a ≤ b := by
  simp only [Scale.decode, div_le_div_iff_of_pos_right S.denominator_pos, Nat.cast_le]

@[simp] theorem Scale.decode_inj (S : Scale) (a b : Nat) :
    S.decode a = S.decode b ↔ a = b := by
  simp only [Scale.decode, div_left_inj' (ne_of_gt S.denominator_pos), Nat.cast_inj]

/-- Filtering is stable: retained successors keep their original list order. -/
def adjacency (S : Scale) (g : Graph V) : Heuristic.Graph V := fun u =>
  (g u).filterMap fun (v,w) => Option.map (fun d => (v,S.encode d)) w

/-- Exact encoding laws; graph operations and finiteness are independent. -/
structure Compatible (S : Scale) (g : Graph V) (h : V → ℚ) : Prop where
  edge_fits : ∀ {u v d}, Edge g u v d → S.Fits d
  heuristic_fits : ∀ u, S.Fits (h u)

/-- A finite collection certifies a particular positive rational instance.
Only the derived exactness laws are needed by the transport theorems. -/
structure FiniteCosts (S : Scale) (g : Graph V) (h : V → ℚ) : Prop where
  values : ∃ values : List ℚ,
    (∀ q ∈ values, S.Fits q) ∧
    (∀ u v d, Edge g u v d → d ∈ values) ∧
    (∀ u, h u ∈ values)
  positive : ∀ u v d, Edge g u v d → 0 < d

theorem FiniteCosts.compatible {S : Scale} {g : Graph V} {h : V → ℚ}
    (F : FiniteCosts S g h) : Compatible S g h := by
  obtain ⟨values, exact, edges, hs⟩ := F.values
  exact ⟨fun he => exact _ (edges _ _ _ he), fun u => exact _ (hs u)⟩

/-- Dropping blocked entries preserves the order of all retained successors. -/
theorem adjacency_order (S : Scale) (g : Graph V) (u : V) :
    List.Sublist ((adjacency S g u).map Prod.fst) ((g u).map Prod.fst) := by
  unfold adjacency
  generalize g u = xs
  induction xs with
  | nil => exact .slnil
  | cons x xs ih =>
    rcases x with ⟨v,w⟩
    cases w with
    | top => exact .cons v ih
    | coe d => exact .cons_cons v ih

theorem mem_adjacency (S : Scale) (g : Graph V) (u v : V) (n : Nat) :
    (v,n) ∈ adjacency S g u ↔ ∃ d, Edge g u v d ∧ S.encode d = n := by
  simp only [adjacency, List.mem_filterMap]
  constructor
  · rintro ⟨⟨w,c⟩,he,hc⟩
    cases c with
    | top => change none = some (v,n) at hc; contradiction
    | coe d =>
      change some (w,S.encode d) = some (v,n) at hc
      simp only [Option.some.injEq, Prod.mk.injEq] at hc
      obtain ⟨rfl,rfl⟩ := hc
      exact ⟨d,he,rfl⟩
  · rintro ⟨d,he,rfl⟩
    exact ⟨(v,(d : WithTop ℚ)),he,rfl⟩

theorem edge_iff {S : Scale} {g : Graph V} {h : V → ℚ}
    (C : Compatible S g h) (u v : V) (n : Nat) :
    (v,n) ∈ adjacency S g u ↔ Edge g u v (S.decode n) := by
  constructor
  · intro he
    obtain ⟨d,hd,rfl⟩ := (mem_adjacency S g u v n).mp he
    rwa [S.decode_encode (C.edge_fits hd)]
  · intro he
    apply (mem_adjacency S g u v n).mpr
    refine ⟨S.decode n,he,?_⟩
    apply (S.decode_inj _ _).mp
    exact S.decode_encode (C.edge_fits he)

theorem Scale.decode_eq_iff (S : Scale) (n : Nat) (q : ℚ) :
    S.decode n = q ↔ (n : ℚ) = q * S.denominator := by
  exact div_eq_iff (ne_of_gt S.denominator_pos)

theorem walk_to_nat {S : Scale} {g : Graph V} {h : V → ℚ}
    (C : Compatible S g h) {s t : V} {c : ℚ} (hw : Walk g s t c) :
    ∃ n, Heuristic.Walk (adjacency S g) s t n ∧ S.decode n = c := by
  induction hw with
  | nil v => exact ⟨0,.nil v,S.decode_zero⟩
  | @cons u v t d c he hw ih =>
    obtain ⟨n,hn,rfl⟩ := ih
    refine ⟨S.encode d+n, .cons ((mem_adjacency S g u v _).mpr ⟨d,he,rfl⟩) hn, ?_⟩
    rw [S.decode_add, S.decode_encode (C.edge_fits he)]

theorem walk_from_nat {S : Scale} {g : Graph V} {h : V → ℚ}
    (C : Compatible S g h) {s t : V} {n : Nat}
    (hw : Heuristic.Walk (adjacency S g) s t n) : Walk g s t (S.decode n) := by
  induction hw with
  | nil v => simpa using Walk.nil (g := g) v
  | @cons u v t d c he hw ih =>
    obtain ⟨q,hq,rfl⟩ := (mem_adjacency S g u v d).mp he
    simpa [S.decode_encode (C.edge_fits hq)] using Walk.cons hq ih

theorem walk_iff {S : Scale} {g : Graph V} {h : V → ℚ}
    (C : Compatible S g h) (s t : V) (n : Nat) :
    Heuristic.Walk (adjacency S g) s t n ↔ Walk g s t (S.decode n) := by
  constructor
  · exact walk_from_nat C
  · intro hw
    obtain ⟨m,hm,he⟩ := walk_to_nat C hw
    exact (S.decode_inj m n).mp he ▸ hm

/-- Accumulated rational cost is multiplied by the chosen common denominator. -/
theorem walk_scaled {S : Scale} {g : Graph V} {h : V → ℚ}
    (C : Compatible S g h) (s t : V) (q : ℚ) :
    Walk g s t q ↔ ∃ n, Heuristic.Walk (adjacency S g) s t n ∧
      (n : ℚ) = q * S.denominator := by
  constructor
  · intro hw
    obtain ⟨n,hn,hq⟩ := walk_to_nat C hw
    exact ⟨n,hn,(S.decode_eq_iff n q).mp hq⟩
  · rintro ⟨n,hn,hq⟩
    have he := (S.decode_eq_iff n q).mpr hq
    simpa only [he] using walk_from_nat C hn

theorem optimistic_iff {S : Scale} {g : Graph V} {h : V → ℚ}
    (C : Compatible S g h) (goal : V → Bool) :
    Heuristic.Optimistic (adjacency S g) (S.encode ∘ h) goal ↔ Optimistic g h goal := by
  constructor
  · intro ho u t c hw ht
    obtain ⟨n,hn,rfl⟩ := walk_to_nat C hw
    rw [← S.decode_encode (C.heuristic_fits u)]
    exact (S.decode_le_decode _ _).mpr (ho u t n hn ht)
  · intro ho u t n hw ht
    apply (S.decode_le_decode _ _).mp
    simpa only [Function.comp_apply, S.decode_encode (C.heuristic_fits u)] using
      ho u t _ (walk_from_nat C hw) ht

theorem monotonic_iff {S : Scale} {g : Graph V} {h : V → ℚ}
    (C : Compatible S g h) :
    Heuristic.Monotonic (adjacency S g) (S.encode ∘ h) ↔ Monotonic g h := by
  constructor
  · intro hm u v d he
    have hh := (S.decode_le_decode _ _).mpr
      (hm u v _ ((mem_adjacency S g u v _).mpr ⟨d,he,rfl⟩))
    simpa [S.decode_encode (C.edge_fits he), S.decode_encode (C.heuristic_fits u),
      S.decode_encode (C.heuristic_fits v)] using hh
  · intro hm u v n he
    obtain ⟨d,hd,rfl⟩ := (mem_adjacency S g u v n).mp he
    apply (S.decode_le_decode _ _).mp
    simpa [S.decode_encode (C.edge_fits hd), S.decode_encode (C.heuristic_fits u),
      S.decode_encode (C.heuristic_fits v)] using hm u v d hd

theorem distance_iff {S : Scale} {g : Graph V} {h : V → ℚ}
    (C : Compatible S g h) (goal : V → Bool) (s : V) (out : Option Nat) :
    Heuristic.DistanceResult (adjacency S g) goal s out ↔
      DistanceResult g goal s (out.map S.decode) := by
  cases out with
  | none =>
    constructor
    · intro hn t c hw ht
      obtain ⟨n,hn',_⟩ := walk_to_nat C hw
      rw [hn t n hn'] at ht
      contradiction
    · intro hn t n hw
      exact Bool.eq_false_iff.mpr (hn t _ (walk_from_nat C hw))
  | some n =>
    constructor
    · rintro ⟨t,hw,ht,hm⟩
      refine ⟨t,walk_from_nat C hw,ht,?_⟩
      intro u d hu hg
      obtain ⟨m,hm',rfl⟩ := walk_to_nat C hu
      exact (S.decode_le_decode _ _).mpr (hm u m hm' hg)
    · rintro ⟨t,hw,ht,hm⟩
      refine ⟨t,(walk_iff C s t n).mpr hw,ht,?_⟩
      intro u m hu hg
      exact (S.decode_le_decode _ _).mp (hm u _ (walk_from_nat C hu) hg)

/-- An executable decoded distance with an independent rational specification. -/
def distanceRep (g : Graph V) (goal : V → Bool) (s : V) : Relational.RelRep :=
  ⟨Option ℚ, Unit, fun out _ => DistanceResult g goal s out⟩

def decodeDistance [DecidableEq V] {S : Scale} {g : Graph V} {h : V → ℚ}
    (C : Compatible S g h) (goal : V → Bool) (s : V) :
    Relational.RelSquare (Heuristic.distanceRep (adjacency S g) goal s)
      (distanceRep g goal s) where
  impl := Option.map S.decode
  spec _ := ()
  preserves := by intro out _ ho; exact (distance_iff C goal s out).mp ho

/-- Compose the existing search-to-distance consumer with cost decoding. -/
def distanceSquare [DecidableEq V] (Q : Heuristic.Frontier V)
    {S : Scale} {g : Graph V} {h : V → ℚ} (C : Compatible S g h)
    (goal : V → Bool) (s : V) (ho : Optimistic g h goal) :
    Relational.RelSquare
      (Heuristic.completedRep Q (adjacency S g) (S.encode ∘ h) goal s)
      (distanceRep g goal s) :=
  Relational.compose (decodeDistance C goal s)
    (Heuristic.distanceSquare Q (adjacency S g) (S.encode ∘ h) goal s
      ((optimistic_iff C goal).mpr ho))

theorem distanceSquare_apply [DecidableEq V] (Q : Heuristic.Frontier V)
    {S : Scale} {g : Graph V} {h : V → ℚ} (C : Compatible S g h)
    (goal : V → Bool) (s : V) (ho : Optimistic g h goal)
    (budget : Heuristic.Completed Q (adjacency S g) (S.encode ∘ h) goal s) :
    (distanceSquare Q C goal s ho).impl budget =
      ((Heuristic.run Q .reopen (adjacency S g) (S.encode ∘ h) goal budget.val []
        (Heuristic.start Q (S.encode ∘ h) s)).get budget.property).map
          (fun p => S.decode p.cost) := by
  change (((Heuristic.run Q .reopen (adjacency S g) (S.encode ∘ h) goal budget.val []
    (Heuristic.start Q (S.encode ∘ h) s)).get budget.property).map Heuristic.Path.cost).map
      S.decode = _
  rw [Option.map_map]
  rfl

theorem distanceSquare_correct [DecidableEq V] (Q : Heuristic.Frontier V)
    {S : Scale} {g : Graph V} {h : V → ℚ} (C : Compatible S g h)
    (goal : V → Bool) (s : V) (ho : Optimistic g h goal)
    (budget : Heuristic.Completed Q (adjacency S g) (S.encode ∘ h) goal s) :
    DistanceResult g goal s ((distanceSquare Q C goal s ho).impl budget) :=
  (distanceSquare Q C goal s ho).preserves (s := ()) True.intro

/-- Only finite, traversable edges require closure. Blocked destinations are
irrelevant to termination. The chosen domain need not contain every vertex. -/
theorem completed_exists [DecidableEq V] (Q : Heuristic.Frontier V)
    (S : Scale) (g : Graph V) (h : V → ℚ) (goal : V → Bool)
    (domain : List V) (s : V) (hs : s ∈ domain)
    (closed : ∀ u ∈ domain, ∀ v d, Edge g u v d → v ∈ domain) :
    Nonempty (Heuristic.Completed Q (adjacency S g) (S.encode ∘ h) goal s) := by
  apply Heuristic.completed_exists Q _ _ goal domain s hs
  intro u hu v n he
  obtain ⟨d,hd,_⟩ := (mem_adjacency S g u v n).mp he
  exact closed u hu v d hd

theorem walk_nonnegative {g : Graph V}
    (hp : ∀ u v d, Edge g u v d → 0 ≤ d)
    {s t : V} {c : ℚ} (hw : Walk g s t c) : 0 ≤ c := by
  induction hw with
  | nil => exact le_rfl
  | cons he hw ih => exact add_nonneg (hp _ _ _ he) ih

/-- Clamping supports signed optimistic heuristics. It can change priorities. -/
def normalize (h : V → ℚ) (v : V) : ℚ := max 0 (h v)

theorem normalize_optimistic {g : Graph V} {h : V → ℚ} {goal : V → Bool}
    (hp : ∀ u v d, Edge g u v d → 0 ≤ d) (ho : Optimistic g h goal) :
    Optimistic g (normalize h) goal := by
  intro u t c hw ht
  exact max_le (walk_nonnegative hp hw) (ho u t c hw ht)

theorem normalize_monotonic {g : Graph V} {h : V → ℚ}
    (hp : ∀ u v d, Edge g u v d → 0 ≤ d) (hm : Monotonic g h) :
    Monotonic g (normalize h) := by
  intro u v d he
  change max 0 (h u) ≤ d + max 0 (h v)
  apply max_le
  · exact add_nonneg (hp u v d he) (le_max_left (0 : ℚ) (h v))
  · have hh := hm u v d he
    have hv : h v ≤ max 0 (h v) := le_max_right _ _
    linarith

/-- Positive scaling preserves cost-plus-heuristic priority order and ties for
exactly encodable heuristics. It does not select a path among tied alternatives. -/
theorem priority_le_iff {S : Scale} {h : V → ℚ} (u v : V) (a b : Nat)
    (hu : S.Fits (h u)) (hv : S.Fits (h v)) :
    a + S.encode (h u) ≤ b + S.encode (h v) ↔
      S.decode a + h u ≤ S.decode b + h v := by
  rw [← S.decode_le_decode]
  simp [S.decode_encode hu, S.decode_encode hv]

theorem priority_eq_iff {S : Scale} {h : V → ℚ} (u v : V) (a b : Nat)
    (hu : S.Fits (h u)) (hv : S.Fits (h v)) :
    a + S.encode (h u) = b + S.encode (h v) ↔
      S.decode a + h u = S.decode b + h v := by
  simp only [le_antisymm_iff, priority_le_iff u v a b hu hv,
    priority_le_iff v u b a hv hu]

end Search.RationalCost
