import Applications.Parallel.MeasuredScan
import Applications.Optimization.Thinning
import Mathlib.Data.List.Forall2

/-!
# Finite scan search with bounded continuation profiles

A profile observes actual shared-gate work and every output's input dependency
paths in each supported continuation. The residual context budget makes
extension preservation explicit; no additive work formula is assumed.
-/
namespace Applications.Parallel.ScanSearch
open Optimization Optimization.Thinning

namespace WireTiming

abbrev Path := Option Nat × Nat

def paths : Wire → List Path
  | .input i => [(some i, 0)]
  | .one => [(none, 0)]
  | .mul a b => (paths a ++ paths b).map (fun p => (p.1, p.2 + 1))

def value (t : Nat → Nat) (p : Path) : Nat :=
  (p.1.map t).getD 0 + p.2

@[simp] theorem value_succ (t : Nat → Nat) (p : Path) :
    value t (p.1, p.2 + 1) = value t p + 1 := by simp [value, Nat.add_assoc]

theorem path_le (t : Nat → Nat) (w : Wire) (p : Path) (hp : p ∈ paths w) :
    value t p ≤ w.arrival t := by
  induction w generalizing p with
  | input i =>
    have := List.mem_singleton.mp hp
    subst p
    simp [value, Wire.arrival]
  | one =>
    have := List.mem_singleton.mp hp
    subst p
    simp [value, Wire.arrival]
  | mul a b ia ib =>
    obtain ⟨q, hq, rfl⟩ := List.mem_map.mp hp
    rw [value_succ, Wire.arrival]
    rcases List.mem_append.mp hq with ha | hb
    · exact Nat.add_le_add_right (le_trans (ia q ha) (le_max_left _ _)) 1
    · exact Nat.add_le_add_right (le_trans (ib q hb) (le_max_right _ _)) 1

theorem attained (t : Nat → Nat) (w : Wire) :
    ∃ p ∈ paths w, value t p = w.arrival t := by
  induction w with
  | input i => exact ⟨(some i, 0), by simp [paths], by simp [value, Wire.arrival]⟩
  | one => exact ⟨(none, 0), by simp [paths], rfl⟩
  | mul a b ia ib =>
    obtain ⟨p, hp, hv⟩ := ia
    obtain ⟨q, hq, hw⟩ := ib
    by_cases h : a.arrival t ≤ b.arrival t
    · refine ⟨(q.1, q.2 + 1), List.mem_map.mpr ⟨q, List.mem_append_right _ hq, rfl⟩, ?_⟩
      simp [value_succ, Wire.arrival, max_eq_right h, hw]
    · refine ⟨(p.1, p.2 + 1), List.mem_map.mpr ⟨p, List.mem_append_left _ hp, rfl⟩, ?_⟩
      simp [value_succ, Wire.arrival, max_eq_left (le_of_not_ge h), hv]

/-- A decidable sufficient comparison of max-plus dependency signatures. -/
def Faster (a b : Wire) : Prop :=
  ∀ p ∈ paths a, ∃ q ∈ paths b, p.1 = q.1 ∧ p.2 ≤ q.2

instance (a b : Wire) : Decidable (Faster a b) := by unfold Faster; infer_instance

theorem faster_refl (a : Wire) : Faster a a := fun p hp => ⟨p, hp, rfl, le_rfl⟩
theorem faster_trans (a b c : Wire) (h : Faster a b) (k : Faster b c) : Faster a c := by
  intro p hp
  obtain ⟨q, hq, he, hl⟩ := h p hp
  obtain ⟨r, hr, hf, hm⟩ := k q hq
  exact ⟨r, hr, he.trans hf, le_trans hl hm⟩

theorem arrival_le (a b : Wire) (h : Faster a b) (t : Nat → Nat) :
    a.arrival t ≤ b.arrival t := by
  obtain ⟨p, hp, hv⟩ := attained t a
  obtain ⟨q, hq, he, hl⟩ := h p hp
  have hval : value t p ≤ value t q := by simp only [value, he]; omega
  rw [← hv]
  exact le_trans hval (path_le t b q hq)

end WireTiming

def ObservedLE (p q : ScanPlan) : Prop :=
  p.work ≤ q.work ∧ List.Forall₂ WireTiming.Faster p.outputs q.outputs
instance (p q : ScanPlan) : Decidable (ObservedLE p q) := by unfold ObservedLE; infer_instance

theorem observed_refl (p : ScanPlan) : ObservedLE p p :=
  ⟨le_rfl, List.forall₂_same.mpr (fun a _ => WireTiming.faster_refl a)⟩

private theorem faster_list_trans {as bs cs : List Wire}
    (h : List.Forall₂ WireTiming.Faster as bs) (k : List.Forall₂ WireTiming.Faster bs cs) :
    List.Forall₂ WireTiming.Faster as cs := by
  induction h generalizing cs with
  | nil => cases k; exact .nil
  | cons hab _ ih =>
    cases k with
    | cons hbc hs => exact .cons (WireTiming.faster_trans _ _ _ hab hbc) (ih hs)

theorem observed_trans (p q r : ScanPlan) (h : ObservedLE p q) (k : ObservedLE q r) :
    ObservedLE p r := ⟨le_trans h.1 k.1, faster_list_trans h.2 k.2⟩

private theorem faster_list_arrivals {as bs : List Wire}
    (h : List.Forall₂ WireTiming.Faster as bs) (t : Nat → Nat) :
    List.Forall₂ (· ≤ ·) (as.map (Wire.arrival t)) (bs.map (Wire.arrival t)) := by
  induction h with
  | nil => exact .nil
  | cons hab _ ih => exact .cons (WireTiming.arrival_le _ _ hab t) ih

theorem observed_arrivals (p q : ScanPlan) (h : ObservedLE p q) (t : Nat → Nat) :
    List.Forall₂ (· ≤ ·) (p.arrivals t) (q.arrivals t) := faster_list_arrivals h.2 t

/-- Matching ordered output ports forces matching scan arity. -/
theorem observed_size (p q : ScanPlan) (h : ObservedLE p q) :
    p.shape.size = q.shape.size := by
  have hh := h.2.length_eq
  simpa [ScanPlan.outputs] using hh

private theorem max_fold_mono {xs ys : List Nat} (h : List.Forall₂ (· ≤ ·) xs ys)
    (a b : Nat) (hab : a ≤ b) : xs.foldl max a ≤ ys.foldl max b := by
  induction h generalizing a b with
  | nil => exact hab
  | cons hxy _ ih => exact ih (max a _) (max b _) (max_le_max hab hxy)

theorem observed_depth (p q : ScanPlan) (h : ObservedLE p q) : p.depth ≤ q.depth :=
  max_fold_mono (observed_arrivals p q h (fun _ => 0)) 0 0 le_rfl

/-- All four one-hole recipe constructors, with a fixed sibling. -/
inductive Frame where
  | prodLeft (sibling : ScanPlan)
  | prodRight (sibling : ScanPlan)
  | compOuter (sibling : ScanPlan)
  | compInner (sibling : ScanPlan)
  deriving DecidableEq, Repr

def Frame.apply : Frame → ScanPlan → ScanPlan
  | .prodLeft q, p => .prod p q
  | .prodRight q, p => .prod q p
  | .compOuter q, p => .comp p q
  | .compInner q, p => .comp q p

/-- The first frame is the outermost; appending frames adds inner continuations. -/
def plug (c : List Frame) (p : ScanPlan) : ScanPlan := c.foldr Frame.apply p

theorem plug_append (c d : List Frame) (p : ScanPlan) :
    plug (c ++ d) p = plug c (plug d p) := by simp [plug, List.foldr_append]

/-- All supported continuation words up to the residual length bound. -/
def contexts (frames : List Frame) : Nat → List (List Frame)
  | 0 => [[]]
  | n + 1 => [] :: (contexts frames n).flatMap (fun c => frames.map (fun f => c ++ [f]))

theorem mem_contexts (frames : List Frame) (n : Nat) (c : List Frame) :
    c ∈ contexts frames n ↔ c.length ≤ n ∧ ∀ f ∈ c, f ∈ frames := by
  induction n generalizing c with
  | zero => simp [contexts]; rintro rfl; simp
  | succ n ih =>
    simp only [contexts, List.mem_cons, List.mem_flatMap, List.mem_map]
    constructor
    · rintro (rfl | ⟨d, hd, f, hf, rfl⟩)
      · simp
      · obtain ⟨hl, hall⟩ := (ih d).mp hd
        refine ⟨by simp; omega, ?_⟩
        intro g hg
        rcases List.mem_append.mp hg with hg | hg
        · exact hall g hg
        · simpa using (List.mem_singleton.mp hg) ▸ hf
    · rintro ⟨hl, hall⟩
      cases hc : c.reverse with
      | nil => left; exact List.reverse_eq_nil_iff.mp hc
      | cons f ds =>
        right
        have he : c = ds.reverse ++ [f] := by
          have := congrArg List.reverse hc
          simpa using this
        subst c
        refine ⟨ds.reverse, (ih _).mpr ⟨by simp only [List.length_append, List.length_singleton] at hl; omega, ?_⟩,
          f, hall f (by simp), rfl⟩
        intro g hg
        exact hall g (List.mem_append_left _ hg)

theorem nil_context (frames : List Frame) (n : Nat) : [] ∈ contexts frames n :=
  (mem_contexts frames n []).mpr ⟨Nat.zero_le _, by simp⟩

theorem extend_context (frames : List Frame) (n : Nat) (f : Frame) (hf : f ∈ frames)
    (c : List Frame) (hc : c ∈ contexts frames n) : c ++ [f] ∈ contexts frames (n+1) := by
  simp only [contexts, List.mem_cons, List.mem_flatMap, List.mem_map]
  exact Or.inr ⟨c, hc, f, hf, rfl⟩

structure Candidate where
  remaining : Nat
  plan : ScanPlan
  deriving DecidableEq, Repr

/-- Compare a declared observation in every supported bounded continuation. -/
def ProfileDominates (observe : ScanPlan → ScanPlan → Prop) (frames : List Frame)
    (a b : Candidate) : Prop :=
  a.remaining = b.remaining ∧
    ∀ c ∈ contexts frames a.remaining, observe (plug c a.plan) (plug c b.plan)
instance (observe : ScanPlan → ScanPlan → Prop) [DecidableRel observe]
    (frames : List Frame) (a b : Candidate) : Decidable (ProfileDominates observe frames a b) := by
  unfold ProfileDominates; infer_instance

theorem profile_refl (observe : ScanPlan → ScanPlan → Prop) (hr : ∀ p, observe p p)
    (frames : List Frame) (a : Candidate) : ProfileDominates observe frames a a :=
  ⟨rfl, fun _ _ => hr _⟩

theorem profile_trans (observe : ScanPlan → ScanPlan → Prop)
    (ht : ∀ p q r, observe p q → observe q r → observe p r)
    (frames : List Frame) (a b c : Candidate)
    (h : ProfileDominates observe frames a b) (k : ProfileDominates observe frames b c) :
    ProfileDominates observe frames a c :=
  ⟨h.1.trans k.1, fun d hd => ht _ _ _ (h.2 d hd) (k.2 d (h.1 ▸ hd))⟩

/-- The universal profile retains every ordered output for all input arrivals. -/
abbrev Dominates := ProfileDominates ObservedLE

theorem dominates_refl (frames : List Frame) (a : Candidate) : Dominates frames a a :=
  ⟨rfl, fun _ _ => observed_refl _⟩

theorem dominates_trans (frames : List Frame) (a b c : Candidate)
    (h : Dominates frames a b) (k : Dominates frames b c) : Dominates frames a c := by
  refine ⟨h.1.trans k.1, ?_⟩
  intro d hd
  exact observed_trans _ _ _ (h.2 d hd) (k.2 d (h.1 ▸ hd))

theorem dominates_observed (frames : List Frame) (a b : Candidate)
    (h : Dominates frames a b) : ObservedLE a.plan b.plan :=
  h.2 [] (nil_context _ _)

/-- The decidable profile implies actual shared work and ordered arrivals in every
supported continuation, for every input-arrival assignment. -/
theorem dominates_context (frames : List Frame) (a b : Candidate)
    (h : Dominates frames a b) (c : List Frame) (hc : c ∈ contexts frames a.remaining)
    (t : Nat → Nat) :
    (plug c a.plan).shape.size = (plug c b.plan).shape.size ∧
    (plug c a.plan).work ≤ (plug c b.plan).work ∧
    List.Forall₂ (· ≤ ·) ((plug c a.plan).arrivals t) ((plug c b.plan).arrivals t) :=
  ⟨observed_size _ _ (h.2 c hc), (h.2 c hc).1, observed_arrivals _ _ (h.2 c hc) t⟩

/-- A zero budget freezes the candidate. Otherwise every catalog frame is generated. -/
def extend (frames : List Frame) (a : Candidate) : List Candidate :=
  match a.remaining with
  | 0 => [a]
  | n+1 => frames.map (fun f => ⟨n, f.apply a.plan⟩)

theorem profile_extend_covers (observe : ScanPlan → ScanPlan → Prop) (frames : List Frame) (a b : Candidate) (h : ProfileDominates observe frames a b) :
    Covers (ProfileDominates observe frames) (extend frames a) (extend frames b) := by
  obtain ⟨n, p⟩ := a
  obtain ⟨m, q⟩ := b
  have he := h.1
  dsimp at he
  subst m
  cases n with
  | zero =>
    intro y hy
    have hy' : y = ⟨0,q⟩ := List.mem_singleton.mp hy
    subst y
    exact ⟨⟨0,p⟩, by simp [extend], h⟩
  | succ n =>
    intro y hy
    obtain ⟨f, hf, rfl⟩ := List.mem_map.mp hy
    refine ⟨⟨n, f.apply p⟩, List.mem_map.mpr ⟨f, hf, rfl⟩, rfl, ?_⟩
    intro c hc
    simpa [plug_append, plug] using h.2 (c ++ [f]) (extend_context frames n f hf c hc)


theorem extend_covers (frames : List Frame) (a b : Candidate) (h : Dominates frames a b) :
    Covers (Dominates frames) (extend frames a) (extend frames b) :=
  profile_extend_covers ObservedLE frames a b h

def step (frames : List Frame) (_ : Unit) (xs : List Candidate) : List Candidate :=
  xs.flatMap (extend frames)

def prune (frames : List Frame) (xs : List Candidate) : List Candidate :=
  thinBy (Dominates frames) xs

theorem prune_correct (frames : List Frame) (xs : List Candidate) :
    Represents (Dominates frames) xs (prune frames xs) :=
  (thinBy_correct _ (dominates_refl frames) (dominates_trans frames) xs).represents

theorem step_preserves (frames : List Frame) (d : Unit) (xs ys : List Candidate)
    (h : Represents (Dominates frames) xs ys) :
    Represents (Dominates frames) (step frames d xs) (step frames d ys) :=
  represents_flatMap (extend frames) (extend_covers frames) h

def generate (frames : List Frame) (seeds : List ScanPlan) (budget : Nat) : List Candidate :=
  (List.replicate budget ()).foldr (step frames) (seeds.map (fun p => ⟨budget,p⟩))

def profilePrune (observe : ScanPlan → ScanPlan → Prop) [DecidableRel observe]
    (frames : List Frame) (xs : List Candidate) : List Candidate :=
  thinBy (ProfileDominates observe frames) xs

def profileSearch (observe : ScanPlan → ScanPlan → Prop) [DecidableRel observe]
    (frames : List Frame) (seeds : List ScanPlan) (budget : Nat) : List Candidate :=
  profilePrune observe frames (pruneFold (step frames) (profilePrune observe frames)
    (profilePrune observe frames (seeds.map (fun p => ⟨budget,p⟩))) (List.replicate budget ()))

theorem profile_search_represents (observe : ScanPlan → ScanPlan → Prop) [DecidableRel observe]
    (hr : ∀ p, observe p p) (ht : ∀ p q r, observe p q → observe q r → observe p r)
    (frames : List Frame) (seeds : List ScanPlan) (budget : Nat) :
    Represents (ProfileDominates observe frames) (generate frames seeds budget)
      (profileSearch observe frames seeds budget) := by
  have pc : ∀ xs, Represents (ProfileDominates observe frames) xs (profilePrune observe frames xs) :=
    fun xs => (thinBy_correct _ (profile_refl observe hr frames)
      (profile_trans observe ht frames) xs).represents
  have sp : ∀ d xs ys, Represents (ProfileDominates observe frames) xs ys →
      Represents (ProfileDominates observe frames) (step frames d xs) (step frames d ys) :=
    fun _ _ _ h => represents_flatMap (extend frames) (profile_extend_covers observe frames) h
  have hg : Represents (ProfileDominates observe frames)
      ((List.replicate budget ()).foldr (step frames) (seeds.map (fun p => ⟨budget,p⟩)))
      ((List.replicate budget ()).foldr (step frames)
        (profilePrune observe frames (seeds.map (fun p => ⟨budget,p⟩)))) := by
    induction List.replicate budget () with
    | nil => exact pc _
    | cons d ds ih => exact sp d _ _ ih
  exact represents_trans (profile_trans observe ht frames) hg
    (represents_trans (profile_trans observe ht frames)
      (pruneFold_refinement _ (profile_refl observe hr frames) (profile_trans observe ht frames)
        (step frames) (profilePrune observe frames) sp pc _ _)
      (pc _))

def search (frames : List Frame) (seeds : List ScanPlan) (budget : Nat) : List Candidate :=
  profileSearch ObservedLE frames seeds budget

theorem search_represents (frames : List Frame) (seeds : List ScanPlan) (budget : Nat) :
    Represents (Dominates frames) (generate frames seeds budget) (search frames seeds budget) :=
  profile_search_represents ObservedLE observed_refl observed_trans frames seeds budget

/-- Independent production rules, including the exhausted-budget convention. -/
inductive Production (frames : List Frame) : Candidate → Candidate → Prop
  | frozen (p : ScanPlan) : Production frames ⟨0,p⟩ ⟨0,p⟩
  | frame (n : Nat) (p : ScanPlan) (f : Frame) (hf : f ∈ frames) :
      Production frames ⟨n+1,p⟩ ⟨n,f.apply p⟩

inductive Grammar (frames : List Frame) (seeds : List ScanPlan) (budget : Nat) :
    Nat → Candidate → Prop
  | seed (p : ScanPlan) (hp : p ∈ seeds) : Grammar frames seeds budget 0 ⟨budget,p⟩
  | next {k : Nat} {a b : Candidate} : Grammar frames seeds budget k a →
      Production frames a b → Grammar frames seeds budget (k+1) b

theorem grammar_remaining (frames : List Frame) (seeds : List ScanPlan) (budget k : Nat)
    (a : Candidate) (h : Grammar frames seeds budget k a) : a.remaining = budget - k := by
  induction h with
  | seed p hp => rfl
  | @next k a b ha hab ih =>
    cases hab with
    | frozen p => dsimp at ih ⊢; omega
    | frame n p f hf => dsimp at ih ⊢; omega

theorem mem_extend (frames : List Frame) (a b : Candidate) :
    b ∈ extend frames a ↔ Production frames a b := by
  obtain ⟨n,p⟩ := a
  cases n with
  | zero =>
    constructor
    · intro h
      have he := List.mem_singleton.mp h
      subst b
      exact .frozen p
    · intro h
      cases h
      simp [extend]
  | succ n =>
    constructor
    · intro h
      obtain ⟨f,hf,rfl⟩ := List.mem_map.mp h
      exact .frame n p f hf
    · intro h
      cases h with
      | frame n p f hf => exact List.mem_map.mpr ⟨f,hf,rfl⟩

theorem enumeration_iff (frames : List Frame) (seeds : List ScanPlan) (budget k : Nat)
    (a : Candidate) :
    a ∈ (List.replicate k ()).foldr (step frames) (seeds.map (fun p => ⟨budget,p⟩)) ↔
      Grammar frames seeds budget k a := by
  induction k generalizing a with
  | zero =>
    constructor
    · intro h
      obtain ⟨p,hp,rfl⟩ := List.mem_map.mp h
      exact .seed p hp
    · intro h
      cases h with
      | seed p hp => exact List.mem_map.mpr ⟨p,hp,rfl⟩
  | succ k ih =>
    simp only [List.replicate_succ, List.foldr_cons, step, List.mem_flatMap]
    constructor
    · rintro ⟨b,hb,ha⟩
      exact .next ((ih b).mp hb) ((mem_extend frames b a).mp ha)
    · intro h
      cases h with
      | next hb ha => exact ⟨_, (ih _).mpr hb, (mem_extend frames _ _).mpr ha⟩

theorem generate_iff (frames : List Frame) (seeds : List ScanPlan) (budget : Nat)
    (a : Candidate) : a ∈ generate frames seeds budget ↔ Grammar frames seeds budget budget a :=
  enumeration_iff frames seeds budget budget a

theorem retained_origin (frames : List Frame) (seeds : List ScanPlan) (budget : Nat)
    (a : Candidate) (ha : a ∈ search frames seeds budget) :
    Grammar frames seeds budget budget a :=
  (generate_iff frames seeds budget a).mp ((search_represents frames seeds budget).1 ha)

theorem search_exhausts_budget (frames : List Frame) (seeds : List ScanPlan) (budget : Nat)
    (a : Candidate) (ha : a ∈ search frames seeds budget) : a.remaining = 0 := by
  simpa using grammar_remaining frames seeds budget budget a (retained_origin frames seeds budget a ha)

def work (a : Candidate) : Nat := a.plan.work
def weighted (workWeight depthWeight : Nat) (a : Candidate) : Nat :=
  workWeight * a.plan.work + depthWeight * a.plan.depth
def costs (a : Candidate) : Nat × Nat := (a.plan.work, a.plan.depth)

theorem dominates_costs (frames : List Frame) (a b : Candidate) (h : Dominates frames a b) :
    costs a ≤ costs b :=
  ⟨(dominates_observed frames a b h).1, observed_depth _ _ (dominates_observed frames a b h)⟩

theorem weighted_mono (frames : List Frame) (a b : Candidate)
    (h : Dominates frames a b) (w d : Nat) : weighted w d a ≤ weighted w d b := by
  have hh := dominates_costs frames a b h
  exact Nat.add_le_add (Nat.mul_le_mul_left w hh.1) (Nat.mul_le_mul_left d hh.2)

theorem selected_work (frames : List Frame) (seeds : List ScanPlan) (budget : Nat)
    (z : Candidate) (hz : argmin work (search frames seeds budget) = some z) :
    z ∈ minimizers {a | a ∈ generate frames seeds budget} work :=
  minimizer_of_represents (search_represents frames seeds budget) work
    (fun a _ b _ h => (dominates_costs frames a b h).1)
    (argmin_correct work _ z hz)

theorem selected_weighted (frames : List Frame) (seeds : List ScanPlan) (budget : Nat)
    (w d : Nat) (z : Candidate)
    (hz : argmin (weighted w d) (search frames seeds budget) = some z) :
    z ∈ minimizers {a | a ∈ generate frames seeds budget} (weighted w d) :=
  minimizer_of_represents (search_represents frames seeds budget) (weighted w d)
    (fun a _ b _ h => weighted_mono frames a b h w d)
    (argmin_correct (weighted w d) _ z hz)

def feasible (deadline : Nat) (xs : List Candidate) : List Candidate :=
  xs.filter (fun a => decide (a.plan.depth ≤ deadline))

theorem feasible_represents (frames : List Frame) (deadline : Nat) (xs ys : List Candidate)
    (h : Represents (Dominates frames) xs ys) :
    Represents (Dominates frames) (feasible deadline xs) (feasible deadline ys) := by
  constructor
  · intro a ha
    obtain ⟨hm,hd⟩ := List.mem_filter.mp ha
    exact List.mem_filter.mpr ⟨h.1 hm,hd⟩
  · intro a ha
    obtain ⟨hm,hd⟩ := List.mem_filter.mp ha
    obtain ⟨b,hb,hba⟩ := h.2 a hm
    refine ⟨b, List.mem_filter.mpr ⟨hb, ?_⟩, hba⟩
    simp only [decide_eq_true_eq] at hd ⊢
    exact le_trans (dominates_costs frames b a hba).2 hd

theorem selected_deadline (frames : List Frame) (seeds : List ScanPlan) (budget deadline : Nat)
    (z : Candidate) (hz : argmin work (feasible deadline (search frames seeds budget)) = some z) :
    z ∈ minimizers {a | a ∈ feasible deadline (generate frames seeds budget)} work :=
  minimizer_of_represents
    (feasible_represents frames deadline _ _ (search_represents frames seeds budget)) work
    (fun a _ b _ h => (dominates_costs frames a b h).1)
    (argmin_correct work _ z hz)

/-- Coverage transports Pareto claims but does not assert the output is an antichain. -/
theorem pareto_of_search (frames : List Frame) (seeds : List ScanPlan) (budget : Nat)
    (z : Candidate) (hz : z ∈ pareto {a | a ∈ search frames seeds budget} costs) :
    z ∈ pareto {a | a ∈ generate frames seeds budget} costs := by
  have h := search_represents frames seeds budget
  refine ⟨h.1 hz.1, ?_⟩
  intro q hq hqz
  obtain ⟨r,hr,hrq⟩ := h.2 q hq
  have hrc := dominates_costs frames r q hrq
  exact le_trans (hz.2 r hr (le_trans hrc hqz)) hrc

/-- Positive work/depth scalarization yields a Pareto point, not a least vector. -/
theorem weighted_pareto {xs : List Candidate} {z : Candidate} {w d : Nat}
    (hw : 0 < w) (hd : 0 < d) (hz : z ∈ minimizers {a | a ∈ xs} (weighted w d)) :
    z ∈ pareto {a | a ∈ xs} costs := by
  refine ⟨hz.1, ?_⟩
  intro q hq hqz
  have hm := hz.2 hq
  change w * z.plan.work + d * z.plan.depth ≤ w * q.plan.work + d * q.plan.depth at hm
  change q.plan.work ≤ z.plan.work ∧ q.plan.depth ≤ z.plan.depth at hqz
  change z.plan.work ≤ q.plan.work ∧ z.plan.depth ≤ q.plan.depth
  have hww := Nat.mul_le_mul_left w hqz.1
  have hdd := Nat.mul_le_mul_left d hqz.2
  exact ⟨Nat.le_of_mul_le_mul_left (by omega) hw,
    Nat.le_of_mul_le_mul_left (by omega) hd⟩

namespace Workload

/-- A declared input-arrival map, including inputs introduced by enclosing frames. -/
def depthAt (t : Nat → Nat) (p : ScanPlan) : Nat := (p.arrivals t).foldl max 0

def Observation (t : Nat → Nat) (p q : ScanPlan) : Prop :=
  p.shape.size = q.shape.size ∧ p.work ≤ q.work ∧ depthAt t p ≤ depthAt t q
instance (t : Nat → Nat) (p q : ScanPlan) : Decidable (Observation t p q) := by
  unfold Observation; infer_instance

theorem observation_refl (t : Nat → Nat) (p : ScanPlan) : Observation t p p :=
  ⟨rfl, le_rfl, le_rfl⟩
theorem observation_trans (t : Nat → Nat) (p q r : ScanPlan)
    (h : Observation t p q) (k : Observation t q r) : Observation t p r :=
  ⟨h.1.trans k.1, le_trans h.2.1 k.2.1, le_trans h.2.2 k.2.2⟩

abbrev Dominates (t : Nat → Nat) := ProfileDominates (Observation t)

def search (t : Nat → Nat) (frames : List Frame) (seeds : List ScanPlan) (budget : Nat) :
    List Candidate := profileSearch (Observation t) frames seeds budget

theorem search_represents (t : Nat → Nat) (frames : List Frame) (seeds : List ScanPlan)
    (budget : Nat) : Represents (Dominates t frames) (generate frames seeds budget)
      (search t frames seeds budget) :=
  profile_search_represents (Observation t) (observation_refl t) (observation_trans t)
    frames seeds budget

theorem dominates_current (t : Nat → Nat) (frames : List Frame) (a b : Candidate)
    (h : Dominates t frames a b) : Observation t a.plan b.plan := h.2 [] (nil_context _ _)

theorem extension_safe (t : Nat → Nat) (frames : List Frame) (a b : Candidate)
    (h : Dominates t frames a b) :
    Covers (Dominates t frames) (extend frames a) (extend frames b) :=
  profile_extend_covers (Observation t) frames a b h

/-- A certified workload profile permits scalar selection on the original grammar. -/
theorem selected_work (t : Nat → Nat) (frames : List Frame) (seeds : List ScanPlan)
    (budget : Nat) (z : Candidate) (hz : argmin work (search t frames seeds budget) = some z) :
    z ∈ minimizers {a | a ∈ generate frames seeds budget} work :=
  minimizer_of_represents (search_represents t frames seeds budget) work
    (fun a _ b _ h => (dominates_current t frames a b h).2.1)
    (argmin_correct work _ z hz)

def weighted (t : Nat → Nat) (w d : Nat) (a : Candidate) : Nat :=
  w * a.plan.work + d * depthAt t a.plan

theorem selected_weighted (t : Nat → Nat) (frames : List Frame) (seeds : List ScanPlan)
    (budget w d : Nat) (z : Candidate)
    (hz : argmin (weighted t w d) (search t frames seeds budget) = some z) :
    z ∈ minimizers {a | a ∈ generate frames seeds budget} (weighted t w d) := by
  apply minimizer_of_represents (search_represents t frames seeds budget) (weighted t w d)
    _ (argmin_correct (weighted t w d) _ z hz)
  intro a _ b _ h
  have hh := dominates_current t frames a b h
  exact Nat.add_le_add (Nat.mul_le_mul_left w hh.2.1) (Nat.mul_le_mul_left d hh.2.2)

def feasible (t : Nat → Nat) (deadline : Nat) (xs : List Candidate) : List Candidate :=
  xs.filter (fun a => decide (depthAt t a.plan ≤ deadline))

theorem feasible_represents (t : Nat → Nat) (frames : List Frame) (deadline : Nat)
    (xs ys : List Candidate) (h : Represents (Dominates t frames) xs ys) :
    Represents (Dominates t frames) (feasible t deadline xs) (feasible t deadline ys) := by
  constructor
  · intro a ha
    obtain ⟨hm,hd⟩ := List.mem_filter.mp ha
    exact List.mem_filter.mpr ⟨h.1 hm,hd⟩
  · intro a ha
    obtain ⟨hm,hd⟩ := List.mem_filter.mp ha
    obtain ⟨b,hb,hba⟩ := h.2 a hm
    refine ⟨b, List.mem_filter.mpr ⟨hb, ?_⟩, hba⟩
    simp only [decide_eq_true_eq] at hd ⊢
    exact le_trans (dominates_current t frames b a hba).2.2 hd

theorem selected_deadline (t : Nat → Nat) (frames : List Frame) (seeds : List ScanPlan)
    (budget deadline : Nat) (z : Candidate)
    (hz : argmin work (feasible t deadline (search t frames seeds budget)) = some z) :
    z ∈ minimizers {a | a ∈ feasible t deadline (generate frames seeds budget)} work :=
  minimizer_of_represents
    (feasible_represents t frames deadline _ _ (search_represents t frames seeds budget)) work
    (fun a _ b _ h => (dominates_current t frames a b h).2.1)
    (argmin_correct work _ z hz)

/-- The all-arrivals interface specializes to every declared workload. -/
theorem of_observed (t : Nat → Nat) (p q : ScanPlan) (h : ObservedLE p q) :
    Observation t p q :=
  ⟨observed_size p q h, h.1,
    max_fold_mono (observed_arrivals p q h t) 0 0 le_rfl⟩

theorem of_universal (t : Nat → Nat) (frames : List Frame) (a b : Candidate)
    (h : ScanSearch.Dominates frames a b) : Dominates t frames a b :=
  ⟨h.1, fun c hc => of_observed t _ _ (h.2 c hc)⟩

end Workload

end Applications.Parallel.ScanSearch
