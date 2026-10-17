/-
  A Felix-style, total denotational FRP specification.

  Adapted from docs/history/frp/FRPSpec.lean and checked with the repository
  toolchain. Included in the project proof audit.
  There is no executable FRP scheduler here. The Homomorphism structure states
  obligations for a representation; it is not a claim that a runtime satisfies
  them. No `sorry` or new axioms are used in this draft.

  Deliberate choices:
  * continuous semantic time, Real;
  * finite batches of ordered simultaneous occurrences;
  * past-finite event support (a productive, initialized fragment);
  * strict switching: a change at s takes effect only at t > s;
  * equality of representations is pulled back from their denotations.

  Origin: the accompanying research answer on Elliott's push-pull FRP.
-/

import Mathlib

namespace FRPSpec

abbrev Behavior (α : Type) := ℝ → α

namespace Behavior

def pure {α : Type} (a : α) : Behavior α := fun _ => a

def map {α β : Type} (f : α → β) (b : Behavior α) : Behavior β :=
  fun t => f (b t)

def ap {α β : Type} (f : Behavior (α → β))
    (a : Behavior α) : Behavior β := fun t => f t (a t)

def clock : Behavior ℝ := id

-- Extensional/offline semantics. Online realizability needs additional bounds.
def warp {α : Type} (b : Behavior α) (u : Behavior ℝ) : Behavior α :=
  fun t => b (u t)

end Behavior

-- A support prefix, not a finite whole future.
def PastSupport {α : Type} (e : ℝ → List α) (t : ℝ) : Set ℝ :=
  {s | s < t ∧ e s ≠ []}

structure Event (α : Type) where
  «at» : ℝ → List α
  finite_past : ∀ t, (PastSupport «at» t).Finite

namespace Event

@[ext] theorem ext {α : Type} {e f : Event α}
    (h : e.at = f.at) : e = f := by
  cases e
  cases f
  cases h
  rfl

def never {α : Type} : Event α where
  «at» := fun _ => []
  finite_past := by
    intro t
    have h : PastSupport (fun _ => ([] : List α)) t = ∅ := by
      ext s
      simp [PastSupport]
    rw [h]
    exact Set.finite_empty

def map {α β : Type} (f : α → β) (e : Event α) : Event β where
  «at» := fun t => (e.at t).map f
  finite_past := by
    intro t
    apply (e.finite_past t).subset
    intro s hs
    rcases hs with ⟨hlt, hne⟩
    refine ⟨hlt, ?_⟩
    intro hn
    apply hne
    simp [hn]

-- Simultaneous occurrences from l precede those from r.
def merge {α : Type} (l r : Event α) : Event α where
  «at» := fun t => l.at t ++ r.at t
  finite_past := by
    intro t
    apply ((l.finite_past t).union (r.finite_past t)).subset
    intro s hs
    rcases hs with ⟨hlt, hne⟩
    classical
    by_cases hl : l.at s = []
    · right
      refine ⟨hlt, ?_⟩
      intro hr
      apply hne
      simp [hl, hr]
    · left
      exact ⟨hlt, hl⟩

noncomputable def once {α : Type} (τ : ℝ) (a : α) : Event α := by
  classical
  exact {
    «at» := fun t => if t = τ then [a] else []
    finite_past := by
      intro t
      apply (Set.finite_singleton τ).subset
      intro s hs
      rcases hs with ⟨_, hne⟩
      by_cases h : s = τ
      · simpa using h
      · exact False.elim (hne (ite_eq_right h))
  }

def snapshot {α β : Type} (e : Event α) (b : Behavior β) : Event (α × β) where
  «at» := fun t => (e.at t).map (fun a => (a, b t))
  finite_past := by
    intro t
    apply (e.finite_past t).subset
    intro s hs
    rcases hs with ⟨hlt, hne⟩
    refine ⟨hlt, ?_⟩
    intro hn
    apply hne
    simp [hn]

-- Classical specification only: do not execute a scan over all real numbers.
noncomputable def past {α : Type} (e : Event α) (t : ℝ) : List α := by
  classical
  exact (((e.finite_past t).toFinset).sort (· ≤ ·)).flatMap e.at

-- At t itself, occurrences at t have not yet changed the selected behavior.
noncomputable def switcher {α : Type} (initial : Behavior α)
    (changes : Event (Behavior α)) : Behavior α :=
  fun t => ((past changes t).foldl (fun _ next => next) initial) t

noncomputable def stepper {α : Type} (initial : α) (changes : Event α) : Behavior α :=
  switcher (Behavior.pure initial) (map Behavior.pure changes)

theorem merge_assoc {α : Type} (a b c : Event α) :
    merge (merge a b) c = merge a (merge b c) := by
  apply Event.ext
  funext t
  exact List.append_assoc (a.at t) (b.at t) (c.at t)

theorem merge_never {α : Type} (a : Event α) : merge a never = a := by
  apply Event.ext
  funext t
  exact List.append_nil (a.at t)

end Event

/-
  Raw program operations. Objects are indexed by their semantic types.
  A concrete IR need not store semantic functions: its input/output storage can
  be given separately by a realization relation. This is a many-sorted/cartesian
  specialization of Felix's raw-structure + homomorphism organization.
-/
structure Raw (H : Type → Type → Type) where
  ident : {α : Type} → H α α
  comp : {α β γ : Type} → H β γ → H α β → H α γ
  pair : {α β γ : Type} → H α β → H α γ → H α (β × γ)
  fst : {α β : Type} → H (α × β) α
  snd : {α β : Type} → H (α × β) β
  terminal : {α : Type} → H α Unit
  pureB : {α : Type} → H α (Behavior α)
  mapB : {α β : Type} → (α → β) → H (Behavior α) (Behavior β)
  apB : {α β : Type} → H (Behavior (α → β) × Behavior α) (Behavior β)
  clock : H Unit (Behavior ℝ)
  warp : {α : Type} → H (Behavior α × Behavior ℝ) (Behavior α)
  never : {α : Type} → H Unit (Event α)
  once : {α : Type} → H (ℝ × α) (Event α)
  mapE : {α β : Type} → (α → β) → H (Event α) (Event β)
  merge : {α : Type} → H (Event α × Event α) (Event α)
  snapshot : {α β : Type} → H (Event α × Behavior β) (Event (α × β))
  switcher : {α : Type} →
    H (Behavior α × Event (Behavior α)) (Behavior α)

-- Proof fields are specification obligations, not assumptions about a runtime.
structure Homomorphism (H : Type → Type → Type) (r : Raw H) where
  denote : {α β : Type} → H α β → (α → β)
  ident_hom : ∀ {α : Type}, denote (r.ident (α := α)) = id
  comp_hom : ∀ {α β γ : Type} (g : H β γ) (f : H α β),
    denote (r.comp g f) = denote g ∘ denote f
  pair_hom : ∀ {α β γ : Type} (f : H α β) (g : H α γ),
    denote (r.pair f g) = fun a => (denote f a, denote g a)
  fst_hom : ∀ {α β : Type}, denote (r.fst (α := α) (β := β)) = Prod.fst
  snd_hom : ∀ {α β : Type}, denote (r.snd (α := α) (β := β)) = Prod.snd
  terminal_hom : ∀ {α : Type},
    denote (r.terminal (α := α)) = fun _ => ()
  pureB_hom : ∀ {α : Type},
    denote (r.pureB (α := α)) = Behavior.pure
  mapB_hom : ∀ {α β : Type} (f : α → β),
    denote (r.mapB f) = Behavior.map f
  apB_hom : ∀ {α β : Type},
    denote (r.apB (α := α) (β := β)) = fun p => Behavior.ap p.1 p.2
  clock_hom : denote r.clock = fun _ => Behavior.clock
  warp_hom : ∀ {α : Type},
    denote (r.warp (α := α)) = fun p => Behavior.warp p.1 p.2
  never_hom : ∀ {α : Type},
    denote (r.never (α := α)) = fun _ => Event.never
  once_hom : ∀ {α : Type},
    denote (r.once (α := α)) = fun p => Event.once p.1 p.2
  mapE_hom : ∀ {α β : Type} (f : α → β),
    denote (r.mapE f) = Event.map f
  merge_hom : ∀ {α : Type},
    denote (r.merge (α := α)) = fun p => Event.merge p.1 p.2
  snapshot_hom : ∀ {α β : Type},
    denote (r.snapshot (α := α) (β := β)) = fun p => Event.snapshot p.1 p.2
  switcher_hom : ∀ {α : Type},
    denote (r.switcher (α := α)) = fun p => Event.switcher p.1 p.2

namespace Homomorphism

variable {H : Type → Type → Type} {r : Raw H} (D : Homomorphism H r)

def Eqv {α β : Type} (f g : H α β) : Prop := D.denote f = D.denote g

-- A representative "laws for free" result: equality is semantic, not structural.
theorem comp_assoc {α β γ δ : Type} (h : H γ δ) (g : H β γ) (f : H α β) :
    D.Eqv (r.comp (r.comp h g) f) (r.comp h (r.comp g f)) := by
  unfold Eqv
  rw [D.comp_hom, D.comp_hom, D.comp_hom, D.comp_hom]
  rfl

end Homomorphism

-- Prefix noninterference for ordinary behavior inputs and outputs.
def AgreeThrough {α : Type} (t : ℝ) (x y : Behavior α) : Prop :=
  ∀ s, s ≤ t → x s = y s

def Causal {α β : Type} (f : Behavior α → Behavior β) : Prop :=
  ∀ t x y, AgreeThrough t x y → AgreeThrough t (f x) (f y)

structure CausalMap (α β : Type) where
  run : Behavior α → Behavior β
  causal : Causal run

/- An explicit partial-information specification for source protocols.
   This is deliberately distinct from the Event denotation.
   Known no-occurrence is represented by absence in a COMPLETE prefix.
   Nothing is inferred about times at or after the frontier.
-/
structure Prefix (α : Type) where
  frontier : ℝ
  data : Event α

-- data may contain extra future observations; only the prefix is certified.
def Prefix.Sound {α : Type} (p : Prefix α) (truth : Event α) : Prop :=
  ∀ t, t < p.frontier → p.data.at t = truth.at t

def Prefix.Refines {α : Type} (p q : Prefix α) : Prop :=
  p.frontier ≤ q.frontier ∧
    ∀ t, t < p.frontier → p.data.at t = q.data.at t

def Prefix.Compatible {α : Type} (p q : Prefix α) : Prop :=
  ∃ truth : Event α, p.Sound truth ∧ q.Sound truth

-- A frontier crossing really does certify a complete timestamp batch.
theorem batch_exact {α : Type} (p : Prefix α) (e : Event α)
    (h : p.Sound e) (t : ℝ) (ht : t < p.frontier) : p.data.at t = e.at t :=
  h t ht

/- A reactive normal form, as a mathematical specification of the IR.
   Executable Phase syntax and an online realization of `changes` are still
   needed. Keeping those choices separate is intentional.
-/
structure RNF (Phase : Type → Type) (α : Type) where
  initial : Phase α
  changes : Event (Phase α)

noncomputable def denoteRNF {Phase : Type → Type}
    (denotePhase : {α : Type} → Phase α → Behavior α)
    {α : Type} (r : RNF Phase α) : Behavior α :=
  Event.switcher (denotePhase r.initial) (Event.map denotePhase r.changes)

end FRPSpec
