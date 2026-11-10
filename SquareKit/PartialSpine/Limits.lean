import SquareKit.IdealCompletion
import SquareKit.PartialSpine.Cut
import SquareKit.PartialSpine.Observations

/-!
# Directed limits and continuous folds of partial-spine observations

The existing observation carrier receives the named pointed-ideal CPO.
Semantic constructors and folds are specializations of one generic extension.
Monotone steps suffice for input continuity; evaluating a cons requires
continuity of the corresponding tail step. Labels carry no order.
-/

set_option autoImplicit false
set_option warningAsError true

noncomputable section

namespace SquareKit.PartialSpine.Observations

open Order

universe u v w
variable {α : Type u} {B : Type v} {C : Type w}

instance : CompletePartialOrder (Observations α) := IdealCompletion.pointedIdealCPO

theorem mem_sSup (S : Set (Observations α)) (nonempty : S.Nonempty)
    (directed : DirectedOn (· ≤ ·) S) (q : PartialSpine α) :
    q ∈ sSup S ↔ ∃ I ∈ S, q ∈ I :=
  IdealCompletion.mem_pointedSup S nonempty directed q

/-- Membership in a principal-valued extension uses this owner's actual ideal
CPO. The source may be any preorder; no alternative CPO on the target is assumed. -/
theorem mem_extend_principal {P : Type v} [Preorder P]
    (g : P → PartialSpine α) (monotone : Monotone g)
    (I : Ideal P) (q : PartialSpine α) :
    q ∈ IdealCompletion.extend (fun s => Ideal.principal (g s)) I ↔
      ∃ s ∈ I, q ≤ g s := by
  change q ∈ sSup ((fun s => Ideal.principal (g s)) '' (I : Set P)) ↔ _
  rw [mem_sSup ((fun s => Ideal.principal (g s)) '' (I : Set P)) (I.nonempty.image _)
    (I.directed.mono_comp (IdealCompletion.principal_monotone.comp monotone))]
  constructor
  · rintro ⟨_, ⟨s, hs, rfl⟩, hq⟩
    exact ⟨s, hs, Ideal.mem_principal.mp hq⟩
  · rintro ⟨s, hs, hq⟩
    exact ⟨Ideal.principal (g s), ⟨s, hs, rfl⟩, Ideal.mem_principal.mpr hq⟩

@[simp] theorem sSup_empty : sSup (∅ : Set (Observations α)) = ⊥ :=
  IdealCompletion.pointedSup_empty

theorem principal_cons_monotone (a : α) :
    Monotone (fun s : PartialSpine α => Ideal.principal (PartialSpine.cons a s)) := by
  intro s t h
  exact IdealCompletion.principal_monotone (Below.cons a h)

/-- Prepend one known label; the continuation retains its existing observations. -/
def cons (a : α) (I : Observations α) : Observations α :=
  IdealCompletion.extend (fun s => Ideal.principal (PartialSpine.cons a s)) I

@[simp] theorem cons_principal (a : α) (s : PartialSpine α) :
    cons a (Ideal.principal s) = Ideal.principal (.cons a s) :=
  IdealCompletion.extend_principal (principal_cons_monotone a) s

theorem cons_monotone (a : α) : Monotone (cons a) :=
  IdealCompletion.extend_monotone (principal_cons_monotone a)

theorem cons_continuous (a : α) : ScottContinuous (cons a) :=
  IdealCompletion.extend_scottContinuous (principal_cons_monotone a)

theorem mem_cons (a : α) (I : Observations α) (q : PartialSpine α) :
    q ∈ cons a I ↔ q = ⊥ ∨ ∃ t ∈ I, q = PartialSpine.cons a t := by
  change q ∈ sSup ((fun s => Ideal.principal (PartialSpine.cons a s)) '' (I : Set _)) ↔ _
  rw [mem_sSup _ (I.nonempty.image _) (I.directed.mono_comp (principal_cons_monotone a))]
  constructor
  · rintro ⟨_, ⟨s, hs, rfl⟩, hq⟩
    rcases (le_cons_iff q a s).mp (Ideal.mem_principal.mp hq) with bottom | ⟨t, rfl, ht⟩
    · exact Or.inl bottom
    · exact Or.inr ⟨t, I.lower ht hs, rfl⟩
  · rintro (bottom | ⟨t, ht, rfl⟩)
    · refine ⟨Ideal.principal (.cons a ⊥), ⟨⊥, I.bot_mem, rfl⟩, ?_⟩
      rw [bottom]
      exact Ideal.mem_principal.mpr bot_le
    · exact ⟨Ideal.principal (.cons a t), ⟨t, ht, rfl⟩, Ideal.mem_principal_self⟩

@[simp] theorem cons_bottom (a : α) : cons a ⊥ = Ideal.principal (.cons a .bottom) :=
  cons_principal a .bottom

/-- Scott continuity does not force preservation of the empty directed limit. -/
theorem cons_not_strict (a : α) : cons a ⊥ ≠ ⊥ := by
  rw [cons_bottom]
  intro same
  have finite := principal_injective same
  cases finite

theorem stream_prefixes_directed (σ : Stream' α) :
    DirectedOn (· ≤ ·) (Set.range fun n => Ideal.principal (openPrefix (σ.take n))) := by
  have monotone : Monotone (fun n => Ideal.principal (openPrefix (σ.take n))) := by
    intro m n h
    exact IdealCompletion.principal_monotone (streamPrefix_mono σ h)
  exact monotone.directed_le.directedOn_range

theorem stream_prefixes_isLUB (σ : Stream' α) :
    IsLUB (Set.range fun n => Ideal.principal (openPrefix (σ.take n))) (stream σ) := by
  constructor
  · rintro _ ⟨n, rfl⟩
    exact Ideal.principal_le_iff.mpr (stream_observes_prefix σ n)
  · intro I upper q hq
    obtain ⟨n, hn⟩ := hq
    exact upper ⟨n, rfl⟩ hn

/-- The independent infinite-stream ideal is the limit of all its principal prefixes. -/
theorem stream_eq_sSup_prefixes (σ : Stream' α) :
    stream σ = sSup (Set.range fun n => Ideal.principal (openPrefix (σ.take n))) :=
  (stream_prefixes_isLUB σ).unique (stream_prefixes_directed σ).isLUB_sSup

theorem stream_cons (σ : Stream' α) :
    stream σ = cons (σ 0) (stream (fun n => σ (n + 1))) := by
  apply Ideal.ext
  apply Set.ext
  intro q
  change q ∈ stream σ ↔ q ∈ cons (σ 0) (stream (fun n => σ (n + 1)))
  rw [mem_cons]
  constructor
  · rintro ⟨n, hn⟩
    cases n with
    | zero => exact Or.inl (le_bot_iff.mp hn)
    | succ n =>
      change q ≤ PartialSpine.cons (σ 0) (openPrefix (Stream'.take n (fun k => σ (k + 1)))) at hn
      rcases (le_cons_iff q _ _).mp hn with bottom | ⟨t, rfl, ht⟩
      · exact Or.inl bottom
      · exact Or.inr ⟨t, ⟨n, ht⟩, rfl⟩
  · rintro (rfl | ⟨t, ⟨n, ht⟩, rfl⟩)
    · exact ⟨0, le_rfl⟩
    · exact ⟨n + 1, Below.cons (σ 0) ht⟩

section FiniteOrder

variable [Preorder B]

theorem finiteFold_seed_monotone (bottom : B) (f : α → B → B)
    (monotone : ∀ a, Monotone (f a)) (s : PartialSpine α) :
    Monotone (fun e => PartialSpine.foldr bottom f e s) := by
  intro e e' he
  induction s with
  | bottom => exact le_rfl
  | nil => exact he
  | cons a s ih => exact monotone a ih

theorem finiteFold_seed_continuous (bottom : B) (f : α → B → B)
    (continuous : ∀ a, ScottContinuous (f a)) (s : PartialSpine α) :
    ScottContinuous (fun e => PartialSpine.foldr bottom f e s) := by
  induction s with
  | bottom => exact ScottContinuous.const bottom
  | nil => exact ScottContinuous.id
  | cons a s ih => exact ih.comp (continuous a)

variable [OrderBot B]

theorem finiteFold_monotone (f : α → B → B) (e : B)
    (monotone : ∀ a, Monotone (f a)) : Monotone (PartialSpine.foldr ⊥ f e) := by
  intro s t h
  induction h with
  | bottom => exact bot_le
  | nil => exact le_rfl
  | cons a _ ih => exact monotone a ih

end FiniteOrder

section Fold

variable [CompletePartialOrder B]

/-- Interpret every finite observation, then take its directed limit. -/
def foldr (f : α → B → B) (e : B) (I : Observations α) : B :=
  IdealCompletion.extend (PartialSpine.foldr ⊥ f e) I

theorem finiteFold_le_foldr (f : α → B → B) (e : B)
    (monotone : ∀ a, Monotone (f a)) (I : Observations α) {s : PartialSpine α} (hs : s ∈ I) :
    PartialSpine.foldr ⊥ f e s ≤ foldr f e I :=
  IdealCompletion.le_extend (finiteFold_monotone f e monotone) I hs

theorem foldr_le (f : α → B → B) (e : B) (monotone : ∀ a, Monotone (f a))
    (I : Observations α) {b : B} (upper : ∀ s ∈ I, PartialSpine.foldr ⊥ f e s ≤ b) :
    foldr f e I ≤ b :=
  IdealCompletion.extend_le (finiteFold_monotone f e monotone) I upper

theorem foldr_monotone (f : α → B → B) (e : B) (monotone : ∀ a, Monotone (f a)) :
    Monotone (foldr f e) :=
  IdealCompletion.extend_monotone (finiteFold_monotone f e monotone)

theorem foldr_continuous (f : α → B → B) (e : B) (monotone : ∀ a, Monotone (f a)) :
    ScottContinuous (foldr f e) :=
  IdealCompletion.extend_scottContinuous (finiteFold_monotone f e monotone)

theorem foldr_principal (f : α → B → B) (e : B) (monotone : ∀ a, Monotone (f a))
    (s : PartialSpine α) : foldr f e (Ideal.principal s) = PartialSpine.foldr ⊥ f e s :=
  IdealCompletion.extend_principal (finiteFold_monotone f e monotone) s

@[simp] theorem foldr_bottom (f : α → B → B) (e : B) (monotone : ∀ a, Monotone (f a)) :
    foldr f e ⊥ = ⊥ :=
  foldr_principal f e monotone .bottom

@[simp] theorem foldr_nil (f : α → B → B) (e : B) (monotone : ∀ a, Monotone (f a)) :
    foldr f e (Ideal.principal .nil) = e :=
  foldr_principal f e monotone .nil

theorem foldr_ofList (f : α → B → B) (e : B) (monotone : ∀ a, Monotone (f a))
    (xs : List α) : foldr f e (Ideal.principal (ofList xs)) = xs.foldr f e := by
  rw [foldr_principal f e monotone, PartialSpine.foldr_ofList]

/-- The selected tail step must preserve directed limits to evaluate a semantic cons. -/
theorem foldr_cons (f : α → B → B) (e : B) (monotone : ∀ a, Monotone (f a))
    (a : α) (continuous : ScottContinuous (f a)) (I : Observations α) :
    foldr f e (cons a I) = f a (foldr f e I) := by
  apply IdealCompletion.continuous_ext
    ((cons_continuous a).comp (foldr_continuous f e monotone))
    ((foldr_continuous f e monotone).comp continuous) (I := I)
  intro s
  change foldr f e (cons a (Ideal.principal s)) = f a (foldr f e (Ideal.principal s))
  rw [cons_principal, foldr_principal f e monotone, foldr_principal f e monotone]
  rfl

theorem foldr_seed_monotone (f : α → B → B) (monotone : ∀ a, Monotone (f a))
    (I : Observations α) : Monotone (fun e => foldr f e I) := by
  intro e e' he
  exact IdealCompletion.extend_mono_interpreter (finiteFold_monotone f e monotone)
    (finiteFold_monotone f e' monotone)
    (fun s => finiteFold_seed_monotone ⊥ f monotone s he) I

theorem foldr_seed_continuous (f : α → B → B) (continuous : ∀ a, ScottContinuous (f a))
    (I : Observations α) : ScottContinuous (fun e => foldr f e I) :=
  IdealCompletion.extend_param_scottContinuous (fun e s => PartialSpine.foldr ⊥ f e s)
    (fun e => finiteFold_monotone f e (fun a => (continuous a).monotone))
    (fun s => finiteFold_seed_continuous ⊥ f continuous s) I

end Fold

/-- Constructor folding recovers every ideal, including genuine infinite streams. -/
theorem foldr_cons_identity (I : Observations α) :
    foldr cons (Ideal.principal .nil) I = I := by
  apply IdealCompletion.continuous_ext
    (foldr_continuous cons (Ideal.principal .nil) cons_monotone) ScottContinuous.id (I := I)
  intro s
  rw [foldr_principal cons (Ideal.principal .nil) cons_monotone]
  exact (PartialSpine.foldr_unique (⊥ : Observations α) cons (Ideal.principal .nil)
    Ideal.principal rfl rfl (fun a t => (cons_principal a t).symm) s).symm

section Fusion

variable [CompletePartialOrder B] [CompletePartialOrder C]

theorem foldr_fusion (f : α → B → B) (g : α → C → C) (e : B)
    (fMonotone : ∀ a, Monotone (f a)) (gMonotone : ∀ a, Monotone (g a))
    (h : B → C) (continuous : ScottContinuous h) (strict : h ⊥ = ⊥)
    (commute : ∀ a b, h (f a b) = g a (h b)) (I : Observations α) :
    h (foldr f e I) = foldr g (h e) I :=
  IdealCompletion.extend_fusion (finiteFold_monotone f e fMonotone)
    (finiteFold_monotone g (h e) gMonotone) continuous
    (fun s => PartialSpine.foldr_fusion ⊥ ⊥ f g h e strict commute s) I

theorem foldr_fusion_continuous (f : α → B → B) (g : α → C → C) (e : B)
    (fContinuous : ∀ a, ScottContinuous (f a)) (gContinuous : ∀ a, ScottContinuous (g a))
    (h : B → C) (continuous : ScottContinuous h) (strict : h ⊥ = ⊥)
    (commute : ∀ a b, h (f a b) = g a (h b)) (I : Observations α) :
    h (foldr f e I) = foldr g (h e) I :=
  foldr_fusion f g e (fun a => (fContinuous a).monotone)
    (fun a => (gContinuous a).monotone) h continuous strict commute I

theorem fusion_requires_strict (f : α → B → B) (g : α → C → C) (e : B)
    (fMonotone : ∀ a, Monotone (f a)) (gMonotone : ∀ a, Monotone (g a)) (h : B → C)
    (all : ∀ I : Observations α, h (foldr f e I) = foldr g (h e) I) : h ⊥ = ⊥ := by
  simpa only [foldr_bottom f e fMonotone, foldr_bottom g (h e) gMonotone] using all ⊥

end Fusion
end SquareKit.PartialSpine.Observations
