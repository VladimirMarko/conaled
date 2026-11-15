import SquareKit.ListFusion
import Mathlib.Logic.Equiv.Defs
import Mathlib.Order.BoundedOrder.Basic

/-!
# Finite observations of a partial list spine

Known constructors end in either an unknown continuation or a completed nil.
The independent normal form is an ordered prefix and its completed-end flag.
Fold fusion reuses the standard finite-list law with both possible terminal
states. Labels are fixed values under the information order.
-/

set_option autoImplicit false
set_option warningAsError true

namespace SquareKit

universe u v w

/-- A finite observation, with distinct unknown and completed ends. -/
inductive PartialSpine (α : Type u) where
  | bottom
  | nil
  | cons (head : α) (tail : PartialSpine α)
deriving Repr, DecidableEq

namespace PartialSpine

variable {α : Type u} {β : Type v} {γ : Type w}

/-- Ordered known labels, together with whether a final nil was observed. -/
def view : PartialSpine α → List α × Bool
  | .bottom => ([], false)
  | .nil => ([], true)
  | .cons a s => (a :: (view s).1, (view s).2)

/-- Reconstruct an observation from its independent prefix/end description. -/
def fromView (p : List α × Bool) : PartialSpine α :=
  p.1.foldr cons (if p.2 then .nil else .bottom)

@[simp] theorem view_fromView (p : List α × Bool) : view (fromView p) = p := by
  rcases p with ⟨xs, complete⟩
  induction xs with
  | nil => cases complete <;> rfl
  | cons a xs ih =>
    change (a :: (view (fromView (xs, complete))).1,
      (view (fromView (xs, complete))).2) = _
    rw [ih]

@[simp] theorem fromView_view (s : PartialSpine α) : fromView (view s) = s := by
  induction s with
  | bottom => rfl
  | nil => rfl
  | cons a s ih =>
    change cons a (fromView (view s)) = cons a s
    exact congrArg (cons a) ih

def viewEquiv : PartialSpine α ≃ List α × Bool where
  toFun := view
  invFun := fromView
  left_inv := fromView_view
  right_inv := view_fromView

theorem view_injective : Function.Injective (view (α := α)) := viewEquiv.injective

@[simp] theorem view_inj {s t : PartialSpine α} : view s = view t ↔ s = t :=
  view_injective.eq_iff

/-- The exact completed finite-list embedding. -/
def ofList (xs : List α) : PartialSpine α := fromView (xs, true)

/-- A known prefix that makes no claim about a completed end. -/
def openPrefix (xs : List α) : PartialSpine α := fromView (xs, false)

@[simp] theorem ofList_nil : ofList ([] : List α) = .nil := rfl
@[simp] theorem ofList_cons (a : α) (xs : List α) :
    ofList (a :: xs) = .cons a (ofList xs) := rfl
@[simp] theorem openPrefix_nil : openPrefix ([] : List α) = .bottom := rfl
@[simp] theorem openPrefix_cons (a : α) (xs : List α) :
    openPrefix (a :: xs) = .cons a (openPrefix xs) := rfl

@[simp] theorem view_ofList (xs : List α) : view (ofList xs) = (xs, true) :=
  view_fromView _

@[simp] theorem view_openPrefix (xs : List α) : view (openPrefix xs) = (xs, false) :=
  view_fromView _

/-- The entire finite spine through the last nil has been observed. -/
def IsTotal (s : PartialSpine α) : Prop := (view s).2 = true

@[simp] theorem ofList_isTotal (xs : List α) : IsTotal (ofList xs) := by
  simp [IsTotal]

theorem isTotal_iff_exists (s : PartialSpine α) :
    IsTotal s ↔ ∃ xs : List α, ofList xs = s := by
  constructor
  · intro h
    refine ⟨(view s).1, view_injective ?_⟩
    rw [view_ofList]
    exact Prod.ext rfl h.symm
  · rintro ⟨xs, rfl⟩
    exact ofList_isTotal xs

theorem ofList_injective : Function.Injective (ofList (α := α)) := by
  intro xs ys h
  simpa using congrArg (fun s => (view s).1) h

/-- The two ends have separate interpretations; a step may ignore its tail. -/
def foldr (bottom : β) (f : α → β → β) (e : β) : PartialSpine α → β
  | .bottom => bottom
  | .nil => e
  | .cons a s => f a (foldr bottom f e s)

theorem foldr_eq_view (bottom : β) (f : α → β → β) (e : β) (s : PartialSpine α) :
    foldr bottom f e s = (view s).1.foldr f (if (view s).2 then e else bottom) := by
  induction s with
  | bottom => rfl
  | nil => rfl
  | cons a s ih =>
    change f a (foldr bottom f e s) =
      f a ((view s).1.foldr f (if (view s).2 then e else bottom))
    exact congrArg (f a) ih

theorem foldr_unique (bottom : β) (f : α → β → β) (e : β)
    (k : PartialSpine α → β) (atBottom : k .bottom = bottom) (atNil : k .nil = e)
    (atCons : ∀ a s, k (.cons a s) = f a (k s)) (s : PartialSpine α) :
    k s = foldr bottom f e s := by
  induction s with
  | bottom => exact atBottom
  | nil => exact atNil
  | cons a s ih => simp only [atCons, ih, foldr]

theorem foldr_ofList (bottom : β) (f : α → β → β) (e : β) (xs : List α) :
    foldr bottom f e (ofList xs) = xs.foldr f e := by
  simp only [foldr_eq_view, view_ofList, ↓reduceIte]

theorem foldr_openPrefix (bottom : β) (f : α → β → β) (e : β) (xs : List α) :
    foldr bottom f e (openPrefix xs) = xs.foldr f bottom := by
  simp only [foldr_eq_view, view_openPrefix, Bool.false_eq_true, ↓reduceIte]

theorem foldr_ofList_independent_bottom (b c : β) (f : α → β → β) (e : β)
    (xs : List α) : foldr b f e (ofList xs) = foldr c f e (ofList xs) := by
  rw [foldr_ofList, foldr_ofList]

theorem foldr_invariant (bottom : β) (f : α → β → β) (e : β) (P : β → Prop)
    (atBottom : P bottom) (atNil : P e) (atCons : ∀ a b, P b → P (f a b))
    (s : PartialSpine α) : P (foldr bottom f e s) := by
  rw [foldr_eq_view]
  apply List.foldrRecOn
  · split <;> assumption
  · exact fun b hb a _ => atCons a b hb

/-- Both terminal states must be valid; only reachable accumulator laws are needed. -/
theorem foldr_fusion_reachable (bottomB : β) (bottomC : γ)
    (f : α → β → β) (g : α → γ → γ) (h : β → γ) (e : β)
    (P : β → Prop) (atBottom : P bottomB) (atNil : P e)
    (atCons : ∀ a b, P b → P (f a b)) (strict : h bottomB = bottomC)
    (law : ∀ a b, P b → h (f a b) = g a (h b)) (s : PartialSpine α) :
    h (foldr bottomB f e s) = foldr bottomC g (h e) s := by
  rw [foldr_eq_view, foldr_eq_view]
  cases hc : (view s).2 with
  | false =>
    simpa only [hc, Bool.false_eq_true, ↓reduceIte, strict] using
      ListFusion.foldr_reachable f g h P bottomB atBottom atCons law (view s).1
  | true =>
    simpa only [hc, ↓reduceIte] using
      ListFusion.foldr_reachable f g h P e atNil atCons law (view s).1

theorem foldr_fusion (bottomB : β) (bottomC : γ)
    (f : α → β → β) (g : α → γ → γ) (h : β → γ) (e : β)
    (strict : h bottomB = bottomC) (law : ∀ a b, h (f a b) = g a (h b))
    (s : PartialSpine α) : h (foldr bottomB f e s) = foldr bottomC g (h e) s :=
  foldr_fusion_reachable bottomB bottomC f g h e (fun _ => True) trivial trivial
    (fun _ _ _ => trivial) strict (fun a b _ => law a b) s

/-- Exact necessity and sufficiency; the target seed is the observed source seed. -/
theorem foldr_fusion_iff (bottomB : β) (bottomC : γ)
    (f : α → β → β) (g : α → γ → γ) (h : β → γ) (e : β) :
    (∀ s : PartialSpine α, h (foldr bottomB f e s) = foldr bottomC g (h e) s) ↔
      h bottomB = bottomC ∧
      (∀ a s, h (f a (foldr bottomB f e s)) = g a (h (foldr bottomB f e s))) := by
  constructor
  · intro fusion
    refine ⟨fusion .bottom, ?_⟩
    intro a s
    simpa only [foldr, fusion s] using fusion (.cons a s)
  · rintro ⟨strict, law⟩ s
    induction s with
    | bottom => exact strict
    | nil => rfl
    | cons a s ih => simp only [foldr, law, ih]

theorem foldr_fusion_iff_strict_of_commuting (bottomB : β) (bottomC : γ)
    (f : α → β → β) (g : α → γ → γ) (h : β → γ) (e : β)
    (law : ∀ a b, h (f a b) = g a (h b)) :
    (∀ s : PartialSpine α, h (foldr bottomB f e s) = foldr bottomC g (h e) s) ↔
      h bottomB = bottomC :=
  ⟨fun fusion => ((foldr_fusion_iff bottomB bottomC f g h e).mp fusion).1,
    fun strict s => foldr_fusion bottomB bottomC f g h e strict law s⟩

/-- Total finite inputs require no preservation of an unobserved bottom. -/
theorem foldr_fusion_ofList (bottomB : β) (bottomC : γ)
    (f : α → β → β) (g : α → γ → γ) (h : β → γ) (e : β)
    (law : ∀ a b, h (f a b) = g a (h b)) (xs : List α) :
    h (foldr bottomB f e (ofList xs)) = foldr bottomC g (h e) (ofList xs) := by
  rw [foldr_ofList, foldr_ofList]
  exact ListFusion.foldr_reachable f g h (fun _ => True) e trivial
    (fun _ _ _ => trivial) (fun a b _ => law a b) xs

def map (f : α → β) : PartialSpine α → PartialSpine β
  | .bottom => .bottom
  | .nil => .nil
  | .cons a s => .cons (f a) (map f s)

theorem view_map (f : α → β) (s : PartialSpine α) :
    view (map f s) = ((view s).1.map f, (view s).2) := by
  induction s <;> simp_all [map, view]

theorem map_ofList (f : α → β) (xs : List α) : map f (ofList xs) = ofList (xs.map f) := by
  apply view_injective
  simp [view_map]

theorem map_openPrefix (f : α → β) (xs : List α) :
    map f (openPrefix xs) = openPrefix (xs.map f) := by
  apply view_injective
  simp [view_map]

theorem map_eq_foldr (f : α → β) (s : PartialSpine α) :
    map f s = foldr .bottom (fun a t => .cons (f a) t) .nil s :=
  foldr_unique _ _ _ (map f) rfl rfl (fun _ _ => rfl) s

theorem map_id (s : PartialSpine α) : map id s = s := by
  apply view_injective
  simp [view_map]

theorem map_fusion (f : β → γ) (g : α → β) (s : PartialSpine α) :
    map f (map g s) = map (f ∘ g) s := by
  apply view_injective
  simp [view_map, List.map_map]

theorem foldr_map (bottom : γ) (f : β → γ → γ) (e : γ) (g : α → β)
    (s : PartialSpine α) :
    foldr bottom f e (map g s) = foldr bottom (fun a b => f (g a) b) e s := by
  simp only [foldr_eq_view, view_map, List.foldr_map]

theorem foldr_cons_identity (s : PartialSpine α) : foldr .bottom cons .nil s = s :=
  (foldr_unique .bottom cons .nil id rfl rfl (fun _ _ => rfl) s).symm

/-- Refinement of spine information holds the known labels fixed. -/
inductive Below : PartialSpine α → PartialSpine α → Prop where
  | bottom (s) : Below .bottom s
  | nil : Below .nil .nil
  | cons (a) {s t} : Below s t → Below (.cons a s) (.cons a t)

instance : PartialOrder (PartialSpine α) where
  le := Below
  le_refl s := by
    induction s with
    | bottom => exact .bottom _
    | nil => exact .nil
    | cons a s ih => exact .cons a ih
  le_trans _ _ r h k := by
    induction h generalizing r with
    | bottom => exact .bottom _
    | nil => exact k
    | cons a _ ih => cases k with | cons _ k => exact .cons a (ih _ k)
  le_antisymm _ _ h k := by
    induction h with
    | bottom => cases k; rfl
    | nil => rfl
    | cons a _ ih => cases k with | cons _ k => exact congrArg (cons a) (ih k)

instance : OrderBot (PartialSpine α) where
  bot := .bottom
  bot_le s := .bottom s

@[simp] theorem bottom_eq_bot : (bottom : PartialSpine α) = ⊥ := rfl

@[simp] theorem le_nil_iff (s : PartialSpine α) : s ≤ .nil ↔ s = .bottom ∨ s = .nil := by
  constructor
  · intro h; cases h <;> simp
  · rintro (rfl | rfl)
    · exact bot_le
    · exact le_rfl

@[simp] theorem nil_le_iff (s : PartialSpine α) : .nil ≤ s ↔ .nil = s := by
  constructor
  · intro h; cases h; rfl
  · rintro rfl; exact le_rfl

theorem le_cons_iff (s : PartialSpine α) (a : α) (t : PartialSpine α) :
    s ≤ .cons a t ↔ s = .bottom ∨ ∃ r, s = .cons a r ∧ r ≤ t := by
  constructor
  · intro h
    cases h with
    | bottom => exact Or.inl rfl
    | cons _ h => exact Or.inr ⟨_, rfl, h⟩
  · rintro (rfl | ⟨r, rfl, h⟩)
    · exact bot_le
    · exact .cons a h

@[simp] theorem cons_le_cons (a b : α) (s t : PartialSpine α) :
    cons a s ≤ cons b t ↔ a = b ∧ s ≤ t := by
  constructor
  · intro h; cases h with | cons _ h => exact ⟨rfl, h⟩
  · rintro ⟨rfl, h⟩; exact .cons _ h

theorem prefix_of_le {s t : PartialSpine α} (h : s ≤ t) : (view s).1 <+: (view t).1 := by
  induction h with
  | bottom => exact List.nil_prefix
  | nil => exact List.prefix_rfl
  | cons a _ ih => exact List.cons_prefix_cons.mpr ⟨rfl, ih⟩

theorem openPrefix_le_iff (xs : List α) (s : PartialSpine α) :
    openPrefix xs ≤ s ↔ xs <+: (view s).1 := by
  induction xs generalizing s with
  | nil => simp
  | cons a xs ih =>
    cases s <;> simp [view, le_nil_iff, cons_le_cons, ih]

theorem ofList_le_iff (xs : List α) (s : PartialSpine α) : ofList xs ≤ s ↔ ofList xs = s := by
  induction xs generalizing s with
  | nil => simp
  | cons a xs ih =>
    cases s <;> simp [le_nil_iff, cons_le_cons, ih]

/-- Independent prefix/end characterization of the constructor information order. -/
theorem fromView_le_fromView (xs ys : List α) (complete resultComplete : Bool) :
    fromView (xs, complete) ≤ fromView (ys, resultComplete) ↔
      if complete then xs = ys ∧ resultComplete = true else xs <+: ys := by
  cases complete with
  | false =>
    change openPrefix xs ≤ fromView (ys, resultComplete) ↔ xs <+: ys
    rw [openPrefix_le_iff, view_fromView]
  | true =>
    change ofList xs ≤ fromView (ys, resultComplete) ↔ xs = ys ∧ resultComplete = true
    rw [ofList_le_iff, ← view_inj, view_ofList, view_fromView]
    simp only [Prod.mk.injEq, eq_comm (a := true)]

/-- Number of labels already known; an open end is not a claim of total length. -/
def knownLength (s : PartialSpine α) : Nat := (view s).1.length

theorem knownLength_mono {s t : PartialSpine α} (h : s ≤ t) : knownLength s ≤ knownLength t :=
  (prefix_of_le h).length_le

@[simp] theorem knownLength_openPrefix (xs : List α) : knownLength (openPrefix xs) = xs.length := by
  simp [knownLength]

end PartialSpine
end SquareKit
