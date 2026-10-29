import Applications.Progress.DependentFeedback
import SquareKit.Temporal.Relations
import Mathlib.Data.Fin.Rev

/-! Occurrence identity in growing histories. Equal payloads need not identify
an occurrence; the cursor remains data indexed by the actual feedback state. -/
namespace Progress.Feedback.Occurrence
open DependentSquares
variable {α : Type}

abbrev Cursor (xs : List α) := Fin xs.length

def forward (initial : List α) : Initialized α (List α) (List α) where
  initial := initial
  step := fun (a,s) => (s++[a],s++[a])

def backward (initial : List α) : Initialized α (List α) (List α) where
  initial := initial
  step := fun (a,s) => ((a::s).reverse,a::s)

def keep (a : α) (s : List α) (i : Cursor s) : Cursor (s++[a]) :=
  ⟨i.val,by simp only [List.length_append,List.length_singleton]; omega⟩
def move (a : α) (s : List α) (i : Cursor s) : Cursor (a::s) := i.succ

def Repr (s t : List α) : Prop := s = t.reverse

def CursorRel : TyRel (Repr (α := α)) Cursor Cursor :=
  fun s _ _ i j => i.val+j.val+1 = s.length

def encode (s t : List α) (h : Repr s t) (i : Cursor s) : Cursor t :=
  Fin.cast (by simpa [Repr] using congrArg List.length h) i.rev

theorem encode_related (s t : List α) (h : Repr s t) (i : Cursor s) :
    CursorRel s t h i (encode s t h i) := by
  change i.val + (s.length - (i.val+1)) + 1 = s.length
  have := i.isLt
  omega

theorem encode_unique (s t : List α) (h : Repr s t) (i : Cursor s) (j : Cursor t)
    (related : CursorRel s t h i j) : encode s t h i = j := by
  apply Fin.ext
  have he := encode_related s t h i
  change i.val + _ + 1 = s.length at he related
  omega

theorem repr_step (a : α) (s t : List α) (h : Repr s t) : Repr (s++[a]) (a::t) := by
  simpa [Repr,List.reverse_cons] using congrArg (fun x => x++[a]) h

theorem cursor_step (a : α) (s t : List α) (h : Repr s t) (i : Cursor s) (j : Cursor t)
    (related : CursorRel s t h i j) :
    CursorRel _ _ (repr_step a s t h) (keep a s i) (move a t j) := by
  change i.val+j.val+1 = s.length at related
  change i.val+(j.val+1)+1 = (s++[a]).length
  simp only [List.length_append,List.length_singleton]
  omega

/-- Reversing the occurrence commutes with growing the two representations. -/
theorem encode_advance (a : α) (s t : List α) (h : Repr s t) (i : Cursor s) :
    encode _ _ (repr_step a s t h) (keep a s i) = move a t (encode s t h i) :=
  encode_unique _ _ _ _ _ (cursor_step a s t h i _ (encode_related s t h i))

theorem lookup (s t : List α) (h : Repr s t) (i : Cursor s) (j : Cursor t)
    (related : CursorRel s t h i j) : s[i.val] = t[j.val] := by
  change s = t.reverse at h
  subst s
  rw [List.getElem_reverse]
  have hr : i.val+j.val+1 = t.length := by simpa [CursorRel] using related
  have he : t.length-1-i.val = j.val := by omega
  simp only [he]

def forwardCursor (initial : List α) (i : Cursor initial) (a : Stream α) (n : Nat) :
    Cursor (state (forward initial) a n) :=
  Dependent.certificate (forward initial) Cursor keep i a n

def backwardCursor (initial : List α) (i : Cursor initial) (a : Stream α) (n : Nat) :
    Cursor (state (backward initial) a n) :=
  Dependent.certificate (backward initial) Cursor move i a n

theorem base_step (s₀ t₀ : List α) (a b : α) (s t : List α)
    (hi : a = b) (hr : Repr s t) :
    ((forward s₀).step (a,s)).1 = ((backward t₀).step (b,t)).1 ∧
      Repr ((forward s₀).step (a,s)).2 ((backward t₀).step (b,t)).2 := by
  subst b
  exact ⟨repr_step a s t hr,repr_step a s t hr⟩

/-- Relates the actual selected occurrences over the original recursive solutions. -/
theorem cursors_related (s t : List α) (h : Repr s t) (i : Cursor s) (j : Cursor t)
    (initial : CursorRel s t h i j) (a : Stream α) (n : Nat) :
    ∃ hr : Repr (state (forward s) a n) (state (backward t) a n),
      CursorRel _ _ hr (forwardCursor s i a n) (backwardCursor t j a n) := by
  exact Dependent.transport (forward s) (backward t) Cursor Cursor keep move i j
    Eq Repr Eq CursorRel h initial (base_step s t)
    (by intro x y u v hi hr c d he; subst y; exact cursor_step x u v hr c d he)
    a a (fun _ => rfl) n

theorem history_related (s t : List α) (h : Repr s t) (a : Stream α) (n : Nat) :
    Repr (state (forward s) a n) (state (backward t) a n) :=
  (Feedback.transport (forward s) (backward t) Eq Repr Eq h (base_step s t)
    a a (fun _ => rfl)).1 n

theorem cursor_lookup (s t : List α) (h : Repr s t) (i : Cursor s) (j : Cursor t)
    (initial : CursorRel s t h i j) (a : Stream α) (n : Nat) :
    (state (forward s) a n)[(forwardCursor s i a n).val] =
      (state (backward t) a n)[(backwardCursor t j a n).val] := by
  obtain ⟨hr,hc⟩ := cursors_related s t h i j initial a n
  exact lookup _ _ hr _ _ hc

theorem cast_lookup {s t : List α} (h : s = t) (i : Cursor s) :
    t[(Dependent.castWitness h i).val] = s[i.val] := by
  cases h; rfl

/-- The selected payload is retained at every prefix, not only compared between stores. -/
theorem selected_value (s : List α) (i : Cursor s) (a : Stream α) (n : Nat) :
    (state (forward s) a n)[(forwardCursor s i a n).val] = s[i.val] := by
  let fixed : Initialized α Unit Unit := ⟨fun _ => ((),()),()⟩
  have h := (Feedback.transport (Dependent.lift (forward s) Cursor keep i) fixed Eq
    (fun z _ => z.1[z.2.val] = s[i.val]) (fun _ _ => True) rfl
    (by
      intro x y z u _ hr
      refine ⟨True.intro,?_⟩
      change (z.1++[x])[z.2.val] = _
      rw [List.getElem_append_left z.2.isLt]
      exact hr)
    a a (fun _ => rfl)).1 n
  exact (cast_lookup (Dependent.projection (forward s) Cursor keep i a n) _).trans h

abbrev Parameters (α : Type) := Stream α × Nat

def forwardFamily (s : List α) : Parameters α → Type :=
  fun p => Cursor (state (forward s) p.1 p.2)
def backwardFamily (t : List α) : Parameters α → Type :=
  fun p => Cursor (state (backward t) p.1 p.2)
def forwardSection (s : List α) (i : Cursor s) : Tm (forwardFamily s) :=
  fun p => forwardCursor s i p.1 p.2
def backwardSection (t : List α) (j : Cursor t) : Tm (backwardFamily t) :=
  fun p => backwardCursor t j p.1 p.2

def sectionRel (s t : List α) (h : Repr s t) :
    TyRel (Eq : Parameters α → Parameters α → Prop) (forwardFamily s) (backwardFamily t) :=
  fun p q hp => by
    cases hp
    exact CursorRel _ _ (history_related s t h p.1 p.2)

theorem sections_related (s t : List α) (h : Repr s t) (i : Cursor s) (j : Cursor t)
    (initial : CursorRel s t h i j) :
    TermRelated Eq (sectionRel s t h) (forwardSection s i) (backwardSection t j) := by
  intro p q hp
  cases hp
  obtain ⟨hr,he⟩ := cursors_related s t h i j initial p.1 p.2
  exact he

/-- This changes an observation parameter, not the machine's operational clock. -/
def later : Parameters α → Parameters α := fun p => (p.1,p.2+1)

def mapUntil (s t : List α) (h : Repr s t) (a : Stream α) {n : Nat}
    (w : Temporal.Until (fun _ => PUnit) (fun n => forwardFamily s (a,n)) n) :
    Temporal.Until (fun _ => PUnit) (fun n => backwardFamily t (a,n)) n :=
  w.map (fun _ => id) (fun n => encode _ _ (history_related s t h a n))

theorem until_related (s t : List α) (h : Repr s t) (a : Stream α) {n : Nat}
    (w : Temporal.Until (fun _ => PUnit) (fun n => forwardFamily s (a,n)) n) :
    Temporal.Until.Rel (fun _ => Eq)
      (fun n => CursorRel _ _ (history_related s t h a n)) w (mapUntil s t h a w) := by
  have mapped := (Temporal.Until.Rel.refl w).map
    (A' := fun _ => PUnit) (B' := fun n => forwardFamily s (a,n))
    (C' := fun _ => PUnit) (D' := fun n => backwardFamily t (a,n))
    (fun _ => id) (fun _ => id) (fun _ => id)
    (fun n => encode _ _ (history_related s t h a n))
    (RA' := fun _ => Eq)
    (RB' := fun n => CursorRel _ _ (history_related s t h a n))
    (fun _ _ _ he => he)
    (by intro n x y he; cases he; exact encode_related _ _ _ x)
  rw [Temporal.Until.map_id w] at mapped
  exact mapped

end Progress.Feedback.Occurrence
