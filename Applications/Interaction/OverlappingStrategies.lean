import Applications.Interaction.FiniteStrategies

/-! A finite indexed family of Boolean arenas. Global order is observable; each
slot has its own sequential justification discipline. This is a restricted
nonalternating game, not a model of general asynchronous innocence. -/
namespace Interaction.OverlappingStrategies
open FiniteStrategies

/-- The interface specifies independently outstanding Boolean questions. -/
structure Arena where
  slots : Nat

variable {A : Arena}

abbrev Event (A : Arena) (M : Type) := Fin A.slots × M

/-- Projection keeps order and forgets events on other slots. -/
def project (i : Fin A.slots) (xs : List (Event A M)) : List M :=
  xs.flatMap fun (j, m) => if j = i then [m] else []

/-- A local move translation preserves the correlation slot. -/
def translate (f : Fin A.slots → M → List N) (xs : List (Event A M)) :
    List (Event A N) := xs.flatMap fun (i, m) => (f i m).map (i, ·)

@[simp] theorem project_nil (i : Fin A.slots) : project i ([] : List (Event A M)) = [] := rfl
@[simp] theorem project_cons (i j : Fin A.slots) (m : M) (xs : List (Event A M)) :
    project i ((j,m) :: xs) = (if j = i then [m] else []) ++ project i xs := by
  simp [project]
@[simp] theorem project_append (i : Fin A.slots) (xs ys : List (Event A M)) :
    project i (xs ++ ys) = project i xs ++ project i ys := by simp [project]

@[simp] theorem project_tag (i j : Fin A.slots) (xs : List M) :
    project i (xs.map (j, ·)) = if j = i then xs else [] := by
  induction xs with
  | nil => simp
  | cons x xs ih => simp [ih]; split <;> simp_all

/-- Slot projection commutes with any slot-local translation, including hiding. -/
theorem project_translate (i : Fin A.slots) (f : Fin A.slots → M → List N)
    (xs : List (Event A M)) :
    project i (translate f xs) = (project i xs).flatMap (f i) := by
  induction xs with
  | nil => rfl
  | cons x xs ih =>
    rcases x with ⟨j,m⟩
    simp only [translate, List.flatMap_cons, project_append, project_tag,
      project_cons, List.flatMap_append] at *
    by_cases h : j = i
    · subst j; simpa using ih
    · simpa [h] using ih

/-- Strategies in this family choose a Boolean response transformation per slot.
Legality and compositional laws below are derived, not supplied as fields. -/
structure Strategy (A : Arena) where
  response : Fin A.slots → Bool → Bool

variable {s t u : Strategy A}

def Strategy.Play (s : Strategy A) (xs : List (Event A RelayMove)) : Prop :=
  ∀ i, RelayPlay (s.response i) (project i xs)

def Strategy.identity (A : Arena) : Strategy A := ⟨fun _ => id⟩
def Strategy.comp (s t : Strategy A) : Strategy A :=
  ⟨fun i => s.response i ∘ t.response i⟩

theorem Strategy.empty (s : Strategy A) : s.Play [] := fun _ => relay_nonempty _
theorem Strategy.prefix (h : s.Play (xs ++ ys)) : s.Play xs := by
  intro i
  exact relay_prefix (by simpa using h i)

/-- A single shared internal B event occurs in both component projections. -/
def InteractionPlay (s t : Strategy A) (wire : List (Event A WireMove)) : Prop :=
  ∀ i, ∃ q, Path (wireStep (s.response i) (t.response i)) .idle (project i wire) q

def hide (wire : List (Event A WireMove)) : List (Event A RelayMove) :=
  translate (fun _ => hideMiddle) wire

theorem interaction_components (h : InteractionPlay s t wire) :
    s.Play (translate (fun _ => leftMoves) wire) ∧
    t.Play (translate (fun _ => rightMoves) wire) := by
  constructor
  · intro i
    rw [project_translate]
    obtain ⟨q,hq⟩ := h i
    exact (components hq).1
  · intro i
    rw [project_translate]
    obtain ⟨q,hq⟩ := h i
    exact (components hq).2

theorem interaction_hide (h : InteractionPlay s t wire) : (s.comp t).Play (hide wire) := by
  intro i
  rw [hide, project_translate]
  obtain ⟨q,hq⟩ := h i
  exact hide_legal (f := s.response i) (g := t.response i) hq

/-- Composition retains every finite external position of a legal interaction. -/
def CompositePlay (s t : Strategy A) (xs : List (Event A RelayMove)) : Prop :=
  ∃ wire, InteractionPlay s t wire ∧ hide wire = xs

private theorem translate_append (f : Fin A.slots → M → List N)
    (xs ys : List (Event A M)) : translate f (xs ++ ys) = translate f xs ++ translate f ys := by
  simp [translate]
private theorem translate_tag (f : Fin A.slots → M → List N) (i : Fin A.slots)
    (xs : List M) : translate f (xs.map (i, ·)) = (xs.flatMap (f i)).map (i, ·) := by
  induction xs with
  | nil => rfl
  | cons x xs ih => simp [translate] at *; exact ih

/-- The insertion witness preserves global external event order, not only each
slot's projection. -/
theorem hide_insert (t : Strategy A) (xs : List (Event A RelayMove)) :
    hide (translate (fun i => insertMiddle (t.response i)) xs) = xs := by
  induction xs with
  | nil => rfl
  | cons x xs ih =>
    rcases x with ⟨i,m⟩
    change translate _ ((insertMiddle (t.response i) m).map (i, ·) ++ _) = _
    rw [translate_append, translate_tag]
    have hm : (insertMiddle (t.response i) m).flatMap hideMiddle = [m] := by
      cases m <;> rfl
    rw [hm]
    change (i,m) :: hide (translate (fun i => insertMiddle (t.response i)) xs) = (i,m) :: xs
    rw [ih]

/-- Soundness and completeness hold for all finite interleavings and pending
prefixes. No global alternation or fairness premise is used. -/
theorem compose_exact : CompositePlay s t xs ↔ (s.comp t).Play xs := by
  constructor
  · rintro ⟨wire,h,rfl⟩; exact interaction_hide h
  · intro h
    refine ⟨translate (fun i => insertMiddle (t.response i)) xs, ?_, hide_insert t xs⟩
    intro i
    rw [project_translate]
    obtain ⟨q,hq⟩ := h i
    obtain ⟨r,hr,_⟩ := lift_path (f := s.response i) (g := t.response i) hq .idle
    exact ⟨r,hr⟩

theorem identity_left : CompositePlay (Strategy.identity A) s xs ↔ s.Play xs := compose_exact
theorem identity_right : CompositePlay s (Strategy.identity A) xs ↔ s.Play xs := compose_exact

theorem associative : CompositePlay (s.comp t) u xs ↔ CompositePlay s (t.comp u) xs :=
  (compose_exact (s := s.comp t) (t := u)).trans
    (compose_exact (s := s) (t := t.comp u)).symm

/-- With one slot, the construction recovers the previous serial language. -/
theorem serial_recovery (s : Strategy ⟨1⟩) (xs : List RelayMove) :
    s.Play (xs.map (⟨0,by decide⟩, ·)) ↔ RelayPlay (s.response ⟨0,by decide⟩) xs := by
  constructor
  · intro h; simpa only [project_tag (A := ⟨1⟩), ite_true] using h ⟨0,by decide⟩
  · intro h i
    have hi : i = ⟨0,by decide⟩ := Subsingleton.elim _ _
    subst i
    simpa only [project_tag (A := ⟨1⟩), ite_true] using h

end Interaction.OverlappingStrategies
