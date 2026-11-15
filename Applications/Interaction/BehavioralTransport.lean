import Applications.Interaction.OverlappingCaller

/-! Boundary-preserving correctness maps for the finite response-policy family.
These maps act on a single shared interaction witness, including pending phases. -/
namespace Interaction.BehavioralTransport
open FiniteStrategies OverlappingStrategies

variable {A : Arena}
abbrev Boundary (A : Arena) := Fin A.slots → Bool → Bool

/-- Source replies are interpreted on both boundaries. The direction is from
implementation values to specification values; no inverse is assumed. -/
def Preserves (left right : Boundary A) (source target : Strategy A) : Prop :=
  ∀ i b, target.response i (right i b) = left i (source.response i b)

theorem preserves_comp {a b c d : Boundary A} {s t u : Strategy A}
    (h : Preserves a b s t) (k : Preserves c d t u) :
    Preserves (fun i => c i ∘ a i) (fun i => d i ∘ b i) s u := by
  intro i x
  simp only [Function.comp_apply, k i, h i]

def relayMove (a b : Bool → Bool) : RelayMove → RelayMove
  | .leftAsk => .leftAsk | .rightAsk => .rightAsk
  | .rightReply x => .rightReply (b x)
  | .leftReply x => .leftReply (a x)

def wireMove (a b c : Bool → Bool) : WireMove → WireMove
  | .aAsk => .aAsk | .bAsk => .bAsk | .cAsk => .cAsk
  | .aReply x => .aReply (a x) | .bReply x => .bReply (b x)
  | .cReply x => .cReply (c x)

def wireState (c : Bool → Bool) : Stage → Stage
  | .idle => .idle | .aAsked => .aAsked | .bAsked => .bAsked | .waiting => .waiting
  | .cAnswered x => .cAnswered (c x) | .bAnswered x => .bAnswered (c x)

def relayState (a : Bool → Bool) : Phase → Phase
  | .idle => .idle | .requested => .requested | .waiting => .waiting
  | .answered x => .answered (a x)

def mapEvents (f : Fin A.slots → M → N) (xs : List (Event A M)) : List (Event A N) :=
  xs.map fun (i,m) => (i, f i m)

def mapRelay (a b : Boundary A) := mapEvents (fun i => relayMove (a i) (b i))
def mapWire (a b c : Boundary A) := mapEvents (fun i => wireMove (a i) (b i) (c i))

theorem project_mapEvents (f : Fin A.slots → M → N) (i : Fin A.slots)
    (xs : List (Event A M)) : project i (mapEvents f xs) = (project i xs).map (f i) := by
  induction xs with
  | nil => rfl
  | cons x xs ih =>
    rcases x with ⟨j,m⟩
    simp only [mapEvents, List.map_cons, project_cons, List.map_append] at *
    by_cases h : j = i
    · subst j; simpa using ih
    · simp [h, ih]

/-- Every event keeps its correlation slot in the same global position. -/
theorem correlation (f : Fin A.slots → M → N) (xs : List (Event A M)) :
    (mapEvents f xs).map Prod.fst = xs.map Prod.fst := by simp [mapEvents, List.map_map]

theorem relay_local {a b f g : Bool → Bool} (law : ∀ x, g (b x) = a (f x))
    (h : relayStep f p m = some q) :
    relayStep g (relayState a p) (relayMove a b m) = some (relayState a q) := by
  cases p <;> cases m <;> cases q <;> simp_all [relayStep, relayState, relayMove]
  rename_i x y
  cases x <;> simp_all

theorem wire_local {a b c f g f' g' : Bool → Bool}
    (left : ∀ x, f' (b x) = a (f x)) (right : ∀ x, g' (c x) = b (g x))
    (h : wireStep f g p m = some q) :
    wireStep f' g' (wireState c p) (wireMove a b c m) = some (wireState c q) := by
  cases p <;> cases m <;> cases q <;> simp_all [wireStep, wireState, wireMove]
  · rename_i x y z
    cases z <;> simp_all
  · rename_i x y
    have hl : ∀ z, f' (b z) = a (f z) := by intro z; cases z <;> simp_all
    have hr : ∀ z, g' (c z) = b (g z) := by intro z; cases z <;> simp_all
    rw [hr, hl]

theorem relay_path {a b f g : Bool → Bool} (law : ∀ x, g (b x) = a (f x))
    (h : Path (relayStep f) p xs q) :
    Path (relayStep g) (relayState a p) (xs.map (relayMove a b)) (relayState a q) := by
  induction h with
  | nil => exact .nil
  | cons hs _ ih => exact .cons (relay_local law hs) ih

theorem wire_path {a b c f g f' g' : Bool → Bool}
    (left : ∀ x, f' (b x) = a (f x)) (right : ∀ x, g' (c x) = b (g x))
    (h : Path (wireStep f g) p xs q) :
    Path (wireStep f' g') (wireState c p) (xs.map (wireMove a b c)) (wireState c q) := by
  induction h with
  | nil => exact .nil
  | cons hs _ ih => exact .cons (wire_local left right hs) ih

theorem play_map {a b : Boundary A} {s s' : Strategy A}
    (law : Preserves a b s s') (h : s.Play xs) : s'.Play (mapRelay a b xs) := by
  intro i
  rw [mapRelay, project_mapEvents]
  obtain ⟨q,hq⟩ := h i
  exact ⟨_, relay_path (law i) hq⟩

/-- The external response equation agrees with the response of the interacting
components, using the same middle interpretation. -/
theorem preserves_interaction {a b c : Boundary A} {s t s' t' : Strategy A}
    (left : Preserves a b s s') (right : Preserves b c t t') :
    Preserves a c (s.comp t) (s'.comp t') := by
  intro i x
  change s'.response i (t'.response i (c i x)) = a i (s.response i (t.response i x))
  rw [right i, left i]

/-- Both component laws use exactly the same middle map b. -/
theorem interaction_map {a b c : Boundary A} {s t s' t' : Strategy A}
    (left : Preserves a b s s') (right : Preserves b c t t')
    (h : InteractionPlay s t wire) : InteractionPlay s' t' (mapWire a b c wire) := by
  intro i
  rw [mapWire, project_mapEvents]
  obtain ⟨q,hq⟩ := h i
  exact ⟨_, wire_path (left i) (right i) hq⟩

/-- The same translated wire projects to both translated component traces. -/
theorem left_projection (a b c : Boundary A) (wire : List (Event A WireMove)) :
    translate (fun _ => leftMoves) (mapWire a b c wire) =
      mapRelay a b (translate (fun _ => leftMoves) wire) := by
  induction wire with
  | nil => rfl
  | cons x xs ih =>
    rcases x with ⟨i,m⟩
    cases m <;> simp_all [mapWire, mapRelay, mapEvents, translate, wireMove, relayMove, leftMoves]

theorem right_projection (a b c : Boundary A) (wire : List (Event A WireMove)) :
    translate (fun _ => rightMoves) (mapWire a b c wire) =
      mapRelay b c (translate (fun _ => rightMoves) wire) := by
  induction wire with
  | nil => rfl
  | cons x xs ih =>
    rcases x with ⟨i,m⟩
    cases m <;> simp_all [mapWire, mapRelay, mapEvents, translate, wireMove, relayMove, rightMoves]

/-- Exact hiding law, retaining order and every pending external prefix. -/
theorem hide_map (a b c : Boundary A) (wire : List (Event A WireMove)) :
    hide (mapWire a b c wire) = mapRelay a c (hide wire) := by
  induction wire with
  | nil => rfl
  | cons x xs ih =>
    rcases x with ⟨i,m⟩
    cases m <;> simp_all [hide, mapWire, mapRelay, mapEvents, translate, wireMove, relayMove, hideMiddle]

/-- A concrete single witness proves computational composition respects both
correctness comparisons. Independent existential component lifts are unnecessary. -/
theorem interaction_compatible {a b c : Boundary A} {s t s' t' : Strategy A}
    (left : Preserves a b s s') (right : Preserves b c t t')
    (h : InteractionPlay s t wire) :
    ∃ lifted, InteractionPlay s' t' lifted ∧
      translate (fun _ => leftMoves) lifted = mapRelay a b (translate (fun _ => leftMoves) wire) ∧
      translate (fun _ => rightMoves) lifted = mapRelay b c (translate (fun _ => rightMoves) wire) ∧
      hide lifted = mapRelay a c (hide wire) :=
  ⟨mapWire a b c wire, interaction_map left right h, left_projection _ _ _ _,
    right_projection _ _ _ _, hide_map _ _ _ _⟩

theorem composite_map {a b c : Boundary A} {s t s' t' : Strategy A}
    (left : Preserves a b s s') (right : Preserves b c t t')
    (h : OverlappingStrategies.CompositePlay s t xs) :
    OverlappingStrategies.CompositePlay s' t' (mapRelay a c xs) := by
  obtain ⟨wire,hw,rfl⟩ := h
  exact ⟨mapWire a b c wire, interaction_map left right hw, hide_map _ _ _ _⟩

/-- Vertical composition is pointwise composition on each of the three boundaries. -/
theorem wire_map_comp (a b c d e f : Boundary A) (wire : List (Event A WireMove)) :
    mapWire d e f (mapWire a b c wire) =
      mapWire (fun i => d i ∘ a i) (fun i => e i ∘ b i) (fun i => f i ∘ c i) wire := by
  induction wire with
  | nil => rfl
  | cons x xs ih =>
    rcases x with ⟨i,m⟩
    cases m <;> simp_all [mapWire, mapEvents, wireMove, Function.comp_def]

/-- Two vertical stages use the same intermediate wire. This is an exact
observation law, not associativity of strategy composition. -/
theorem interchange (a b c d e f : Boundary A) (wire : List (Event A WireMove)) :
    hide (mapWire (fun i => d i ∘ a i) (fun i => e i ∘ b i) (fun i => f i ∘ c i) wire) =
      mapRelay d f (mapRelay a c (hide wire)) := by
  rw [← wire_map_comp, hide_map, hide_map]

end Interaction.BehavioralTransport
