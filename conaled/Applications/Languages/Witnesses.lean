import Squares

/-!
# Proof-relevant language semantics

Here a language returns a type of parses, rather than a proposition or a
Boolean. A semantic equivalence includes maps in both directions and proofs
that the maps are inverse. In particular the concatenation derivative keeps
the parse of an empty left operand; Boolean recognition subsequently forgets
this information. This module uses only Lean's kernel library and `Squares`.
-/

namespace LanguageWitnesses

universe u
variable {α : Type u}

abbrev Language (α : Type u) := List α → Type u

structure Iso (A B : Type u) where
  forward : A → B
  backward : B → A
  backward_forward : ∀ a, backward (forward a) = a
  forward_backward : ∀ b, forward (backward b) = b

def derivative (P : Language α) (a : α) : Language α := fun w => P (a :: w)

def derivativeWord (P : Language α) (u : List α) : Language α := fun v => P (u ++ v)

structure Concat (P Q : Language α) (w : List α) where
  leftWord : List α
  rightWord : List α
  joined : leftWord ++ rightWord = w
  leftParse : P leftWord
  rightParse : Q rightWord

variable {P Q : Language α} {a : α} {w : List α}

def nullableConcatIso (P Q : Language α) : Iso (Concat P Q []) (P [] × Q []) where
  forward := by
    intro c
    have hu : c.leftWord = [] := (List.append_eq_nil_iff.mp c.joined).1
    have hv : c.rightWord = [] := (List.append_eq_nil_iff.mp c.joined).2
    exact (hu ▸ c.leftParse, hv ▸ c.rightParse)
  backward := fun pq => ⟨[], [], rfl, pq.1, pq.2⟩
  backward_forward := by
    rintro ⟨u, v, h, p, q⟩
    obtain ⟨rfl, rfl⟩ := List.append_eq_nil_iff.mp h
    rfl
  forward_backward := by intro pq; cases pq; rfl

def splitConcat (c : Concat P Q (a :: w)) :
    (P [] × Q (a :: w)) ⊕ Concat (derivative P a) Q w := by
  rcases c with ⟨u, v, h, p, q⟩
  cases u with
  | nil =>
    have hv : v = a :: w := h
    subst v
    exact .inl (p, q)
  | cons b u =>
    have hb : b = a := (List.cons.inj h).1
    subst a
    exact .inr ⟨u, v, (List.cons.inj h).2, p, q⟩

def joinConcat : (P [] × Q (a :: w)) ⊕ Concat (derivative P a) Q w →
    Concat P Q (a :: w)
  | .inl pq => ⟨[], a :: w, rfl, pq.1, pq.2⟩
  | .inr c => ⟨a :: c.leftWord, c.rightWord,
      congrArg (List.cons a) c.joined, c.leftParse, c.rightParse⟩

theorem join_splitConcat (c : Concat P Q (a :: w)) : joinConcat (splitConcat c) = c := by
  rcases c with ⟨u, v, h, p, q⟩
  cases u with
  | nil =>
    have hv : v = a :: w := h
    subst v
    rfl
  | cons b u =>
    have hh : b = a ∧ u ++ v = w := List.cons.inj h
    rcases hh with ⟨rfl, rfl⟩
    simp [splitConcat, joinConcat]

theorem split_joinConcat (c : (P [] × Q (a :: w)) ⊕ Concat (derivative P a) Q w) :
    splitConcat (joinConcat c) = c := by
  cases c with
  | inl pq => cases pq; rfl
  | inr c =>
    rcases c with ⟨u, v, h, p, q⟩
    cases h
    simp [splitConcat, joinConcat]

/-- The derivative product rule as a bijection on actual parse witnesses. -/
def derivativeConcatIso (P Q : Language α) (a : α) (w : List α) :
    Iso (Concat P Q (a :: w)) ((P [] × Q (a :: w)) ⊕ Concat (derivative P a) Q w) where
  forward := splitConcat
  backward := joinConcat
  backward_forward := join_splitConcat
  forward_backward := split_joinConcat

abbrev ParsedWord (P : Language α) := Sigma P

def flattenParses (ps : List (ParsedWord P)) : List α := ps.flatMap Sigma.fst

/-- Kleene closure retains the entire list of constituent parses. -/
abbrev Star (P : Language α) (w : List α) :=
  {ps : List (ParsedWord P) // flattenParses ps = w}

def emptyParses : List (P []) → List (ParsedWord P)
  | [] => []
  | p :: ps => ⟨[], p⟩ :: emptyParses ps

theorem flatten_emptyParses (ps : List (P [])) : flattenParses (emptyParses ps) = [] := by
  induction ps with
  | nil => rfl
  | cons p ps ih => exact ih

def extractEmpty : (ps : List (ParsedWord P)) → flattenParses ps = [] → List (P [])
  | [], _ => []
  | ⟨u, p⟩ :: ps, h => by
    have hu : u = [] := (List.append_eq_nil_iff.mp h).1
    subst u
    exact p :: extractEmpty ps (List.append_eq_nil_iff.mp h).2

theorem empty_extract (ps : List (ParsedWord P)) (h : flattenParses ps = []) :
    emptyParses (extractEmpty ps h) = ps := by
  induction ps with
  | nil => rfl
  | cons up ps ih =>
    rcases up with ⟨u, p⟩
    have hu : u = [] ∧ flattenParses ps = [] := List.append_eq_nil_iff.mp h
    rcases hu with ⟨rfl, hp⟩
    simp [extractEmpty, emptyParses, ih hp]

theorem extract_empty (ps : List (P [])) :
    extractEmpty (emptyParses ps) (flatten_emptyParses ps) = ps := by
  induction ps with
  | nil => rfl
  | cons p ps ih => simp [emptyParses, extractEmpty, ih]

/-- Nullable star is a list of nullable parses, not a single truth value. -/
def nullableStarIso (P : Language α) : Iso (Star P []) (List (P [])) where
  forward := fun s => extractEmpty s.1 s.2
  backward := fun ps => ⟨emptyParses ps, flatten_emptyParses ps⟩
  backward_forward := by intro s; apply Subtype.ext; exact empty_extract s.1 s.2
  forward_backward := extract_empty

theorem flattenParses_append (ps qs : List (ParsedWord P)) :
    flattenParses (ps ++ qs) = flattenParses ps ++ flattenParses qs :=
  List.flatMap_append

/-- Find the first constituent parse which consumes a character. -/
def splitStar : (ps : List (ParsedWord P)) → flattenParses ps = a :: w →
    List (P []) × Concat (derivative P a) (Star P) w
  | [], h => by cases h
  | ⟨[], p⟩ :: ps, h =>
    let rest := splitStar ps h
    (p :: rest.1, rest.2)
  | ⟨b :: u, p⟩ :: ps, h => by
    have hb : b = a := (List.cons.inj h).1
    subst a
    exact ([], ⟨u, flattenParses ps, (List.cons.inj h).2, p, ⟨ps, rfl⟩⟩)

def joinStar (x : List (P []) × Concat (derivative P a) (Star P) w) : Star P (a :: w) :=
  ⟨emptyParses x.1 ++ ⟨a :: x.2.leftWord, x.2.leftParse⟩ :: x.2.rightParse.1, by
    rw [flattenParses_append, flatten_emptyParses, List.nil_append]
    change a :: (x.2.leftWord ++ flattenParses x.2.rightParse.1) = a :: w
    rw [x.2.rightParse.2, x.2.joined]⟩

theorem join_splitStar (ps : List (ParsedWord P)) (h : flattenParses ps = a :: w) :
    joinStar (splitStar ps h) = ⟨ps, h⟩ := by
  induction ps with
  | nil => cases h
  | cons up ps ih =>
    rcases up with ⟨u, p⟩
    cases u with
    | nil =>
      apply Subtype.ext
      change ⟨[], p⟩ :: (joinStar (splitStar ps h)).1 = ⟨[], p⟩ :: ps
      rw [congrArg Subtype.val (ih h)]
    | cons b u =>
      have hh : b = a ∧ u ++ flattenParses ps = w := List.cons.inj h
      rcases hh with ⟨rfl, rfl⟩
      rfl

theorem split_joinStar (x : List (P []) × Concat (derivative P a) (Star P) w) :
    splitStar (joinStar x).1 (joinStar x).2 = x := by
  rcases x with ⟨eps, u, v, h, p, ps, hv⟩
  subst v
  cases h
  induction eps with
  | nil => rfl
  | cons e eps ih =>
    change (e :: (splitStar (joinStar (eps,
      ⟨u, flattenParses ps, rfl, p, ⟨ps, rfl⟩⟩)).1
      (joinStar (eps, ⟨u, flattenParses ps, rfl, p, ⟨ps, rfl⟩⟩)).2).1,
      (splitStar (joinStar (eps, ⟨u, flattenParses ps, rfl, p, ⟨ps, rfl⟩⟩)).1
      (joinStar (eps, ⟨u, flattenParses ps, rfl, p, ⟨ps, rfl⟩⟩)).2).2) = _
    rw [ih]

/--
The proof-relevant star derivative includes an arbitrary list of nullable
parses before the first consuming parse. Omitting this factor loses witnesses.
-/
def derivativeStarIso (P : Language α) (a : α) (w : List α) :
    Iso (Star P (a :: w)) (List (P []) × Concat (derivative P a) (Star P) w) where
  forward := fun s => splitStar s.1 s.2
  backward := joinStar
  backward_forward := fun s => join_splitStar s.1 s.2
  forward_backward := split_joinStar

end LanguageWitnesses
