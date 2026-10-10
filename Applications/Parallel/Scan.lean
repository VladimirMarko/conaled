import Applications.Parallel.Shape
import Mathlib.Algebra.Group.Basic

/-!
# Generic exclusive scan and its two composition rules

The specification is the ordinary left-to-right accumulator traversal.
The implementation scans substructures independently and adjusts their
prefixes afterwards.  Every theorem is polymorphic over a monoid, without
commutativity, so the laws also cover ordered strings and endomorphisms.
-/

namespace Applications.Parallel

universe u

variable {M : Type u} [Monoid M]

/-- Independent sequential specification: exclusive prefixes and final total. -/
def sequential (seed : M) : List M → List M × M
  | [] => ([], seed)
  | a :: as =>
    let rest := sequential (seed * a) as
    (seed :: rest.1, rest.2)

@[simp] theorem sequential_nil (seed : M) : sequential seed [] = ([], seed) := rfl

@[simp] theorem sequential_cons (seed a : M) (as : List M) :
    sequential seed (a :: as) =
      (seed :: (sequential (seed * a) as).1, (sequential (seed * a) as).2) := rfl

theorem sequential_shift (seed initial : M) (as : List M) :
    sequential (seed * initial) as =
      ((sequential initial as).1.map (seed * ·), seed * (sequential initial as).2) := by
  induction as generalizing initial with
  | nil => rfl
  | cons a as ih =>
    simp only [sequential_cons, mul_assoc, ih, List.map_cons]

theorem sequential_seed (seed : M) (as : List M) :
    sequential seed as =
      ((sequential 1 as).1.map (seed * ·), seed * (sequential 1 as).2) := by
  simpa using sequential_shift seed 1 as

theorem sequential_append (seed : M) (as bs : List M) :
    sequential seed (as ++ bs) =
      ((sequential seed as).1 ++ (sequential (sequential seed as).2 bs).1,
       (sequential (sequential seed as).2 bs).2) := by
  induction as generalizing seed with
  | nil => rfl
  | cons a as ih => simp only [List.cons_append, sequential_cons, ih, List.cons_append]

theorem sequential_product (as bs : List M) :
    sequential 1 (as ++ bs) =
      ((sequential 1 as).1 ++ (sequential 1 bs).1.map ((sequential 1 as).2 * ·),
       (sequential 1 as).2 * (sequential 1 bs).2) := by
  rw [sequential_append, sequential_seed (sequential 1 as).2]

@[simp] theorem sequential_length (seed : M) (as : List M) :
    (sequential seed as).1.length = as.length := by
  induction as generalizing seed with
  | nil => rfl
  | cons a as ih => simp [ih]

theorem sequential_total (seed : M) (as : List M) :
    (sequential seed as).2 = as.foldl (· * ·) seed := by
  induction as generalizing seed with
  | nil => rfl
  | cons a as ih => exact ih (seed * a)

namespace Shape

/-- Product scan: the two recursive scans are independent. -/
def scan (s : Shape) : s.Data M → s.Data M × M :=
  match s with
  | .empty => fun _ => (PUnit.unit, 1)
  | .leaf => fun a => (1, a)
  | .prod s t => fun x =>
      let l := s.scan x.1
      let r := t.scan x.2
      ((l.1, t.map (l.2 * ·) r.1), l.2 * r.2)

theorem scan_correct (s : Shape) (x : s.Data M) :
    (s.flatten (s.scan x).1, (s.scan x).2) = sequential 1 (s.flatten x) := by
  induction s with
  | empty => rfl
  | leaf => simp [scan, flatten, sequential]
  | prod s t ihs iht =>
    have hl := ihs x.1
    have hr := iht x.2
    have hl₁ := congrArg Prod.fst hl
    have hl₂ := congrArg Prod.snd hl
    have hr₁ := congrArg Prod.fst hr
    have hr₂ := congrArg Prod.snd hr
    simp only at hl₁ hl₂ hr₁ hr₂
    simp only [scan, flatten, flatten_map, hl₁, hl₂, hr₁, hr₂]
    exact (sequential_product _ _).symm

def scanSquare (s : Shape) (M : Type u) [Monoid M] :
    Squares.Square (s.rep M)
      (Squares.product (s.rep M) ⟨M, M, id⟩) where
  impl := s.scan
  spec := sequential 1
  commutes := s.scan_correct

/--
Functor composition: scan all chunks, scan their totals, then adjust each
chunk by its corresponding exclusive total prefix.  Both levels are real
algorithms; the sequential specification does not occur in this definition.
-/
def scanNestedWith (outer inner : Shape)
    (outerRun : outer.Data M → outer.Data M × M)
    (innerRun : inner.Data M → inner.Data M × M)
    (x : outer.Data (inner.Data M)) : outer.Data (inner.Data M) × M :=
  let locals := outer.map innerRun x
  let totals := outerRun (outer.map Prod.snd locals)
  let adjusted := outer.zipWith
    (fun total prefixes => inner.map (total * ·) prefixes)
    totals.1 (outer.map Prod.fst locals)
  (adjusted, totals.2)

def scanNested (outer inner : Shape) :
    outer.Data (inner.Data M) → outer.Data (inner.Data M) × M :=
  outer.scanNestedWith inner outer.scan inner.scan

end Shape

private theorem map_mul_map (a b : M) (xs : List M) :
    (xs.map (b * ·)).map (a * ·) = xs.map ((a * b) * ·) := by
  simp only [List.map_map]
  congr 1
  funext x
  exact (mul_assoc a b x).symm

private theorem zipWith_map_mul (a : M) (totals : List M) (chunks : List (List M)) :
    List.zipWith (fun t xs => xs.map (t * ·))
      (totals.map (a * ·)) chunks =
      (List.zipWith (fun t xs => xs.map (t * ·)) totals chunks).map
        (fun xs => xs.map (a * ·)) := by
  induction totals generalizing chunks with
  | nil => simp
  | cons t ts ih =>
    cases chunks with
    | nil => simp
    | cons xs xss => simp [ih, map_mul_map]

/-- The list-level calculation for composition, independent of any shape. -/
theorem sequential_chunks (chunks : List (List M)) :
    let locals := chunks.map (sequential 1)
    let totals := sequential 1 (locals.map Prod.snd)
    ((List.zipWith (fun t xs => xs.map (t * ·)) totals.1
      (locals.map Prod.fst)).flatten, totals.2) =
      sequential 1 chunks.flatten := by
  induction chunks with
  | nil => simp [sequential]
  | cons xs xss ih =>
    simp only [List.map_cons, List.map_map, sequential_cons, one_mul] at *
    rw [sequential_seed (sequential 1 xs).2]
    simp only [List.zipWith_cons_cons, List.flatten_cons, List.map_id_fun]
    rw [zipWith_map_mul]
    simp only [← List.map_flatten]
    have h₁ := congrArg Prod.fst ih
    have h₂ := congrArg Prod.snd ih
    simp only at h₁ h₂
    rw [h₁, h₂]
    simpa using (sequential_product xs xss.flatten).symm

namespace Shape

theorem scanNestedWith_correct (outer inner : Shape)
    (outerRun : outer.Data M → outer.Data M × M)
    (innerRun : inner.Data M → inner.Data M × M)
    (outerLaw : ∀ y, (outer.flatten (outerRun y).1, (outerRun y).2) =
      sequential 1 (outer.flatten y))
    (innerLaw : ∀ y, (inner.flatten (innerRun y).1, (innerRun y).2) =
      sequential 1 (inner.flatten y))
    (x : outer.Data (inner.Data M)) :
    ((outer.flatten (outer.scanNestedWith inner outerRun innerRun x).1).flatMap inner.flatten,
      (outer.scanNestedWith inner outerRun innerRun x).2) =
      sequential 1 ((outer.flatten x).flatMap inner.flatten) := by
  let chunks := (outer.flatten x).map inner.flatten
  let locals := outer.map innerRun x
  have ht := outerLaw (outer.map Prod.snd locals)
  have ht₁ := congrArg Prod.fst ht
  have ht₂ := congrArg Prod.snd ht
  have hl₁ : (outer.flatten locals).map (fun p => inner.flatten p.1) =
      (chunks.map (sequential 1)).map Prod.fst := by
    simp only [locals, chunks, flatten_map, List.map_map]
    apply List.map_congr_left
    intro a _
    exact congrArg Prod.fst (innerLaw a)
  have hl₂ : (outer.flatten locals).map Prod.snd =
      (chunks.map (sequential 1)).map Prod.snd := by
    simp only [locals, chunks, flatten_map, List.map_map]
    apply List.map_congr_left
    intro a _
    exact congrArg Prod.snd (innerLaw a)
  simp only [flatten_map] at ht₁ ht₂
  rw [hl₂] at ht₁ ht₂
  change
    ((outer.flatten (outer.zipWith
      (fun total prefixes => inner.map (total * ·) prefixes)
      (outerRun (outer.map Prod.snd locals)).1 (outer.map Prod.fst locals))).flatMap
       inner.flatten, (outerRun (outer.map Prod.snd locals)).2) = _
  rw [flatten_zipWith, ht₁, ht₂]
  have h := sequential_chunks chunks
  dsimp only at h
  rw [← hl₁] at h
  simpa only [chunks, List.flatMap, List.map_zipWith, flatten_map, List.zipWith_map_right,
    List.map_map] using h


theorem scanNested_correct (outer inner : Shape)
    (x : outer.Data (inner.Data M)) :
    ((outer.flatten (outer.scanNested inner x).1).flatMap inner.flatten,
      (outer.scanNested inner x).2) =
      sequential 1 ((outer.flatten x).flatMap inner.flatten) :=
  outer.scanNestedWith_correct inner outer.scan inner.scan
    outer.scan_correct inner.scan_correct x

def nestedScanSquare (outer inner : Shape) (M : Type u) [Monoid M] :
    Squares.Square (nestedRep outer inner M)
      (Squares.product (nestedRep outer inner M) ⟨M, M, id⟩) where
  impl := outer.scanNested inner
  spec := sequential 1
  commutes := outer.scanNested_correct inner

/-- Prefix powers, the paper's first scan application. -/
def powers (s : Shape) (a : M) : s.Data M × M := s.scan (s.pure a)

theorem powers_correct (s : Shape) (a : M) :
    (s.flatten (s.powers a).1, (s.powers a).2) =
      sequential 1 (List.replicate s.size a) := by
  simpa [powers] using s.scan_correct (s.pure a)

end Shape
end Applications.Parallel
