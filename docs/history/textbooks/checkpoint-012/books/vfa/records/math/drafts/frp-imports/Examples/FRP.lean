import Applications.FRP.Finite
import Applications.FRP.Equivalence
import Squares

/-! Checked uses of the historical FRP specifications and the square interface. -/
noncomputable section

namespace Examples.FRP

/-- Here the represented carrier is a mathematical event, not a runtime. -/
def eventRep (A : Type) : Squares.Rep where
  R := FRP.OldEvent ℝ A
  S := FRP.Batch ℝ A
  decode := FRP.OldEvent.group

def mapSquare {A B : Type} (f : A → B) :
    Squares.Square (eventRep A) (eventRep B) where
  impl := FRP.OldEvent.map f
  spec := FRP.Batch.map f
  commutes := fun e => FRP.OldEvent.group_map e f

/-- Map preservation composes through the repository's existing square API. -/
theorem map_twice {A B C : Type} (f : A → B) (g : B → C)
    (e : FRP.OldEvent ℝ A) :
    (e.map f |>.map g).group = FRP.Batch.map g (FRP.Batch.map f e.group) :=
  (Squares.compose (mapSquare g) (mapSquare f)).commutes e

/-- At the change time itself, strict switching still returns the initial value. -/
theorem switch_at_change :
    FRPSpec.Event.switcher (fun _ => (3 : ℕ))
      (FRPSpec.Event.once 2 (fun _ => 7)) 2 = 3 := by
  have empty : FRPSpec.PastSupport
      (FRPSpec.Event.once 2 (fun _ : ℝ => (7 : ℕ))).at 2 = ∅ := by
    ext s
    by_cases h : s = 2
    · subst s
      simp [FRPSpec.PastSupport]
    · simp [FRPSpec.PastSupport, FRPSpec.Event.once, h]
  simp [FRPSpec.Event.switcher, FRPSpec.Event.past, empty]

/-- Simultaneous occurrences retain input order and multiplicity. -/
theorem ordered_batch :
    (FRPSpec.Event.merge (FRPSpec.Event.once 2 (3 : ℕ))
      (FRPSpec.Event.once 2 7)).at 2 = [3, 7] := by
  simp [FRPSpec.Event.merge, FRPSpec.Event.once]

/-- The finite-history equivalence is a decoding representation for shared squares. -/
def finiteRep (A : Type) : Squares.Rep where
  R := {e : FRP.OldEvent ℝ A // e.FiniteHistory}
  S := FRPSpec.Event A
  decode := FRP.Native.oldEquiv

def mergeSquare (A : Type) :
    Squares.Square (Squares.product (finiteRep A) (finiteRep A)) (finiteRep A) where
  impl p := FRP.Native.merge p.1 p.2
  spec p := FRPSpec.Event.merge p.1 p.2
  commutes p := FRP.Native.merge_preserves p.1 p.2

/-- Reuse square composition to observe a merged event's ordered batch. -/
def observeSquare (A : Type) (t : ℝ) :
    Squares.Square (finiteRep A) (⟨List A, List A, id⟩) where
  impl e := (FRP.Native.oldEquiv e).at t
  spec e := e.at t
  commutes _ := rfl

theorem merge_observe {A : Type}
    (l r : {e : FRP.OldEvent ℝ A // e.FiniteHistory}) (t : ℝ) :
    (FRP.Native.oldEquiv (FRP.Native.merge l r)).at t =
      (FRP.Native.oldEquiv l).at t ++ (FRP.Native.oldEquiv r).at t :=
  (Squares.compose (observeSquare A t) (mergeSquare A)).commutes (l, r)

/-- Empty and repeated finite batches survive the bridge without deduplication. -/
theorem finite_batch_roundtrip (xs : List ℕ) :
    FRP.CoList.toList (FRP.CoList.ofList xs)
      (FRP.CoList.ofList_finite xs) = xs := by
  apply FRP.CoList.ofList_injective
  exact FRP.CoList.ofList_toList _ _

/-- Three simultaneous inputs include a repeated value and a distinguishable tie. -/
theorem merged_native_roundtrip :
    (FRP.Native.oldEquiv
      (FRP.Native.merge
        (FRP.Native.oldEquiv.symm (FRPSpec.Event.merge
          (FRPSpec.Event.once 2 (3 : ℕ)) (FRPSpec.Event.once 2 3)))
        (FRP.Native.oldEquiv.symm (FRPSpec.Event.once 2 7)))).at 2 = [3, 3, 7] := by
  rw [merge_observe]
  simp [FRPSpec.Event.merge, FRPSpec.Event.once]

/-- An unbounded infinite future still has finite history at every real time. -/
def ticks : FRP.OldEvent ℝ ℕ where
  seq := FRP.CoList.ofStream (fun n => (n, n))
  ordered := by
    intro i j h
    change (i.val : ℝ) ≤ (j.val : ℝ)
    exact_mod_cast (show i.val ≤ j.val from h)

theorem ticks_finiteHistory : ticks.FiniteHistory := by
  intro t
  obtain ⟨n, hn⟩ := exists_nat_gt t
  apply ((Set.finite_Iio n).preimage Subtype.val_injective.injOn).subset
  intro i hi
  change i.val < n
  have hit : (i.val : ℝ) < t := hi
  exact_mod_cast lt_trans hit hn

/-- The bridge accepts this infinite future without bounding the whole event. -/
theorem ticks_roundtrip :
    (FRP.Native.oldEquiv.symm
      (FRP.Native.oldEquiv ⟨ticks, ticks_finiteHistory⟩)).val = ticks :=
  congrArg Subtype.val (FRP.Native.oldEquiv.symm_apply_apply ⟨ticks, ticks_finiteHistory⟩)

/-- FRP interpretations compose with the shared map into Mathlib's bundled arrows. -/
theorem composed_semantic_map {H : Type → Type → Type} {r : FRPSpec.Raw H}
    (D : FRPSpec.Homomorphism H r) :
    SquareKit.MapLaws (D.semanticMap.comp SquareKit.FunctionCategory.toTypes)
      D.semanticEquality (SquareKit.equality _) :=
  SquareKit.RawMap.comp_laws D.mapLaws SquareKit.FunctionCategory.toTypes_laws

/-- Product eta is inherited through the shared product comparison. -/
theorem semantic_pair_eta {H : Type → Type → Type} {r : FRPSpec.Raw H}
    (D : FRPSpec.Homomorphism H r) {A B C : Type} (f : H A (B × C)) :
    D.Eqv (r.pair (r.comp r.fst f) (r.comp r.snd f)) f := D.productLaws.pair_eta f

end Examples.FRP
