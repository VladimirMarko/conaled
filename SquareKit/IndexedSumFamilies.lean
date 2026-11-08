import SquareKit.IndexedSumChoices

/-! Independently specified indexed sums and their slice realization. -/
noncomputable section
namespace SquareKit.IndexedSumFamilies
open CategoryTheory Limits ConcreteCategory
open IndexedSumBaseChange
universe u
variable {Γ Δ Ε : Type u} (I : Γ → Type u) (P : (γ : Γ) → I γ → Type u)

/-- The selected existential includes both the index and its fiber value. -/
abbrev Selected (γ : Γ) := (i : I γ) × P γ i

/-- Existential truth forgets precisely the selection. -/
abbrev Truth (γ : Γ) : Prop := Nonempty (Selected I P γ)

abbrev indexMap : (Sigma I) ⟶ Γ := ↾Sigma.fst
abbrev family : Over (Sigma I) := Over.mk (↾fun x : (a : Sigma I) × P a.1 a.2 => x.1)

variable (σ : Δ ⟶ Γ)
abbrev square := IsPullback.of_hasPullback (indexMap I) σ
abbrev index₁ := pullback (indexMap I) σ
abbrev family₁ := (Over.pullback (pullback.fst (indexMap I) σ)).obj (family I P)

/-- Independent family data, encoded at the substituted index. -/
def chosenIndex (δ : Δ) (s : Selected I P (σ δ)) : index₁ I σ :=
  encode σ (Over.mk (indexMap I)) δ ⟨⟨σ δ, s.1⟩, rfl⟩

def chosenValue (δ : Δ) (s : Selected I P (σ δ)) :
    Fiber (pullback.fst (indexMap I) σ) (family I P) (chosenIndex I P σ δ s) :=
  ⟨⟨⟨σ δ, s.1⟩, s.2⟩, (encode_value σ (Over.mk (indexMap I)) δ ⟨⟨σ δ, s.1⟩, rfl⟩).symm⟩

def first (δ : Δ) (s : Selected I P (σ δ)) :=
  transport (square I σ) (family I P) (chosenIndex I P σ δ s) (chosenValue I P σ δ s)

/-- The categorical sum comparison retains the entire native dependent pair. -/
theorem first_value (δ : Δ) (s : Selected I P (σ δ)) :
    pullback.fst ((family I P).hom ≫ indexMap I) σ (first I P σ δ s) =
      ⟨⟨σ δ, s.1⟩, s.2⟩ :=
  transport_value (square I σ) (family I P) (chosenIndex I P σ δ s) (chosenValue I P σ δ s)

theorem first_base (δ : Δ) (s : Selected I P (σ δ)) :
    pullback.snd ((family I P).hom ≫ indexMap I) σ (first I P σ δ s) = δ := by
  rw [first, transport_base]
  exact encode_base σ (Over.mk (indexMap I)) δ _

/-- Change both sum adjoints to the tagged realization before base change. -/
def taggedFirst (δ : Δ) (s : Selected I P (σ δ)) :=
  ((((Over.mapPullbackAdj (pullback.snd (indexMap I) σ)).leftAdjointUniq
      (taggedAdjunction (pullback.snd (indexMap I) σ))).hom.app (family₁ I P σ)) ≫
    (withSumChoices (square I σ) (taggedAdjunction (indexMap I))
      (taggedAdjunction (pullback.snd (indexMap I) σ))).hom.app (family I P)).left
    (encode _ _ (chosenIndex I P σ δ s) (chosenValue I P σ δ s))

/-- Canonical comparison retains the same index and fiber under both choices. -/
theorem taggedFirst_value (δ : Δ) (s : Selected I P (σ δ)) :
    pullback.fst ((taggedSum (indexMap I)).obj (family I P)).hom σ
      (taggedFirst I P σ δ s) = (PUnit.unit, ⟨⟨σ δ, s.1⟩, s.2⟩) := by
  unfold taggedFirst
  rw [choices_agree]
  change pullback.fst ((taggedSum (indexMap I)).obj (family I P)).hom σ
    (((Over.pullback σ).map (((Over.mapPullbackAdj (indexMap I)).leftAdjointUniq
      (taggedAdjunction (indexMap I))).hom.app (family I P))).left
      (first I P σ δ s)) = _
  erw [reindex_value σ (((Over.mapPullbackAdj (indexMap I)).leftAdjointUniq
      (taggedAdjunction (indexMap I))).hom.app (family I P)) (first I P σ δ s)]
  erw [first_value I P σ δ s, selected_tagging]

variable (τ : Ε ⟶ Δ)
abbrev square₂ := IsPullback.of_hasPullback (pullback.snd (indexMap I) σ) τ

/-- The input to the second sum comparison is the first reindexed fiber. -/
def inner (ε : Ε) (s : Selected I P (σ (τ ε))) : (family₁ I P σ).left :=
  encode _ _ (chosenIndex I P σ (τ ε) s) (chosenValue I P σ (τ ε) s)

def secondIndex (ε : Ε) (s : Selected I P (σ (τ ε))) :=
  encode τ (Over.mk (pullback.snd (indexMap I) σ)) ε
    ⟨chosenIndex I P σ (τ ε) s, encode_base σ (Over.mk (indexMap I)) (τ ε) _⟩

def secondValue (ε : Ε) (s : Selected I P (σ (τ ε))) :
    Fiber (pullback.fst (pullback.snd (indexMap I) σ) τ)
      (family₁ I P σ) (secondIndex I P σ τ ε s) :=
  ⟨inner I P σ τ ε s, by
    change pullback.snd (family I P).hom (pullback.fst (indexMap I) σ) (inner I P σ τ ε s) = _
    unfold inner secondIndex
    exact (encode_base _ _ _ _).trans
      (encode_value τ (Over.mk (pullback.snd (indexMap I) σ)) ε
        ⟨chosenIndex I P σ (τ ε) s, encode_base σ (Over.mk (indexMap I)) (τ ε) _⟩).symm⟩

/-- Apply both canonical sum comparisons, reindexing the first along τ. -/
def twice (ε : Ε) (s : Selected I P (σ (τ ε))) :=
  ((Over.pullback τ).map ((DependentBaseChange.leftComparison (square I σ)).hom.app
    (family I P))).left
      (transport (square₂ I σ τ) (family₁ I P σ)
        (secondIndex I P σ τ ε s) (secondValue I P σ τ ε s))

theorem twice_value (ε : Ε) (s : Selected I P (σ (τ ε))) :
    pullback.fst ((family I P).hom ≫ indexMap I) σ
      (pullback.fst (pullback.snd ((family I P).hom ≫ indexMap I) σ) τ
        (twice I P σ τ ε s)) = ⟨⟨σ (τ ε), s.1⟩, s.2⟩ := by
  unfold twice
  erw [reindex_value τ ((DependentBaseChange.leftComparison (square I σ)).hom.app
      (family I P)) (transport (square₂ I σ τ) (family₁ I P σ)
        (secondIndex I P σ τ ε s) (secondValue I P σ τ ε s))]
  erw [transport_value (square₂ I σ τ) (family₁ I P σ)
    (secondIndex I P σ τ ε s) (secondValue I P σ τ ε s)]
  exact first_value I P σ (τ ε) s

/-- Two substitutions also retain the selected new context. -/
theorem twice_base (ε : Ε) (s : Selected I P (σ (τ ε))) :
    pullback.snd (pullback.snd ((family I P).hom ≫ indexMap I) σ) τ
      (twice I P σ τ ε s) = ε := by
  unfold twice
  erw [reindex_base τ ((DependentBaseChange.leftComparison (square I σ)).hom.app
      (family I P)) (transport (square₂ I σ τ) (family₁ I P σ)
        (secondIndex I P σ τ ε s) (secondValue I P σ τ ε s))]
  erw [transport_base (square₂ I σ τ) (family₁ I P σ)
    (secondIndex I P σ τ ε s) (secondValue I P σ τ ε s)]
  exact encode_base τ (Over.mk (pullback.snd (indexMap I) σ)) ε _
end SquareKit.IndexedSumFamilies
