import SquareKit.Internal.Cubical.CartesianCofibrations
import Examples.CartesianSmallFamilyClassification
import SquareKit.Internal.Cubical.CartesianUniverse

/-! Empty cubes, variable-free patterns, proper diagonals and interval quantification. -/
set_option autoImplicit false
set_option warningAsError true
namespace Examples.CartesianCofibrations
open CategoryTheory SquareKit.Cubical.Cartesian
universe u

/-- In dimension zero there are exactly the empty and total sieves. -/
theorem zero_sieve (S : Sieve (⟨0⟩ : Cube)) : S = ⊥ ∨ S = ⊤ := by
  classical
  by_cases h : S (𝟙 (⟨0⟩ : Cube))
  · right
    apply Sieve.ext
    intro J f
    constructor
    · intro _; trivial
    · intro _
      simpa using S.downward_closed h f
  · left
    apply Sieve.ext
    intro J f
    constructor
    · intro hf
      let s : (⟨0⟩ : Cube) ⟶ J := fun _ => .endpoint false
      have hs := S.downward_closed hf s
      have he : s ≫ f = 𝟙 (⟨0⟩ : Cube) := by funext j; exact Fin.elim0 j
      exact h (he ▸ hs)
    · exact False.elim

/-- The split projection theorem also applies when its target has no coordinates. -/
theorem split_zero_target {J : Cube} (f : J ⟶ (⟨0⟩ : Cube)) :
    ∃ s : (⟨0⟩ : Cube) ⟶ J, s ≫ f = 𝟙 (⟨0⟩ : Cube) := by
  obtain ⟨k, hk, _p, i, s, _hsp, _hpi, hsi⟩ := Cube.split_variable_factorization f
  have hk0 : k = 0 := Nat.eq_zero_of_le_zero hk
  subst k
  have hi : i = 𝟙 (⟨0⟩ : Cube) := by funext j; exact Fin.elim0 j
  exact ⟨s, hsi.trans hi⟩

/-- The finite formula theorem includes the empty cube without an inhabited-variable premise. -/
theorem zero_formula (S : Sieve (⟨0⟩ : Cube)) {J : Cube} (f : J ⟶ ⟨0⟩) :
    ((Face.ofSieve S).subst f).Holds ↔ S f := Face.ofSieve_holds S f

/-- A pattern with no variables fixes every output coordinate, at every source dimension. -/
theorem vertex_pattern {J K : Cube} (v : (⟨0⟩ : Cube) ⟶ J) (f : K ⟶ J) :
    ((Face.pattern v).subst f).Holds ↔
      f = (fun i => (v i).subst (fun j => Fin.elim0 j)) := by
  rw [Face.pattern_holds]
  constructor
  · rintro ⟨g, rfl⟩
    have hg : g = (fun j => Fin.elim0 j) := by funext j; exact Fin.elim0 j
    rw [hg]
    rfl
  · intro h
    refine ⟨(fun j => Fin.elim0 j), ?_⟩
    exact h.symm

def duplicate : (⟨1⟩ : Cube) ⟶ ⟨2⟩ := fun _ => .var 0

/-- Repetition imposes a genuine diagonal, rather than an endpoint-only condition. -/
theorem duplicate_pattern {K : Cube} (f : K ⟶ ⟨2⟩) :
    ((Face.pattern duplicate).subst f).Holds ↔ f 0 = f 1 := by
  rw [Face.pattern_holds]
  constructor
  · rintro ⟨g, rfl⟩; rfl
  · intro h
    refine ⟨(fun _ => f 0), ?_⟩
    funext i
    refine Fin.cases rfl (fun j => ?_) i
    refine Fin.cases h (fun k => Fin.elim0 k) j

theorem duplicate_generic_proper :
    ¬ ((Face.pattern duplicate).subst (𝟙 (⟨2⟩ : Cube))).Holds := by
  rw [duplicate_pattern]
  intro h
  exact Fin.zero_ne_one (Dim.var.inj h)

theorem duplicate_substitution : ((Face.pattern duplicate).subst duplicate).Holds :=
  (duplicate_pattern duplicate).mpr rfl

def boundary (Γ : Context.{u}) : Subcontext (total (interval Γ)) :=
  (Subcontext.intervalFace Γ false).join (Subcontext.intervalFace Γ true)

theorem boundary_endpoint (Γ : Context.{u}) (x : Γ.Elements) (b : Bool) :
    (boundary Γ).holds (extendObj (interval Γ) x ⟨Cube.endpoint x.obj.unop b⟩) := by
  cases b
  · exact Or.inl rfl
  · exact Or.inr rfl

/-- Covering every endpoint does not cover the generic interval. -/
theorem boundary_forall (Γ : Context.{u}) : (boundary Γ).forallInterval = Subcontext.bot := by
  apply Subcontext.ext
  intro x
  constructor
  · intro h
    change (Dim.var (0 : Fin (x.obj.unop.dimension + 1)) = .endpoint false ∨
      Dim.var (0 : Fin (x.obj.unop.dimension + 1)) = .endpoint true) at h
    rcases h with h | h <;> cases h
  · exact False.elim

theorem boundary_quantified_all_refinements (Γ : Context.{u}) (x : Γ.Elements) :
    ¬ (∀ {y : Γ.Elements} (_f : x ⟶ y) (r : (interval Γ).obj y),
      (boundary Γ).holds (extendObj (interval Γ) y r)) := by
  intro h
  have hh := (Subcontext.forallInterval_iff (boundary Γ) x).mpr h
  rw [boundary_forall] at hh
  exact hh

/-- Raw formulas differ even when their extensional cofibrations are equal. -/
theorem raw_formula_distinction (n : ℕ) :
    (Face.top : Face n) ≠ .meet .top .top ∧
      (Face.top : Face n).cofibration = (Face.meet .top .top : Face n).cofibration := by
  constructor
  · intro h; cases h
  · apply Cofibration.ext
    intro x
    change True ↔ True ∧ True
    simp

/-- Conversion does not expose a selected presentation in the filling boundary. -/
theorem cofibration_roundtrip {Γ : Context.{u}} (φ : Cofibration Γ) :
    φ.toSubcontext.toCofibration = φ := (cofibrationEquiv Γ).left_inv φ

end Examples.CartesianCofibrations

namespace Examples.CartesianCofibrations
open CategoryTheory SquareKit.Cubical.Cartesian
abbrev smallSquare : Context := representable ⟨2⟩
abbrev universeSquare := raisedContext smallSquare

def smallCoordinate (i : Fin 2) : Term (interval smallSquare) where
  val x := ⟨fun _ => x.val.down i⟩
  property f := by
    apply ULift.ext
    funext j
    exact congrArg (fun z => z.down i) f.map_val

def universeCoordinate (i : Fin 2) : Term (interval universeSquare) :=
  UniversalTransport.raiseInterval (smallCoordinate i)

noncomputable def universeCap : Term (SmallUniverse.family universeSquare) :=
  SmallUniverse.term (Examples.CartesianSmallFamilyClassification.finThree smallSquare).code

def universeDiagonalPoint : universeSquare.Elements :=
  universeSquare.elementsMk (.op ⟨1⟩) ⟨⟨fun _ => .var 0⟩⟩

noncomputable def universeDiagonalBox : OpenBox
    (reindex (SmallUniverse.family universeSquare) (projection (interval universeSquare)))
    Subcontext.bot (universeCoordinate 0) where
  tube := ⟨fun _ h => h.elim, fun _ h => h.elim⟩
  base := universeCap
  boundary _ h := h.elim

theorem universe_coordinates_distinct : universeCoordinate 0 ≠ universeCoordinate 1 := by
  intro h
  have hv := congrArg (fun r => (r.val
    (universeSquare.elementsMk (.op ⟨2⟩) ⟨⟨𝟙 _⟩⟩)).down 0) h
  change Dim.var (0 : Fin 2) = Dim.var 1 at hv
  cases hv

/-- The constructed universe operation recovers its exact code on a proper diagonal. -/
theorem universe_proper_diagonal :
    HEq (((SmallUniverse.filling universeSquare).comp
      (projection (interval universeSquare)) Subcontext.bot (universeCoordinate 0)
      (universeCoordinate 1) universeDiagonalBox).val universeDiagonalPoint)
      (universeCap.val universeDiagonalPoint) :=
  Filling.comp_diagonal (SmallUniverse.filling_lawful universeSquare)
    _ _ _ _ universeDiagonalBox universeDiagonalPoint rfl
end Examples.CartesianCofibrations
