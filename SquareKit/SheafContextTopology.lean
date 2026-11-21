import SquareKit.SheafCover
import Mathlib.CategoryTheory.Sites.Coverage
import Mathlib.CategoryTheory.Sites.Over

/-! The locally surjective topology on sheaf contexts and its slice coverage. -/
noncomputable section
set_option autoImplicit false
set_option warningAsError true
namespace SquareKit.SheafCover
open CategoryTheory Opposite
universe u v
variable {C : Type u} [Category.{v} C] {J : GrothendieckTopology C}

/-- The topology on sheaf contexts in which a covering sieve contains a locally
surjective map. This is distinct from the original site topology `J`. -/
def topology : GrothendieckTopology (Sheaf J (Type (max u v))) where
  sieves X := {R | ∃ (Y : Sheaf J (Type (max u v))) (f : Y ⟶ X),
    Presheaf.IsLocallySurjective J f.hom ∧ R f}
  top_mem' X := ⟨X, 𝟙 X, inferInstance, by trivial⟩
  pullback_stable' {_ _ R} g := by
    rintro ⟨Y, f, hf, hR⟩
    obtain ⟨W, p, q, hp, eq⟩ := cover_pullback f g
    refine ⟨W, p, hp, ?_⟩
    change R (p ≫ g)
    rw [← eq]
    exact Sieve.downward_closed _ hR q
  transitive' := by
    rintro X S ⟨Y, f, hf, hS⟩ R hR
    obtain ⟨Z, g, hg, h⟩ := hR hS
    refine ⟨Z, g ≫ f, ?_, h⟩
    change Presheaf.IsLocallySurjective J (g.hom ≫ f.hom)
    infer_instance

/-- Singleton locally surjective covers in a slice of sheaf contexts. -/
def overCoverage (S : Sheaf J (Type (max u v))) : Coverage (Over S) where
  coverings X := {R | ∃ (Y : Over S) (f : Y ⟶ X),
    R = Presieve.singleton f ∧ Presheaf.IsLocallySurjective J f.left.hom}
  pullback := by
    rintro X Y g R ⟨Z, f, rfl, hf⟩
    obtain ⟨W, p, q, hp, eq⟩ := cover_pullback f.left g.left
    let W' : Over S := Over.mk (p ≫ Y.hom)
    let p' : W' ⟶ Y := Over.homMk p
    let q' : W' ⟶ Z := Over.homMk q (by
      dsimp [W']; rw [← Over.w f, ← Category.assoc, eq, Category.assoc, Over.w g])
    refine ⟨Presieve.singleton p', ⟨W', p', rfl, hp⟩, ?_⟩
    intro V a ha
    cases ha
    exact ⟨Z, q', f, Presieve.singleton_self _, by apply Over.OverMorphism.ext; exact eq⟩

lemma over_topology_le (S : Sheaf J (Type (max u v))) :
    (topology (J := J)).over S ≤ (overCoverage S).toGrothendieck := by
  intro X R hR
  obtain ⟨Y, f, hf, h⟩ := hR
  let Y' : Over S := Over.mk (f ≫ X.hom)
  let f' : Y' ⟶ X := Over.homMk f
  apply Coverage.mem_toGrothendieck_sieves_of_superset (overCoverage S)
    (R := Presieve.singleton f')
  · intro Z g hg
    cases hg
    exact (Sieve.overEquiv_iff _ _).mp h
  · exact ⟨Y', f', rfl, hf⟩

end SquareKit.SheafCover
