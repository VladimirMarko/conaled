import SquareKit.Internal.PathTransport.GroupoidFiberFaithful
import Mathlib.CategoryTheory.NatIso

/-! Fullness through selected lifts of base arrows and vertical fullness. -/
noncomputable section
namespace SquareKit.Internal.PathTransport.GroupoidFiberFull
open CategoryTheory
universe u v w z u₁ v₁ u₂ v₂
variable {C : Type u} [Groupoid.{v} C] {D : Type w} [Groupoid.{z} D]
variable {B : Type u₁} [Category.{v₁} B] {K : Type u₂} [Category.{v₂} K]

/-- An arbitrary target arrow factors into a selected base lift and a vertical
arrow. Equality of object images is used only to state that vertical boundary. -/
theorem full_of_vertical (E : C ⥤ D) (P : C ⥤ B) (Q : D ⥤ K)
    (R : B ⥤ K) [R.Full] (square : E ⋙ Q = P ⋙ R)
    (lift : ∀ (x y : C) (b : P.obj x ⟶ P.obj y),
      ∃ (z : C) (e : x ≅ z) (h : P.obj z = P.obj y), P.map e.hom ≫ eqToHom h = b)
    (vertical : ∀ (x y : C) (h : P.obj x = P.obj y) (p : E.obj x ⟶ E.obj y),
      Q.map p ≫ (eqToIso square).hom.app y =
        (eqToIso square).hom.app x ≫ R.map (eqToHom h) →
      ∃ g : x ⟶ y, E.map g = p) : E.Full where
  map_surjective {x y} p := by
    let η := eqToIso square
    let b : P.obj x ⟶ P.obj y := R.preimage (η.inv.app x ≫ Q.map p ≫ η.hom.app y)
    have hb : η.hom.app x ≫ R.map b = Q.map p ≫ η.hom.app y := by
      simp [b]
    obtain ⟨z,e,h,he⟩ := lift x y b
    let q : E.obj z ⟶ E.obj y := E.map e.inv ≫ p
    have hq : Q.map q ≫ η.hom.app y = η.hom.app z ≫ R.map (eqToHom h) := by
      have hi : P.map e.inv ≫ b = eqToHom h := by
        rw [← he, ← Category.assoc, ← P.map_comp]
        simp
      calc
        Q.map q ≫ η.hom.app y = Q.map (E.map e.inv) ≫ (Q.map p ≫ η.hom.app y) := by
          simp [q, Category.assoc]
        _ = Q.map (E.map e.inv) ≫ (η.hom.app x ≫ R.map b) := by rw [hb]
        _ = η.hom.app z ≫ (R.map (P.map e.inv) ≫ R.map b) := by
          have hn := η.hom.naturality e.inv
          simp only [Functor.comp_map] at hn
          rw [← Category.assoc, hn, Category.assoc]
        _ = η.hom.app z ≫ R.map (eqToHom h) := by rw [← R.map_comp, hi]
    obtain ⟨g,hg⟩ := vertical z y h q hq
    refine ⟨e.hom ≫ g, ?_⟩
    simp [E.map_comp, hg, q, ← Category.assoc, ← E.map_comp]

end SquareKit.Internal.PathTransport.GroupoidFiberFull
