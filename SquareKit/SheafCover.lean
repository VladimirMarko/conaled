import SquareKit.SplitSheaf
import Mathlib.CategoryTheory.Sites.LocallyBijective

/-! Locally surjective covers of sheaf contexts, shared by descent clients. -/
noncomputable section
set_option autoImplicit false
set_option warningAsError true
namespace SquareKit.SheafCover
open CategoryTheory Opposite
universe u v
variable {C : Type u} [Category.{v} C] {J : GrothendieckTopology C}
variable {X Y : Sheaf J (Type (max u v))} {A : SplitSheaf.Ty X}

/-- A split cover remains locally surjective after arbitrary parameter change. -/
instance baseChangeCover_isLocallySurjective (f : Y ⟶ X)
    [Presheaf.IsLocallySurjective J (SplitSheaf.p A).hom] :
    Presheaf.IsLocallySurjective J (SplitSheaf.p (SplitSheaf.tySub A f)).hom where
  imageSieve_mem {U} y := by
    apply J.superset_covering _
      (Presheaf.imageSieve_mem J (SplitSheaf.p A).hom (f.hom.app (Opposite.op U) y))
    intro V k hk
    obtain ⟨⟨x,b⟩, hx⟩ := hk
    change x = X.obj.map k.op (f.hom.app (Opposite.op U) y) at hx
    subst x
    have hn := NatTrans.naturality_apply f.hom k.op y
    change f.hom.app (Opposite.op V) (Y.obj.map k.op y) =
      X.obj.map k.op (f.hom.app (Opposite.op U) y) at hn
    rw [← hn] at b
    exact ⟨⟨Y.obj.map k.op y,b⟩, rfl⟩

instance splitDisplay_isLocallySurjective {Y : Sheaf J (Type (max u v))} (f : Y ⟶ X)
    [Presheaf.IsLocallySurjective J f.hom] :
    Presheaf.IsLocallySurjective J (SplitSheaf.p (SplitSheaf.ofDisplay f)).hom := by
  rw [← SplitSheaf.displayIso_projection]
  change Presheaf.IsLocallySurjective J ((SplitSheaf.displayIso f).hom.hom ≫ f.hom)
  infer_instance

theorem display_sieve {Y : Sheaf J (Type (max u v))} (f : Y ⟶ X) :
    Sieve.ofArrows _ (fun _ : Unit => SplitSheaf.p (SplitSheaf.ofDisplay f)) =
      Sieve.ofArrows _ (fun _ : Unit => f) := by
  ext Z g
  simp only [Sieve.mem_ofArrows_iff]
  constructor
  · rintro ⟨i, h, rfl⟩
    exact ⟨(), h ≫ (SplitSheaf.displayIso f).hom, by
      rw [Category.assoc, SplitSheaf.displayIso_projection]⟩
  · rintro ⟨i, h, rfl⟩
    exact ⟨(), h ≫ (SplitSheaf.displayIso f).inv, by
      simp [← SplitSheaf.displayIso_projection]⟩

/-- Locally surjective maps have locally surjective refinements after any base change. -/
theorem cover_pullback {X Y Z : Sheaf J (Type (max u v))} (f : Y ⟶ X) (g : Z ⟶ X)
    [Presheaf.IsLocallySurjective J f.hom] :
    ∃ (W : Sheaf J (Type (max u v))) (p : W ⟶ Z) (q : W ⟶ Y),
      Presheaf.IsLocallySurjective J p.hom ∧ q ≫ f = p ≫ g := by
  let A := SplitSheaf.ofDisplay f
  refine ⟨SplitSheaf.extension (SplitSheaf.tySub A g), SplitSheaf.p _,
    SplitSheaf.lift A g ≫ (SplitSheaf.displayIso f).hom, inferInstance, ?_⟩
  rw [Category.assoc, SplitSheaf.displayIso_projection, SplitSheaf.lift_p]

end SquareKit.SheafCover
