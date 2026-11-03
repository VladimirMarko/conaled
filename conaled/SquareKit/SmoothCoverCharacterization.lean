import SquareKit.SmoothPresentationSheaf
import SquareKit.SmoothSitePullback

/-! Experimental exact characterization of principal families that cover in the
generated topology. Sheaf separatedness excludes families missing a real point. -/
noncomputable section
namespace SquareKit.SmoothPresentationSite
open CategoryTheory Opposite SmoothAlgebra PresentedLocalization PrincipalCover

/-- Categorical sheaf separatedness, usable for a covering sieve without an algebraic cover proof. -/
theorem covering_separated (A : Code) {k : ℕ} (s : Fin k → Carrier A)
    (hs : principalSieve A s ∈ topology (op A)) (a b : Carrier A)
    (he : ∀ i, atBase A.equations (s i) a=atBase A.equations (s i) b) : a=b := by
  apply (scalar_isSheaf.isSheafFor (principalPresieve A s) hs).isSeparatedFor.ext
  rintro Y f ⟨i⟩
  exact he i

/-- Exactly the ordinary unit-ideal principal families generate covering sieves. -/
theorem principal_covering_iff (A : Code) {k : ℕ} (s : Fin k → Carrier A) :
    principalSieve A s ∈ topology (op A) ↔ Covers s := by
  constructor
  · intro hs
    have hc : Covers (fun i => Presentation.projection A.equations (representative A.equations (s i))) := by
      apply (covers_iff_zero_locus A.equations (fun i => representative A.equations (s i))).mpr
      intro x hx
      by_contra hn
      push Not at hn
      let B := free 0
      let h : A ⟶ B := Hom.comp DualExtension.realHom (realPoint A.equations x hx)
      have hz (i : Fin k) : (smoothMap h).toFun (s i)=0 := by
        rw [← representative_eq A.equations (s i)]
        change DualExtension.realHom ((representative A.equations (s i)).val x)=0
        rw [hn i]
        exact (DualExtension.realHom : Hom ℝ (Carrier B)).toAlgHom.map_zero
      have ht : principalSieve B (fun i => (smoothMap h).toFun (s i)) ∈ topology (op B) := by
        rw [← principalSieve_pullback h s]
        exact topology.pullback_stable h.op hs
      have he : (0 : Carrier B)=1 := covering_separated B _ ht 0 1 (fun i => by
        have hnil : IsNilpotent (Presentation.projection B.equations (representative B.equations ((smoothMap h).toFun (s i)))) := by
          rw [representative_eq,hz i]
          exact ⟨1,zero_pow (by decide)⟩
        have := nilpotent_subsingleton B.equations (representative B.equations ((smoothMap h).toFun (s i))) hnil
        exact Subsingleton.elim _ _)
      let e : Hom (Carrier B) ℝ := Hom.comp (evaluate (Fin.elim0 : Fin 0 → ℝ)) (freeValue 0)
      have hh := congrArg e.toAlgHom he
      exact zero_ne_one (by simpa only [map_zero,map_one] using hh)
    simpa only [representative_eq] using hc
  · exact principal_covering A s

/-- A principal sieve is maximal precisely when one member is already a unit. -/
theorem principal_maximal_iff (A : Code) {k : ℕ} (s : Fin k → Carrier A) :
    principalSieve A s=⊤ ↔ ∃ i, IsUnit (s i) := by
  rw [← Sieve.id_mem_iff_eq_top]
  constructor
  · rintro ⟨Y,u,v,⟨i⟩,he⟩
    have hu := (atBase_isUnit A.equations (s i)).map (smoothMap u.unop).toAlgHom
    have hh := congrArg (fun f : A ⟶ A => (smoothMap f).toFun (s i)) (congrArg Quiver.Hom.unop he)
    change (smoothMap u.unop).toFun (atBase A.equations (s i) (s i))=s i at hh
    change IsUnit ((smoothMap u.unop).toFun (atBase A.equations (s i) (s i))) at hu
    exact ⟨i,hh ▸ hu⟩
  · rintro ⟨i,hi⟩
    have hp : IsUnit (Presentation.projection A.equations (representative A.equations (s i))) := by simpa using hi
    let u : localization A (s i) ⟶ A := unitRetraction A.equations (representative A.equations (s i)) hp
    refine ⟨_,u.op,(localizationBase A (s i)).op,⟨i⟩,?_⟩
    exact congrArg Quiver.Hom.op (show localizationBase A (s i) ≫ u=𝟙 A from unit_base_inverse _ _ _)


end SquareKit.SmoothPresentationSite
