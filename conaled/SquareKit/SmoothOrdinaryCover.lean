import SquareKit.SmoothOpenSubdomain
import SquareKit.SmoothOpenTopology

/-! Experimental comparison of ordinary principal-open covers with the actual
arbitrary-principal site. Analytic families allow Type u indices; the small
site's covering assertion uses Type indices. -/
noncomputable section
namespace SquareKit.EuclideanOpen
open CategoryTheory Opposite SmoothAlgebra SmoothPresentationSite Localization
variable (U : Domain) {ι : Type*} (g : ι → Free U.dimension)

def Covers : Prop := ∀ x : Points U, ∃ i, (g i).val x.val ≠ 0

theorem covers_iff_union : Covers U g ↔
    ∀ x ∈ Points U, ∃ i, x ∈ Points (subdomain U (g i)) := by
  constructor
  · intro h x hx
    obtain ⟨i,hi⟩ := h ⟨x,hx⟩
    exact ⟨i,mul_ne_zero hx hi⟩
  · intro h x
    obtain ⟨i,hi⟩ := h x.val x.property
    exact ⟨i,right_ne_zero_of_mul hi⟩

theorem point_base (h : Hom (Principal U.defining) ℝ) (a : Free U.dimension) :
    h (principalBase U.defining a) = a.val (realPoints U.defining h).val := by
  exact (congrArg (fun e : Hom (Principal U.defining) ℝ => e (principalBase U.defining a))
    ((realPoints U.defining).symm_apply_apply h)).symm.trans
    ((toOpen_realPoint U.defining (realPoints U.defining h) (principalBase U.defining a)).symm.trans
      (toOpen_base U.defining a (realPoints U.defining h)))

theorem covers_iff_algebra : Covers U g ↔ OpenCover.Covers (fun i => element U (g i)) := by
  constructor
  · intro hc h
    obtain ⟨i,hi⟩ := hc (realPoints U.defining h)
    exact ⟨i,fun he => hi ((point_base U h (g i)).symm.trans he)⟩
  · intro hc x
    obtain ⟨i,hi⟩ := hc ((realPoints U.defining).symm x)
    have he := point_base U ((realPoints U.defining).symm x) (g i)
    have he' := congrArg (fun y : locus U.defining => (g i).val y.val)
      ((realPoints U.defining).apply_symm_apply x)
    exact ⟨i,fun hz => hi (he.trans (he'.trans hz))⟩

theorem empty_cover_iff (g : Fin 0 → Free U.dimension) : Covers U g ↔ IsEmpty (Points U) := by
  constructor
  · intro h
    exact ⟨fun x => (h x).elim (fun i _ => Fin.elim0 i)⟩
  · intro h x
    exact h.false x |>.elim

def coverPresieve : Presieve (toSite.obj U) :=
  Presieve.ofArrows (fun i => toSite.obj (subdomain U (g i))) (fun i => toSite.map (subInclusion U (g i)))
def coverSieve : Sieve (toSite.obj U) := Sieve.generate (coverPresieve U g)

theorem coverSieve_eq : coverSieve U g = principalSieve (code U) (fun i => element U (g i)) := by
  apply le_antisymm
  · apply (Sieve.generate_le_iff _ _).mpr
    rintro X h ⟨i⟩
    refine ⟨_,(toSubdomain U (g i)).op,_,⟨i⟩,?_⟩
    exact congrArg Quiver.Hom.op (toSubdomain_base U (g i))
  · apply (Sieve.generate_le_iff _ _).mpr
    rintro X h ⟨i⟩
    refine ⟨_,(fromSubdomain U (g i)).op,_,⟨i⟩,?_⟩
    exact congrArg Quiver.Hom.op (fromSubdomain_base U (g i))

theorem covering {ι : Type} (g : ι → Free U.dimension) (hc : Covers U g) :
    coverSieve U g ∈ SmoothOpenSite.topology (toSite.obj U) := by
  rw [coverSieve_eq]
  exact SmoothOpenSite.principal_covering _ _ ((covers_iff_algebra U g).mp hc)

end SquareKit.EuclideanOpen
