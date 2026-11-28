import SquareKit.Internal.Cubical.NativePathComposition
import SquareKit.Internal.Cubical.EquivalenceFamilies

/-! Concatenation acts on native path families and their higher paths. -/
set_option autoImplicit false
set_option warningAsError true
namespace SquareKit.Cubical.Presheaf.NativeWhiskering
open CategoryTheory EquivalenceFamilies
universe u

/-- Return a path in a substituted family to the substituted path presentation. -/
def unreindex {Γ Δ : Context.{u}} {A : Family Γ} {a b : Term A} (σ : Δ ⟶ Γ)
    (p : Term (homogeneousPath (reindex A σ) (Term.reindex a σ) (Term.reindex b σ))) :
    Term (reindex (homogeneousPath A a b) σ) :=
  Term.map (homogeneousReindexIso A a b σ).inv p

theorem unreindex_reindex {Γ Δ Θ : Context.{u}} {A : Family Γ} {a b : Term A}
    (σ : Δ ⟶ Γ) (τ : Θ ⟶ Δ)
    (p : Term (homogeneousPath (reindex A σ) (Term.reindex a σ) (Term.reindex b σ))) :
    Term.reindex (unreindex σ p) τ = unreindex (τ ≫ σ) (homogeneousReindex p τ) := by
  let e := homogeneousReindexIso A a b σ
  let d := homogeneousReindexIso (reindex A σ) (Term.reindex a σ) (Term.reindex b σ) τ
  let c := homogeneousReindexIso A a b (τ ≫ σ)
  apply Term.map_injective_of_iso c
  apply Term.ext
  intro x
  exact (congrArg (d.hom.app x) (e.inv_hom_id_app_apply (τ.mapElements.obj x)
    (p.val (τ.mapElements.obj x)))).trans
    (c.inv_hom_id_app_apply x (d.hom.app x (p.val (τ.mapElements.obj x)))).symm

@[simp] theorem unreindex_id {Γ : Context.{u}} {A : Family Γ} {a b : Term A}
    (p : Term (homogeneousPath A a b)) : unreindex (𝟙 Γ) p = p :=
  Term.map_iso_roundtrip (homogeneousReindexIso A a b (𝟙 Γ)) p

variable {Γ : Context.{u}} {A : Family Γ} (F : Filling A) (hF : F.Lawful)
  {a b c : Term A}

noncomputable def rightSection (q : Term (homogeneousPath A b c)) :
    Term (reindex (homogeneousPath A a c) (projection (homogeneousPath A a b))) :=
  let π := projection (homogeneousPath A a b)
  unreindex π (homogeneousConcat (F.reindex π) (hF.reindex π)
    (Term.map (homogeneousReindexIso A a b π).hom (generic (homogeneousPath A a b)))
    (homogeneousReindex q π))

/-- Concatenate on the right at every generalized argument. -/
noncomputable def rightMap (q : Term (homogeneousPath A b c)) :
    homogeneousPath A a b ⟶ homogeneousPath A a c :=
  EquivalenceFamilies.decodeMap (lam (rightSection F hF q))

@[simp] theorem rightMap_apply (p : Term (homogeneousPath A a b))
    (q : Term (homogeneousPath A b c)) :
    Term.map (rightMap F hF q) p = homogeneousConcat F hF p q := by
  change Term.reindex (rightSection F hF q) (pair (𝟙 Γ) p) = _
  rw [rightSection, unreindex_reindex, homogeneousConcat_reindex]
  exact unreindex_id (homogeneousConcat F hF p q)

noncomputable def leftSection (p : Term (homogeneousPath A a b)) :
    Term (reindex (homogeneousPath A a c) (projection (homogeneousPath A b c))) :=
  let π := projection (homogeneousPath A b c)
  unreindex π (homogeneousConcat (F.reindex π) (hF.reindex π)
    (homogeneousReindex p π)
    (Term.map (homogeneousReindexIso A b c π).hom (generic (homogeneousPath A b c))))

/-- Concatenate on the left at every generalized argument. -/
noncomputable def leftMap (p : Term (homogeneousPath A a b)) :
    homogeneousPath A b c ⟶ homogeneousPath A a c :=
  EquivalenceFamilies.decodeMap (lam (leftSection F hF p))

@[simp] theorem leftMap_apply (p : Term (homogeneousPath A a b))
    (q : Term (homogeneousPath A b c)) :
    Term.map (leftMap F hF p) q = homogeneousConcat F hF p q := by
  change Term.reindex (leftSection F hF p) (pair (𝟙 Γ) q) = _
  rw [leftSection, unreindex_reindex, homogeneousConcat_reindex]
  exact unreindex_id (homogeneousConcat F hF p q)

/-- Native right whiskering retains the supplied 2-path and its two endpoints. -/
noncomputable def right {p p' : Term (homogeneousPath A a b)}
    (H : Term (homogeneousPath (homogeneousPath A a b) p p'))
    (q : Term (homogeneousPath A b c)) :
    Term (homogeneousPath (homogeneousPath A a c)
      (homogeneousConcat F hF p q) (homogeneousConcat F hF p' q)) :=
  Term.convert (congrArg₂ (homogeneousPath (homogeneousPath A a c))
    (rightMap_apply F hF p q) (rightMap_apply F hF p' q))
    (homogeneousPathMap (rightMap F hF q) H)

/-- Native left whiskering retains the supplied 2-path and its two endpoints. -/
noncomputable def left (p : Term (homogeneousPath A a b))
    {q q' : Term (homogeneousPath A b c)}
    (H : Term (homogeneousPath (homogeneousPath A b c) q q')) :
    Term (homogeneousPath (homogeneousPath A a c)
      (homogeneousConcat F hF p q) (homogeneousConcat F hF p q')) :=
  Term.convert (congrArg₂ (homogeneousPath (homogeneousPath A a c))
    (leftMap_apply F hF p q) (leftMap_apply F hF p q'))
    (homogeneousPathMap (leftMap F hF p) H)

end SquareKit.Cubical.Presheaf.NativeWhiskering
