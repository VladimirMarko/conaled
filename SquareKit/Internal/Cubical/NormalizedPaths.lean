import SquareKit.Internal.Cubical.Conversion
import SquareKit.Internal.Cubical.RangeSubtype

/-! Path families as the endpoint-constrained part of normalized products. -/
namespace SquareKit.Cubical.Presheaf
open CategoryTheory
universe u

abbrev LocalPath {Γ : Context.{u}} (B : Family (total (interval Γ)))
    (a₀ : Term (reindex B (endpointSub Γ false)))
    (a₁ : Term (reindex B (endpointSub Γ true))) (x : Γ.Elements) :=
  {s : LocalPi (interval Γ) B x // ∃ p : PathElement B a₀ a₁ x, p.val.toLocal = s}

def PathElement.toLocal {Γ : Context.{u}} {B : Family (total (interval Γ))}
    {a₀ : Term (reindex B (endpointSub Γ false))}
    {a₁ : Term (reindex B (endpointSub Γ true))} {x : Γ.Elements}
    (p : PathElement B a₀ a₁ x) : LocalPath B a₀ a₁ x := ⟨p.val.toLocal,p,rfl⟩

def LocalPath.fromLocal {Γ : Context.{u}} {B : Family (total (interval Γ))}
    {a₀ : Term (reindex B (endpointSub Γ false))}
    {a₁ : Term (reindex B (endpointSub Γ true))} {x : Γ.Elements}
    (s : LocalPath B a₀ a₁ x) : PathElement B a₀ a₁ x :=
  ⟨s.val.fromLocal, by
    obtain ⟨p,hp⟩ := s.property
    have h := congrArg LocalPi.fromLocal hp
    have he : p.val = s.val.fromLocal := (LocalPi.fromLocal_toLocal p.val).symm.trans h
    exact he ▸ (fun {_} f => p.property f)⟩

theorem LocalPath.fromLocal_toLocal {Γ : Context.{u}} {B : Family (total (interval Γ))}
    {a₀ : Term (reindex B (endpointSub Γ false))}
    {a₁ : Term (reindex B (endpointSub Γ true))} {x : Γ.Elements}
    (p : PathElement B a₀ a₁ x) : p.toLocal.fromLocal = p :=
  Subtype.ext (LocalPi.fromLocal_toLocal p.val)

theorem LocalPath.toLocal_fromLocal {Γ : Context.{u}} {B : Family (total (interval Γ))}
    {a₀ : Term (reindex B (endpointSub Γ false))}
    {a₁ : Term (reindex B (endpointSub Γ true))} {x : Γ.Elements}
    (s : LocalPath B a₀ a₁ x) : s.fromLocal.toLocal = s :=
  Subtype.ext (LocalPi.toLocal_fromLocal s.val)

private def pathSubstitutionEquiv {Γ Δ : Context.{u}} (B : Family (total (interval Γ)))
    (a₀ : Term (reindex B (endpointSub Γ false)))
    (a₁ : Term (reindex B (endpointSub Γ true))) (σ : Δ ⟶ Γ) (x : Δ.Elements) :
    PathElement B a₀ a₁ (σ.mapElements.obj x) ≃
      PathElement (reindex B (liftSub (interval Γ) σ)) (a₀.reindex σ) (a₁.reindex σ) x where
  toFun := (pathReindexIso B a₀ a₁ σ).hom.app x
  invFun := (pathReindexIso B a₀ a₁ σ).inv.app x
  left_inv p := congrArg (fun t => t.app x p) (pathReindexIso B a₀ a₁ σ).hom_inv_id
  right_inv p := congrArg (fun t => t.app x p) (pathReindexIso B a₀ a₁ σ).inv_hom_id

/-- Endpoint constraints respect the same literal substitution equality as products. -/
theorem localPath_substitution {Γ Δ : Context.{u}} (B : Family (total (interval Γ)))
    (a₀ : Term (reindex B (endpointSub Γ false)))
    (a₁ : Term (reindex B (endpointSub Γ true))) (σ : Δ ⟶ Γ) (x : Δ.Elements) :
    LocalPath B a₀ a₁ (σ.mapElements.obj x) =
      LocalPath (reindex B (liftSub (interval Γ) σ)) (a₀.reindex σ) (a₁.reindex σ) x := by
  exact rangeSubtype_eq (pathSubstitutionEquiv B a₀ a₁ σ x) (localPi_substitution (interval Γ) B σ x).symm
    (fun p => p.val.toLocal) (fun p => p.val.toLocal)
    (fun p => (toLocal_substitution (interval Γ) B σ x p.val).symm)

theorem pathToLocal_substitution {Γ Δ : Context.{u}} (B : Family (total (interval Γ)))
    (a₀ : Term (reindex B (endpointSub Γ false)))
    (a₁ : Term (reindex B (endpointSub Γ true))) (σ : Δ ⟶ Γ) (x : Δ.Elements)
    (p : PathElement B a₀ a₁ (σ.mapElements.obj x)) :
    HEq p.toLocal (((pathReindex B a₀ a₁ σ).app x p).toLocal) := by
  apply (Subtype.heq_iff_coe_heq (localPi_substitution (interval Γ) B σ x).symm
    (rangePredicate_heq (pathSubstitutionEquiv B a₀ a₁ σ x)
      (localPi_substitution (interval Γ) B σ x).symm
      (fun p => p.val.toLocal) (fun p => p.val.toLocal)
      (fun p => (toLocal_substitution (interval Γ) B σ x p.val).symm))).mpr
  exact (toLocal_substitution (interval Γ) B σ x p.val).symm

/-- Endpoint constraints are retained by the pointwise equivalence. -/
def localPathEquiv {Γ : Context.{u}} (B : Family (total (interval Γ)))
    (a₀ : Term (reindex B (endpointSub Γ false)))
    (a₁ : Term (reindex B (endpointSub Γ true))) (x : Γ.Elements) :
    (path B a₀ a₁).obj x ≃ LocalPath B a₀ a₁ x where
  toFun := PathElement.toLocal
  invFun := LocalPath.fromLocal
  left_inv := LocalPath.fromLocal_toLocal
  right_inv := LocalPath.toLocal_fromLocal

def normalizedPath {Γ : Context.{u}} (B : Family (total (interval Γ)))
    (a₀ : Term (reindex B (endpointSub Γ false)))
    (a₁ : Term (reindex B (endpointSub Γ true))) : Family Γ :=
  (path B a₀ a₁).copyObj (LocalPath B a₀ a₁)
    (fun x => (localPathEquiv B a₀ a₁ x).toIso)

def normalizedPathIso {Γ : Context.{u}} (B : Family (total (interval Γ)))
    (a₀ : Term (reindex B (endpointSub Γ false)))
    (a₁ : Term (reindex B (endpointSub Γ true))) : path B a₀ a₁ ≅ normalizedPath B a₀ a₁ :=
  (path B a₀ a₁).isoCopyObj (LocalPath B a₀ a₁)
    (fun x => (localPathEquiv B a₀ a₁ x).toIso)

theorem normalizedPath_reindex {Γ Δ : Context.{u}} (B : Family (total (interval Γ)))
    (a₀ : Term (reindex B (endpointSub Γ false)))
    (a₁ : Term (reindex B (endpointSub Γ true))) (σ : Δ ⟶ Γ) :
    reindex (normalizedPath B a₀ a₁) σ =
      normalizedPath (reindex B (liftSub (interval Γ) σ)) (a₀.reindex σ) (a₁.reindex σ) := by
  have ho : ∀ x, (reindex (normalizedPath B a₀ a₁) σ).obj x =
      (normalizedPath (reindex B (liftSub (interval Γ) σ)) (a₀.reindex σ) (a₁.reindex σ)).obj x :=
    localPath_substitution B a₀ a₁ σ
  apply Functor.hext ho
  intro x y f
  apply typeHom_hext (ho x) (ho y)
  intro s t hst
  change LocalPath B a₀ a₁ (σ.mapElements.obj x) at s
  change LocalPath (reindex B (liftSub (interval Γ) σ)) (a₀.reindex σ) (a₁.reindex σ) x at t
  have ht : t = ((pathReindex B a₀ a₁ σ).app x s.fromLocal).toLocal :=
    eq_of_heq (hst.symm.trans ((heq_of_eq s.toLocal_fromLocal).symm.trans
      (pathToLocal_substitution B a₀ a₁ σ x s.fromLocal)))
  subst t
  change HEq ((path B a₀ a₁).map (σ.mapElements.map f) s.fromLocal).toLocal
    ((path (reindex B (liftSub (interval Γ) σ)) (a₀.reindex σ) (a₁.reindex σ)).map f
      (((pathReindex B a₀ a₁ σ).app x s.fromLocal).toLocal.fromLocal)).toLocal
  exact (pathToLocal_substitution B a₀ a₁ σ y
    ((path B a₀ a₁).map (σ.mapElements.map f) s.fromLocal)).trans
      (heq_of_eq (congrArg (fun p =>
        ((path (reindex B (liftSub (interval Γ) σ)) (a₀.reindex σ) (a₁.reindex σ)).map f p).toLocal)
        (LocalPath.fromLocal_toLocal ((pathReindex B a₀ a₁ σ).app x s.fromLocal))).symm)

end SquareKit.Cubical.Presheaf
