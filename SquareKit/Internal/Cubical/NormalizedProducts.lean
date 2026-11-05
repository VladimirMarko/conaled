import SquareKit.Internal.Cubical.LocalProducts

/-! Dependent products represented by sections of local diagrams. -/
namespace SquareKit.Cubical.Presheaf
open CategoryTheory
universe u

def normalizedPi {Γ : Context.{u}} (A : Family Γ) (B : Family (total A)) : Family Γ :=
  (pi A B).copyObj (LocalPi A B) (fun x => (localPiEquiv A B x).toIso)

/-- Mathlib transports functor laws and supplies the natural isomorphism. -/
def normalizedPiIso {Γ : Context.{u}} (A : Family Γ) (B : Family (total A)) :
    pi A B ≅ normalizedPi A B :=
  (pi A B).isoCopyObj (LocalPi A B) (fun x => (localPiEquiv A B x).toIso)

/-- Normalizing after the old substitution comparison agrees with equality transport
of the local diagram. -/
theorem toLocal_substitution {Γ Δ : Context.{u}} (A : Family Γ) (B : Family (total A))
    (σ : Δ ⟶ Γ) (x : Δ.Elements) (p : PiElement A B (σ.mapElements.obj x)) :
    HEq (((piReindex A B σ).app x p).toLocal) p.toLocal := by
  apply ProjectionDiagram.Section.hext (localProductDiagram_substitution A B σ x)
  intro f a b hab
  have hy : σ.mapElements.obj ((localize Δ x).obj f) =
      (localize Γ (σ.mapElements.obj x)).obj f :=
    congrArg (Γ.elementsMk f.right) (σ.naturality_apply f.hom x.val)
  exact p.pair_heq hy (σ.mapElements.map (localArrow x f))
    (localArrow (σ.mapElements.obj x) f)
    (elementHom_hext rfl hy _ _ HEq.rfl) a b hab

theorem typeHom_hext {X X' Y Y' : Type u} (hx : X = X') (hy : Y = Y')
    (f : X ⟶ Y) (g : X' ⟶ Y')
    (h : ∀ x x', HEq x x' → HEq (f x) (g x')) : HEq f g := by
  cases hx
  cases hy
  apply heq_of_eq
  apply ConcreteCategory.hom_ext
  intro x
  exact eq_of_heq (h x x HEq.rfl)

/-- Dependent product formation now commutes with substitution as family equality. -/
theorem normalizedPi_reindex {Γ Δ : Context.{u}} (A : Family Γ) (B : Family (total A))
    (σ : Δ ⟶ Γ) : reindex (normalizedPi A B) σ =
      normalizedPi (reindex A σ) (reindex B (liftSub A σ)) := by
  have ho : ∀ x, (reindex (normalizedPi A B) σ).obj x =
      (normalizedPi (reindex A σ) (reindex B (liftSub A σ))).obj x :=
    fun x => (localPi_substitution A B σ x).symm
  apply Functor.hext ho
  intro x y f
  apply typeHom_hext (ho x) (ho y)
  intro s t hst
  change LocalPi A B (σ.mapElements.obj x) at s
  change LocalPi (reindex A σ) (reindex B (liftSub A σ)) x at t
  have ht : t = ((piReindex A B σ).app x s.fromLocal).toLocal :=
    eq_of_heq (hst.symm.trans ((toLocal_substitution A B σ x s.fromLocal).trans
      (heq_of_eq s.toLocal_fromLocal)).symm)
  subst t
  change HEq (s.fromLocal.restrict (σ.mapElements.map f)).toLocal
    ((((piReindex A B σ).app x s.fromLocal).toLocal.fromLocal).restrict f).toLocal
  exact (toLocal_substitution A B σ y (s.fromLocal.restrict (σ.mapElements.map f))).symm.trans
    (heq_of_eq (congrArg (fun p => (p.restrict f).toLocal)
      (LocalPi.fromLocal_toLocal ((piReindex A B σ).app x s.fromLocal))).symm)

end SquareKit.Cubical.Presheaf
