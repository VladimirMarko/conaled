import SquareKit.Internal.Cubical.FunctionFillingSubstitution
import SquareKit.Internal.Cubical.FillingTransportLaws

/-! Chosen normalized product filling obeys literal family substitution. -/
namespace SquareKit.Cubical.Presheaf
open CategoryTheory
universe u

def Filling.convert {Γ : Context.{u}} {A B : Family Γ} (e : A = B) (F : Filling A) : Filling B := e ▸ F

theorem Filling.transport_eqToIso {Γ : Context.{u}} {A B : Family Γ} (e : A = B)
    (F : Filling A) : F.transport (eqToIso e) = F.convert e := by
  cases e
  rfl

theorem piFilling_reindex_iso {Γ Δ : Context.{u}} {A : Family Γ} {B : Family (total A)}
    (F : Filling A) (hF : F.Lawful) (G : Filling B) (σ : Δ ⟶ Γ) :
    ((piFilling F hF G).reindex σ).transport (piReindexIso A B σ) =
      piFilling (F.reindex σ) (hF.reindex σ) (G.reindex (liftSub A σ)) :=
  Filling.transport_eq _ _ _ (piFilling_reindex F hF G σ)

theorem normalizedPiIso_reindex {Γ Δ : Context.{u}} (A : Family Γ) (B : Family (total A))
    (σ : Δ ⟶ Γ) :
    (Functor.isoWhiskerLeft σ.mapElements (normalizedPiIso A B)).trans (eqToIso (normalizedPi_reindex A B σ)) =
      (piReindexIso A B σ).trans (normalizedPiIso (Presheaf.reindex A σ) (reindex B (liftSub A σ))) := by
  apply Iso.ext
  apply NatTrans.ext
  funext x
  apply ConcreteCategory.hom_ext
  intro p
  have cast_heq : ∀ {C D : Family Δ} (e : C = D) (v : C.obj x), HEq ((eqToHom e).app x v) v := by
    intro C D e v
    cases e
    rfl
  exact eq_of_heq ((cast_heq (normalizedPi_reindex A B σ) p.toLocal).trans
    (toLocal_substitution A B σ x p).symm)

noncomputable def normalizedPiFilling {Γ : Context.{u}} {A : Family Γ} {B : Family (total A)}
    (F : Filling A) (hF : F.Lawful) (G : Filling B) : Filling (normalizedPi A B) :=
  (piFilling F hF G).transport (normalizedPiIso A B)

theorem normalizedPiFilling_reindex {Γ Δ : Context.{u}} {A : Family Γ} {B : Family (total A)}
    (F : Filling A) (hF : F.Lawful) (G : Filling B) (σ : Δ ⟶ Γ) :
    ((normalizedPiFilling F hF G).reindex σ).convert (normalizedPi_reindex A B σ) =
      normalizedPiFilling (F.reindex σ) (hF.reindex σ) (G.reindex (liftSub A σ)) := by
  let e := normalizedPi_reindex A B σ
  let n := normalizedPiIso (Presheaf.reindex A σ) (reindex B (liftSub A σ))
  calc
    _ = ((piFilling F hF G).reindex σ).transport
        ((Functor.isoWhiskerLeft σ.mapElements (normalizedPiIso A B)).trans (eqToIso e)) :=
      (Filling.transport_eqToIso e ((normalizedPiFilling F hF G).reindex σ)).symm
    _ = ((piFilling F hF G).reindex σ).transport ((piReindexIso A B σ).trans n) :=
      congrArg (fun k => ((piFilling F hF G).reindex σ).transport k) (normalizedPiIso_reindex A B σ)
    _ = _ := congrArg (fun H => H.transport n) (piFilling_reindex_iso F hF G σ)

end SquareKit.Cubical.Presheaf
