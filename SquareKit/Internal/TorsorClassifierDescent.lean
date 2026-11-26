import SquareKit.Internal.SheafRepresentableClassification
import SquareKit.SheafTorsorDescent

/-! Effective torsor descent followed by representable classification.
The decoder retains the group action, display, and every compatible local map. -/
set_option autoImplicit false
set_option warningAsError true
noncomputable section
namespace SquareKit.RepresentableClassification.TorsorDescent
open CategoryTheory SheafTorsor
universe u v
variable {C : Type u} [Category.{v} C] {J : GrothendieckTopology C}
variable {G : Sheaf J GrpCat.{max u v}} {X : Sheaf J (Type (max u v))}

/-- The comparison is derived by generic-element evaluation. -/
abbrev recovery (P : Torsor G X) := PresheafFamily.recovery.{u,u,v} P.family.family

@[simp] theorem recovery_inv_hom (P : Torsor G X) (x : X.obj.Elements)
    (p : P.family.family.obj x) :
    (recovery P).hom.app x ((recovery P).inv.app x p) = p :=
  ConcreteCategory.congr_hom ((recovery P).inv_hom_id_app x) p

@[simp] theorem recovery_hom_inv (P : Torsor G X) (x : X.obj.Elements)
    (p : (PresheafFamily.decodeSheaf.{u,u,v} P.family).family.obj x) :
    (recovery P).inv.app x ((recovery P).hom.app x p) = p :=
  ConcreteCategory.congr_hom ((recovery P).hom_inv_id_app x) p

def decodedAction (P : Torsor G X) : Action G X where
  family := PresheafFamily.decodeSheaf.{u,u,v} P.family
  act x g p := (recovery P).inv.app x (P.act x g ((recovery P).hom.app x p))
  one_act x p := by simp [P.one_act]
  mul_act x g h p := by simp [P.mul_act]; rfl
  natural {x y} f g p := by
    change _ = (recovery P).inv.app y (P.act y _ _)
    erw [← NatTrans.naturality_apply (recovery P).inv f]
    rw [P.natural]
    congr 2
    exact (NatTrans.naturality_apply (recovery P).hom f p).symm

theorem decoded_principal (P : Torsor G X) (x : X.obj.Elements)
    (p q : (decodedAction P).family.family.obj x) :
    ∃! g, (decodedAction P).act x g p = q := by
  obtain ⟨g, hg, hu⟩ := P.principal x ((recovery P).hom.app x p) ((recovery P).hom.app x q)
  refine ⟨g, ?_, ?_⟩
  · change (recovery P).inv.app x (P.act x g ((recovery P).hom.app x p)) = q
    rw [hg]
    exact recovery_hom_inv P x q
  · intro h hh
    apply hu
    have he := congrArg ((recovery P).hom.app x) hh
    change (recovery P).hom.app x ((recovery P).inv.app x _) = _ at he
    simpa only [recovery_inv_hom] using he

/-- Local existence is transported along the sheaf isomorphism over X. -/
instance decoded_isLocallySurjective (P : Torsor G X) :
    Presheaf.IsLocallySurjective J (SplitSheaf.p (decodedAction P).family).hom := by
  have h := congrArg (fun f => f.hom) (PresheafFamily.decodeSheafIso_projection.{u,u,v} P.family)
  change (PresheafFamily.decodeSheafIso.{u,u,v} P.family).hom.hom ≫ (SplitSheaf.p P.family).hom =
    (SplitSheaf.p (decodedAction P).family).hom at h
  rw [← h]
  have : IsIso (PresheafFamily.decodeSheafIso.{u,u,v} P.family).hom.hom :=
    (sheafToPresheaf J (Type (max u v))).map_isIso (PresheafFamily.decodeSheafIso.{u,u,v} P.family).hom
  exact Presheaf.isLocallySurjective_comp J
    (PresheafFamily.decodeSheafIso.{u,u,v} P.family).hom.hom (SplitSheaf.p P.family).hom

def decoded (P : Torsor G X) : Torsor G X where
  toAction := decodedAction P
  principal := decoded_principal P
  isLocallySurjective := decoded_isLocallySurjective P

def comparison (P : Torsor G X) : Arrow (decoded P) P where
  iso := recovery P
  equivariant x g p := by
    change (recovery P).hom.app x ((recovery P).inv.app x _) = _
    exact recovery_inv_hom P x _

/-- Maps of decoded objects are conjugated by the proved recovery. -/
def decodedMap {P Q : Torsor G X} (h : Arrow P Q) : Arrow (decoded P) (decoded Q) :=
  ((comparison P).comp h).comp (comparison Q).inverse

theorem decodedMap_comparison {P Q : Torsor G X} (h : Arrow P Q) :
    (decodedMap h).comp (comparison Q) = (comparison P).comp h := by
  apply SheafTorsor.Arrow.ext
  change ((recovery P).hom ≫ h.iso.hom ≫ (recovery Q).inv) ≫ (recovery Q).hom = _
  simp only [Category.assoc, Iso.inv_hom_id, Category.comp_id]
  rfl

variable {A : SplitSheaf.Ty X} {P Q : Torsor G (SplitSheaf.extension A)}
variable [Presheaf.IsLocallySurjective J (SplitSheaf.p A).hom]

/-- Construct descent first, then classify and decode the resulting family. -/
def glue (d : Descent.Datum A P) : Torsor G X := decoded (Descent.torsor d)

/-- Recovery on the whole cover, preserving the actual action. -/
def localComparison (d : Descent.Datum A P) :
    Arrow (reindex (glue d) (SplitSheaf.p A)) P :=
  ((comparison (Descent.torsor d)).reindex (SplitSheaf.p A)).comp (Descent.comparison d)

/-- Every compatible equivariant local map descends, and every global map
recovers its local datum. The inverses come from effective descent and classification. -/
def mapEquiv (d : Descent.Datum A P) (e : Descent.Datum A Q) :
    Descent.Map d e ≃ Arrow (glue d) (glue e) :=
  ((Descent.mapEquiv d e).trans equivariantArrowEquiv).trans
    (CategoryTheory.Iso.homCongr (comparison (Descent.torsor d)).toIso.symm
      (comparison (Descent.torsor e)).toIso.symm)

@[simp] theorem mapEquiv_apply (d : Descent.Datum A P) (e : Descent.Datum A Q)
    (h : Descent.Map d e) : mapEquiv d e h = decodedMap h.arrow := rfl

/-- Descending and recovering a compatible local map loses no arrow data. -/
theorem recover_map (d : Descent.Datum A P) (e : Descent.Datum A Q)
    (h : Descent.Map d e) : (mapEquiv d e).symm (mapEquiv d e h) = h :=
  (mapEquiv d e).symm_apply_apply h

/-- Recovery commutes with every descended map. -/
theorem map_comparison (d : Descent.Datum A P) (e : Descent.Datum A Q)
    (h : Descent.Map d e) :
    (mapEquiv d e h).comp (comparison (Descent.torsor e)) =
      (comparison (Descent.torsor d)).comp h.arrow :=
  decodedMap_comparison h.arrow

/-- Classification does not replace the original display by a bare total space. -/
theorem projection (d : Descent.Datum A P) :
    (PresheafFamily.decodeSheafIso (Descent.torsor d).family).hom ≫
      SplitSheaf.p (Descent.torsor d).family = SplitSheaf.p (glue d).family :=
  PresheafFamily.decodeSheafIso_projection _

def canonicalRecovery (T : Torsor G X) :
    Arrow (glue (Descent.canonicalDatum A T)) T :=
  (comparison _).comp (Descent.canonicalRecovery A T)

end SquareKit.RepresentableClassification.TorsorDescent
