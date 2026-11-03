import SquareKit.SmoothOpenDuality
import SquareKit.SmoothOpenScalar

/-! Experimental fully faithful embedding of Euclidean principal open domains
and all their ordinary smooth maps into the arbitrary-cover sheaf model. -/
noncomputable section
namespace SquareKit.EuclideanOpen
open CategoryTheory Opposite SmoothAlgebra
open SmoothPresentationSite

structure Domain where
  dimension : ℕ
  defining : Free dimension

abbrev Points (U : Domain) := Localization.locus U.defining
theorem domain_open (U : Domain) : IsOpen (Points U) := Localization.locus_open U.defining

abbrev Functions (U : Domain) := Localization.Functions U.defining
abbrev Map (U V : Domain) := Localization.OpenMap U.defining V.defining

instance : Category Domain where
  Hom := Map
  id U := OpenFunctions.Map.ident (Points U)
  comp f g := OpenFunctions.Map.comp g f
  id_comp _ := OpenFunctions.Map.ext (fun _ => rfl)
  comp_id _ := OpenFunctions.Map.ext (fun _ => rfl)
  assoc _ _ _ := OpenFunctions.Map.ext (fun _ => rfl)

/-- The already constructed single-inverse presentation, without a second localization. -/
def code (U : Domain) : Code :=
  ⟨U.dimension+1,1,Localization.relation (fun _ : Fin 1 => U.defining)⟩

def toSite : Domain ⥤ Site where
  obj U := op (code U)
  map h := (show code _ ⟶ code _ from Localization.pullback h).op
  map_id U := congrArg Quiver.Hom.op (Localization.pullback_ident U.defining)
  map_comp f g := congrArg Quiver.Hom.op (Localization.pullback_comp f g)

def toSiteFullyFaithful : toSite.FullyFaithful where
  preimage h := Localization.reconstruct h.unop
  map_preimage h := congrArg Quiver.Hom.op (Localization.pullback_reconstruct h.unop)
  preimage_map h := Localization.reconstruct_pullback h

/-- Subcanonicity has already been proved for the arbitrary-principal topology. -/
def embedding : Domain ⥤ Sheaf SmoothOpenSite.topology Type :=
  toSite ⋙ SmoothOpenSite.topology.yoneda

def fullyFaithful : embedding.FullyFaithful :=
  toSiteFullyFaithful.comp SmoothOpenSite.topology.yonedaFullyFaithful

def homEquiv (U V : Domain) : (U ⟶ V) ≃ (embedding.obj U ⟶ embedding.obj V) :=
  fullyFaithful.homEquiv

theorem inverse_forward {U V : Domain} (h : U ⟶ V) : (homEquiv U V).symm (embedding.map h) = h :=
  (homEquiv U V).symm_apply_apply h

theorem forward_inverse {U V : Domain} (h : embedding.obj U ⟶ embedding.obj V) :
    embedding.map ((homEquiv U V).symm h) = h := (homEquiv U V).apply_symm_apply h

/-- The sheaf map acts by composition with actual pullback on coordinate algebras. -/
theorem embedding_apply {U V : Domain} (h : U ⟶ V) (A : Code) (a : code U ⟶ A) :
    ((embedding.map h).hom.app (op (op A)) a.op).unop = a.comp (Localization.pullback h) := rfl

theorem point_evaluation {U V : Domain} (h : U ⟶ V) (x : Points U)
    (a : Localization.Principal V.defining) :
    (Localization.toOpen U.defining (Localization.pullback h a)).val x =
      (Localization.toOpen V.defining a).val ((show Map U V from h) x) := Localization.pullback_apply h a x

end SquareKit.EuclideanOpen
