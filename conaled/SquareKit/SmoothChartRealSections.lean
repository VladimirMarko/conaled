import SquareKit.SmoothOpenRealSections
import SquareKit.SmoothChartRealization

/-! Ordinary real sections of a chart realization. -/
noncomputable section
open CategoryTheory CategoryTheory.Limits
namespace SquareKit.EuclideanOpen
open SmoothAlgebra SmoothOpenSite

def constantMap (U V : Domain) (y : Points V) : U ⟶ V where
  toFun _ := y
  smooth i := (OpenFunctions.representative_iff _ (fun _ => y.val i)
    (fun _ => rfl)).mpr contDiffOn_const

namespace Charts
variable {M : Type} (A : Charts M)

def realDiagram : MultispanIndex A.shape (Type) where
  left r := realSections.obj (embedding.obj r.domain)
  right i := realSections.obj (embedding.obj (A.domain i))
  fst r := realSections.map (embedding.map r.left)
  snd r := realSections.map (embedding.map r.right)

def realCocone : Multicofork A.realDiagram :=
  Multicofork.ofπ _ M (fun i => TypeCat.ofHom (fun a => A.coordinate i (realSectionEquiv _ a)))
    (fun r => by
      ext a
      exact (congrArg (A.coordinate r.first) (realSectionEquiv_naturality r.left a)).trans
        ((r.agreement (realSectionEquiv _ a)).trans
          (congrArg (A.coordinate r.second) (realSectionEquiv_naturality r.right a)).symm))

/-- Every compatible family on the evaluated diagram identifies equal ordinary
points, using a zero-dimensional ordinary overlap test. -/
theorem realCocone_identifies (K : Multicofork A.realDiagram)
    (i j : A.Index) (x : Points (A.domain i)) (y : Points (A.domain j))
    (h : A.coordinate i x = A.coordinate j y) :
    K.π i ((realSectionEquiv _).symm x) = K.π j ((realSectionEquiv _).symm y) := by
  let D : Domain := ⟨0, 1⟩
  let z : Points D := ⟨Fin.elim0, one_ne_zero⟩
  let r : A.Relation := ⟨i, j, D, constantMap D _ x, constantMap D _ y, fun _ => h⟩
  have he := ConcreteCategory.congr_hom (K.condition r) ((realSectionEquiv D).symm z)
  have hl : realSections.map (embedding.map r.left) ((realSectionEquiv D).symm z) =
      (realSectionEquiv _).symm x := by
    apply (realSectionEquiv _).injective
    rw [realSectionEquiv_naturality, Equiv.apply_symm_apply]
    exact ((realSectionEquiv _).apply_symm_apply x).symm
  have hr : realSections.map (embedding.map r.right) ((realSectionEquiv D).symm z) =
      (realSectionEquiv _).symm y := by
    apply (realSectionEquiv _).injective
    rw [realSectionEquiv_naturality, Equiv.apply_symm_apply]
    exact ((realSectionEquiv _).apply_symm_apply y).symm
  change K.π i (realSections.map (embedding.map r.left) _) =
    K.π j (realSections.map (embedding.map r.right) _) at he
  rwa [hl, hr] at he

variable (hc : ∀ x, ∃ i y, A.coordinate i y = x)

def realCoconeIsColimit : IsColimit A.realCocone := by
  let pick (x : M) := (hc x).choose
  let value (x : M) := (hc x).choose_spec.choose
  have hv (x : M) : A.coordinate (pick x) (value x) = x := (hc x).choose_spec.choose_spec
  apply Multicofork.IsColimit.mk A.realCocone
    (fun K => TypeCat.ofHom (fun x => K.π (pick x) ((realSectionEquiv _).symm (value x))))
  · intro K i
    ext a
    change K.π (pick (A.coordinate i (realSectionEquiv _ a)))
      ((realSectionEquiv _).symm (value (A.coordinate i (realSectionEquiv _ a)))) = K.π i a
    exact (A.realCocone_identifies K _ i _ (realSectionEquiv _ a) (hv _)).trans
      (congrArg (fun z => K.π i z) ((realSectionEquiv _).symm_apply_apply a))
  · intro K f hf
    ext x
    have he := ConcreteCategory.congr_hom (hf (pick x)) ((realSectionEquiv _).symm (value x))
    change f (A.coordinate (pick x) (realSectionEquiv _ ((realSectionEquiv _).symm (value x)))) = _ at he
    rw [Equiv.apply_symm_apply] at he
    exact (congrArg (fun z : M => f z) (hv x).symm).trans he

def realDiagramIso : A.realDiagram.multispan ≅ A.diagram.multispan ⋙ realSections :=
  NatIso.ofComponents (fun j => by cases j <;> exact Iso.refl _) (by
    intro j k f
    cases f with
    | id j =>
      rw [WalkingMultispan.Hom.id_eq_id, A.realDiagram.multispan.map_id,
        (A.diagram.multispan ⋙ realSections).map_id, Category.id_comp, Category.comp_id]
    | fst r =>
      change realSections.map (embedding.map r.left) ≫ 𝟙 _ =
        𝟙 _ ≫ realSections.map (embedding.map r.left)
      rw [Category.id_comp, Category.comp_id]
    | snd r =>
      change realSections.map (embedding.map r.right) ≫ 𝟙 _ =
        𝟙 _ ≫ realSections.map (embedding.map r.right)
      rw [Category.id_comp, Category.comp_id])

/-- The evaluated sheaf colimit is still a colimit at the real stage. -/
def evaluatedCocone : Multicofork A.realDiagram :=
  (Cocone.precompose A.realDiagramIso.hom).obj
    (realSections.mapCocone (Multicoequalizer.multicofork A.diagram))

def evaluatedCoconeIsColimit : IsColimit A.evaluatedCocone :=
  (IsColimit.precomposeHomEquiv A.realDiagramIso _).symm
    (isColimitOfPreserves realSections (colimit.isColimit A.diagram.multispan))

/-- Real sections of any covering chart presentation are exactly its ordinary
points. The conclusion is confined to the real stage. -/
def realEquiv : realSections.obj A.realization ≃ M :=
  (A.evaluatedCoconeIsColimit.coconePointUniqueUpToIso (A.realCoconeIsColimit hc)).toEquiv

theorem realEquiv_chart (i : A.Index) (a : realSections.obj (embedding.obj (A.domain i))) :
    A.realEquiv hc (realSections.map (A.chart i) a) = A.coordinate i (realSectionEquiv _ a) :=
  ConcreteCategory.congr_hom
    (A.evaluatedCoconeIsColimit.comp_coconePointUniqueUpToIso_hom
      (A.realCoconeIsColimit hc) (WalkingMultispan.right i)) a

end Charts
end SquareKit.EuclideanOpen
