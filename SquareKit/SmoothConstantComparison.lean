import SquareKit.SmoothConstantOrdinary
import Mathlib.Topology.LocallyConstant.Algebra

/-! Ordinary-open sections of the sheafified constant group, with their actual
point-label comparison. The inverse glues constants on open label fibers. -/
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
noncomputable section
open CategoryTheory Opposite
open scoped ContDiff
namespace SquareKit.EuclideanOpen
open SmoothAlgebra

/-- Empty ordinary domains are initial against every sheaf, by the empty cover. -/
theorem empty_domain_hom_ext (U : Domain) (hU : IsEmpty (Points U))
    (F : Sheaf SmoothOpenSite.topology Type) (a b : embedding.obj U ⟶ F) : a = b := by
  apply cover_jointly_epic U (fun i : Fin 0 => Fin.elim0 i)
    ((empty_cover_iff U _).mpr hU) F a b
  exact fun i => Fin.elim0 i

/-- The intersection with an ambient principal open maps into that open. -/
def principalRight (U : Domain) (q : Free U.dimension) :
    subdomain U q ⟶ (⟨U.dimension, q⟩ : Domain) where
  toFun x := ⟨x.val, right_ne_zero_of_mul x.property⟩
  smooth i := (OpenFunctions.representative_iff _ (fun x => x i) (fun _ => rfl)).mpr
    (contDiff_apply ℝ (fun _ : Fin U.dimension => ℝ) i).contDiffOn

end SquareKit.EuclideanOpen
namespace SquareKit.SmoothOpenSite
open SmoothAlgebra SmoothPresentationSite EuclideanOpen
variable (G : Type) [Group G]

/-- Equality of these particular sections is detected by ordinary points.
The proof uses local constant representatives, not point detection for arbitrary sheaves. -/
theorem ordinaryLabel_injective (U : Domain) : Function.Injective (ordinaryLabel G U) := by
  intro a b hab
  let S := Presheaf.imageSieve (constantLabel G) a ⊓ Presheaf.imageSieve (constantLabel G) b
  have hS : S ∈ topology (toSite.obj U) := topology.intersection_covering
    (Presheaf.imageSieve_mem topology (constantLabel G) a)
    (Presheaf.imageSieve_mem topology (constantLabel G) b)
  have loc (x : Points U) := covering_local_inclusion S hS U (𝟙 _) x
  choose q u hu hy hs using loc
  choose y hy using hy
  let v (x : Points U) := principalRight U (q x)
  have square (x : Points U) : v x ≫ u x = subInclusion U (q x) := by
    apply OpenFunctions.Map.ext
    intro z
    exact Subtype.ext (hu x ((show Map _ _ from v x) z))
  have hc : Covers U q := by
    intro x
    refine ⟨x, ?_⟩
    have he := congrArg Subtype.val (hy x)
    rw [hu] at he
    exact he ▸ (y x).property
  apply topology.yonedaEquiv.symm.injective
  apply cover_jointly_epic U q hc (locallyConstantGroupSheaf G)
  intro x
  apply topology.yonedaEquiv.injective
  change topology.yonedaEquiv (topology.yoneda.map (toSite.map (subInclusion U (q x))) ≫ topology.yonedaEquiv.symm a) =
    topology.yonedaEquiv (topology.yoneda.map (toSite.map (subInclusion U (q x))) ≫ topology.yonedaEquiv.symm b)
  rw [← topology.yonedaEquiv_naturality, ← topology.yonedaEquiv_naturality,
    Equiv.apply_symm_apply, Equiv.apply_symm_apply]
  obtain ⟨k, hk⟩ := (hs x).1
  obtain ⟨l, hl⟩ := (hs x).2
  have hk' : (locallyConstantGroupSheaf G).obj.map (toSite.map (u x)).op a =
      (constantLabel G).app _ k := by
    change (locallyConstantGroup G).obj.map (toSite.map (u x)).op a = _
    simpa only [Category.comp_id] using hk.symm
  have hl' : (locallyConstantGroupSheaf G).obj.map (toSite.map (u x)).op b =
      (constantLabel G).app _ l := by
    change (locallyConstantGroup G).obj.map (toSite.map (u x)).op b = _
    simpa only [Category.comp_id] using hl.symm
  have he : k = l := by
    have h := congrFun hab x
    rw [← hy x, ← ordinaryLabel_natural G (u x) a (y x),
      ← ordinaryLabel_natural G (u x) b (y x), hk', hl',
      ordinaryLabel_constant, ordinaryLabel_constant] at h
    exact h
  rw [← square x, toSite.map_comp, op_comp, Functor.map_comp]
  change (locallyConstantGroupSheaf G).obj.map (toSite.map (v x)).op
      ((locallyConstantGroupSheaf G).obj.map (toSite.map (u x)).op a) =
    (locallyConstantGroupSheaf G).obj.map (toSite.map (v x)).op
      ((locallyConstantGroupSheaf G).obj.map (toSite.map (u x)).op b)
  rw [hk', hl', he]

/-- Principal descriptions supplied for the fibers of an independent point label.
Coverage and compatible constant labels are derived from this local contract. -/
structure PrincipalLabelData (U : Domain) (l : LocallyConstant (Points U) G) where
  defining : G → Free U.dimension
  fiber_iff : ∀ k (x : Points U), (defining k).val x.val ≠ 0 ↔ l x = k

namespace PrincipalLabelData
variable {G} {U : Domain} {l : LocallyConstant (Points U) G}

theorem covers (d : PrincipalLabelData G U l) :
    Covers U d.defining := fun x =>
  ⟨l x, (d.fiber_iff (l x) x).mpr rfl⟩

def localLabel (d : PrincipalLabelData G U l) (k : G) :
    embedding.obj (subdomain U (d.defining k)) ⟶ locallyConstantGroupSheaf G :=
  constantSection _ k

theorem compatible (d : PrincipalLabelData G U l) (i j : G) :
    embedding.map (overlapLeft U (d.defining i) (d.defining j)) ≫ d.localLabel i =
    embedding.map (overlapRight U (d.defining i) (d.defining j)) ≫ d.localLabel j := by
  by_cases h : i = j
  · subst j
    rfl
  · apply empty_domain_hom_ext
    refine ⟨fun x => h ?_⟩
    let y : Points U := ⟨x.val, left_ne_zero_of_mul (left_ne_zero_of_mul x.property)⟩
    have hi := (d.fiber_iff i y).mp
      (right_ne_zero_of_mul (left_ne_zero_of_mul x.property))
    have hj := (d.fiber_iff j y).mp (right_ne_zero_of_mul x.property)
    exact hi.symm.trans hj

/-- Gluing the constant section on each label fiber. -/
def gluedSection (d : PrincipalLabelData G U l) :
    (locallyConstantGroupSheaf G).obj.obj (op (toSite.obj U)) :=
  topology.yonedaEquiv ((sheaf_exists_unique U d.defining d.covers
    _ d.localLabel d.compatible).choose)

theorem restrict (d : PrincipalLabelData G U l) (k : G) :
    (locallyConstantGroupSheaf G).obj.map (toSite.map (subInclusion U (d.defining k))).op
      d.gluedSection = (constantLabel G).app _ k := by
  exact (topology.yonedaEquiv_naturality _ _).trans
    (congrArg topology.yonedaEquiv ((sheaf_exists_unique U d.defining
      d.covers _ d.localLabel d.compatible).choose_spec.1 k))

theorem label_section (d : PrincipalLabelData G U l) (x : Points U) :
    ordinaryLabel G U d.gluedSection x = l x := by
  let y : Points (subdomain U (d.defining (l x))) :=
    ⟨x.val, mul_ne_zero x.property ((d.fiber_iff (l x) x).mpr rfl)⟩
  have hy : (show Map _ _ from subInclusion U (d.defining (l x))) y = x := rfl
  rw [← hy, ← ordinaryLabel_natural, restrict, ordinaryLabel_constant]
  rfl

/-- Uniqueness uses point detection for this particular sheaf. -/
theorem unique (d : PrincipalLabelData G U l)
    (a : (locallyConstantGroupSheaf G).obj.obj (op (toSite.obj U)))
    (ha : ∀ x, ordinaryLabel G U a x = l x) : a = d.gluedSection :=
  ordinaryLabel_injective G U (funext (fun x => (ha x).trans (d.label_section x).symm))

theorem independent (d e : PrincipalLabelData G U l) : d.gluedSection = e.gluedSection :=
  e.unique _ d.label_section

end PrincipalLabelData

/-- A label fiber is an ordinary principal open. -/
def labelDefining (U : Domain) (l : LocallyConstant (Points U) G) (k : G) :
    Free U.dimension :=
  openDefining (Subtype.val '' {x : Points U | l x = k})
    ((domain_open U).isOpenMap_subtype_val _ (l.isLocallyConstant.isOpen_fiber k))

omit [Group G] in
theorem labelDefining_iff (U : Domain) (l : LocallyConstant (Points U) G)
    (k : G) (x : Points U) : (labelDefining G U l k).val x.val ≠ 0 ↔ l x = k := by
  change x.val ∈ Localization.locus (openDefining _ _) ↔ _
  rw [openDefining_locus]
  constructor
  · rintro ⟨y, hy, he⟩
    exact (Subtype.ext he : y = x) ▸ hy
  · intro hx
    exact ⟨x, hx, rfl⟩

/-- The classical selector supplies an instance of the explicit-data API. -/
def selectedPrincipalLabelData (U : Domain) (l : LocallyConstant (Points U) G) :
    PrincipalLabelData G U l := ⟨labelDefining G U l, labelDefining_iff G U l⟩

theorem label_covers (U : Domain) (l : LocallyConstant (Points U) G) :
    Covers U (labelDefining G U l) := (selectedPrincipalLabelData G U l).covers

def fiberLabel (U : Domain) (l : LocallyConstant (Points U) G) (k : G) :
    embedding.obj (subdomain U (labelDefining G U l k)) ⟶ locallyConstantGroupSheaf G :=
  (selectedPrincipalLabelData G U l).localLabel k

theorem fiberLabel_compatible (U : Domain) (l : LocallyConstant (Points U) G) (i j : G) :
    embedding.map (overlapLeft U (labelDefining G U l i) (labelDefining G U l j)) ≫ fiberLabel G U l i =
    embedding.map (overlapRight U (labelDefining G U l i) (labelDefining G U l j)) ≫ fiberLabel G U l j :=
  (selectedPrincipalLabelData G U l).compatible i j

/-- Gluing the constant section on each label fiber. -/
def ofOrdinaryLocallyConstant (U : Domain) (l : LocallyConstant (Points U) G) :
    (locallyConstantGroupSheaf G).obj.obj (op (toSite.obj U)) :=
  (selectedPrincipalLabelData G U l).gluedSection

theorem ofOrdinaryLocallyConstant_restrict (U : Domain) (l : LocallyConstant (Points U) G) (k : G) :
    (locallyConstantGroupSheaf G).obj.map (toSite.map (subInclusion U (labelDefining G U l k))).op
      (ofOrdinaryLocallyConstant G U l) = (constantLabel G).app _ k :=
  (selectedPrincipalLabelData G U l).restrict k

theorem ordinaryLabel_ofOrdinaryLocallyConstant (U : Domain)
    (l : LocallyConstant (Points U) G) (x : Points U) :
    ordinaryLabel G U (ofOrdinaryLocallyConstant G U l) x = l x := by
  let y : Points (subdomain U (labelDefining G U l (l x))) :=
    ⟨x.val, mul_ne_zero x.property ((labelDefining_iff G U l (l x) x).mpr rfl)⟩
  have hy : (show Map _ _ from subInclusion U (labelDefining G U l (l x))) y = x := rfl
  rw [← hy, ← ordinaryLabel_natural, ofOrdinaryLocallyConstant_restrict, ordinaryLabel_constant]
  rfl

theorem PrincipalLabelData.eq_ofOrdinaryLocallyConstant {U : Domain}
    {l : LocallyConstant (Points U) G} (d : PrincipalLabelData G U l) :
    d.gluedSection = ofOrdinaryLocallyConstant G U l :=
  d.independent (selectedPrincipalLabelData G U l)

/-- The actual point-label map is an equivalence on every ordinary domain. -/
def ordinaryLocallyConstantEquiv (U : Domain) :
    (locallyConstantGroupSheaf G).obj.obj (op (toSite.obj U)) ≃ LocallyConstant (Points U) G where
  toFun := ordinaryLocallyConstant G U
  invFun := ofOrdinaryLocallyConstant G U
  left_inv _a := ordinaryLabel_injective G U (funext (ordinaryLabel_ofOrdinaryLocallyConstant G U _))
  right_inv l := DFunLike.ext _ _ (ordinaryLabel_ofOrdinaryLocallyConstant G U l)

@[simp] theorem ordinaryLocallyConstantEquiv_apply (U : Domain)
    (a : (locallyConstantGroupSheaf G).obj.obj (op (toSite.obj U))) :
    ordinaryLocallyConstantEquiv G U a = ordinaryLocallyConstant G U a := rfl

/-- Naturality includes every admitted smooth ordinary map. -/
theorem ordinaryLocallyConstantEquiv_natural {U V : Domain} (f : U ⟶ V)
    (a : (locallyConstantGroupSheaf G).obj.obj (op (toSite.obj V))) :
    ordinaryLocallyConstantEquiv G U ((locallyConstantGroupSheaf G).obj.map (toSite.map f).op a) =
      (ordinaryLocallyConstantEquiv G V a).comap ⟨(show Map _ _ from f), map_continuous f⟩ := by
  exact DFunLike.ext _ _ (ordinaryLabel_natural G f a)

theorem ofOrdinaryLocallyConstant_natural {U V : Domain} (f : U ⟶ V)
    (l : LocallyConstant (Points V) G) :
    (locallyConstantGroupSheaf G).obj.map (toSite.map f).op (ofOrdinaryLocallyConstant G V l) =
      ofOrdinaryLocallyConstant G U (l.comap ⟨(show Map _ _ from f), map_continuous f⟩) := by
  apply (ordinaryLocallyConstantEquiv G U).injective
  rw [ordinaryLocallyConstantEquiv_natural]
  exact congrArg (fun t => t.comap ⟨(show Map _ _ from f), map_continuous f⟩)
    ((ordinaryLocallyConstantEquiv G V).apply_symm_apply l) |>.trans
      ((ordinaryLocallyConstantEquiv G U).apply_symm_apply _).symm

theorem ordinaryLocallyConstantEquiv_mul (U : Domain)
    (a b : (locallyConstantGroup G).obj.obj (op (toSite.obj U))) :
    ordinaryLocallyConstantEquiv G U (a * b) =
      ordinaryLocallyConstantEquiv G U a * ordinaryLocallyConstantEquiv G U b :=
  DFunLike.ext _ _ (ordinaryLabel_mul G U a b)

/-- Supplied descriptions can be chosen independently after restriction. -/
theorem PrincipalLabelData.natural {U V : Domain} (f : U ⟶ V)
    {l : LocallyConstant (Points V) G} (d : PrincipalLabelData G V l)
    (e : PrincipalLabelData G U (l.comap ⟨(show Map _ _ from f), map_continuous f⟩)) :
    (locallyConstantGroupSheaf G).obj.map (toSite.map f).op d.gluedSection = e.gluedSection := by
  rw [d.eq_ofOrdinaryLocallyConstant, e.eq_ofOrdinaryLocallyConstant]
  exact ofOrdinaryLocallyConstant_natural G f l

/-- Multiplication compares global sections, with independent data for each label. -/
theorem PrincipalLabelData.mul {U : Domain} {l m : LocallyConstant (Points U) G}
    (d : PrincipalLabelData G U l) (e : PrincipalLabelData G U m)
    (p : PrincipalLabelData G U (l * m)) :
    (show (locallyConstantGroup G).obj.obj (op (toSite.obj U)) from d.gluedSection) *
      (show (locallyConstantGroup G).obj.obj (op (toSite.obj U)) from e.gluedSection) =
      p.gluedSection := by
  apply p.unique
  intro x
  rw [ordinaryLabel_mul, d.label_section, e.label_section]
  rfl

/-- Empty-domain sections agree, including their non-real restrictions. -/
theorem ordinary_empty_section_unique (U : Domain) [IsEmpty (Points U)]
    (a b : (locallyConstantGroupSheaf G).obj.obj (op (toSite.obj U))) : a = b :=
  ordinaryLabel_injective G U (funext (fun x => isEmptyElim x))

/-- Yoneda followed by the designated ordinary section comparison. -/
def ordinaryHomLabelEquiv (U : Domain) :
    (embedding.obj U ⟶ locallyConstantGroupSheaf G) ≃ LocallyConstant (Points U) G :=
  topology.yonedaEquiv.trans (ordinaryLocallyConstantEquiv G U)

theorem ordinaryHomLabelEquiv_constant (U : Domain) (k : G) (x : Points U) :
    ordinaryHomLabelEquiv G U (constantSection _ k) x = k := ordinaryLabel_constant G U k x

theorem ordinaryHomLabelEquiv_natural {U V : Domain} (f : U ⟶ V)
    (g : embedding.obj V ⟶ locallyConstantGroupSheaf G) (x : Points U) :
    ordinaryHomLabelEquiv G U (embedding.map f ≫ g) x =
      ordinaryHomLabelEquiv G V g ((show Map _ _ from f) x) := by
  change ordinaryLabel G U (topology.yonedaEquiv (topology.yoneda.map (toSite.map f) ≫ g)) x = _
  rw [← topology.yonedaEquiv_naturality]
  exact ordinaryLabel_natural G f _ x

end SquareKit.SmoothOpenSite
