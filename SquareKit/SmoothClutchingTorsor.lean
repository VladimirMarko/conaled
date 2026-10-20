import Mathlib.CategoryTheory.Monoidal.Closed.FunctorToTypes
import Mathlib.CategoryTheory.Monoidal.Closed.Cartesian
import SquareKit.SmoothConstantOrdinary
import SquareKit.SheafTorsorLocal
import SquareKit.SheafRelation
import SquareKit.SheafPushoutLocal
import SquareKit.SmoothOpenSheafDescent
import Mathlib.CategoryTheory.Sites.LeftExact
import Mathlib.CategoryTheory.Sites.CartesianClosed

/-! Two-chart clutching on the actual smooth sheaf topos. -/
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
open CategoryTheory CategoryTheory.Limits Opposite
open scoped ContDiff
namespace SquareKit.SmoothClutching
open EuclideanOpen SmoothOpenSite SmoothAlgebra SmoothPresentationSite

abbrev line : Domain := full 1
abbrev punctured : Domain := subdomain line (generator 0)
abbrev lineSheaf := embedding.obj line
abbrev puncturedSheaf := embedding.obj punctured
abbrev inclusion : puncturedSheaf ⟶ lineSheaf := embedding.map (subInclusion line (generator 0))

instance inclusion_mono : Mono inclusion := by
  apply (sheafToPresheaf SmoothOpenSite.topology Type).mono_of_mono_map
  have : ∀ A, Mono (((sheafToPresheaf SmoothOpenSite.topology Type).map inclusion).app A) := fun A => by
    apply (CategoryTheory.mono_iff_injective _).mpr
    intro a b h
    apply Quiver.Hom.unop_inj
    apply Localization.sub_unique line.defining (generator 0)
    rw [← nested_pullback]
    exact congrArg Quiver.Hom.unop h
  exact NatTrans.mono_of_mono_app _

/-- The doubled-origin line is the sheaf pushout, so its sections include
all local gluings, rather than only globally selected charts. -/
def base := pushout inclusion inclusion
abbrev left : lineSheaf ⟶ base := pushout.inl _ _
abbrev right : lineSheaf ⟶ base := pushout.inr _ _

theorem overlap : IsPullback inclusion inclusion left right :=
  Adhesive.isPullback_of_isPushout_of_mono_left (IsPushout.of_hasPushout inclusion inclusion)

instance left_mono : Mono left :=
  Adhesive.mono_of_isPushout_of_mono_right (IsPushout.of_hasPushout inclusion inclusion)
instance right_mono : Mono right :=
  Adhesive.mono_of_isPushout_of_mono_left (IsPushout.of_hasPushout inclusion inclusion)


def signOpen (b : Bool) : Set (Fin 1 → ℝ) :=
  if b then {x | 0 < x 0} else {x | x 0 < 0}

theorem signOpen_open (b : Bool) : IsOpen (signOpen b) := by
  cases b <;> simp only [signOpen, Bool.false_eq_true, ↓reduceIte]
  · exact isOpen_lt (continuous_apply 0) continuous_const
  · exact isOpen_lt continuous_const (continuous_apply 0)

def signDefining (b : Bool) : Free 1 := openDefining (signOpen b) (signOpen_open b)

theorem signDefining_iff (b : Bool) (x : Fin 1 → ℝ) :
    (signDefining b).val x ≠ 0 ↔ x ∈ signOpen b := by
  change x ∈ Localization.locus (signDefining b) ↔ _
  rw [signDefining, openDefining_locus]

theorem sign_covers : Covers punctured signDefining := by
  intro x
  have hx : x.val 0 ≠ 0 := by
    have hx := x.property
    change (1 : ℝ) * x.val 0 ≠ 0 at hx
    simpa only [one_mul] using hx
  rcases lt_or_gt_of_ne hx with h | h
  · exact ⟨false, (signDefining_iff false x.val).mpr h⟩
  · exact ⟨true, (signDefining_iff true x.val).mpr h⟩

/-- Arrows from an empty ordinary open into any sheaf agree by the empty
cover, including stages with nilpotents. -/
theorem empty_hom_ext (U : Domain) (hU : IsEmpty (Points U))
    (F : Sheaf SmoothOpenSite.topology Type) (a b : embedding.obj U ⟶ F) : a = b := by
  apply cover_jointly_epic U (fun i : Fin 0 => Fin.elim0 i)
    ((empty_cover_iff U _).mpr hU) F a b
  exact fun i => Fin.elim0 i

variable (G : Type) [Group G] (c : G)

def localLabel (b : Bool) : embedding.obj (subdomain punctured (signDefining b)) ⟶
    locallyConstantGroupSheaf G :=
  constantSection _ (if b then c else 1)

theorem localLabel_compatible (i j : Bool) :
    embedding.map (overlapLeft punctured (signDefining i) (signDefining j)) ≫ localLabel G c i =
    embedding.map (overlapRight punctured (signDefining i) (signDefining j)) ≫ localLabel G c j := by
  by_cases h : i = j
  · subst j
    rfl
  · apply empty_hom_ext
    refine ⟨fun x => ?_⟩
    have hi := (signDefining_iff i x.val).mp
      (right_ne_zero_of_mul (left_ne_zero_of_mul x.property))
    have hj := (signDefining_iff j x.val).mp (right_ne_zero_of_mul x.property)
    cases i <;> cases j <;> simp_all [signOpen]
    all_goals linarith

/-- The transition is glued in the sheaf category from different labels on
the two components of the punctured line. -/
def transition : puncturedSheaf ⟶ locallyConstantGroupSheaf G :=
  (sheaf_exists_unique punctured signDefining sign_covers _ (localLabel G c)
    (localLabel_compatible G c)).choose

theorem transition_restrict (b : Bool) :
    embedding.map (subInclusion punctured (signDefining b)) ≫ transition G c = localLabel G c b :=
  (sheaf_exists_unique punctured signDefining sign_covers _ (localLabel G c)
    (localLabel_compatible G c)).choose_spec.1 b


/-- Multiplication of section-valued arrows uses the constructed group sheaf. -/
def multiply {X : Sheaf SmoothOpenSite.topology Type}
    (a b : X ⟶ locallyConstantGroupSheaf G) : X ⟶ locallyConstantGroupSheaf G := ⟨{
  app U := ↾fun x => (show (locallyConstantGroup G).obj.obj U from a.hom.app U x) *
    (show (locallyConstantGroup G).obj.obj U from b.hom.app U x)
  naturality U V f := by
    ext x
    symm
    change (locallyConstantGroup G).obj.map f ((show (locallyConstantGroup G).obj.obj U from a.hom.app U x) * (show (locallyConstantGroup G).obj.obj U from b.hom.app U x)) = _
    rw [((locallyConstantGroup G).obj.map f).hom.map_mul]
    exact congrArg₂ (· * ·) (NatTrans.naturality_apply a.hom f x).symm
      (NatTrans.naturality_apply b.hom f x).symm }⟩

theorem multiply_comp {X Y : Sheaf SmoothOpenSite.topology Type}
    (f : X ⟶ Y) (a b : Y ⟶ locallyConstantGroupSheaf G) :
    f ≫ multiply G a b = multiply G (f ≫ a) (f ≫ b) := rfl

def inverse {X : Sheaf SmoothOpenSite.topology Type}
    (a : X ⟶ locallyConstantGroupSheaf G) : X ⟶ locallyConstantGroupSheaf G := ⟨{
  app U := ↾fun x => (fun z : (locallyConstantGroup G).obj.obj U => z⁻¹) (a.hom.app U x)
  naturality U V f := by
    ext x
    symm
    change (locallyConstantGroup G).obj.map f
      (show (locallyConstantGroup G).obj.obj U from a.hom.app U x)⁻¹ = _
    rw [((locallyConstantGroup G).obj.map f).hom.map_inv]
    exact congrArg Inv.inv (NatTrans.naturality_apply a.hom f x).symm }⟩

theorem multiply_inverse_cancel {X : Sheaf SmoothOpenSite.topology Type}
    (a b : X ⟶ locallyConstantGroupSheaf G) :
    multiply G (multiply G a (inverse G b)) b = a := by
  ext U x
  exact inv_mul_cancel_right (show (locallyConstantGroup G).obj.obj U from a.hom.app U x)
    (show (locallyConstantGroup G).obj.obj U from b.hom.app U x)

theorem multiply_cancel_inverse {X : Sheaf SmoothOpenSite.topology Type}
    (a b : X ⟶ locallyConstantGroupSheaf G) :
    multiply G (multiply G a b) (inverse G b) = a := by
  ext U x
  exact mul_inv_cancel_right (show (locallyConstantGroup G).obj.obj U from a.hom.app U x)
    (show (locallyConstantGroup G).obj.obj U from b.hom.app U x)

theorem multiply_right_cancel {X : Sheaf SmoothOpenSite.topology Type}
    (a b d : X ⟶ locallyConstantGroupSheaf G)
    (h : multiply G a d = multiply G b d) : a = b := by
  ext U x
  apply @mul_right_cancel ((locallyConstantGroup G).obj.obj U) _ _ _
    (show (locallyConstantGroup G).obj.obj U from d.hom.app U x)
  exact (congrArg (fun k : X ⟶ locallyConstantGroupSheaf G =>
    k.hom.app U x) h)

abbrev totalLine := prod lineSheaf (locallyConstantGroupSheaf G)
abbrev totalOverlap := prod puncturedSheaf (locallyConstantGroupSheaf G)
abbrev overlapProjection : totalOverlap G ⟶ puncturedSheaf := prod.fst
abbrev lineProjection : totalLine G ⟶ lineSheaf := prod.fst

/-- Untwisted and twisted inclusions of the overlap in the two local regular
torsors. Multiplication is on the right to preserve the left regular action. -/
def totalLeft : totalOverlap G ⟶ totalLine G := prod.map inclusion (𝟙 _)
def totalRight : totalOverlap G ⟶ totalLine G :=
  prod.lift (overlapProjection G ≫ inclusion)
    (multiply G prod.snd (overlapProjection G ≫ transition G c))


theorem left_pullback : IsPullback (totalLeft G) (overlapProjection G)
    (lineProjection G) inclusion := (IsPullback.of_prod_fst_with_id inclusion _).flip

theorem right_pullback : IsPullback (totalRight G c) (overlapProjection G)
    (lineProjection G) inclusion where
  w := by simp [totalRight]
  isLimit' := ⟨PullbackCone.isLimitAux' _ (fun s => by
    refine ⟨prod.lift s.snd (multiply G (s.fst ≫ prod.snd)
      (inverse G (s.snd ≫ transition G c))), ?_, ?_, ?_⟩
    · change prod.lift _ _ ≫ totalRight G c = s.fst
      apply prod.hom_ext
      · simp [totalRight, ← s.condition]
      · simp only [totalRight, Category.assoc, prod.lift_snd,
          multiply_comp, prod.lift_fst_assoc]
        exact multiply_inverse_cancel G _ _
    · simp
    · intro m h₁ h₂
      change m ≫ totalRight G c = s.fst at h₁
      change m ≫ overlapProjection G = s.snd at h₂
      apply prod.hom_ext
      · simpa using h₂
      · simp only [prod.lift_snd]
        have h := congrArg (fun k => k ≫ (prod.snd : totalLine G ⟶ _)) h₁
        simp only [totalRight, Category.assoc, prod.lift_snd, multiply_comp] at h
        rw [← Category.assoc, h₂] at h
        rw [← h]
        exact (multiply_cancel_inverse G _ _).symm)⟩

/-- The actual total sheaf is formed by gluing the two regular torsors. -/
def total := pushout (totalLeft G) (totalRight G c)
abbrev totalChartLeft : totalLine G ⟶ total G c := pushout.inl _ _
abbrev totalChartRight : totalLine G ⟶ total G c := pushout.inr _ _

def projection : total G c ⟶ base :=
  pushout.desc (lineProjection G ≫ left) (lineProjection G ≫ right) (by
    change totalLeft G ≫ prod.fst ≫ left = totalRight G c ≫ prod.fst ≫ right
    simp only [totalLeft, totalRight, prod.map_fst_assoc, prod.lift_fst_assoc,
      Category.assoc]
    exact congrArg (fun k => overlapProjection G ≫ k)
      (pushout.condition (f := inclusion) (g := inclusion)))


/-- Each chart pulls the constructed display map back to the genuine product
with the locally constant group sheaf. This is effective gluing in sheaves. -/
theorem localTrivial :
    IsPullback (totalChartLeft G c) (lineProjection G) (projection G c) left ∧
    IsPullback (totalChartRight G c) (lineProjection G) (projection G c) right := by
  apply (Adhesive.van_kampen (IsPushout.of_hasPushout inclusion inclusion)
    (totalLeft G) (totalRight G c) (totalChartLeft G c) (totalChartRight G c)
    (overlapProjection G) (lineProjection G) (lineProjection G) (projection G c)
    (left_pullback G) (right_pullback G c) ?_ ?_ ?_).mp
  · exact IsPushout.of_hasPushout _ _
  · exact ⟨pushout.inl_desc _ _ _⟩
  · exact ⟨pushout.inr_desc _ _ _⟩
  · exact ⟨pushout.condition⟩


instance totalLeft_mono : Mono (totalLeft G) := by
  dsimp [totalLeft]
  infer_instance

instance totalChartRight_mono : Mono (totalChartRight G c) :=
  Adhesive.mono_of_isPushout_of_mono_left
    (IsPushout.of_hasPushout (totalLeft G) (totalRight G c))

/-- Any global section would give chartwise labels satisfying the genuine
clutching equation on the punctured-line sheaf. -/
theorem section_labels (s : base ⟶ total G c) (hs : s ≫ projection G c = 𝟙 _) :
    ∃ a b : lineSheaf ⟶ locallyConstantGroupSheaf G,
      multiply G (inclusion ≫ a) (transition G c) = inclusion ≫ b := by
  let pl := (localTrivial G c).1
  let pr := (localTrivial G c).2
  let l := pl.lift (left ≫ s) (𝟙 _) (by simp [Category.assoc, hs])
  let r := pr.lift (right ≫ s) (𝟙 _) (by simp [Category.assoc, hs])
  have hl : l ≫ lineProjection G = 𝟙 _ := pl.lift_snd _ _ _
  have hr : r ≫ lineProjection G = 𝟙 _ := pr.lift_snd _ _ _
  have hlt : l ≫ totalChartLeft G c = left ≫ s := pl.lift_fst _ _ _
  have hrt : r ≫ totalChartRight G c = right ≫ s := pr.lift_fst _ _ _
  let v : puncturedSheaf ⟶ totalOverlap G := prod.lift (𝟙 _) (inclusion ≫ l ≫ prod.snd)
  have hv : v ≫ totalLeft G = inclusion ≫ l := by
    apply prod.hom_ext
    · simp only [v, totalLeft, prod.map_fst, prod.lift_fst_assoc, Category.id_comp,
        Category.assoc, hl, Category.comp_id]
    · simp [v, totalLeft]
  have hv' : v ≫ totalRight G c = inclusion ≫ r := by
    apply (cancel_mono (totalChartRight G c)).mp
    calc
      (v ≫ totalRight G c) ≫ totalChartRight G c =
          (v ≫ totalLeft G) ≫ totalChartLeft G c := by
        simpa only [total, totalChartLeft, totalChartRight, Category.assoc] using congrArg (fun k => v ≫ k)
          (pushout.condition (f := totalLeft G) (g := totalRight G c)).symm
      _ = inclusion ≫ left ≫ s := by rw [hv, Category.assoc, hlt]
      _ = inclusion ≫ right ≫ s := by
        rw [← Category.assoc, ← Category.assoc]
        exact congrArg (fun k => k ≫ s)
          (pushout.condition (f := inclusion) (g := inclusion))
      _ = (inclusion ≫ r) ≫ totalChartRight G c := by rw [Category.assoc, hrt]
  refine ⟨l ≫ prod.snd, r ≫ prod.snd, ?_⟩
  have h := congrArg (fun k => k ≫ (prod.snd : totalLine G ⟶ _)) hv'
  simpa only [totalRight, Category.assoc, prod.lift_snd, multiply_comp, v,
    prod.lift_snd, prod.lift_fst_assoc, Category.id_comp] using h


def labelAt {U : Domain} (h : embedding.obj U ⟶ locallyConstantGroupSheaf G)
    (x : Points U) : G :=
  (constantLabelRealEquiv G).symm (h.hom.app (op (op (free 0))) (ordinaryPoint U x))

theorem labelAt_eq_ordinary {U : Domain} (h : embedding.obj U ⟶ locallyConstantGroupSheaf G)
    (x : Points U) : labelAt G h x =
    ordinaryLabel G U (SmoothOpenSite.topology.yonedaEquiv h) x := by
  unfold labelAt ordinaryLabel
  congr 1
  exact (SmoothOpenSite.topology.yonedaEquiv_naturality h (ordinaryPoint U x)).symm

theorem labelAt_comp {U V : Domain} (f : U ⟶ V)
    (h : embedding.obj V ⟶ locallyConstantGroupSheaf G) (x : Points U) :
    labelAt G (embedding.map f ≫ h) x = labelAt G h ((show Map _ _ from f) x) := by
  rw [labelAt_eq_ordinary, labelAt_eq_ordinary]
  have hn := SmoothOpenSite.topology.yonedaEquiv_naturality h (toSite.map f)
  change (locallyConstantGroupSheaf G).obj.map (toSite.map f).op
    (SmoothOpenSite.topology.yonedaEquiv h) =
    SmoothOpenSite.topology.yonedaEquiv (embedding.map f ≫ h) at hn
  exact (congrArg (fun z => ordinaryLabel G U z x) hn.symm).trans
    (ordinaryLabel_natural G f _ x)

theorem labelAt_constant (U : Domain) (k : G) (x : Points U) :
    labelAt G (constantSection (embedding.obj U) k) x = k :=
  (constantLabelRealEquiv G).symm_apply_apply k

theorem labelAt_multiply {U : Domain} (a b : embedding.obj U ⟶ locallyConstantGroupSheaf G)
    (x : Points U) : labelAt G (multiply G a b) x = labelAt G a x * labelAt G b x := by
  apply (constantLabelRealEquiv G).injective
  have he (h : embedding.obj U ⟶ locallyConstantGroupSheaf G) :
      (constantLabelRealEquiv G) (labelAt G h x) =
        h.hom.app (op (op (free 0))) (ordinaryPoint U x) :=
    (constantLabelRealEquiv G).apply_symm_apply _
  rw [he]
  change (show (locallyConstantGroup G).obj.obj _ from a.hom.app _ (ordinaryPoint U x)) *
    (show (locallyConstantGroup G).obj.obj _ from b.hom.app _ (ordinaryPoint U x)) =
    (constantLabel G).app _ (labelAt G a x * labelAt G b x)
  rw [((constantLabel G).app _).hom.map_mul]
  exact congrArg₂ (· * ·) (he a).symm (he b).symm

theorem transition_label (b : Bool) (x : Points punctured) (hx : x.val ∈ signOpen b) :
    labelAt G (transition G c) x = if b then c else 1 := by
  let y : Points (subdomain punctured (signDefining b)) :=
    ⟨x.val, mul_ne_zero x.property ((signDefining_iff b x.val).mpr hx)⟩
  have hy : (show Map _ _ from subInclusion punctured (signDefining b)) y = x := rfl
  rw [← hy, ← labelAt_comp, transition_restrict]
  exact labelAt_constant G _ _ y


def puncturedPoint (r : ℝ) (hr : r ≠ 0) : Points punctured :=
  ⟨fun _ => r, by change (1 : ℝ) * r ≠ 0; simpa only [one_mul] using hr⟩

/-- The overlap label is not globally constant when its two values differ.
This checks that disconnected-stage labels survived sheafification. -/
theorem transition_not_constant (hc : c ≠ 1) (k : G) :
    transition G c ≠ constantSection puncturedSheaf k := by
  intro he
  have hn := transition_label G c false (puncturedPoint (-1) (by norm_num))
    (by norm_num [signOpen, puncturedPoint])
  have hp := transition_label G c true (puncturedPoint 1 one_ne_zero)
    (by norm_num [signOpen, puncturedPoint])
  rw [he, labelAt_constant] at hn hp
  exact hc (hp.symm.trans hn)

theorem labelAt_line_constant (a : lineSheaf ⟶ locallyConstantGroupSheaf G) (r s : ℝ) :
    labelAt G a (realLinePoint r) = labelAt G a (realLinePoint s) := by
  rw [labelAt_eq_ordinary, labelAt_eq_ordinary]
  exact realLineLabel_constant G _ r s

/-- The effectively glued display has no global section for any nonidentity
clutching label. Nontriviality is proved inside the actual smooth sheaf model. -/
theorem no_section (hc : c ≠ 1) :
    ¬ ∃ s : base ⟶ total G c, s ≫ projection G c = 𝟙 _ := by
  rintro ⟨s, hs⟩
  obtain ⟨a, b, he⟩ := section_labels G c s hs
  have hn := congrArg (fun k => labelAt G k (puncturedPoint (-1) (by norm_num))) he
  have hp := congrArg (fun k => labelAt G k (puncturedPoint 1 one_ne_zero)) he
  rw [labelAt_multiply, transition_label G c false _ (by norm_num [signOpen, puncturedPoint])] at hn
  rw [labelAt_multiply, transition_label G c true _ (by norm_num [signOpen, puncturedPoint])] at hp
  change labelAt G (embedding.map (subInclusion line (generator 0)) ≫ a) _ * 1 =
    labelAt G (embedding.map (subInclusion line (generator 0)) ≫ b) _ at hn
  change labelAt G (embedding.map (subInclusion line (generator 0)) ≫ a) _ * c =
    labelAt G (embedding.map (subInclusion line (generator 0)) ≫ b) _ at hp
  rw [mul_one, labelAt_comp, labelAt_comp] at hn
  rw [labelAt_comp, labelAt_comp] at hp
  change labelAt G a (realLinePoint (-1)) = labelAt G b (realLinePoint (-1)) at hn
  change labelAt G a (realLinePoint 1) * c = labelAt G b (realLinePoint 1) at hp
  rw [labelAt_line_constant G a 1 (-1), labelAt_line_constant G b 1 (-1), ← hn] at hp
  exact hc (mul_left_cancel (hp.trans (mul_one _).symm))


theorem multiply_assoc {X : Sheaf SmoothOpenSite.topology Type}
    (a b d : X ⟶ locallyConstantGroupSheaf G) :
    multiply G (multiply G a b) d = multiply G a (multiply G b d) := by
  ext U x
  exact mul_assoc (show (locallyConstantGroup G).obj.obj U from a.hom.app U x)
    (show (locallyConstantGroup G).obj.obj U from b.hom.app U x)
    (show (locallyConstantGroup G).obj.obj U from d.hom.app U x)

def localAction (X : Sheaf SmoothOpenSite.topology Type) :
    prod (locallyConstantGroupSheaf G) (prod X (locallyConstantGroupSheaf G)) ⟶
      prod X (locallyConstantGroupSheaf G) :=
  prod.lift (prod.snd ≫ prod.fst) (multiply G prod.fst (prod.snd ≫ prod.snd))

theorem localAction_left :
    prod.map (𝟙 (locallyConstantGroupSheaf G)) (totalLeft G) ≫ localAction G lineSheaf =
      localAction G puncturedSheaf ≫ totalLeft G := by
  apply prod.hom_ext <;>
    simp [localAction, totalLeft, multiply_comp, Category.assoc]

theorem localAction_right :
    prod.map (𝟙 (locallyConstantGroupSheaf G)) (totalRight G c) ≫ localAction G lineSheaf =
      localAction G puncturedSheaf ≫ totalRight G c := by
  apply prod.hom_ext <;>
    simp [localAction, totalRight, multiply_comp, Category.assoc, multiply_assoc]

-- Align the inherited monoidal structure with the cartesian structure before
-- invoking the product adjunction; Mathlib exposes both instance paths.
local instance productLeftAdjoint (X : Sheaf SmoothOpenSite.topology Type) :
    (prod.functor.obj X).IsLeftAdjoint := by
  let hC : MonoidalClosed (Sheaf SmoothOpenSite.topology Type) := inferInstance
  let : MonoidalCategory (Sheaf SmoothOpenSite.topology Type) :=
    (inferInstance : CartesianMonoidalCategory (Sheaf SmoothOpenSite.topology Type)).toSemiCartesianMonoidalCategory.toMonoidalCategory
  let : MonoidalClosed (Sheaf SmoothOpenSite.topology Type) := hC
  exact CartesianMonoidalCategory.isLeftAdjoint_prod_functor X

/-- Multiplication on the left commutes with the right-translation clutching,
so it descends along the product-preserved sheaf pushout. -/
def actionMap : prod (locallyConstantGroupSheaf G) (total G c) ⟶ total G c :=
  ((IsPushout.of_hasPushout (totalLeft G) (totalRight G c)).map
    (prod.functor.obj (locallyConstantGroupSheaf G))).desc
    (localAction G lineSheaf ≫ totalChartLeft G c)
    (localAction G lineSheaf ≫ totalChartRight G c) (by
      change prod.map (𝟙 _) (totalLeft G) ≫ localAction G lineSheaf ≫ totalChartLeft G c =
        prod.map (𝟙 _) (totalRight G c) ≫ localAction G lineSheaf ≫ totalChartRight G c
      rw [← Category.assoc, localAction_left, Category.assoc,
        ← Category.assoc (prod.map _ _) _, localAction_right, Category.assoc]
      exact congrArg (fun k => localAction G puncturedSheaf ≫ k)
        (pushout.condition (f := totalLeft G) (g := totalRight G c)))


@[reassoc] theorem actionMap_left :
    prod.map (𝟙 _) (totalChartLeft G c) ≫ actionMap G c =
      localAction G lineSheaf ≫ totalChartLeft G c :=
  IsPushout.inl_desc _ _ _ _

@[reassoc] theorem actionMap_right :
    prod.map (𝟙 _) (totalChartRight G c) ≫ actionMap G c =
      localAction G lineSheaf ≫ totalChartRight G c :=
  IsPushout.inr_desc _ _ _ _

def pairSection (X Y : Sheaf SmoothOpenSite.topology Type) (U : Siteᵒᵖ)
    (x : X.obj.obj U) (y : Y.obj.obj U) : (prod X Y).obj.obj U :=
  (SheafRelation.productIso X Y).hom.hom.app U (x, y)

@[simp] theorem pairSection_fst (X Y : Sheaf SmoothOpenSite.topology Type) (U : Siteᵒᵖ)
    (x : X.obj.obj U) (y : Y.obj.obj U) :
    (prod.fst : prod X Y ⟶ X).hom.app U (pairSection X Y U x y) = x :=
  congrArg (fun k : SheafRelation.product X Y ⟶ X => k.hom.app U (x, y))
    (SheafRelation.productIso_fst X Y)

@[simp] theorem pairSection_snd (X Y : Sheaf SmoothOpenSite.topology Type) (U : Siteᵒᵖ)
    (x : X.obj.obj U) (y : Y.obj.obj U) :
    (prod.snd : prod X Y ⟶ Y).hom.app U (pairSection X Y U x y) = y :=
  congrArg (fun k : SheafRelation.product X Y ⟶ Y => k.hom.app U (x, y))
    (SheafRelation.productIso_snd X Y)

theorem productSection_ext (X Y : Sheaf SmoothOpenSite.topology Type) (U : Siteᵒᵖ)
    (p q : (prod X Y).obj.obj U)
    (hf : (prod.fst : prod X Y ⟶ X).hom.app U p = (prod.fst : prod X Y ⟶ X).hom.app U q)
    (hs : (prod.snd : prod X Y ⟶ Y).hom.app U p = (prod.snd : prod X Y ⟶ Y).hom.app U q) : p = q := by
  have hpq : ((prod.fst : prod X Y ⟶ X).hom.app U p,
      (prod.snd : prod X Y ⟶ Y).hom.app U p) =
      ((prod.fst : prod X Y ⟶ X).hom.app U q, (prod.snd : prod X Y ⟶ Y).hom.app U q) :=
    Prod.ext hf hs
  have h := congrArg ((SheafRelation.productIso X Y).hom.hom.app U) hpq
  have hi (z : (prod X Y).obj.obj U) := congrArg
    (fun k : prod X Y ⟶ prod X Y => k.hom.app U z) (SheafRelation.productIso X Y).inv_hom_id
  exact (hi p).symm.trans (h.trans (hi q))

@[simp] theorem pairSection_map {X Y X' Y' : Sheaf SmoothOpenSite.topology Type}
    (f : X ⟶ X') (g : Y ⟶ Y') (U : Siteᵒᵖ) (x : X.obj.obj U) (y : Y.obj.obj U) :
    (prod.map f g).hom.app U (pairSection X Y U x y) =
      pairSection X' Y' U (f.hom.app U x) (g.hom.app U y) := by
  apply productSection_ext
  · have h := congrArg (fun k : prod X Y ⟶ X' => k.hom.app U (pairSection X Y U x y))
      (prod.map_fst f g)
    change (prod.fst : prod X' Y' ⟶ X').hom.app U
      ((prod.map f g).hom.app U (pairSection X Y U x y)) =
      f.hom.app U ((prod.fst : prod X Y ⟶ X).hom.app U (pairSection X Y U x y)) at h
    simpa only [pairSection_fst] using h
  · have h := congrArg (fun k : prod X Y ⟶ Y' => k.hom.app U (pairSection X Y U x y))
      (prod.map_snd f g)
    change (prod.snd : prod X' Y' ⟶ Y').hom.app U
      ((prod.map f g).hom.app U (pairSection X Y U x y)) =
      g.hom.app U ((prod.snd : prod X Y ⟶ Y).hom.app U (pairSection X Y U x y)) at h
    simpa only [pairSection_snd] using h

/-- The descended action on actual stage sections. -/
def sectionAction (U : Siteᵒᵖ) (g : (locallyConstantGroup G).obj.obj U)
    (p : (total G c).obj.obj U) : (total G c).obj.obj U :=
  (actionMap G c).hom.app U (pairSection (locallyConstantGroupSheaf G) _ U g p)


@[simp] theorem pairSection_lift {X Y Z : Sheaf SmoothOpenSite.topology Type}
    (f : Z ⟶ X) (g : Z ⟶ Y) (U : Siteᵒᵖ) (z : Z.obj.obj U) :
    (prod.lift f g).hom.app U z = pairSection X Y U (f.hom.app U z) (g.hom.app U z) := by
  apply productSection_ext
  · rw [pairSection_fst]
    exact congrArg (fun k : Z ⟶ X => k.hom.app U z)
      (prod.lift_fst f g)
  · rw [pairSection_snd]
    exact congrArg (fun k : Z ⟶ Y => k.hom.app U z)
      (prod.lift_snd f g)

theorem pairSection_natural {X Y : Sheaf SmoothOpenSite.topology Type}
    {U V : Siteᵒᵖ} (f : U ⟶ V) (x : X.obj.obj U) (y : Y.obj.obj U) :
    (prod X Y).obj.map f (pairSection X Y U x y) =
      pairSection X Y V (X.obj.map f x) (Y.obj.map f y) := by
  have h := congrArg (fun k : (SheafRelation.product X Y).obj.obj U ⟶ (prod X Y).obj.obj V =>
    k (x, y)) ((SheafRelation.productIso X Y).hom.hom.naturality f)
  exact h.symm

theorem localAction_apply (X : Sheaf SmoothOpenSite.topology Type) (U : Siteᵒᵖ)
    (g : (locallyConstantGroup G).obj.obj U) (p : (prod X (locallyConstantGroupSheaf G)).obj.obj U) :
    (localAction G X).hom.app U (pairSection (locallyConstantGroupSheaf G) _ U g p) =
      pairSection _ _ U ((prod.fst : prod X _ ⟶ X).hom.app U p)
        (g * (show (locallyConstantGroup G).obj.obj U from (prod.snd : prod X _ ⟶ _).hom.app U p)) := by
  unfold localAction
  rw [pairSection_lift]
  congr 1
  · change (prod.fst : prod X _ ⟶ X).hom.app U
      ((prod.snd : prod _ (prod X _) ⟶ _).hom.app U (pairSection (locallyConstantGroupSheaf G) _ U g p)) = _
    rw [pairSection_snd]
  · change (show (locallyConstantGroup G).obj.obj U from
      (prod.fst : prod _ (prod X _) ⟶ _).hom.app U (pairSection (locallyConstantGroupSheaf G) _ U g p)) *
      (show (locallyConstantGroup G).obj.obj U from
        (prod.snd : prod X _ ⟶ _).hom.app U
          ((prod.snd : prod _ (prod X _) ⟶ _).hom.app U (pairSection (locallyConstantGroupSheaf G) _ U g p))) = _
    rw [pairSection_fst, pairSection_snd]

theorem sectionAction_chart (k : totalLine G ⟶ total G c)
    (hk : prod.map (𝟙 _) k ≫ actionMap G c = localAction G lineSheaf ≫ k)
    (U : Siteᵒᵖ) (g : (locallyConstantGroup G).obj.obj U) (p : (totalLine G).obj.obj U) :
    sectionAction G c U g (k.hom.app U p) = k.hom.app U
      (pairSection _ _ U ((lineProjection G).hom.app U p)
        (g * (show (locallyConstantGroup G).obj.obj U from (prod.snd : totalLine G ⟶ _).hom.app U p))) := by
  have h := congrArg (fun f => f.hom.app U (pairSection (locallyConstantGroupSheaf G) _ U g p)) hk
  change (actionMap G c).hom.app U
    ((prod.map (𝟙 _) k).hom.app U (pairSection (locallyConstantGroupSheaf G) _ U g p)) =
    k.hom.app U ((localAction G lineSheaf).hom.app U (pairSection (locallyConstantGroupSheaf G) _ U g p)) at h
  rw [pairSection_map, localAction_apply] at h
  exact h

theorem sectionAction_natural {U V : Siteᵒᵖ} (f : U ⟶ V)
    (g : (locallyConstantGroup G).obj.obj U) (p : (total G c).obj.obj U) :
    (total G c).obj.map f (sectionAction G c U g p) =
      sectionAction G c V ((locallyConstantGroup G).obj.map f g) ((total G c).obj.map f p) := by
  unfold sectionAction
  rw [← NatTrans.naturality_apply, pairSection_natural]
  rfl


@[simp] theorem pairSection_eta (X Y : Sheaf SmoothOpenSite.topology Type) (U : Siteᵒᵖ)
    (p : (prod X Y).obj.obj U) :
    pairSection X Y U ((prod.fst : prod X Y ⟶ X).hom.app U p)
      ((prod.snd : prod X Y ⟶ Y).hom.app U p) = p := by
  apply productSection_ext <;> simp

theorem actionMap_projection : actionMap G c ≫ projection G c = prod.snd ≫ projection G c := by
  apply ((IsPushout.of_hasPushout (totalLeft G) (totalRight G c)).map
    (prod.functor.obj (locallyConstantGroupSheaf G))).hom_ext
  · change prod.map (𝟙 _) (totalChartLeft G c) ≫ (actionMap G c ≫ projection G c) =
      prod.map (𝟙 _) (totalChartLeft G c) ≫
        (prod.snd : prod (locallyConstantGroupSheaf G) (total G c) ⟶ _) ≫ projection G c
    rw [← Category.assoc, actionMap_left, Category.assoc]
    simp [projection, localAction, totalChartLeft, Category.assoc]
  · change prod.map (𝟙 _) (totalChartRight G c) ≫ (actionMap G c ≫ projection G c) =
      prod.map (𝟙 _) (totalChartRight G c) ≫
        (prod.snd : prod (locallyConstantGroupSheaf G) (total G c) ⟶ _) ≫ projection G c
    rw [← Category.assoc, actionMap_right, Category.assoc]
    simp [projection, localAction, totalChartRight, Category.assoc]

theorem sectionAction_base (U : Siteᵒᵖ) (g : (locallyConstantGroup G).obj.obj U)
    (p : (total G c).obj.obj U) :
    (projection G c).hom.app U (sectionAction G c U g p) = (projection G c).hom.app U p := by
  have h := congrArg (fun k => k.hom.app U
    (pairSection (locallyConstantGroupSheaf G) (total G c) U g p)) (actionMap_projection G c)
  change (projection G c).hom.app U (sectionAction G c U g p) =
    (projection G c).hom.app U ((prod.snd : prod _ (total G c) ⟶ _).hom.app U
      (pairSection (locallyConstantGroupSheaf G) (total G c) U g p)) at h
  simpa only [pairSection_snd] using h

theorem sectionAction_one_chart (k : totalLine G ⟶ total G c)
    (hk : prod.map (𝟙 _) k ≫ actionMap G c = localAction G lineSheaf ≫ k)
    (U : Siteᵒᵖ) (p : (totalLine G).obj.obj U) :
    sectionAction G c U 1 (k.hom.app U p) = k.hom.app U p := by
  rw [sectionAction_chart G c k hk, one_mul, pairSection_eta]

theorem sectionAction_one (U : Siteᵒᵖ) (p : (total G c).obj.obj U) :
    sectionAction G c U 1 p = p := by
  apply (((isSheaf_iff_isSheaf_of_type _ _).mp (total G c).property)
    (SheafPushoutLocal.chartSieve (totalLeft G) (totalRight G c) p)
    (SheafPushoutLocal.chartSieve_cover (totalLeft G) (totalRight G c) p)).isSeparatedFor.ext
  intro V f hf
  rw [sectionAction_natural]
  change sectionAction G c (op V) ((locallyConstantGroup G).obj.map f.op 1) _ = _
  rw [((locallyConstantGroup G).obj.map f.op).hom.map_one]
  rcases hf with ⟨q, hq⟩ | ⟨q, hq⟩
  · change (totalChartLeft G c).hom.app (op V) q = (total G c).obj.map f.op p at hq
    rw [← hq]
    exact sectionAction_one_chart G c _ (actionMap_left G c) _ q
  · change (totalChartRight G c).hom.app (op V) q = (total G c).obj.map f.op p at hq
    rw [← hq]
    exact sectionAction_one_chart G c _ (actionMap_right G c) _ q

theorem sectionAction_mul_chart (k : totalLine G ⟶ total G c)
    (hk : prod.map (𝟙 _) k ≫ actionMap G c = localAction G lineSheaf ≫ k)
    (U : Siteᵒᵖ) (g h : (locallyConstantGroup G).obj.obj U) (p : (totalLine G).obj.obj U) :
    sectionAction G c U (g * h) (k.hom.app U p) =
      sectionAction G c U g (sectionAction G c U h (k.hom.app U p)) := by
  rw [sectionAction_chart G c k hk, sectionAction_chart G c k hk,
    sectionAction_chart G c k hk]
  simp only [lineProjection, pairSection_fst, pairSection_snd, mul_assoc]

theorem sectionAction_mul (U : Siteᵒᵖ) (g h : (locallyConstantGroup G).obj.obj U)
    (p : (total G c).obj.obj U) :
    sectionAction G c U (g * h) p = sectionAction G c U g (sectionAction G c U h p) := by
  apply (((isSheaf_iff_isSheaf_of_type _ _).mp (total G c).property)
    (SheafPushoutLocal.chartSieve (totalLeft G) (totalRight G c) p)
    (SheafPushoutLocal.chartSieve_cover (totalLeft G) (totalRight G c) p)).isSeparatedFor.ext
  intro V f hf
  rw [sectionAction_natural, sectionAction_natural, sectionAction_natural,
    ((locallyConstantGroup G).obj.map f.op).hom.map_mul]
  rcases hf with ⟨q, hq⟩ | ⟨q, hq⟩
  · change (totalChartLeft G c).hom.app (op V) q = (total G c).obj.map f.op p at hq
    rw [← hq]
    exact sectionAction_mul_chart G c _ (actionMap_left G c) _ _ _ q
  · change (totalChartRight G c).hom.app (op V) q = (total G c).obj.map f.op p at hq
    rw [← hq]
    exact sectionAction_mul_chart G c _ (actionMap_right G c) _ _ _ q

/-- The action lives on the actual fibers of the glued display. -/
def action : SheafTorsor.Action (locallyConstantGroup G) base :=
  SheafTorsor.Action.ofDisplay (projection G c) (sectionAction G c)
    (sectionAction_base G c) (sectionAction_one G c) (sectionAction_mul G c)
    (sectionAction_natural G c)


theorem projection_chart (j : lineSheaf ⟶ base) (k : totalLine G ⟶ total G c)
    (hk : k ≫ projection G c = lineProjection G ≫ j) (U : Siteᵒᵖ)
    (x : lineSheaf.obj.obj U) (g : (locallyConstantGroup G).obj.obj U) :
    (projection G c).hom.app U (k.hom.app U (pairSection _ _ U x g)) = j.hom.app U x := by
  have h := congrArg (fun f => f.hom.app U (pairSection lineSheaf (locallyConstantGroupSheaf G) U x g)) hk
  change (projection G c).hom.app U (k.hom.app U (pairSection _ _ U x g)) =
    j.hom.app U ((prod.fst : totalLine G ⟶ _).hom.app U (pairSection _ _ U x g)) at h
  simpa only [pairSection_fst] using h

/-- The glued display is locally surjective because its two charts are
products with an inhabited group sheaf and cover the actual base pushout. -/
instance projection_locallySurjective :
    Presheaf.IsLocallySurjective SmoothOpenSite.topology (projection G c).hom where
  imageSieve_mem {U} x := by
    apply SmoothOpenSite.topology.superset_covering _
      (SheafPushoutLocal.chartSieve_cover inclusion inclusion x)
    intro V f hf
    rcases hf with ⟨y, hy⟩ | ⟨y, hy⟩
    · refine ⟨(totalChartLeft G c).hom.app (op V)
        (pairSection lineSheaf (locallyConstantGroupSheaf G) (op V) y (1 : (locallyConstantGroup G).obj.obj (op V))), ?_⟩
      exact (projection_chart G c left (totalChartLeft G c) (localTrivial G c).1.w _ y 1).trans hy
    · refine ⟨(totalChartRight G c).hom.app (op V)
        (pairSection lineSheaf (locallyConstantGroupSheaf G) (op V) y (1 : (locallyConstantGroup G).obj.obj (op V))), ?_⟩
      exact (projection_chart G c right (totalChartRight G c) (localTrivial G c).2.w _ y 1).trans hy

instance action_locallySurjective : Presheaf.IsLocallySurjective SmoothOpenSite.topology
    (SplitSheaf.p (action G c).family).hom := by
  change Presheaf.IsLocallySurjective SmoothOpenSite.topology
    (SplitSheaf.p (SplitSheaf.ofDisplay (projection G c))).hom
  rw [← SplitSheaf.displayIso_projection]
  change Presheaf.IsLocallySurjective SmoothOpenSite.topology
    ((SplitSheaf.displayIso (projection G c)).hom.hom ≫ (projection G c).hom)
  infer_instance

end SquareKit.SmoothClutching
