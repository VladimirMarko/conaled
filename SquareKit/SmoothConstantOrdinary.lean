import SquareKit.SmoothConstantRigidity
import SquareKit.SmoothOrdinaryCoverLifting
import SquareKit.SmoothOpenRealSections
import Mathlib.Topology.LocallyConstant.Basic
open scoped ContDiff

/-! Real-point functions of locally constant group sections on ordinary opens. -/
noncomputable section
open CategoryTheory Opposite
namespace SquareKit.SmoothOpenSite
open SmoothPresentationSite EuclideanOpen
variable (G : Type) [Group G]

theorem constantLabel_real_surjective : Function.Surjective
    ((constantLabel G).app (op (op (free 0)))) := by
  intro g
  obtain ⟨Y, f, ⟨k, hk⟩, y, hy⟩ := realPoint_lift _
    (Presheaf.imageSieve_mem topology (constantLabel G) g) (𝟙 _)
  refine ⟨k, ?_⟩
  have h := congrArg ((locallyConstantGroup G).obj.map y.op) hk
  have hn := NatTrans.naturality_apply (constantLabel G) y.op k
  have hh := congrArg (fun t => t g) ((locallyConstantGroup G).obj.map_comp f.op y.op)
  have hid := congrArg (fun t => t g) ((locallyConstantGroup G).obj.map_id (op (op (free 0))))
  rw [← op_comp, hy] at hh
  exact hn.trans (h.trans (hh.symm.trans hid))

def constantLabelRealEquiv : G ≃ (locallyConstantGroupSheaf G).obj.obj (op (op (free 0))) :=
  Equiv.ofBijective ((constantLabel G).app _) ⟨constantLabel_injective G _ (𝟙 _),
    constantLabel_real_surjective G⟩

def ordinaryPoint (U : Domain) (x : Points U) : op (free 0) ⟶ toSite.obj U :=
  (realSectionEquiv U).symm x

def ordinaryLabel (U : Domain)
    (g : (locallyConstantGroupSheaf G).obj.obj (op (toSite.obj U))) (x : Points U) : G :=
  (constantLabelRealEquiv G).symm
    ((locallyConstantGroupSheaf G).obj.map (ordinaryPoint U x).op g)

theorem ordinaryLabel_constant (U : Domain) (k : G) (x : Points U) :
    ordinaryLabel G U ((constantLabel G).app _ k) x = k := by
  unfold ordinaryLabel
  have h := NatTrans.naturality_apply (constantLabel G) (ordinaryPoint U x).op k
  change _ = (locallyConstantGroupSheaf G).obj.map (ordinaryPoint U x).op
    ((constantLabel G).app _ k) at h
  rw [← h]
  exact (constantLabelRealEquiv G).symm_apply_apply k

@[simp] theorem ordinaryLabel_mul (U : Domain)
    (g h : (locallyConstantGroup G).obj.obj (op (toSite.obj U))) (x : Points U) :
    ordinaryLabel G U (g * h) x = ordinaryLabel G U g x * ordinaryLabel G U h x := by
  apply (constantLabelRealEquiv G).injective
  have he (a : (locallyConstantGroup G).obj.obj (op (toSite.obj U))) :
      (constantLabelRealEquiv G) (ordinaryLabel G U a x) =
        (locallyConstantGroup G).obj.map (ordinaryPoint U x).op a :=
    (constantLabelRealEquiv G).apply_symm_apply _
  rw [he]
  change (locallyConstantGroup G).obj.map (ordinaryPoint U x).op (g * h) =
    (constantLabel G).app _ (ordinaryLabel G U g x * ordinaryLabel G U h x)
  rw [((constantLabel G).app _).hom.map_mul,
    ((locallyConstantGroup G).obj.map (ordinaryPoint U x).op).hom.map_mul]
  exact congrArg₂ (· * ·) (he g).symm (he h).symm

theorem ordinaryLabel_natural {U V : Domain} (f : U ⟶ V)
    (g : (locallyConstantGroupSheaf G).obj.obj (op (toSite.obj V))) (x : Points U) :
    ordinaryLabel G U ((locallyConstantGroupSheaf G).obj.map (toSite.map f).op g) x =
      ordinaryLabel G V g ((show Map _ _ from f) x) := by
  unfold ordinaryLabel
  congr 1
  rw [← types_comp_apply, ← Functor.map_comp, ← op_comp]
  congr 4
  apply (realSectionEquiv V).injective
  exact (realSectionEquiv_naturality f _).trans
    (congrArg (show Map _ _ from f) ((realSectionEquiv U).apply_symm_apply x) |>.trans ((realSectionEquiv V).apply_symm_apply _).symm)

/-- Restricting a sheafified group section to ordinary real points gives an
actual locally constant function. The proof refines the section's covering
witness to ordinary coordinate neighborhoods. -/
theorem ordinaryLabel_isLocallyConstant (U : Domain)
    (g : (locallyConstantGroupSheaf G).obj.obj (op (toSite.obj U))) :
    IsLocallyConstant (ordinaryLabel G U g) := by
  apply (IsLocallyConstant.iff_exists_open _).mpr
  intro x
  obtain ⟨q, u, hu, ⟨y, hy⟩, k, hk⟩ := covering_local_inclusion
    (Presheaf.imageSieve (constantLabel G) g)
    (Presheaf.imageSieve_mem topology (constantLabel G) g) U (𝟙 _) x
  have hres : (locallyConstantGroupSheaf G).obj.map (toSite.map u).op g =
      (constantLabel G).app _ k := by
    change (locallyConstantGroup G).obj.map (toSite.map u).op g = _
    simpa only [Category.comp_id] using hk.symm
  let O : Set (Points U) := {z | q.val z.val ≠ 0}
  have hO : IsOpen O := (isOpen_ne_fun (show ContDiff ℝ ∞ q.val from q.property).continuous continuous_const).preimage
    continuous_subtype_val
  have hx : x ∈ O := by
    change q.val x.val ≠ 0
    rw [← hy, hu]
    exact y.property
  have he (z : Points U) (hz : z ∈ O) : ordinaryLabel G U g z = k := by
    let z' : Points (⟨U.dimension, q⟩ : Domain) := ⟨z.val, hz⟩
    have hzu : (show Map _ _ from u) z' = z := Subtype.ext (hu z')
    rw [← hzu, ← ordinaryLabel_natural G u g z', hres]
    exact ordinaryLabel_constant G _ k z'
  exact ⟨O, hO, hx, fun z hz => (he z hz).trans (he x hx).symm⟩

/-- The public comparison retains the point-label function and its proved
local constancy; it makes no point-detection claim for arbitrary sheaves. -/
def ordinaryLocallyConstant (U : Domain)
    (g : (locallyConstantGroupSheaf G).obj.obj (op (toSite.obj U))) :
    LocallyConstant (Points U) G := ⟨ordinaryLabel G U g, ordinaryLabel_isLocallyConstant G U g⟩

theorem ordinaryLabel_eq_of_preconnected (U : Domain) [PreconnectedSpace (Points U)]
    (g : (locallyConstantGroupSheaf G).obj.obj (op (toSite.obj U))) (x y : Points U) :
    ordinaryLabel G U g x = ordinaryLabel G U g y :=
  (ordinaryLocallyConstant G U g).apply_eq_of_preconnectedSpace x y


/-- Ordinary scalar coordinates give a connected parameter for the comparison. -/
def realLinePoint (r : ℝ) : Points (full 1) := ⟨fun _ => r, one_ne_zero⟩

theorem continuous_realLinePoint : Continuous realLinePoint :=
  (continuous_pi (fun _ => continuous_id)).subtype_mk _

/-- Every sheafified group section over the real line has one global point
label, derived from actual local covering witnesses. -/
theorem realLineLabel_constant
    (g : (locallyConstantGroupSheaf G).obj.obj (op (toSite.obj (full 1)))) (r s : ℝ) :
    ordinaryLabel G (full 1) g (realLinePoint r) =
      ordinaryLabel G (full 1) g (realLinePoint s) :=
  ((ordinaryLabel_isLocallyConstant G (full 1) g).comp_continuous
    continuous_realLinePoint).apply_eq_of_preconnectedSpace r s

/-- A nonidentity clutching label on the positive overlap, with identity on
its negative component, cannot come from two global trivializing sections.
This consumes the smooth-site comparison, rather than assuming locally
constant functions as input. -/
theorem realLine_clutching_obstruction (c : G) (hc : c ≠ 1)
    (a b : (locallyConstantGroupSheaf G).obj.obj (op (toSite.obj (full 1))))
    (hneg : ordinaryLabel G (full 1) a (realLinePoint (-1)) =
      ordinaryLabel G (full 1) b (realLinePoint (-1)))
    (hpos : ordinaryLabel G (full 1) a (realLinePoint 1) =
      c * ordinaryLabel G (full 1) b (realLinePoint 1)) : False := by
  have he : c * ordinaryLabel G (full 1) b (realLinePoint 1) =
      1 * ordinaryLabel G (full 1) b (realLinePoint 1) := by
    rw [one_mul, ← hpos, realLineLabel_constant G a 1 (-1), hneg,
      realLineLabel_constant G b (-1) 1]
  exact hc (mul_right_cancel he)

end SquareKit.SmoothOpenSite
