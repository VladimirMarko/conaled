import SquareKit.SmoothDescentDual
import SquareKit.SmoothPresentedDual
import Examples.SmoothFormalLocalization

/-! Experimental finite-cover descent clients: a nontrivial real-line cover,
nonpolynomial local data, actual dual coefficients and failed-cover boundaries. -/
noncomputable section
open scoped ContDiff
namespace Examples.SmoothPrincipalDescent
open SquareKit.SmoothAlgebra
open PresentedLocalization PrincipalCover
attribute [local instance] DualExtension.smoothStructure

abbrev r : Fin 0 → Free 1 := noRelations 1
abbrev x : Free 1 := generator 0
def p : Fin 2 → Free 1 := ![x,1-x]
abbrev A := Presentation.Carrier r

theorem cover : Covers (fun i => Presentation.projection r (p i)) := by
  refine ⟨fun _ => 1,?_⟩
  simp only [Fin.sum_univ_two,one_mul,p,Matrix.cons_val_zero,Matrix.cons_val_one]
  change (Presentation.projection r).toAlgHom x+(Presentation.projection r).toAlgHom (1-x)=1
  rw [map_sub,map_one]
  ring

def point (t : ℝ) : Hom A ℝ := realPoint r (fun _ => t) (fun j => Fin.elim0 j)

/-- Neither principal open alone covers the real line. -/
theorem no_member_unit (i : Fin 2) : ¬IsUnit (Presentation.projection r (p i)) := by
  intro hi
  fin_cases i
  · have h := hi.map (point 0).toAlgHom
    change IsUnit (0 : ℝ) at h
    exact (not_isUnit_zero h)
  · have h := hi.map (point 1).toAlgHom
    change IsUnit ((1 : ℝ)-1) at h
    simp at h

def expOperation : Operation 1 := SmoothFormalLocalization.exponential

def localExp : Sections r p := sectionAct r p expOperation (fun _ => restrict r p (Presentation.projection r x))
def gluedExp : A := glue r p cover localExp

theorem glued_exp_formula : gluedExp=Presentation.projection r SmoothFormalLocalization.exponential := by
  unfold gluedExp localExp
  rw [glue_act]
  have hi := (descentEquiv r p cover).symm_apply_apply (Presentation.projection r x)
  change glue r p cover (restrict r p (Presentation.projection r x)) = _ at hi
  simp only [hi]
  have h := (Presentation.projection r).map_act expOperation (fun _ : Fin 1 => x)
  exact h.symm

/-- A consumer of the gluing construction: the glued section has its analytic exponential value. -/
theorem glued_exp_at (t : ℝ) : point t gluedExp=Real.exp t := by
  rw [glued_exp_formula]
  rfl

/-- Arbitrary compatible local elements, not only displayed global restrictions, produce a scalar. -/
theorem arbitrary_sections_glue (a : ∀ i, Carrier r (p i)) (ha : Compatible r p a) :
    ∃! b : A, ∀ i, base r (p i) b=a i := exists_unique r p cover a ha

namespace Nilpotent
open SmoothFormalLocalization
abbrev rel := SmoothFormalLocalization.relations
abbrev E := SmoothFormalLocalization.epsilon

def s : Fin 2 → SmoothFormalLocalization.A := ![1+E,E]

theorem cover : Covers s := by
  refine ⟨![1-E,E],?_⟩
  simp only [Fin.sum_univ_two,s,Matrix.cons_val_zero,Matrix.cons_val_one]
  calc
    (1-E)*(1+E)+E*E = 1 := by ring

/-- Glue in the finite dual presentation, then observe the nonzero actual dual coefficient. -/
def localE : AtSections rel s := atDescentEquiv rel s cover E
def gluedE : SmoothFormalLocalization.A := (atDescentEquiv rel s cover).symm localE

theorem glued_eq : gluedE=E := (atDescentEquiv rel s cover).symm_apply_apply E

theorem glued_nonzero : gluedE ≠ 0 := by rw [glued_eq]; exact epsilon_nonzero

theorem actual_dual_coefficient : (value gluedE).snd=1 := by rw [glued_eq,value_epsilon]; rfl

theorem every_real_point_zero (h : Hom SmoothFormalLocalization.A ℝ) : h gluedE=0 := by
  rw [glued_eq]
  have he := congrArg h.toAlgHom epsilon_square
  simp only [map_mul,map_zero] at he
  exact mul_self_eq_zero.mp he

/-- A nonidentity smooth base map transports both the cover and its nilpotent gluing. -/
theorem scaling_glue : scaling gluedE=
    (atDescentEquiv rel (fun i => scaling (s i)) (map_covers scaling s cover)).symm
      (atTransport rel s rel scaling localE) := at_glue_natural rel s cover rel scaling localE

end Nilpotent

/-- A zero principal family cannot detect different scalars. -/
theorem failed_cover : ¬ Covers (fun _ : Fin 1 => (0 : A)) := by
  intro h
  obtain ⟨c,hc⟩ := map_covers (point 0) _ h
  have hz : point 0 (0 : A)=0 := (point 0).toAlgHom.map_zero
  simp [hz] at hc

theorem failed_separatedness : ∃ a b : A, a≠b ∧ base r 0 a=base r 0 b := by
  have hn : IsNilpotent (Presentation.projection r (0 : Free 1)) := by
    have hz : Presentation.projection r (0 : Free 1)=0 := (Presentation.projection r).toAlgHom.map_zero
    rw [hz]
    exact ⟨1,zero_pow (by decide)⟩
  have := nilpotent_subsingleton r 0 hn
  refine ⟨0,1,?_,Subsingleton.elim _ _⟩
  intro he
  have h := congrArg (point 0).toAlgHom he
  exact zero_ne_one (by simpa only [map_zero,map_one] using h)

/-- The empty descent equivalence exists exactly for a trivial base algebra. -/
theorem empty_trivial (r₀ : Fin 1 → Free 0) (h : Subsingleton (Presentation.Carrier r₀)) :
    Nonempty (Presentation.Carrier r₀ ≃ AtSections r₀ (Fin.elim0 : Fin 0 → Presentation.Carrier r₀)) :=
  ⟨atDescentEquiv r₀ Fin.elim0 ((empty_iff _).mpr h)⟩

def improper : Fin 1 → Free 0 := ![1]

theorem improper_trivial : Subsingleton (Presentation.Carrier improper) := by
  apply subsingleton_of_zero_eq_one
  have h := Presentation.relation_zero improper 0
  change (Presentation.projection improper).toAlgHom 1=0 at h
  rw [map_one] at h
  exact h.symm

def emptyGluing : Presentation.Carrier improper ≃
    AtSections improper (Fin.elim0 : Fin 0 → Presentation.Carrier improper) :=
  atDescentEquiv improper Fin.elim0 ((empty_iff _).mpr improper_trivial)

/-- Actual dual reconstruction after gluing, including epsilon rather than only constants. -/
theorem actual_dual_recovered (s : Fin 2 → Presentation.Dual r) (hs : Covers s) :
    Presentation.toDual r
      ((atDescentEquiv (Presentation.relations r (Presentation.dualEquation 1)) s hs).symm
        ((atDescentEquiv (Presentation.relations r (Presentation.dualEquation 1)) s hs)
          (Presentation.fromDual r (DualNumber.eps : DualNumber A))))=DualNumber.eps :=
  recover_dual r s hs DualNumber.eps


end Examples.SmoothPrincipalDescent
