import SquareKit.SmoothGeometricScalar
import SquareKit.SmoothCoverCharacterization
import Examples.SmoothPrincipalDescent

/-! Experimental consumers of the actual finite-principal topology and sheaf condition.
A proper real-line cover, nilpotent sieve matching data and an empty zero-algebra cover. -/
noncomputable section
namespace Examples.SmoothGeometricSite
open CategoryTheory Opposite SquareKit.SmoothAlgebra
open SquareKit.SmoothPresentationSite
open PrincipalCover

abbrev line : Code := free 1
def lineOpens : Fin 2 → Carrier line := fun i => Presentation.projection SmoothPrincipalDescent.r (SmoothPrincipalDescent.p i)

theorem line_cover : principalSieve line lineOpens ∈ topology (op line) :=
  principal_covering line lineOpens SmoothPrincipalDescent.cover

theorem line_cover_proper : principalSieve line lineOpens ≠ ⊤ := by
  intro h
  obtain ⟨i,hi⟩ := (principal_maximal_iff line lineOpens).mp h
  exact SmoothPrincipalDescent.no_member_unit i hi

/-- The constructed topology has a covering sieve absent from bottom coverage. -/
theorem topology_ne_bot : topology ≠ ⊥ := by
  intro he
  have h := line_cover
  rw [he,GrothendieckTopology.bot_covering] at h
  exact line_cover_proper h

/-- The topology is also non-chaotic: the zero family on the real line does not cover. -/
theorem topology_ne_top : topology ≠ ⊤ := by
  intro he
  have hc : principalSieve line (fun _ : Fin 1 => (0 : Carrier line)) ∈ topology (op line) := by
    rw [he]
    exact GrothendieckTopology.top_covering
  exact SmoothPrincipalDescent.failed_cover ((principal_covering_iff line _).mp hc)


namespace Nilpotent
abbrev stage : Code := ⟨1,1,SmoothFormalLocalization.relations⟩
abbrev opens : Fin 2 → Carrier stage := SmoothPrincipalDescent.Nilpotent.s
abbrev epsilon : Carrier stage := SmoothFormalLocalization.epsilon

theorem covering : principalSieve stage opens ∈ topology (op stage) :=
  principal_covering stage opens SmoothPrincipalDescent.Nilpotent.cover

/-- A family on every arrow of the covering sieve, not only the two displayed generators. -/
def matching : Presieve.FamilyOfElements scalarData (principalSieve stage opens).arrows :=
  fun _ f _ => scalarData.map f.op epsilon

theorem matching_compatible : matching.Compatible :=
  Presieve.is_compatible_of_exists_amalgamation matching ⟨epsilon,fun _ _ _ => rfl⟩

def glued : Carrier stage :=
  (scalar_isSheaf (principalSieve stage opens) covering).amalgamate matching matching_compatible

theorem glued_epsilon : glued=epsilon :=
  (scalar_isSheaf (principalSieve stage opens) covering).isSeparatedFor matching _ _
    ((scalar_isSheaf (principalSieve stage opens) covering).isAmalgamation matching_compatible) (fun _ _ _ => rfl)

/-- Categorical matching-family gluing retains a coefficient invisible at real points. -/
theorem glued_dual_coefficient : (SmoothFormalLocalization.value glued).snd=1 := by
  rw [glued_epsilon,SmoothFormalLocalization.value_epsilon]
  rfl

theorem glued_nonzero : glued≠0 := by rw [glued_epsilon]; exact SmoothFormalLocalization.epsilon_nonzero

theorem glued_real_zero (h : Hom (Carrier stage) ℝ) : h glued=0 := by
  rw [glued_epsilon]
  have he := congrArg h.toAlgHom SmoothFormalLocalization.epsilon_square
  simp only [map_mul,map_zero] at he
  exact mul_self_eq_zero.mp he

end Nilpotent

abbrev zeroStage : Code := ⟨0,1,SmoothPrincipalDescent.improper⟩

theorem empty_cover : (⊥ : Sieve (op zeroStage)) ∈ topology (op zeroStage) := by
  have h := principal_covering zeroStage (Fin.elim0 : Fin 0 → Carrier zeroStage)
    ((empty_iff _).mpr SmoothPrincipalDescent.improper_trivial)
  have he : principalSieve zeroStage (Fin.elim0 : Fin 0 → Carrier zeroStage)=⊥ := by
    apply Sieve.ext
    intro Y f
    constructor
    · rintro ⟨Z,u,v,⟨i⟩,_⟩
      exact Fin.elim0 i
    · intro hf
      exact False.elim hf
  rwa [he] at h

/-- The actual sheaf condition on the empty sieve supplies its unique global scalar. -/
theorem empty_amalgamation : ∃! _a : Carrier zeroStage, True := by
  let x : Presieve.FamilyOfElements scalarData (⊥ : Sieve (op zeroStage)).arrows := fun _ _ h => False.elim h
  have hx : x.Compatible := by intro Y Z W g h f e hf; exact False.elim hf
  obtain ⟨a,ha,hu⟩ := scalar_isSheaf (⊥ : Sieve (op zeroStage)) empty_cover x hx
  refine ⟨a,trivial,fun b _ => hu b ?_⟩
  intro Y f hf
  exact False.elim hf

/-- All representables, including arbitrary source presentations, glue sieve matching data. -/
theorem representable_matching (B : Code)
    (x : Presieve.FamilyOfElements (yoneda.obj (op B)) (principalSieve line lineOpens).arrows)
    (hx : x.Compatible) : ∃! h, x.IsAmalgamation h :=
  yoneda_isSheaf (op B) (principalSieve line lineOpens) line_cover x hx

end Examples.SmoothGeometricSite
