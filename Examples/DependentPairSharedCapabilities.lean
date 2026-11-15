import Examples.DependentPairSharedCode
import SquareKit.Institutions.Capabilities

/-! The proof and code routes share one selected-evidence map. The joint law
is derived from local rule and compiler laws, not supplied as a wrapper field. -/
namespace SquareKit.DependentPairSharedFragment
open DependentPairTheoryTransport DependentBranchTheoryMaps
set_option backward.isDefEq.respectTransparency false

def setting (p : Phase) : Institutions.Setting where
  Sentence := Sentence p
  Model := SingleV → Nat
  Evidence _ j := Value j.shape

def connection (p q : Phase) : Institutions.Connection (setting p) (setting q) where
  sentence := sentenceMap
  reduct := id
  evidence _ _ x := x

def proofs (p : Phase) : Institutions.Proofs (setting p) where
  Proof j := Proof p j.shape
  interpret ρ _ d := meaning ρ d

def proofMap (p q : Phase) : Institutions.ProofMap (connection p q) (proofs p) (proofs q) where
  map _ := translate
  commutes ρ _ d := translate_meaning ρ d

def realization (p : Phase) : Institutions.Realization (setting p) where
  Carrier _ j := Code p j.shape.tag
  decode ρ _ c := c.run ρ

def realizationMap (p q : Phase) :
    Institutions.RealizationMap (connection p q) (realization p) (realization q) where
  map _ _ c := c.pass q
  commutes ρ _ c := c.pass_run q ρ

def compatible (p q : Phase) : Institutions.Compatible (connection p q)
    (proofs p) (proofs q) (realization p) (realization q) :=
  ⟨proofMap p q, realizationMap p q⟩

/-- Both routes return the same selected value, for every closed bounded proof
and environment. The program supplied here is the actual proof compiler output. -/
theorem joint_commutes {p q s} (ρ) (d : Proof p s) :
    (realization q).decode ρ (sentenceMap (⟨s⟩ : Sentence p))
      ((compatible p q).realization.map ρ ⟨s⟩ (compileCode d)) =
    (proofs q).interpret ρ (sentenceMap (⟨s⟩ : Sentence p))
      ((compatible p q).proof.map ⟨s⟩ d) := by
  change ((compileCode d).pass q).run ρ = meaning ρ (translate (q := q) d)
  rw [← compileCode_translate, compileCode_sound]

/-- Capability composition uses exactly the same evidence comparison. -/
def twoStageCompatible := (compatible .extended .target).comp (compatible .source .extended)

theorem two_stage_joint {s} (ρ) (d : Proof .source s) :
    (realization .target).decode ρ ⟨s⟩
      (twoStageCompatible.realization.map ρ ⟨s⟩ (compileCode d)) =
    (proofs .target).interpret ρ ⟨s⟩ (twoStageCompatible.proof.map ⟨s⟩ d) := by
  change (((compileCode d).pass .extended).pass .target).run ρ =
    meaning ρ (translate (q := .target) (translate (q := .extended) d))
  rw [← compileCode_translate, ← compileCode_translate, compileCode_sound]

theorem translate_identity {p s} (d : Proof p s) : translate (q := p) d = d := by
  have aux {j : Sentence p} (d : Derivation (rules p) (fun _ => Empty) j) :
      (pass p p).transport (H' := fun _ => Empty) (fun _ e => e.elim) d = d := by
    induction d with
    | hyp e => exact e.elim
    | rule step ds ih =>
      simp only [TheoryMap.transport, pass, Derivation.graft]
      congr 1
      funext i
      exact ih i
  exact aux d

theorem translate_comp {p q r s} (d : Proof p s) :
    translate (q := r) (translate (q := q) d) = translate (q := r) d := by
  have aux {j : Sentence p} (d : Derivation (rules p) (fun _ => Empty) j) :
      (pass q r).transport (H' := fun _ => Empty) (fun _ e => e.elim)
        ((pass p q).transport (H' := fun _ => Empty) (fun _ e => e.elim) d) =
      (pass p r).transport (H' := fun _ => Empty) (fun _ e => e.elim) d := by
    induction d with
    | hyp e => exact e.elim
    | rule step ds ih =>
      simp only [TheoryMap.transport, pass, Derivation.graft]
      congr 1
      funext i
      exact ih i
  exact aux d

theorem realization_identity {p} {s : Shape} (ρ) (c : Code p s.tag) :
    (realizationMap p p).map ρ (⟨s⟩ : Sentence p) c = c := c.pass_identity

theorem realization_two_stages {s : Shape} (ρ) (c : Code .source s.tag) :
    twoStageCompatible.realization.map ρ (⟨s⟩ : Sentence .source) c =
      (realizationMap .source .target).map ρ ⟨s⟩ c := c.pass_comp .extended .target

/-- The runtime square is the existing square specialization of this capability. -/
def runtimeSquare (p q : Phase) (ρ) (s : Shape) := (realizationMap p q).square ρ ⟨s⟩

theorem runtimeSquare_composition (ρ) (s : Shape) :
    twoStageCompatible.realization.square ρ ⟨s⟩ =
      Squares.compose (runtimeSquare .extended .target ρ s) (runtimeSquare .source .extended ρ s) := rfl

end SquareKit.DependentPairSharedFragment
