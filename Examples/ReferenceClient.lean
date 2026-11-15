import SquareKit.Internal.DependentJudgments.ReferenceSoundness
import SquareKit.Internal.DependentJudgments.ReferenceSignature
import Examples.DependentClientMigration

/-! The retained client's selected dependent pair has an independent typed
reference derivation over a finite, declared context. Its interpretation recovers
the chosen arrow, rather than merely an inhabitant of the same hom type. -/
namespace Examples.ReferenceClient
open SquareKit.GuardedTheory
open SquareKit.Internal.DependentJudgments.Contextual
open DependentClientMigration
set_option backward.isDefEq.respectTransparency false
noncomputable section

variable {V : Type} {Ξ : List (Reference.Declaration V)} {Γ A t : Expression V}

def doublePair_typed (ht : Reference.Derives Ξ (.has (.tm Γ A) t)) :
    Reference.Derives Ξ
      (.has (.sub Γ (extend (extend Γ A) (secondFamily Γ A))) (doublePair Γ A t)) := by
  have hA := ht.termFamily
  have hs := Reference.Derives.pair hA (.identitySub hA.typeContext)
    (.convert ht (.eqSymm (.subTyId hA)))
  exact .pair (.identity (.generic hA) (.generic hA)) hs
    (.subTm (.reflexivity (.generic hA)) hs)

abbrev base : Expression (Fin 3) := .var 0
abbrev context := extend empty base
abbrev family : Expression (Fin 3) := .var 1
abbrev point : Expression (Fin 3) := .var 2
abbrev declarations : List (Reference.Declaration (Fin 3)) :=
  [.family empty base, .family context family, .term context family point]
abbrev hBase : Reference.Derives declarations (.has (.ty empty) base) :=
  .familyDecl (by simp [declarations]) .empty
abbrev hFamily : Reference.Derives declarations (.has (.ty context) family) :=
  .familyDecl (by simp [declarations]) (.extend hBase)
abbrev hPoint : Reference.Derives declarations (.has (.tm context family) point) :=
  .termDecl (by simp [declarations]) hFamily

def signature_valid : Reference.WellFormedSignature declarations := by
  have h0 : Reference.WellFormedSignature
      ([.family empty base] : List (Reference.Declaration (Fin 3))) :=
    .family 0 .nil .empty (by simp [Reference.Fresh])
  have hb : Reference.Derives [.family empty base] (.has (.ty empty) base) :=
    .familyDecl (by simp) .empty
  have h1 : Reference.WellFormedSignature [.family empty base, .family context family] :=
    .family 1 h0 (.extend hb) (by simp [Reference.Fresh, Reference.Declaration.name, base])
  have hb' : Reference.Derives [.family empty base, .family context family]
      (.has (.ty empty) base) := .familyDecl (by simp) .empty
  have hf : Reference.Derives [.family empty base, .family context family]
      (.has (.ty context) family) := .familyDecl (by simp) (.extend hb')
  exact .term 2 h1 hf (by simp [Reference.Fresh, Reference.Declaration.name, base, family])

abbrev chosen := doublePair context family point
def chosen_typed := doublePair_typed hPoint

namespace Interpretation
open SquareKit.Internal.DependentJudgments SquareKit.Internal.PathTransport.Typed
open Semantics
universe u
variable (M : Model.{u})

def environment : Fin 3 → Value M.toStructuralModel :=
  ![.family M.empty (M.base M.empty),
    .family (Original.contextCode M) (Original.familyCode M),
    .term (Original.contextCode M) (Original.familyCode M) (Original.point M)]

theorem context_eval : context.eval (Contextual.algebra M) (environment M) =
    .context (Original.contextCode M) := by
  change SquareKit.Internal.DependentJudgments.operation M.toStructuralModel .extend
    ![.context M.empty, .family M.empty (M.base M.empty)] = _
  simp [SquareKit.Internal.DependentJudgments.operation]
  rfl

theorem declarations_valid : ∀ d ∈ declarations,
    d.encode.eval (Contextual.algebra M) (environment M) := by
  intro d hd
  simp [declarations] at hd
  rcases hd with rfl | rfl | rfl
  · exact ⟨M.empty, M.base M.empty, rfl, rfl⟩
  · exact ⟨Original.contextCode M, Original.familyCode M, context_eval M, rfl⟩
  · exact ⟨Original.contextCode M, Original.familyCode M, Original.point M,
      context_eval M, rfl, rfl⟩

/-- This semantic typing result consumes the new reference translation. -/
theorem typed : (Reference.Claim.has
    (.sub context (extend (extend context family) (secondFamily context family))) chosen).Valid
      M (environment M) :=
  Reference.sound M (environment M) (declarations_valid M) chosen_typed

/-- The selected certificate of the original retained argument is recovered
exactly. The source derivation here covers its right endpoint. -/
theorem recovers : chosen.eval (Contextual.algebra M) (environment M) =
    .substitution (Original.contextCode M) (target M)
      (interpretSub M Authoring.CongruenceCaller.dependentPairedRight) := by
  rw [Original.right_selected]
  exact doublePair_eval M (environment M) context family point _ _ _ (context_eval M) rfl rfl

def recovered := (chosen.eval (Contextual.algebra M) (environment M)).substitutionAt
  (Original.contextCode M) (target M)

theorem recovered_eq : recovered M =
    some (interpretSub M Authoring.CongruenceCaller.dependentPairedRight) := by
  unfold recovered
  rw [recovers, Value.substitutionAt_substitution]

/-- Recovering the left endpoint additionally uses the retained client's own
proof; it is not a translation of that proof into the reference calculus. -/
theorem agrees_with_original : recovered M =
    some (interpretSub M Authoring.CongruenceCaller.dependentPairedLeft) := by
  rw [recovered_eq, Original.original_guarantee]

theorem recovered_twice {D E : M.Context}
    (σ : M.Substitution D (Original.contextCode M)) (τ : M.Substitution E D) :
    (recovered M).map (fun f => M.compSub (M.compSub f σ) τ) =
      some (M.compSub (M.compSub
        (interpretSub M Authoring.CongruenceCaller.dependentPairedRight) σ) τ) := by
  rw [recovered_eq]
  rfl

end Interpretation
end
end Examples.ReferenceClient
