import Examples.NestedSetting
import SquareKit.Internal.DependentJudgments.NativeTypeModel
import SquareKit.Internal.DependentJudgments.Templates

/-! One generated nested pairing recipe interpreted in the supplied #319
setting families. The presentations supply semantics; this is not a parser or
an object-language type former for setting presentations. -/
namespace Examples.GuardedInternalSetting
open SquareKit SquareKit.GuardedTheory
open SquareKit.Internal.DependentJudgments
open SquareKit.Internal.FiniteSetting SquareKit.Internal.NestedSetting
set_option backward.isDefEq.respectTransparency false

namespace Source
open SquareKit.Internal.DependentJudgments.Contextual
abbrev E := Contextual.Expression (Fin 11)
abbrev gamma : E := .var 0
abbrev aType : E := .var 1
abbrev bType : E := .var 2
abbrev a : E := .var 3
abbrev b : E := .var 4
abbrev payloadType : E := .var 5
abbrev payload : E := .var 6
abbrev delta : E := .var 7
abbrev sigma : E := .var 8
abbrev theta : E := .var 9
abbrev tau : E := .var 10
abbrev firstContext : E := Contextual.extend gamma aType
abbrev nestedContext : E := Contextual.extend firstContext bType
abbrev firstPair : E := Contextual.pair aType (identitySub gamma) a
abbrev nestedPair : E := Contextual.pair bType firstPair b
abbrev firstProjection : E := Contextual.subTm (generic gamma aType)
  (Contextual.comp (weaken firstContext bType) nestedPair)
abbrev secondProjection : E := Contextual.subTm (generic firstContext bType) nestedPair
abbrev selectedPayload : E := Contextual.subTm payload nestedPair
abbrev payloadTwice : E := Contextual.subTm (Contextual.subTm selectedPayload sigma) tau

abbrev premises : List (Contextual.Judgment (Fin 11)) :=
  [family gamma aType, family firstContext bType,
   term gamma (Contextual.subTy aType (identitySub gamma)) a,
   term gamma (Contextual.subTy bType firstPair) b,
   term nestedContext payloadType payload,
   substitution delta gamma sigma, substitution theta delta tau]

def firstTyping : Contextual.Ty (Ω := premises) gamma aType := .hypothesis (by simp [premises])
def secondTyping : Contextual.Ty (Ω := premises) firstContext bType := .hypothesis (by simp [premises])
def aTyping : Tm (Ω := premises) gamma (Contextual.subTy aType (identitySub gamma)) a :=
  .hypothesis (by simp [premises])
def bTyping : Tm (Ω := premises) gamma (Contextual.subTy bType firstPair) b :=
  .hypothesis (by simp [premises])
def payloadTyping : Tm (Ω := premises) nestedContext payloadType payload :=
  .hypothesis (by simp [premises])
def sigmaTyping : Sub (Ω := premises) delta gamma sigma := .hypothesis (by simp [premises])
def tauTyping : Sub (Ω := premises) theta delta tau := .hypothesis (by simp [premises])

def pairTyping : Sub (Ω := premises) gamma nestedContext nestedPair :=
  Sub.pair secondTyping (Sub.pair firstTyping firstTyping.context.identity aTyping) bTyping

def firstProjectionTyping : Tm (Ω := premises) gamma
    (Contextual.subTy (Contextual.subTy aType (weaken gamma aType))
      (Contextual.comp (weaken firstContext bType) nestedPair)) firstProjection :=
  firstTyping.generic.substitute (secondTyping.weaken.comp pairTyping)

def secondProjectionTyping : Tm (Ω := premises) gamma
    (Contextual.subTy (Contextual.subTy bType (weaken firstContext bType)) nestedPair)
    secondProjection := secondTyping.generic.substitute pairTyping

def selectedTyping : Tm (Ω := premises) gamma
    (Contextual.subTy payloadType nestedPair) selectedPayload :=
  payloadTyping.substitute pairTyping

def twiceTyping : Tm (Ω := premises) theta
    (Contextual.subTy (Contextual.subTy (Contextual.subTy payloadType nestedPair) sigma) tau)
    payloadTwice := (selectedTyping.substitute sigmaTyping).substitute tauTyping

def firstRecovery : Equal (Ω := premises) firstProjection a := by
  have e : Equal (Ω := premises) firstProjection
      (Contextual.subTm (generic gamma aType) firstPair) :=
    Derivation.congruence (T := theory) (.inl .subTm)
      (args := ![generic gamma aType, Contextual.comp (weaken firstContext bType) nestedPair])
      (args' := ![generic gamma aType, firstPair])
      (Fin.cases (.reflexive _) (Fin.cases
        (secondTyping.weakenPair (Sub.pair firstTyping firstTyping.context.identity aTyping) bTyping)
        (fun i => nomatch i)))
  exact .transitive e (firstTyping.variablePair firstTyping.context.identity aTyping)

def secondRecovery : Equal (Ω := premises) secondProjection b :=
  secondTyping.variablePair (Sub.pair firstTyping firstTyping.context.identity aTyping) bTyping

def payloadComposition : Equal (Ω := premises) payloadTwice
    (Contextual.subTm selectedPayload (Contextual.comp sigma tau)) :=
  selectedTyping.subComp sigmaTyping tauTyping

end Source

abbrev native := NativeType.model Unit (fun _ => Unit)

variable {X Y Z : Type} (P : Presentation X) (Q : Presentation (Total P))
    (s : Argument P Q) (A : SquareKit.Internal.NestedSetting.Ty P Q)
    (t : (z : Nested P Q) → A z) (σ : Y → X) (τ : Z → Y)

/-- The second family is over the actual first generic context Total P. -/
def environment : Fin 11 → Value native.toStructuralModel :=
  ![.context X, .family X (Fiber P), .family (Total P) (Fiber Q),
    .term X (Fiber P) ⟨s.1⟩, .term X (fun x => Fiber Q (s.1.graph x)) ⟨s.2⟩,
    .family (Nested P Q) A, .term (Nested P Q) A ⟨t⟩,
    .context Y, .substitution Y X ⟨σ⟩, .context Z, .substitution Z Y ⟨τ⟩]

@[simp] theorem firstPair_value :
    Source.firstPair.eval (Contextual.algebra native) (environment P Q s A t σ τ) =
      .substitution X (Total P) ⟨s.1.graph⟩ := by
  simp [Source.firstPair, Term.eval, Contextual.algebra, operation, environment, native, NativeType.model, NativeType.structuralModel,
    Total, Section.graph, Function.comp_def]
  rfl

@[simp] theorem nestedPair_value :
    Source.nestedPair.eval (Contextual.algebra native) (environment P Q s A t σ τ) =
      .substitution X (Nested P Q) ⟨classify s⟩ := by
  simp [Source.nestedPair, Source.firstPair, Term.eval, Contextual.algebra, operation, environment, native, NativeType.model, NativeType.structuralModel,
    Total, Section.graph, Function.comp_def]
  rfl

/-- Discharge the generated source guards for arbitrary internal P, Q and
selected sections. No interpretation law is requested from the author. -/
theorem environment_valid : ∀ p ∈ Source.premises,
    p.eval (Contextual.algebra native) (environment P Q s A t σ τ) := by
  intro p hp
  simp only [Source.premises, List.mem_cons, List.not_mem_nil, or_false] at hp
  rcases hp with rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact ⟨X, Fiber P, rfl, rfl⟩
  · refine ⟨Total P, Fiber Q, ?_, rfl⟩
    simp [Term.eval, Contextual.algebra, operation, environment, native, NativeType.model, NativeType.structuralModel,
    Total, Section.graph, Function.comp_def]
  · refine ⟨X, Fiber P, ⟨s.1⟩, rfl, ?_, rfl⟩
    simp [Term.eval, Contextual.algebra, operation, environment, native, NativeType.model, NativeType.structuralModel,
    Total, Section.graph, Function.comp_def]
  · refine ⟨X, (fun x => Fiber Q (s.1.graph x)), ⟨s.2⟩, rfl, ?_, rfl⟩
    simp [Source.firstPair, Term.eval, Contextual.algebra, operation, environment, native, NativeType.model, NativeType.structuralModel,
    Total, Section.graph, Function.comp_def]
  · refine ⟨Nested P Q, A, ⟨t⟩, ?_, rfl, rfl⟩
    simp [Term.eval, Contextual.algebra, operation, environment, native, NativeType.model, NativeType.structuralModel,
    Total, Section.graph, Function.comp_def]
  · exact ⟨Y, X, ⟨σ⟩, rfl, rfl, rfl⟩
  · exact ⟨Z, Y, ⟨τ⟩, rfl, rfl, rfl⟩

/-- The interpreted generated derivation establishes the nested classifying
map, with both actual dependent selections retained. -/
theorem generated_pair_typed :
    (Contextual.substitution Source.gamma Source.nestedContext Source.nestedPair).eval
      (Contextual.algebra native) (environment P Q s A t σ τ) :=
  Contextual.interpret Source.pairTyping native _ (environment_valid P Q s A t σ τ)

@[simp] theorem firstProjection_value :
    Source.firstProjection.eval (Contextual.algebra native) (environment P Q s A t σ τ) =
      .term X (Fiber P) ⟨s.1⟩ := by
  have h := Contextual.interpret Source.firstRecovery native _
    (environment_valid P Q s A t σ τ)
  exact h

@[simp] theorem secondProjection_value :
    Source.secondProjection.eval (Contextual.algebra native) (environment P Q s A t σ τ) =
      .term X (fun x => Fiber Q (s.1.graph x)) ⟨s.2⟩ := by
  have h := Contextual.interpret Source.secondRecovery native _
    (environment_valid P Q s A t σ τ)
  exact h

@[simp] theorem payloadTwice_value :
    Source.payloadTwice.eval (Contextual.algebra native) (environment P Q s A t σ τ) =
      .term Z (fun z => A (classify s (σ (τ z)))) ⟨fun z => t (classify s (σ (τ z)))⟩ := by
  have h := Contextual.interpret Source.payloadComposition native _
    (environment_valid P Q s A t σ τ)
  change Source.payloadTwice.eval _ _ = _ at h
  refine h.trans ?_
  simp [Source.selectedPayload, Source.nestedPair, Source.firstPair,
    Term.eval, Contextual.algebra, operation, environment, native, NativeType.model, NativeType.structuralModel,
    Nested, Total, Section.graph, classify, Function.comp_def]

/-- The chosen point at the second base-change stage retains both components. -/
def secondStage (z : Z) :
    SquareKit.Internal.NestedSetting.Pullback (P.subst σ) (reindex P Q σ) τ :=
  ⟨z, classify (argumentSub s σ) (τ z), rfl⟩

/-- #319's constructed context comparison recovers the freshly reindexed pair. -/
theorem selected_context_comparison (z : Z) :
    comparison P Q (σ ∘ τ) (rebase P Q σ τ (secondStage P Q s σ τ z)) =
      classify (argumentSub (argumentSub s σ) τ) z := by
  rw [argumentSub_comp]
  exact selected_comparison s (σ ∘ τ) z

/-- The payload type is transported along that same context comparison. -/
theorem selected_type_comparison (z : Z) :
    typeSub (typeSub A σ) τ
      (comparison P Q (σ ∘ τ) (rebase P Q σ τ (secondStage P Q s σ τ z))) =
      A (classify s (σ (τ z))) :=
  type_comparison A (σ ∘ τ) (rebase P Q σ τ (secondStage P Q s σ τ z))

/-- The arbitrary dependent term uses precisely the preceding type equation. -/
theorem selected_term_comparison (z : Z) :
    cast (selected_type_comparison P Q s A σ τ z)
      (termSub (termSub t σ) τ
        (comparison P Q (σ ∘ τ) (rebase P Q σ τ (secondStage P Q s σ τ z)))) =
      t (classify s (σ (τ z))) :=
  term_comparison t (σ ∘ τ) (rebase P Q σ τ (secondStage P Q s σ τ z))

/-- The source result is the whole dependent value reconstructed by #319's
composition comparison. Both selected components occur in its type index. -/
theorem generated_payload_comparison :
    Source.payloadTwice.eval (Contextual.algebra native) (environment P Q s A t σ τ) =
      .term Z
        (fun z => A (map P Q (σ ∘ τ)
          (comparison P Q (σ ∘ τ) (rebase P Q σ τ (secondStage P Q s σ τ z)))))
        ⟨fun z => termSub (termSub t σ) τ
          (comparison P Q (σ ∘ τ) (rebase P Q σ τ (secondStage P Q s σ τ z)))⟩ := by
  have h :
      (fun z => (⟨map P Q (σ ∘ τ)
          (comparison P Q (σ ∘ τ) (rebase P Q σ τ (secondStage P Q s σ τ z))),
        termSub (termSub t σ) τ
          (comparison P Q (σ ∘ τ) (rebase P Q σ τ (secondStage P Q s σ τ z)))⟩ :
          (a : Nested P Q) × A a)) =
      (fun z => (⟨classify s (σ (τ z)), t (classify s (σ (τ z)))⟩ :
          (a : Nested P Q) × A a)) := by
    funext z
    exact dependent_comparison_comp t σ τ (secondStage P Q s σ τ z)
  have e := congrArg (fun f : Z → (a : Nested P Q) × A a =>
    Value.term (M := native.toStructuralModel) Z
      (fun z => A (f z).1) ⟨fun z => (f z).2⟩) h
  exact (payloadTwice_value P Q s A t σ τ).trans e.symm

/-- Reusing the unchanged two projection recipes in the fresh valuation
recovers the substituted first and dependent second sections. -/
theorem fresh_projection_values :
    Source.firstProjection.eval (Contextual.algebra native)
      (environment ((P.subst σ).subst τ)
        (reindex (P.subst σ) (reindex P Q σ) τ)
        (argumentSub (argumentSub s σ) τ) (typeSub (typeSub A σ) τ)
        (termSub (termSub t σ) τ) id id) =
      .term Z (Fiber ((P.subst σ).subst τ)) ⟨(argumentSub (argumentSub s σ) τ).1⟩ ∧
    Source.secondProjection.eval (Contextual.algebra native)
      (environment ((P.subst σ).subst τ)
        (reindex (P.subst σ) (reindex P Q σ) τ)
        (argumentSub (argumentSub s σ) τ) (typeSub (typeSub A σ) τ)
        (termSub (termSub t σ) τ) id id) =
      .term Z (fun z => Fiber (reindex (P.subst σ) (reindex P Q σ) τ)
        ((argumentSub (argumentSub s σ) τ).1.graph z))
        ⟨(argumentSub (argumentSub s σ) τ).2⟩ :=
  ⟨firstProjection_value _ _ _ _ _ _ _, secondProjection_value _ _ _ _ _ _ _⟩

namespace Concrete
open Examples.NestedSetting

/-- The context component is obtained through the constructed comparison,
then observed. Both selected tags are left after n maps to 2*n+1. -/
theorem selected_tags (n : Nat) :
    tags (map first second (shift ∘ double)
      (comparison first second (shift ∘ double)
        (rebase first second shift double
          (secondStage first second selected shift double n)))) = (true, true) := by
  rw [comparison_original]
  exact expected_successor (2 * n)

/-- The source interpretation retains the concrete finite payload section,
with the actual two-substitution order in its family index. -/
theorem generated_payload :
    Source.payloadTwice.eval (Contextual.algebra native)
      (environment first second selected payload payloadChoice shift double) =
      .term Nat (fun n => payload (classify selected (2 * n + 1)))
        ⟨fun n => payloadChoice (classify selected (2 * n + 1))⟩ :=
  generated_payload_comparison first second selected payload payloadChoice shift double

/-- The same source recipes are interpreted after the two actual base changes. -/
def freshEnvironment : Fin 11 → Value native.toStructuralModel :=
  environment ((first.subst shift).subst double)
    (reindex (first.subst shift) (reindex first second shift) double) substituted
    (typeSub (typeSub payload shift) double)
    (termSub (termSub payloadChoice shift) double) id id

/-- Decode both generated projections, including the second one's type over
its selected first component. The context comparison above relates this fresh
valuation to substitution of the original whole pair. -/
theorem generated_selected_components (n : Nat) :
    Option.map (fun t => (t.down n).isLeft)
      ((Source.firstProjection.eval (Contextual.algebra native) freshEnvironment).termAt Nat
        (Fiber ((first.subst shift).subst double))) = some true ∧
    Option.map (fun t => (t.down n).isLeft)
      ((Source.secondProjection.eval (Contextual.algebra native) freshEnvironment).termAt Nat
        (fun n => Fiber (reindex (first.subst shift) (reindex first second shift) double)
          (substituted.1.graph n))) = some true := by
  have h := fresh_projection_values first second selected payload payloadChoice shift double
  change Source.firstProjection.eval (Contextual.algebra native) freshEnvironment = _ ∧
    Source.secondProjection.eval (Contextual.algebra native) freshEnvironment = _ at h
  rw [h.1, h.2]
  simp only [substituted, Value.termAt_term, Option.map_some]
  exact ⟨rfl, rfl⟩

/-- Decode the selected source result at 2: base 5, payload value 6 in Fin 7. -/
theorem generated_payload_at_two :
    Option.map (fun t => (t.down 2).val)
      ((Source.payloadTwice.eval (Contextual.algebra native)
        (environment first second selected payload payloadChoice shift double)).termAt Nat
        (fun n => payload (classify selected (2 * n + 1)))) = some 6 := by
  rw [generated_payload]
  simp only [Value.termAt_term, Option.map_some]
  rfl

/-- Reversing the substitutions changes the observed source result at zero. -/
theorem generated_order_detected :
    Option.map (fun t => (t.down 0).val)
      ((Source.payloadTwice.eval (Contextual.algebra native)
        (environment first second selected payload payloadChoice shift double)).termAt Nat
        (fun n => payload (classify selected (shift (double n))))) = some 2 ∧
    Option.map (fun t => (t.down 0).val)
      ((Source.payloadTwice.eval (Contextual.algebra native)
        (environment first second selected payload payloadChoice double shift)).termAt Nat
        (fun n => payload (classify selected (double (shift n))))) = some 3 := by
  rw [payloadTwice_value, payloadTwice_value]
  simp only [Value.termAt_term, Option.map_some]
  exact ⟨rfl, rfl⟩

end Concrete
end Examples.GuardedInternalSetting
