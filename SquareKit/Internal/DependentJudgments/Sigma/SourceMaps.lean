import SquareKit.Internal.DependentJudgments.Sigma.Authoring
import SquareKit.Internal.DependentJudgments.Sigma.Maps
import SquareKit.Internal.DependentJudgments.TypedMaps

/-! The admitted Sigma language inherits partial interpretation and typed model
map preservation. Contextual J preservation and Sigma constructor preservation
share one structural map. Undefined equality is not transported. -/
namespace SquareKit.Internal.DependentJudgments.Sigma
open GuardedTheory PathTransport.Typed
set_option backward.isDefEq.respectTransparency false
universe u v w

/-- A single model map preserves the old contextual fragment and the new Sigma
operations. Elimination preservation is derived in `Map.split`. -/
structure SourceMap {M : PathTransport.Typed.Model.{u}} {N : PathTransport.Typed.Model.{v}}
    (S : Capability M.toStructuralModel) (T : Capability N.toStructuralModel)
    extends PathTransport.Typed.ModelMap M N where
  sigma : ∀ {Γ} (A : M.Family Γ) (B : M.Family (M.extend Γ A)),
    family (S.sigma A B) = T.sigma (family A) (displayFamily toStructuralMap A B)
  pack : ∀ {Γ} (A : M.Family Γ) (B : M.Family (M.extend Γ A)),
    HEq (substitution (S.pack A B)) (T.pack (family A) (displayFamily toStructuralMap A B))

namespace SourceMap
variable {M : PathTransport.Typed.Model.{u}} {N : PathTransport.Typed.Model.{v}}
  {P : PathTransport.Typed.Model.{w}}
  {S : Capability M.toStructuralModel} {T : Capability N.toStructuralModel}
  {U : Capability P.toStructuralModel}

def toSigmaMap (F : SourceMap S T) : Map S T where
  toStructuralMap := F.toStructuralMap
  sigma := F.sigma
  pack := F.pack

def identityMap (S : Capability M.toStructuralModel) : SourceMap S S where
  toModelMap := PathTransport.Typed.ModelMap.identityMap M
  sigma _ _ := rfl
  pack _ _ := HEq.rfl

def compose (G : SourceMap T U) (F : SourceMap S T) : SourceMap S U where
  toModelMap := G.toModelMap.compose F.toModelMap
  sigma := (G.toSigmaMap.compose F.toSigmaMap).sigma
  pack := (G.toSigmaMap.compose F.toSigmaMap).pack

@[simp] theorem compose_identity (F : SourceMap S T) : compose (identityMap T) F = F := by
  cases F; rfl

@[simp] theorem identity_compose (F : SourceMap S T) : compose F (identityMap S) = F := by
  cases F; rfl

theorem compose_assoc {Q : PathTransport.Typed.Model} {R : Capability Q.toStructuralModel}
    (H : SourceMap U R) (G : SourceMap T U) (F : SourceMap S T) :
    compose (compose H G) F = compose H (compose G F) := by
  cases F; cases G; cases H; rfl

end SourceMap

variable {M : StructuralModel.{u}} {N : StructuralModel.{v}}

theorem inputs_some {a b : Value M} {p : Inputs M} (h : inputs M a b = some p) :
    a = .family p.context p.first ∧ b = .family (M.extend p.context p.first) p.second := by
  cases a <;> simp only [inputs] at h
  all_goals try contradiction
  rename_i Γ A
  cases hb : Value.familyAt (M.extend Γ A) b with
  | none => simp [hb] at h
  | some B =>
    simp only [hb, pure] at h
    cases h
    exact ⟨rfl, Value.familyAt_some hb⟩

def Inputs.map (F : StructuralMap M N) (p : Inputs M) : Inputs N :=
  ⟨F.context p.context, F.family p.first, displayFamily F p.first p.second⟩

theorem inputs_map (F : StructuralMap M N) {a b : Value M} {p : Inputs M}
    (h : inputs M a b = some p) :
    inputs N (Value.map F a) (Value.map F b) = some (p.map F) := by
  rcases inputs_some h with ⟨ha, hb⟩
  rw [ha, hb]
  simp only [Value.map]
  rw [Value.family_heq_eq (F.extend p.first)
    (show HEq (F.family p.second) (displayFamily F p.first p.second) from (cast_heq _ _).symm)]
  exact inputs_values _ _ _ _

theorem operation_map {S : Capability M} {T : Capability N} (F : Map S T)
    (op : Operation) (args : Fin 2 → Value M) (h : operation M S op args ≠ .invalid) :
    Value.map F.toStructuralMap (operation M S op args) =
      operation N T op (Value.map F.toStructuralMap ∘ args) := by
  cases hp : inputs M (args 0) (args 1) with
  | none => simp [operation, hp] at h
  | some p =>
    have hm := inputs_map F.toStructuralMap hp
    simp only [operation, Function.comp_apply, hp, hm]
    cases op with
    | sigma =>
      exact
        Value.family_heq_eq rfl (heq_of_eq (F.sigma p.first p.second))
    | pack =>
      exact
        Value.substitution_heq_eq (F.sumContext p.first p.second)
          (displayContext F.toStructuralMap p.first p.second) (F.pack p.first p.second)
    | unpack =>
      exact
        Value.substitution_heq_eq (displayContext F.toStructuralMap p.first p.second)
          (F.sumContext p.first p.second) (F.unpack p.first p.second)

theorem operands_defined (S : Capability M) (op : Operation) (args : Fin 2 → Value M)
    (h : operation M S op args ≠ .invalid) : ∀ i, args i ≠ .invalid := by
  cases hp : inputs M (args 0) (args 1) with
  | none => simp [operation, hp] at h
  | some p =>
    rcases inputs_some hp with ⟨ha, hb⟩
    intro i
    fin_cases i
    · change args 0 ≠ .invalid
      rw [ha]; intro h; cases h
    · change args 1 ≠ .invalid
      rw [hb]; intro h; cases h

noncomputable def partialAlgebra (M : PathTransport.Typed.Model.{u})
    (S : Capability M.toStructuralModel) : PartialAlgebra signature where
  toAlgebra := algebra M S
  invalid := .invalid
  strict op args h := by
    cases op with
    | inl op => exact (Contextual.partialAlgebra M).strict op args h
    | inr op => exact operands_defined S op args h

noncomputable def partialHom {M : PathTransport.Typed.Model.{u}} {N : PathTransport.Typed.Model.{v}}
    {S : Capability M.toStructuralModel} {T : Capability N.toStructuralModel}
    (F : SourceMap S T) : PartialHom (partialAlgebra M S) (partialAlgebra N T) where
  map := Value.map F.toStructuralMap
  operation op args h := by
    cases op with
    | inl op => exact (Contextual.partialHom F.toModelMap).operation op args h
    | inr op => exact operation_map F.toSigmaMap op args h
  defined := Value.map_defined F.toStructuralMap
  predicate p args h := by
    cases p with
    | inl p => exact (Contextual.partialHom F.toModelMap).predicate p args h
    | inr p => nomatch p

/-- Every defined source expression, including nested constructor recipes,
commutes with the specified model map. -/
theorem interpret_map {M : PathTransport.Typed.Model.{u}} {N : PathTransport.Typed.Model.{v}}
    {S : Capability M.toStructuralModel} {T : Capability N.toStructuralModel}
    (F : SourceMap S T) {V : Type} (e : Expression V) (ρ : V → Value M.toStructuralModel)
    (h : e.eval (algebra M S) ρ ≠ .invalid) :
    Value.map F.toStructuralMap (e.eval (algebra M S) ρ) =
      e.eval (algebra N T) (Value.map F.toStructuralMap ∘ ρ) :=
  (partialHom F).eval e ρ h

/-- This entry point accepts the interpreted term guard from any admitted
theory on the shared signature, including the stable reindexing extension. -/
theorem interpret_term_map {M : PathTransport.Typed.Model.{u}} {N : PathTransport.Typed.Model.{v}}
    {S : Capability M.toStructuralModel} {T : Capability N.toStructuralModel}
    (F : SourceMap S T) {V : Type} {Γ A t : Expression V}
    (ρ : V → Value M.toStructuralModel)
    (ht : (term Γ A t).eval (algebra M S) ρ) :
    Value.map F.toStructuralMap (t.eval (algebra M S) ρ) =
      t.eval (algebra N T) (Value.map F.toStructuralMap ∘ ρ) := by
  apply interpret_map F
  rcases ht with ⟨Γ', A', t', _, _, ht'⟩
  change t.eval (algebra M S) ρ = .term Γ' A' t' at ht'
  rw [ht']
  intro h
  cases h

variable {V : Type} {Ω : List (Judgment V)}

abbrev Tel (n : Nat) (Γ T : Expression V) :=
  Derivation theory Ω (.pred (.inl (.inr (.telescope n))) ![Γ, T])

structure TypedEquality (Ω : List (Judgment V)) (Γ A s t : Expression V) where
  left : Tm (Ω := Ω) Γ A s
  right : Tm (Ω := Ω) Γ A t
  equality : Equal (Ω := Ω) s t

/-- Evidence of definedness is generated from source typing, not a semantic
condition that an ordinary author must prove at every interpretation. -/
inductive Defined (Ω : List (Judgment V)) : Expression V → Type where
  | context (h : Ctx (Ω := Ω) Γ) : Defined Ω Γ
  | family (h : Ty (Ω := Ω) Γ A) : Defined Ω A
  | term (h : Tm (Ω := Ω) Γ A t) : Defined Ω t
  | substitution (h : Sub (Ω := Ω) Δ Γ σ) : Defined Ω σ
  | telescope (h : Tel (Ω := Ω) n Γ T) : Defined Ω T

theorem Defined.sound {e : Expression V} (he : Defined Ω e)
    (M : PathTransport.Typed.Model.{u}) (S : Capability M.toStructuralModel) (ρ : V → Value M.toStructuralModel)
    (hΩ : ∀ p ∈ Ω, p.eval (algebra M S) ρ) : e.eval (algebra M S) ρ ≠ .invalid := by
  cases he with
  | context h =>
    rcases interpret h M S ρ hΩ with ⟨Γ, hΓ⟩
    change e.eval (algebra M S) ρ = .context Γ at hΓ
    erw [hΓ]
    intro h; cases h
  | family h =>
    rcases interpret h M S ρ hΩ with ⟨Γ, A, _, hA⟩
    change e.eval (algebra M S) ρ = .family Γ A at hA
    erw [hA]
    intro h; cases h
  | term h =>
    rcases interpret h M S ρ hΩ with ⟨Γ, A, t, _, _, ht⟩
    change e.eval (algebra M S) ρ = .term Γ A t at ht
    erw [ht]
    intro h; cases h
  | substitution h =>
    rcases interpret h M S ρ hΩ with ⟨Δ, Γ, σ, _, _, hσ⟩
    change e.eval (algebra M S) ρ = .substitution Δ Γ σ at hσ
    erw [hσ]
    intro h; cases h
  | telescope h =>
    rcases interpret h M S ρ hΩ with ⟨Γ, T, _, hT⟩
    change e.eval (algebra M S) ρ = .telescope Γ _ T at hT
    erw [hT]
    intro h; cases h

/-- Positive guards already entail definedness of each argument. Equality
assumptions additionally retain source typing of both operands. -/
def TypedAssumptions (Ω : List (Judgment V)) : Prop :=
  ∀ s t, Atom.eq s t ∈ Ω → Nonempty (Defined Ω s) ∧ Nonempty (Defined Ω t)

theorem predicate_defined (M : PathTransport.Typed.Model.{u})
    (S : Capability M.toStructuralModel) (p : signature.Predicate)
    (args : Fin (signature.arguments p) → Value M.toStructuralModel)
    (h : (algebra M S).predicate p args) : ∀ i, args i ≠ .invalid := by
  cases p with
  | inl p => exact Contextual.predicate_defined M p args h
  | inr p => nomatch p

/-- Each source assumption transports under the specified model map. No
reflection of equality, sorting, or invalid values is needed. -/
theorem premises_map {M : PathTransport.Typed.Model.{u}} {N : PathTransport.Typed.Model.{v}}
    {S : Capability M.toStructuralModel} {T : Capability N.toStructuralModel}
    (F : SourceMap S T) (typed : TypedAssumptions Ω) (ρ : V → Value M.toStructuralModel)
    (hΩ : ∀ p ∈ Ω, p.eval (algebra M S) ρ) :
    ∀ p ∈ Ω, p.eval (algebra N T) (Value.map F.toStructuralMap ∘ ρ) := by
  intro p hp
  cases p with
  | eq s t =>
    rcases typed s t hp with ⟨⟨hs⟩, ⟨ht⟩⟩
    have h := congrArg (Value.map F.toStructuralMap) (hΩ (.eq s t) hp)
    change Value.map F.toStructuralMap (s.eval (algebra M S) ρ) =
      Value.map F.toStructuralMap (t.eval (algebra M S) ρ) at h
    erw [interpret_map F s ρ (hs.sound M S ρ hΩ), interpret_map F t ρ (ht.sound M S ρ hΩ)] at h
    exact h
  | pred p args =>
    have h := hΩ (.pred p args) hp
    have hd := predicate_defined M S p (fun i => (args i).eval (algebra M S) ρ) h
    have hm := (partialHom F).predicate p (fun i => (args i).eval (algebra M S) ρ) h
    have e : (Value.map F.toStructuralMap ∘ fun i => (args i).eval (algebra M S) ρ) =
        (fun i => (args i).eval (algebra N T) (Value.map F.toStructuralMap ∘ ρ)) :=
      funext (fun i => interpret_map F (args i) ρ (hd i))
    change (algebra N T).predicate p
      (Value.map F.toStructuralMap ∘ fun i => (args i).eval (algebra M S) ρ) at hm
    erw [e] at hm
    exact hm

/-- The same derivation is admitted at the target interpretation. -/
theorem interpret_target {a : Judgment V} (d : Derivation theory Ω a)
    {M : PathTransport.Typed.Model.{u}} {N : PathTransport.Typed.Model.{v}}
    {S : Capability M.toStructuralModel} {T : Capability N.toStructuralModel}
    (F : SourceMap S T) (typed : TypedAssumptions Ω) (ρ : V → Value M.toStructuralModel)
    (hΩ : ∀ p ∈ Ω, p.eval (algebra M S) ρ) :
    a.eval (algebra N T) (Value.map F.toStructuralMap ∘ ρ) :=
  interpret d N T _ (premises_map F typed ρ hΩ)

/-- Typing supplies the side condition for preservation of the retained value. -/
theorem Tm.interpret_map {Γ A t : Expression V} (ht : Tm (Ω := Ω) Γ A t)
    {M : PathTransport.Typed.Model.{u}} {N : PathTransport.Typed.Model.{v}}
    {S : Capability M.toStructuralModel} {T : Capability N.toStructuralModel}
    (F : SourceMap S T) (ρ : V → Value M.toStructuralModel)
    (hΩ : ∀ p ∈ Ω, p.eval (algebra M S) ρ) :
    Value.map F.toStructuralMap (t.eval (algebra M S) ρ) =
      t.eval (algebra N T) (Value.map F.toStructuralMap ∘ ρ) :=
  Sigma.interpret_map F t ρ ((Defined.term ht).sound M S ρ hΩ)

/-- Typed comparison results transport even when the surrounding raw theory
contains untyped equality assumptions: both result operands are defined in the
source interpretation. Reusing all target premises uses `interpret_target`. -/
theorem TypedEquality.map {Γ A s t : Expression V}
    (comparison : TypedEquality Ω Γ A s t)
    {M : PathTransport.Typed.Model.{u}} {N : PathTransport.Typed.Model.{v}}
    {S : Capability M.toStructuralModel} {T : Capability N.toStructuralModel}
    (F : SourceMap S T) (ρ : V → Value M.toStructuralModel)
    (hΩ : ∀ p ∈ Ω, p.eval (algebra M S) ρ) :
    s.eval (algebra N T) (Value.map F.toStructuralMap ∘ ρ) =
      t.eval (algebra N T) (Value.map F.toStructuralMap ∘ ρ) := by
  have h := interpret comparison.equality M S ρ hΩ
  change s.eval (algebra M S) ρ = t.eval (algebra M S) ρ at h
  rw [← comparison.left.interpret_map F ρ hΩ,
    ← comparison.right.interpret_map F ρ hΩ, h]


/-- An ordinary pair author uses source typings; all constructor and model-map
coherence is supplied by the admitted interpretation. -/
theorem Tm.pair_map {Γ A B a b : Expression V}
    (hA : Ty (Ω := Ω) Γ A) (hB : Ty (Ω := Ω) (extend Γ A) B)
    (ha : Tm (Ω := Ω) Γ A a)
    (hb : Tm (Ω := Ω) Γ (subTy B (pairSub A (identitySub Γ) a)) b)
    {M : PathTransport.Typed.Model.{u}} {N : PathTransport.Typed.Model.{v}}
    {S : Capability M.toStructuralModel} {T : Capability N.toStructuralModel}
    (F : SourceMap S T) (ρ : V → Value M.toStructuralModel)
    (hΩ : ∀ p ∈ Ω, p.eval (algebra M S) ρ) :
    Value.map F.toStructuralMap ((Sigma.pair Γ A B a b).eval (algebra M S) ρ) =
      (Sigma.pair Γ A B a b).eval (algebra N T) (Value.map F.toStructuralMap ∘ ρ) :=
  (Tm.pair hA hB ha hb).interpret_map F ρ hΩ

/-- The dependent motive is retained in the source typing used by preservation. -/
theorem Tm.split_map {Γ A B C d : Expression V}
    (hA : Ty (Ω := Ω) Γ A) (hB : Ty (Ω := Ω) (extend Γ A) B)
    (hC : Ty (Ω := Ω) (extend Γ (sigma A B)) C)
    (hd : Tm (Ω := Ω) (branchContext Γ A B) (subTy C (pack A B)) d)
    {M : PathTransport.Typed.Model.{u}} {N : PathTransport.Typed.Model.{v}}
    {S : Capability M.toStructuralModel} {T : Capability N.toStructuralModel}
    (F : SourceMap S T) (ρ : V → Value M.toStructuralModel)
    (hΩ : ∀ p ∈ Ω, p.eval (algebra M S) ρ) :
    Value.map F.toStructuralMap ((Sigma.split A B d).eval (algebra M S) ρ) =
      (Sigma.split A B d).eval (algebra N T) (Value.map F.toStructuralMap ∘ ρ) :=
  (Tm.split hA hB hC hd).interpret_map F ρ hΩ

theorem splitAssumptions_typed : TypedAssumptions (List.ofFn splitRule.premise) := by
  intro s t h
  obtain ⟨i, hi⟩ := List.mem_ofFn.mp h
  fin_cases i <;> cases hi

/-- The fixed, model-independent split derivation is admitted at every target
of a SourceMap; its positive premises transport automatically. -/
theorem splitDerivation_target
    {M : PathTransport.Typed.Model.{u}} {N : PathTransport.Typed.Model.{v}}
    {S : Capability M.toStructuralModel} {T : Capability N.toStructuralModel}
    (F : SourceMap S T) (ρ : Fin 5 → Value M.toStructuralModel)
    (hΩ : ∀ p ∈ List.ofFn splitRule.premise, p.eval (algebra M S) ρ) :
    splitRule.conclusion.eval (algebra N T) (Value.map F.toStructuralMap ∘ ρ) :=
  interpret_target splitDerivation F splitAssumptions_typed ρ hΩ

end SquareKit.Internal.DependentJudgments.Sigma
