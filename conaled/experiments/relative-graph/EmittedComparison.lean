import EmittedEnvironment
import AcceptedGraph

namespace EmittedComparison
open SquareKit.Internal ConLeche ConLeche.SetTheory ConLeche.SetModel
open EmissionEncoding EmissionSemantics
universe w
variable {V : Type w} [SetTheory V]

def carrierLevel : ConLeche.Level := .succ (.param (N.encode `v))
def openModel := GraphEmissionPure.parameterModel.shift.shift

def objects : GraphEmissionPure.Assignment [.input, .output]
  | _, .zero => .bvar 0
  | _, .succ .zero => .bvar 1

/-- The actual producer places x at index zero and z at index one. -/
def assignment (x z A B C F G : V) : Nat → V
  | 0 => x | 1 => z | 2 => G | 3 => F | 4 => C | 5 => B | _ => A

def setting (A B C F G : V) : Setting V where
  carrier | .input => A | .middle => B | .output => C
  arrow | .first => F | .second => G

theorem laws (φ : ConLeche.Name → Nat) (A B C F G : V)
    (hA : A ∈ˢ univ (ConLeche.Level.eval φ carrierLevel))
    (hB : B ∈ˢ univ (ConLeche.Level.eval φ carrierLevel))
    (hC : C ∈ˢ univ (ConLeche.Level.eval φ carrierLevel))
    (hF : ∀ x, x ∈ˢ A → app F x ∈ˢ B)
    (hG : ∀ y, y ∈ˢ B → app G y ∈ˢ C) : Laws (setting A B C F G) carrierLevel φ where
  carrier_mem s := by cases s; exact hA; exact hB; exact hC
  arrow f := by cases f; exact hF; exact hG

theorem compatible (m : ConLeche.Model V env) (φ : ConLeche.Name → Nat) (A B C F G x z : V) :
    Compatible (m := m) (φ := φ) (setting A B C F G) (assignment x z A B C F G) openModel where
  carrier s := by cases s; exact Holds.var _ 6; exact Holds.var _ 5; exact Holds.var _ 4
  arrow f := by cases f; exact Holds.var _ 3; exact Holds.var _ 2

noncomputable def objectValues {A B C F G : V} {φ : ConLeche.Name → Nat}
    (L : Laws (setting A B C F G) carrierLevel φ) (x : GraphAdapter.Member A) (z : GraphAdapter.Member C) :
    SquareKit.Internal.Env (interpretation (setting A B C F G) L) [.input, .output] :=
  fun {s} i => by
    cases i with
    | zero => exact x
    | succ i => cases i with
      | zero => exact z
      | succ i => exact nomatch i

@[simp] theorem objectValues_input {A B C F G : V} {φ : ConLeche.Name → Nat}
    (L : Laws (setting A B C F G) carrierLevel φ) (x : GraphAdapter.Member A) (z : GraphAdapter.Member C) :
    objectValues L x z .zero = x := rfl
@[simp] theorem objectValues_output {A B C F G : V} {φ : ConLeche.Name → Nat}
    (L : Laws (setting A B C F G) carrierLevel φ) (x : GraphAdapter.Member A) (z : GraphAdapter.Member C) :
    objectValues L x z (.succ .zero) = z := rfl

theorem objects_compatible (m : ConLeche.Model V env) (φ : ConLeche.Name → Nat) (A B C F G : V)
    (L : Laws (setting A B C F G) carrierLevel φ) (x : GraphAdapter.Member A) (z : GraphAdapter.Member C) :
    AssignmentCompatible (m := m) (setting A B C F G) L (assignment x.val z.val A B C F G)
      objects (objectValues L x z) := by
  intro s i
  cases i with
  | zero => exact Holds.var _ 0
  | succ i => cases i with
    | zero => exact Holds.var _ 1
    | succ i => exact nomatch i

def premiseCore := GraphEmissionPure.formula openModel objects GraphTarget.forwardDeclaration.premise
def conclusionCore := GraphEmissionPure.formula openModel objects GraphTarget.forwardDeclaration.conclusion
def premise := (encode premiseCore).getD (.bvar 0)
def conclusion := (encode conclusionCore).getD (.bvar 0)

theorem premise_encoded : encode premiseCore = some premise := rfl
theorem conclusion_encoded : encode conclusionCore = some conclusion := rfl

/-- The general theorem is applied to the actual producer's open graph formulas. -/
theorem comparison (m : ConLeche.Model V env) (φ : ConLeche.Name → Nat)
    (pr : GraphAdapter.Primitives m carrierLevel φ) (A B C F G : V)
    (L : Laws (setting A B C F G) carrierLevel φ)
    (x : GraphAdapter.Member A) (z : GraphAdapter.Member C) (P Q : V)
    (hP : Denotes m.cval env φ (assignment x.val z.val A B C F G) premise P)
    (hQ : Denotes m.cval env φ (assignment x.val z.val A B C F G) conclusion Q) :
    ((pt : V) ∈ˢ P ↔ ∃ y : GraphAdapter.Member B,
      y.val = app F x.val ∧ z.val = app G y.val) ∧
    ((pt : V) ∈ˢ Q ↔ z.val = app G (app F x.val)) := by
  have hp := formula_comparison pr (em := openModel) rfl
    (compatible m φ A B C F G x.val z.val) (objects_compatible m φ A B C F G L x z)
    GraphTarget.forwardDeclaration.premise premise P premise_encoded hP
  have hq := formula_comparison pr (em := openModel) rfl
    (compatible m φ A B C F G x.val z.val) (objects_compatible m φ A B C F G L x z)
    GraphTarget.forwardDeclaration.conclusion conclusion Q conclusion_encoded hQ
  constructor
  · apply hp.trans
    change (∃ y : GraphAdapter.Member B,
      y = ⟨app F x.val, L.arrow Graph.Arrow.first x.val x.property⟩ ∧
      z = ⟨app G y.val, L.arrow Graph.Arrow.second y.val y.property⟩) ↔ _
    constructor
    · rintro ⟨y, hy, hz⟩
      exact ⟨y, congrArg Subtype.val hy, congrArg Subtype.val hz⟩
    · rintro ⟨y, hy, hz⟩
      exact ⟨y, Subtype.ext hy, Subtype.ext hz⟩
  · apply hq.trans
    change (z = ⟨app G (app F x.val),
      L.arrow Graph.Arrow.second _ (L.arrow Graph.Arrow.first x.val x.property)⟩) ↔ _
    exact ⟨fun h => congrArg Subtype.val h, fun h => Subtype.ext h⟩

def records : PrimitiveLaws.Records EmittedEnvironment.environment where
  eq := ⟨eqA, by rfl, by decide, rfl⟩
  and := ⟨GraphEnvironment.storedProposition andRaw, by rfl, by decide, rfl⟩
  andIntro := ⟨GraphEnvironment.storedProposition andIntroRaw, by rfl, by decide, rfl⟩
  andRec := ⟨GraphEnvironment.storedProposition andRecRaw, by rfl, by decide, rfl⟩
  existsForm := ⟨GraphEnvironment.storedProposition GraphEnvironment.existsRaw, by rfl, by decide, rfl⟩
  existsIntro := ⟨GraphEnvironment.storedProposition GraphEnvironment.existsIntroRaw, by rfl, by decide, rfl⟩
  existsRec := ⟨GraphEnvironment.storedProposition GraphEnvironment.existsRecRaw, by rfl, by decide, rfl⟩

noncomputable def primitives (m : Model V EmittedEnvironment.environment)
    (u : Level) (φ : Name → Nat) : GraphAdapter.Primitives m u φ :=
  PrimitiveLaws.primitives m records u φ



/-- Primitive signatures in the actual emitted environment discharge its laws. -/
theorem environment_comparison (m : Model V EmittedEnvironment.environment)
    (φ : ConLeche.Name → Nat) (A B C F G : V)
    (hA : A ∈ˢ univ (ConLeche.Level.eval φ carrierLevel))
    (hB : B ∈ˢ univ (ConLeche.Level.eval φ carrierLevel))
    (hC : C ∈ˢ univ (ConLeche.Level.eval φ carrierLevel))
    (hF : ∀ x, x ∈ˢ A → app F x ∈ˢ B)
    (hG : ∀ y, y ∈ˢ B → app G y ∈ˢ C)
    (x : GraphAdapter.Member A) (z : GraphAdapter.Member C) (P Q : V)
    (hP : Denotes m.cval EmittedEnvironment.environment φ (assignment x.val z.val A B C F G) premise P)
    (hQ : Denotes m.cval EmittedEnvironment.environment φ (assignment x.val z.val A B C F G) conclusion Q) :
    ((pt : V) ∈ˢ P ↔ ∃ y : GraphAdapter.Member B,
      y.val = app F x.val ∧ z.val = app G y.val) ∧
    ((pt : V) ∈ˢ Q ↔ z.val = app G (app F x.val)) :=
  comparison m φ (primitives m carrierLevel φ) A B C F G
    (laws φ A B C F G hA hB hC hF hG) x z P Q hP hQ

end EmittedComparison
#audit_graph_module
