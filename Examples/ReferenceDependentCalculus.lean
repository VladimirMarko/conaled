import SquareKit.Internal.DependentJudgments.ReferenceSoundness
import SquareKit.Internal.DependentJudgments.ReferenceGenerated
import SquareKit.Internal.DependentJudgments.ReferenceSignature
import SquareKit.Internal.DependentJudgments.NativeTypeModel

/-! A two-entry dependent tail and a motive mentioning its last generic term.
The branch is constructed by reflexivity and type conversion, then interpreted
through the independent reference calculus's forward translation. -/
namespace Examples.ReferenceDependentCalculus
open SquareKit.GuardedTheory
open SquareKit.Internal.DependentJudgments.Contextual

abbrev A : Expression (Fin 4) := .var 0
abbrev x : Expression (Fin 4) := .var 1
abbrev B : Expression (Fin 4) := .var 2
abbrev C : Expression (Fin 4) := .var 3
abbrev P := path A x
abbrev ΓB := extend P B
abbrev ΓC := extend ΓB C
abbrev declarations : List (Reference.Declaration (Fin 4)) :=
  [.family empty A, .term empty A x, .family P B, .family ΓB C]

abbrev hA : Reference.Derives declarations (.has (.ty empty) A) :=
  .familyDecl (by simp [declarations]) .empty
abbrev hx : Reference.Derives declarations (.has (.tm empty A) x) :=
  .termDecl (by simp [declarations]) hA
abbrev hB : Reference.Derives declarations (.has (.ty P) B) :=
  .familyDecl (by simp [declarations]) (.path hx)
abbrev hC : Reference.Derives declarations (.has (.ty ΓB) C) :=
  .familyDecl (by simp [declarations]) (.extend hB)

abbrev tail : Reference.Tail (Fin 4) := .cons B (.cons C .nil)
abbrev hTail : Reference.Derives declarations (.tail P tail) :=
  .cons hB (.cons hC (.nil (.extend hC)))
abbrev E := subTy C (weaken ΓB C)
abbrev last := generic ΓB C
abbrev hLast : Reference.Derives declarations (.has (.tm ΓC E) last) := .generic hC
abbrev D := identity E last last
abbrev hD : Reference.Derives declarations (.has (.ty ΓC) D) := .identity hLast hLast
abbrev rootMap := tail.map empty (root A x)
noncomputable def hRootMap : Reference.Derives declarations
    (.has (.sub ((tail.reindex empty (root A x)).total empty) ΓC) rootMap) :=
  Reference.Derives.tailMap hTail (.root hx)
abbrev branch := reflexivity (subTy E rootMap) (subTm last rootMap)
noncomputable def hBranch : Reference.Derives declarations
    (.has (.tm ((tail.reindex empty (root A x)).total empty) (subTy D rootMap)) branch) :=
  .convert (.reflexivity (.subTm hLast hRootMap))
    (.eqSymm (.identitySubLaw hLast hLast hRootMap))

noncomputable def dependentJ : Reference.Derives declarations
    (.has (.tm ΓC D) (j A x (tail.code P) D branch)) :=
  .j hx hTail hD hBranch

noncomputable def beta : Reference.Derives declarations
    (.eq (.tm ((tail.reindex empty (root A x)).total empty) (subTy D rootMap))
      (subTm (j A x (tail.code P) D branch) rootMap) branch) :=
  Reference.Derives.jComputation hx hTail hD hBranch

/-- This checks the actual forward correspondence, including its conversions
between finite source tails and explicit target telescope codes. -/
noncomputable def guardedBeta : Reference.Target (Ω := declarations.map Reference.Declaration.encode)
    (.eq (subTm (j A x (tail.code P) D branch) rootMap) branch) := Reference.translate beta

/-- Two genuine extensions are substituted away by composition of weakenings.
The family of the last generic term changes at each step. -/
noncomputable def substitutedTwice : Reference.Derives declarations
    (.eq (.tm (extend (extend ΓC E) (subTy E (weaken ΓC E)))
      (subTy D (comp (weaken ΓC E) (weaken (extend ΓC E) (subTy E (weaken ΓC E))))))
      (subTm (subTm (j A x (tail.code P) D branch) (weaken ΓC E))
        (weaken (extend ΓC E) (subTy E (weaken ΓC E))))
      (subTm (j A x (tail.code P) D branch)
        (comp (weaken ΓC E) (weaken (extend ΓC E) (subTy E (weaken ΓC E)))))) :=
  .subTmComp dependentJ (.weaken (.termFamily hLast))
    (.weaken (.subTy (.termFamily hLast) (.weaken (.termFamily hLast))))

abbrev parameterSub := weaken empty A
abbrev reindexedTail := tail.alongPath A x parameterSub
abbrev newPath := path (subTy A parameterSub) (subTm x parameterSub)
abbrev liftedParameter := tail.alongPathMap A x parameterSub
abbrev reindexedBranch := subTm branch (branchMap A x (tail.code P) parameterSub)
abbrev naturalityClaim : Reference.Claim (Fin 4) :=
  .eq (.tm (reindexedTail.total newPath) (subTy D liftedParameter))
    (subTm (j A x (tail.code P) D branch) liftedParameter)
    (j (subTy A parameterSub) (subTm x parameterSub) (reindexedTail.code newPath)
      (subTy D liftedParameter) reindexedBranch)

noncomputable def naturality : Reference.Derives declarations naturalityClaim :=
  Reference.Derives.jNaturality hx hTail hD hBranch (.weaken hA)

noncomputable def signature_valid : Reference.WellFormedSignature declarations := by
  have h0 : Reference.WellFormedSignature
      ([.family empty A] : List (Reference.Declaration (Fin 4))) :=
    .family 0 .nil .empty (by simp [Reference.Fresh])
  have ha : Reference.Derives [.family empty A] (.has (.ty empty) A) :=
    .familyDecl (by simp) .empty
  have h1 : Reference.WellFormedSignature [.family empty A, .term empty A x] :=
    .term 1 h0 ha (by simp [Reference.Fresh, Reference.Declaration.name, A])
  have ha' : Reference.Derives [.family empty A, .term empty A x] (.has (.ty empty) A) :=
    .familyDecl (by simp) .empty
  have hx' : Reference.Derives [.family empty A, .term empty A x] (.has (.tm empty A) x) :=
    .termDecl (by simp) ha'
  have h2 : Reference.WellFormedSignature [.family empty A, .term empty A x, .family P B] :=
    .family 2 h1 (.path hx') (by simp [Reference.Fresh, Reference.Declaration.name, A, x])
  have ha'' : Reference.Derives [.family empty A, .term empty A x, .family P B] (.has (.ty empty) A) :=
    .familyDecl (by simp) .empty
  have hx'' : Reference.Derives [.family empty A, .term empty A x, .family P B] (.has (.tm empty A) x) :=
    .termDecl (by simp) ha''
  have hb : Reference.Derives [.family empty A, .term empty A x, .family P B] (.has (.ty P) B) :=
    .familyDecl (by simp) (.path hx'')
  exact .family 3 h2 (.extend hb) (by simp [Reference.Fresh, Reference.Declaration.name, A, x, B])

namespace Native
open SquareKit.Internal.DependentJudgments
abbrev M := NativeType.model Nat (fun n => Fin (n + 1))
abbrev a : M.Family M.empty := fun _ => Nat
abbrev point : M.Section M.empty a := ⟨fun _ => 0⟩
abbrev p := M.pathContext a point
abbrev b : M.Family p := fun _ => Nat
abbrev c : M.Family (M.extend p b) := fun z => Fin (z.2 + 1)
noncomputable def environment : Fin 4 → Value M.toStructuralModel :=
  ![.family M.empty a, .term M.empty a point, .family p b, .family (M.extend p b) c]

set_option backward.isDefEq.respectTransparency false in
 theorem declarations_valid : ∀ d ∈ declarations,
    d.encode.eval (algebra M) environment := by
  intro d hd
  simp [declarations] at hd
  rcases hd with rfl | rfl | rfl | rfl
  all_goals simp [Reference.Declaration.encode, A, x, B, C, P, ΓB, environment,
    SquareKit.GuardedTheory.Atom.eval, SquareKit.GuardedTheory.Term.eval, Contextual.algebra, Contextual.operation,
    SquareKit.Internal.DependentJudgments.operation, SquareKit.Internal.DependentJudgments.predicate,
    Contextual.empty, Contextual.path, Contextual.extend, M]

/-- A concrete model satisfies the actual declarations used by the J proof.
Its second tail family varies with the preceding natural-number entry. -/
theorem interpreted_beta : (Reference.Claim.eq
    (.tm ((tail.reindex empty (root A x)).total empty) (subTy D rootMap))
    (subTm (j A x (tail.code P) D branch) rootMap) branch).Valid M environment :=
  Reference.sound M environment declarations_valid beta

theorem interpreted_naturality : naturalityClaim.Valid M environment :=
  Reference.sound M environment declarations_valid naturality

example (z : p) : c ⟨z, 0⟩ = Fin 1 := rfl
example (z : p) : c ⟨z, 2⟩ = Fin 3 := rfl
end Native

namespace Malformed
abbrev raw : Expression (Fin 1) := .var 0
noncomputable def raw_reflexive : Reference.Target (Ω := []) (.eq raw raw) := .reflexive raw

theorem no_typed_reflexive : ¬ Nonempty (Reference.Derives []
    (.eq (.tm empty empty) raw raw)) := by
  intro ⟨h⟩
  apply Reference.not_term_of_invalid Native.M
    (fun _ : Fin 1 => SquareKit.Internal.DependentJudgments.Value.invalid)
    (Ξ := []) (by intro d hd; cases hd) (Γ := empty) (A := empty) (t := raw) rfl
  exact ⟨h.eqOperands.1⟩
end Malformed

namespace Generated
noncomputable def one : Reference.ContextTree declarations (extend empty A) :=
  .extend .empty hA
noncomputable def point : Reference.Arrow (Ξ := declarations) .empty one
    (pair A (identitySub empty) x) :=
  .pair hA (.identity .empty) (.convert hx (.eqSymm (.subTyId hA)))
noncomputable def roundTrip : Reference.Arrow (Ξ := declarations) .empty .empty
    (comp (weaken empty A) (pair A (identitySub empty) x)) :=
  .comp (.weaken .empty hA) point

/-- A generated composite through a nonempty context is the unique empty
substitution in typed source equality. -/
noncomputable def empty_uniqueness : Reference.Derives declarations
    (.eq (.sub empty empty) (comp (weaken empty A) (pair A (identitySub empty) x))
      (identitySub empty)) := roundTrip.emptyUnique
end Generated

end Examples.ReferenceDependentCalculus
