import SquareKit.Internal.DependentJudgments.ReferenceSubstitution
import SquareKit.DependentTheoryMaps

/-! Local rule presentation of the independent finite-tail Id/J calculus.
The table lists primitive inference boundaries, not semantic validity. -/
namespace SquareKit.Internal.DependentJudgments.Contextual.Reference
open GuardedTheory
variable {V : Type}
namespace RulePresentation

inductive Rule (Ξ : List (Declaration V)) : List (Claim V) → Claim V → Type where
  | empty : Rule Ξ ([]) (.has .ctx empty)
  | extend : Rule Ξ ([(.has (.ty Γ) A)]) (.has .ctx (extend Γ A))
  | familyDecl : Declaration.family Γ A ∈ Ξ → Rule Ξ ([(.has .ctx Γ)]) (.has (.ty Γ) A)
  | termDecl : Declaration.term Γ A t ∈ Ξ → Rule Ξ ([(.has (.ty Γ) A)]) (.has (.tm Γ A) t)
  | typeContext : Rule Ξ ([(.has (.ty Γ) A)]) (.has .ctx Γ)
  | termFamily : Rule Ξ ([(.has (.tm Γ A) t)]) (.has (.ty Γ) A)
  | subTy : Rule Ξ ([(.has (.ty Γ) A), (.has (.sub Δ Γ) σ)]) (.has (.ty Δ) (subTy A σ))
  | subTm : Rule Ξ ([(.has (.tm Γ A) t), (.has (.sub Δ Γ) σ)]) (.has (.tm Δ (subTy A σ)) (subTm t σ))
  | identitySub : Rule Ξ ([(.has .ctx Γ)]) (.has (.sub Γ Γ) (identitySub Γ))
  | comp : Rule Ξ ([(.has (.sub Δ Γ) σ), (.has (.sub Θ Δ) τ)]) (.has (.sub Θ Γ) (comp σ τ))
  | weaken : Rule Ξ ([(.has (.ty Γ) A)]) (.has (.sub (extend Γ A) Γ) (weaken Γ A))
  | generic : Rule Ξ ([(.has (.ty Γ) A)]) (.has (.tm (extend Γ A) (subTy A (weaken Γ A))) (generic Γ A))
  | pair : Rule Ξ ([(.has (.ty Γ) A), (.has (.sub Δ Γ) σ), (.has (.tm Δ (subTy A σ)) t)]) (.has (.sub Δ (extend Γ A)) (pair A σ t))
  | identity : Rule Ξ ([(.has (.tm Γ A) x), (.has (.tm Γ A) y)]) (.has (.ty Γ) (identity A x y))
  | reflexivity : Rule Ξ ([(.has (.tm Γ A) x)]) (.has (.tm Γ (identity A x x)) (reflexivity A x))
  | path : Rule Ξ ([(.has (.tm Γ A) x)]) (.has .ctx (path A x))
  | root : Rule Ξ ([(.has (.tm Γ A) x)]) (.has (.sub Γ (path A x)) (root A x))
  | pathSub : Rule Ξ ([(.has (.tm Γ A) x), (.has (.sub Δ Γ) σ)]) (.has (.sub (path (subTy A σ) (subTm x σ)) (path A x)) (pathSub A x σ))
  | nil : Rule Ξ ([(.has .ctx Γ)]) (.tail Γ .nil)
  | cons : Rule Ξ ([(.has (.ty Γ) A), (.tail (extend Γ A) T)]) (.tail Γ (.cons A T))
  | tailCode : Rule Ξ ([(.tail Γ T)]) (.has (.tel T.length Γ) (T.code Γ))
  | contextConvertTel : Rule Ξ ([(.has (.tel n Γ) t), (.eq .ctx Γ Δ)]) (.has (.tel n Δ) t)
  | tailTotal : Rule Ξ ([(.tail Γ T)]) (.has .ctx (T.total Γ))
  | branchMap : Rule Ξ ([(.has (.tm Γ A) x), (.tail (path A x) T), (.has (.sub Δ Γ) σ), (.has .ctx ((T.alongPath A x σ).rootDomain Δ (subTy A σ) (subTm x σ))), (.has .ctx (T.rootDomain Γ A x))]) (.has (.sub ((T.alongPath A x σ).rootDomain Δ (subTy A σ) (subTm x σ))
        (T.rootDomain Γ A x)) (branchMap A x (T.code (path A x)) σ))
  | branchSquare : Rule Ξ ([(.has (.tm Γ A) x), (.tail (path A x) T), (.has (.sub Δ Γ) σ), (.has (.sub ((T.alongPath A x σ).rootDomain Δ (subTy A σ) (subTm x σ))
        (T.total (path A x))) (comp (T.alongPathMap A x σ)
          ((T.alongPath A x σ).map Δ (root (subTy A σ) (subTm x σ))))), (.has (.sub ((T.alongPath A x σ).rootDomain Δ (subTy A σ) (subTm x σ))
        (T.total (path A x))) (comp (T.map Γ (root A x)) (branchMap A x (T.code (path A x)) σ)))]) (.eq (.sub ((T.alongPath A x σ).rootDomain Δ (subTy A σ) (subTm x σ))
        (T.total (path A x))) (comp (T.alongPathMap A x σ)
          ((T.alongPath A x σ).map Δ (root (subTy A σ) (subTm x σ))))
        (comp (T.map Γ (root A x)) (branchMap A x (T.code (path A x)) σ)))
  | j : Rule Ξ ([(.has (.tm Γ A) x), (.tail (path A x) T), (.has (.ty (T.total (path A x))) D), (.has (.tm ((T.reindex Γ (root A x)).total Γ)
        (subTy D (T.map Γ (root A x)))) d)]) (.has (.tm (T.total (path A x)) D) (j A x (T.code (path A x)) D d))
  | jBeta : Rule Ξ ([(.has (.tm Γ A) x), (.tail (path A x) T), (.has (.ty (T.total (path A x))) D), (.has (.tm ((T.reindex Γ (root A x)).total Γ)
        (subTy D (T.map Γ (root A x)))) d), (.has (.tm ((T.reindex Γ (root A x)).total Γ)
        (subTy D (T.map Γ (root A x))))
        (subTm (j A x (T.code (path A x)) D d) (T.map Γ (root A x))))]) (.eq (.tm ((T.reindex Γ (root A x)).total Γ)
        (subTy D (T.map Γ (root A x))))
        (subTm (j A x (T.code (path A x)) D d) (T.map Γ (root A x))) d)
  | jSub : Rule Ξ ([(.has (.tm Γ A) x), (.tail (path A x) T), (.has (.ty (T.total (path A x))) D), (.has (.tm (T.rootDomain Γ A x) (subTy D (T.map Γ (root A x)))) d), (.has (.sub Δ Γ) σ), (.has (.tm ((T.alongPath A x σ).total (path (subTy A σ) (subTm x σ)))
        (subTy D (T.alongPathMap A x σ)))
        (subTm (j A x (T.code (path A x)) D d) (T.alongPathMap A x σ))), (.has (.tm ((T.alongPath A x σ).total (path (subTy A σ) (subTm x σ)))
        (subTy D (T.alongPathMap A x σ)))
        (j (subTy A σ) (subTm x σ) ((T.alongPath A x σ).code (path (subTy A σ) (subTm x σ)))
          (subTy D (T.alongPathMap A x σ)) (subTm d (branchMap A x (T.code (path A x)) σ))))]) (.eq (.tm ((T.alongPath A x σ).total (path (subTy A σ) (subTm x σ)))
        (subTy D (T.alongPathMap A x σ)))
        (subTm (j A x (T.code (path A x)) D d) (T.alongPathMap A x σ))
        (j (subTy A σ) (subTm x σ) ((T.alongPath A x σ).code (path (subTy A σ) (subTm x σ)))
          (subTy D (T.alongPathMap A x σ)) (subTm d (branchMap A x (T.code (path A x)) σ))))
  | convert : Rule Ξ ([(.has (.tm Γ A) t), (.eq (.ty Γ) A B)]) (.has (.tm Γ B) t)
  | contextConvertType : Rule Ξ ([(.has (.ty Γ) A), (.eq .ctx Γ Δ)]) (.has (.ty Δ) A)
  | contextConvertTerm : Rule Ξ ([(.has (.tm Γ A) t), (.eq .ctx Γ Δ)]) (.has (.tm Δ A) t)
  | contextConvertSub : Rule Ξ ([(.has (.sub Δ Γ) σ), (.eq .ctx Δ Δ'), (.eq .ctx Γ Γ')]) (.has (.sub Δ' Γ') σ)
  | pathDef : Rule Ξ ([(.has (.tm Γ A) x)]) (.eq .ctx (path A x) (extend (extend Γ A) (pathFamily Γ A x)))
  | rootDef : Rule Ξ ([(.has (.tm Γ A) x), (.has (.sub Γ (path A x))
        (pair (pathFamily Γ A x) (sectionSub Γ A x) (reflexivity A x)))]) (.eq (.sub Γ (path A x)) (root A x)
        (pair (pathFamily Γ A x) (sectionSub Γ A x) (reflexivity A x)))
  | pairEta : Rule Ξ ([(.has (.ty Γ) A), (.has (.sub Δ (extend Γ A)) σ), (.has (.sub Δ (extend Γ A))
        (pair A (comp (weaken Γ A) σ) (subTm (generic Γ A) σ)))]) (.eq (.sub Δ (extend Γ A))
        (pair A (comp (weaken Γ A) σ) (subTm (generic Γ A) σ)) σ)
  | familyEqDecl : Declaration.familyEq Γ A B ∈ Ξ → Rule Ξ ([(.has (.ty Γ) A), (.has (.ty Γ) B)]) (.eq (.ty Γ) A B)
  | termEqDecl : Declaration.termEq Γ A s t ∈ Ξ → Rule Ξ ([(.has (.tm Γ A) s), (.has (.tm Γ A) t)]) (.eq (.tm Γ A) s t)
  | pairComp : Rule Ξ ([(.has (.ty Γ) A), (.has (.sub Δ Γ) σ), (.has (.tm Δ (subTy A σ)) t), (.has (.sub Θ Δ) τ)]) (.eq (.sub Θ (extend Γ A)) (comp (pair A σ t) τ)
        (pair A (comp σ τ) (subTm t τ)))
  | subTyId : Rule Ξ ([(.has (.ty Γ) A)]) (.eq (.ty Γ) (subTy A (identitySub Γ)) A)
  | subTyComp : Rule Ξ ([(.has (.ty Γ) A), (.has (.sub Δ Γ) σ), (.has (.sub Θ Δ) τ)]) (.eq (.ty Θ) (subTy (subTy A σ) τ) (subTy A (comp σ τ)))
  | subTmId : Rule Ξ ([(.has (.tm Γ A) t)]) (.eq (.tm Γ A) (subTm t (identitySub Γ)) t)
  | subTmComp : Rule Ξ ([(.has (.tm Γ A) t), (.has (.sub Δ Γ) σ), (.has (.sub Θ Δ) τ)]) (.eq (.tm Θ (subTy A (comp σ τ)))
        (subTm (subTm t σ) τ) (subTm t (comp σ τ)))
  | subIdLeft : Rule Ξ ([(.has (.sub Δ Γ) σ)]) (.eq (.sub Δ Γ) (comp (identitySub Γ) σ) σ)
  | subIdRight : Rule Ξ ([(.has (.sub Δ Γ) σ)]) (.eq (.sub Δ Γ) (comp σ (identitySub Δ)) σ)
  | subAssoc : Rule Ξ ([(.has (.sub Δ Γ) σ), (.has (.sub Θ Δ) τ), (.has (.sub Λ Θ) υ)]) (.eq (.sub Λ Γ) (comp (comp σ τ) υ) (comp σ (comp τ υ)))
  | weakenPair : Rule Ξ ([(.has (.ty Γ) A), (.has (.sub Δ Γ) σ), (.has (.tm Δ (subTy A σ)) t)]) (.eq (.sub Δ Γ) (comp (weaken Γ A) (pair A σ t)) σ)
  | genericPair : Rule Ξ ([(.has (.ty Γ) A), (.has (.sub Δ Γ) σ), (.has (.tm Δ (subTy A σ)) t), (.has (.tm Δ (subTy A σ)) (subTm (generic Γ A) (pair A σ t)))]) (.eq (.tm Δ (subTy A σ)) (subTm (generic Γ A) (pair A σ t)) t)
  | identitySubLaw : Rule Ξ ([(.has (.tm Γ A) x), (.has (.tm Γ A) y), (.has (.sub Δ Γ) σ)]) (.eq (.ty Δ) (subTy (identity A x y) σ)
        (identity (subTy A σ) (subTm x σ) (subTm y σ)))
  | reflexivitySubLaw : Rule Ξ ([(.has (.tm Γ A) x), (.has (.sub Δ Γ) σ)]) (.eq (.tm Δ (identity (subTy A σ) (subTm x σ) (subTm x σ)))
        (subTm (reflexivity A x) σ) (reflexivity (subTy A σ) (subTm x σ)))
  | eqRefl : Rule Ξ ([(.has b t)]) (.eq b t t)
  | eqSymm : Rule Ξ ([(.eq b s t)]) (.eq b t s)
  | eqTrans : Rule Ξ ([(.eq b r s), (.eq b s t)]) (.eq b r t)
  | congruence (op : signature.Operation) (bs : Fin (signature.arity op) → Boundary V)
      {args args' : Fin (signature.arity op) → Expression V} : Rule Ξ ([(.has b (.app op args)), (.has b (.app op args'))] ++ List.ofFn (fun i => (.eq (bs i) (args i) (args' i)))) (.eq b (.app op args) (.app op args'))

abbrev rules (Ξ : List (Declaration V)) : DependentTheoryMaps.Rules (Claim V) where
  Label := Σ ps : List (Claim V), Σ c : Claim V, Rule Ξ ps c
  count := fun r => r.1.length
  premise := fun r i => r.1.get i
  conclusion := fun r => r.2.1

noncomputable def applyRule {Ξ : List (Declaration V)} {ps c}
    (r : Rule Ξ ps c) (ds : ∀ i : Fin ps.length, Derives Ξ (ps.get i)) : Derives Ξ c := by
  cases r with
  | empty => exact .empty
  | extend => exact .extend (ds 0)
  | familyDecl g0 => exact .familyDecl g0 (ds 0)
  | termDecl g0 => exact .termDecl g0 (ds 0)
  | typeContext => exact .typeContext (ds 0)
  | termFamily => exact .termFamily (ds 0)
  | subTy => exact .subTy (ds 0) (ds 1)
  | subTm => exact .subTm (ds 0) (ds 1)
  | identitySub => exact .identitySub (ds 0)
  | comp => exact .comp (ds 0) (ds 1)
  | weaken => exact .weaken (ds 0)
  | generic => exact .generic (ds 0)
  | pair => exact .pair (ds 0) (ds 1) (ds 2)
  | identity => exact .identity (ds 0) (ds 1)
  | reflexivity => exact .reflexivity (ds 0)
  | path => exact .path (ds 0)
  | root => exact .root (ds 0)
  | pathSub => exact .pathSub (ds 0) (ds 1)
  | nil => exact .nil (ds 0)
  | cons => exact .cons (ds 0) (ds 1)
  | tailCode => exact .tailCode (ds 0)
  | contextConvertTel => exact .contextConvertTel (ds 0) (ds 1)
  | tailTotal => exact .tailTotal (ds 0)
  | branchMap => exact .branchMap (ds 0) (ds 1) (ds 2) (ds 3) (ds 4)
  | branchSquare => exact .branchSquare (ds 0) (ds 1) (ds 2) (ds 3) (ds 4)
  | j => exact .j (ds 0) (ds 1) (ds 2) (ds 3)
  | jBeta => exact .jBeta (ds 0) (ds 1) (ds 2) (ds 3) (ds 4)
  | jSub => exact .jSub (ds 0) (ds 1) (ds 2) (ds 3) (ds 4) (ds 5) (ds 6)
  | convert => exact .convert (ds 0) (ds 1)
  | contextConvertType => exact .contextConvertType (ds 0) (ds 1)
  | contextConvertTerm => exact .contextConvertTerm (ds 0) (ds 1)
  | contextConvertSub => exact .contextConvertSub (ds 0) (ds 1) (ds 2)
  | pathDef => exact .pathDef (ds 0)
  | rootDef => exact .rootDef (ds 0) (ds 1)
  | pairEta => exact .pairEta (ds 0) (ds 1) (ds 2)
  | familyEqDecl g0 => exact .familyEqDecl g0 (ds 0) (ds 1)
  | termEqDecl g0 => exact .termEqDecl g0 (ds 0) (ds 1)
  | pairComp => exact .pairComp (ds 0) (ds 1) (ds 2) (ds 3)
  | subTyId => exact .subTyId (ds 0)
  | subTyComp => exact .subTyComp (ds 0) (ds 1) (ds 2)
  | subTmId => exact .subTmId (ds 0)
  | subTmComp => exact .subTmComp (ds 0) (ds 1) (ds 2)
  | subIdLeft => exact .subIdLeft (ds 0)
  | subIdRight => exact .subIdRight (ds 0)
  | subAssoc => exact .subAssoc (ds 0) (ds 1) (ds 2)
  | weakenPair => exact .weakenPair (ds 0) (ds 1) (ds 2)
  | genericPair => exact .genericPair (ds 0) (ds 1) (ds 2) (ds 3)
  | identitySubLaw => exact .identitySubLaw (ds 0) (ds 1) (ds 2)
  | reflexivitySubLaw => exact .reflexivitySubLaw (ds 0) (ds 1)
  | eqRefl => exact .eqRefl (ds 0)
  | eqSymm => exact .eqSymm (ds 0)
  | eqTrans => exact .eqTrans (ds 0) (ds 1)
  | congruence op bs =>
    apply Derives.congruence op bs (ds ⟨0, by simp⟩) (ds ⟨1, by simp⟩)
    intro i
    simpa using ds ⟨i.val + 2, by simp⟩


/-- Instantiate one primitive rule; every premise keeps its typed boundary. -/
def Rule.instantiate {Ξ : List (Declaration V)} {ps c}
    (r : Rule Ξ ps c) (θ : V → Expression W) :
    Rule (Ξ.map (Declaration.instantiate θ)) (ps.map (Claim.instantiate θ)) (c.instantiate θ) := by
  cases r with
  | @empty =>
    simpa [Claim.instantiate, Boundary.instantiate, Tail.instantiate, List.map_ofFn, Function.comp_def, Tail.alongPath, Tail.alongPathMap,
      Tail.rootDomain, ← Tail.instantiate_total, ← Tail.instantiate_code] using
      (Rule.empty (Ξ := Ξ.map (Declaration.instantiate θ)))
  | @extend Γ A =>
    simpa [Claim.instantiate, Boundary.instantiate, Tail.instantiate, List.map_ofFn, Function.comp_def, Tail.alongPath, Tail.alongPathMap,
      Tail.rootDomain, ← Tail.instantiate_total, ← Tail.instantiate_code] using
      (Rule.extend (Ξ := Ξ.map (Declaration.instantiate θ)) (Γ := Γ.subst θ) (A := A.subst θ))
  | @familyDecl Γ A g0 =>
    simpa [Claim.instantiate, Boundary.instantiate, Tail.instantiate, List.map_ofFn, Function.comp_def, Tail.alongPath, Tail.alongPathMap,
      Tail.rootDomain, ← Tail.instantiate_total, ← Tail.instantiate_code] using
      (Rule.familyDecl (Ξ := Ξ.map (Declaration.instantiate θ)) (Γ := Γ.subst θ) (A := A.subst θ) (List.mem_map.mpr ⟨_, g0, rfl⟩))
  | @termDecl Γ A t g0 =>
    simpa [Claim.instantiate, Boundary.instantiate, Tail.instantiate, List.map_ofFn, Function.comp_def, Tail.alongPath, Tail.alongPathMap,
      Tail.rootDomain, ← Tail.instantiate_total, ← Tail.instantiate_code] using
      (Rule.termDecl (Ξ := Ξ.map (Declaration.instantiate θ)) (Γ := Γ.subst θ) (A := A.subst θ) (t := t.subst θ) (List.mem_map.mpr ⟨_, g0, rfl⟩))
  | @typeContext Γ A =>
    simpa [Claim.instantiate, Boundary.instantiate, Tail.instantiate, List.map_ofFn, Function.comp_def, Tail.alongPath, Tail.alongPathMap,
      Tail.rootDomain, ← Tail.instantiate_total, ← Tail.instantiate_code] using
      (Rule.typeContext (Ξ := Ξ.map (Declaration.instantiate θ)) (Γ := Γ.subst θ) (A := A.subst θ))
  | @termFamily Γ A t =>
    simpa [Claim.instantiate, Boundary.instantiate, Tail.instantiate, List.map_ofFn, Function.comp_def, Tail.alongPath, Tail.alongPathMap,
      Tail.rootDomain, ← Tail.instantiate_total, ← Tail.instantiate_code] using
      (Rule.termFamily (Ξ := Ξ.map (Declaration.instantiate θ)) (Γ := Γ.subst θ) (A := A.subst θ) (t := t.subst θ))
  | @subTy Γ A Δ σ =>
    simpa [Claim.instantiate, Boundary.instantiate, Tail.instantiate, List.map_ofFn, Function.comp_def, Tail.alongPath, Tail.alongPathMap,
      Tail.rootDomain, ← Tail.instantiate_total, ← Tail.instantiate_code] using
      (Rule.subTy (Ξ := Ξ.map (Declaration.instantiate θ)) (Γ := Γ.subst θ) (A := A.subst θ) (Δ := Δ.subst θ) (σ := σ.subst θ))
  | @subTm Γ A t Δ σ =>
    simpa [Claim.instantiate, Boundary.instantiate, Tail.instantiate, List.map_ofFn, Function.comp_def, Tail.alongPath, Tail.alongPathMap,
      Tail.rootDomain, ← Tail.instantiate_total, ← Tail.instantiate_code] using
      (Rule.subTm (Ξ := Ξ.map (Declaration.instantiate θ)) (Γ := Γ.subst θ) (A := A.subst θ) (t := t.subst θ) (Δ := Δ.subst θ) (σ := σ.subst θ))
  | @identitySub Γ =>
    simpa [Claim.instantiate, Boundary.instantiate, Tail.instantiate, List.map_ofFn, Function.comp_def, Tail.alongPath, Tail.alongPathMap,
      Tail.rootDomain, ← Tail.instantiate_total, ← Tail.instantiate_code] using
      (Rule.identitySub (Ξ := Ξ.map (Declaration.instantiate θ)) (Γ := Γ.subst θ))
  | @comp Δ Γ σ Θ τ =>
    simpa [Claim.instantiate, Boundary.instantiate, Tail.instantiate, List.map_ofFn, Function.comp_def, Tail.alongPath, Tail.alongPathMap,
      Tail.rootDomain, ← Tail.instantiate_total, ← Tail.instantiate_code] using
      (Rule.comp (Ξ := Ξ.map (Declaration.instantiate θ)) (Δ := Δ.subst θ) (Γ := Γ.subst θ) (σ := σ.subst θ) (Θ := Θ.subst θ) (τ := τ.subst θ))
  | @weaken Γ A =>
    simpa [Claim.instantiate, Boundary.instantiate, Tail.instantiate, List.map_ofFn, Function.comp_def, Tail.alongPath, Tail.alongPathMap,
      Tail.rootDomain, ← Tail.instantiate_total, ← Tail.instantiate_code] using
      (Rule.weaken (Ξ := Ξ.map (Declaration.instantiate θ)) (Γ := Γ.subst θ) (A := A.subst θ))
  | @generic Γ A =>
    simpa [Claim.instantiate, Boundary.instantiate, Tail.instantiate, List.map_ofFn, Function.comp_def, Tail.alongPath, Tail.alongPathMap,
      Tail.rootDomain, ← Tail.instantiate_total, ← Tail.instantiate_code] using
      (Rule.generic (Ξ := Ξ.map (Declaration.instantiate θ)) (Γ := Γ.subst θ) (A := A.subst θ))
  | @pair Γ A Δ σ t =>
    simpa [Claim.instantiate, Boundary.instantiate, Tail.instantiate, List.map_ofFn, Function.comp_def, Tail.alongPath, Tail.alongPathMap,
      Tail.rootDomain, ← Tail.instantiate_total, ← Tail.instantiate_code] using
      (Rule.pair (Ξ := Ξ.map (Declaration.instantiate θ)) (Γ := Γ.subst θ) (A := A.subst θ) (Δ := Δ.subst θ) (σ := σ.subst θ) (t := t.subst θ))
  | @identity Γ A x y =>
    simpa [Claim.instantiate, Boundary.instantiate, Tail.instantiate, List.map_ofFn, Function.comp_def, Tail.alongPath, Tail.alongPathMap,
      Tail.rootDomain, ← Tail.instantiate_total, ← Tail.instantiate_code] using
      (Rule.identity (Ξ := Ξ.map (Declaration.instantiate θ)) (Γ := Γ.subst θ) (A := A.subst θ) (x := x.subst θ) (y := y.subst θ))
  | @reflexivity Γ A x =>
    simpa [Claim.instantiate, Boundary.instantiate, Tail.instantiate, List.map_ofFn, Function.comp_def, Tail.alongPath, Tail.alongPathMap,
      Tail.rootDomain, ← Tail.instantiate_total, ← Tail.instantiate_code] using
      (Rule.reflexivity (Ξ := Ξ.map (Declaration.instantiate θ)) (Γ := Γ.subst θ) (A := A.subst θ) (x := x.subst θ))
  | @path Γ A x =>
    simpa [Claim.instantiate, Boundary.instantiate, Tail.instantiate, List.map_ofFn, Function.comp_def, Tail.alongPath, Tail.alongPathMap,
      Tail.rootDomain, ← Tail.instantiate_total, ← Tail.instantiate_code] using
      (Rule.path (Ξ := Ξ.map (Declaration.instantiate θ)) (Γ := Γ.subst θ) (A := A.subst θ) (x := x.subst θ))
  | @root Γ A x =>
    simpa [Claim.instantiate, Boundary.instantiate, Tail.instantiate, List.map_ofFn, Function.comp_def, Tail.alongPath, Tail.alongPathMap,
      Tail.rootDomain, ← Tail.instantiate_total, ← Tail.instantiate_code] using
      (Rule.root (Ξ := Ξ.map (Declaration.instantiate θ)) (Γ := Γ.subst θ) (A := A.subst θ) (x := x.subst θ))
  | @pathSub Γ A x Δ σ =>
    simpa [Claim.instantiate, Boundary.instantiate, Tail.instantiate, List.map_ofFn, Function.comp_def, Tail.alongPath, Tail.alongPathMap,
      Tail.rootDomain, ← Tail.instantiate_total, ← Tail.instantiate_code] using
      (Rule.pathSub (Ξ := Ξ.map (Declaration.instantiate θ)) (Γ := Γ.subst θ) (A := A.subst θ) (x := x.subst θ) (Δ := Δ.subst θ) (σ := σ.subst θ))
  | @nil Γ =>
    simpa [Claim.instantiate, Boundary.instantiate, Tail.instantiate, List.map_ofFn, Function.comp_def, Tail.alongPath, Tail.alongPathMap,
      Tail.rootDomain, ← Tail.instantiate_total, ← Tail.instantiate_code] using
      (Rule.nil (Ξ := Ξ.map (Declaration.instantiate θ)) (Γ := Γ.subst θ))
  | @cons Γ A T =>
    simpa [Claim.instantiate, Boundary.instantiate, Tail.instantiate, List.map_ofFn, Function.comp_def, Tail.alongPath, Tail.alongPathMap,
      Tail.rootDomain, ← Tail.instantiate_total, ← Tail.instantiate_code] using
      (Rule.cons (Ξ := Ξ.map (Declaration.instantiate θ)) (Γ := Γ.subst θ) (A := A.subst θ) (T := T.instantiate θ))
  | @tailCode Γ T =>
    simpa [Claim.instantiate, Boundary.instantiate, Tail.instantiate, List.map_ofFn, Function.comp_def, Tail.alongPath, Tail.alongPathMap,
      Tail.rootDomain, ← Tail.instantiate_total, ← Tail.instantiate_code] using
      (Rule.tailCode (Ξ := Ξ.map (Declaration.instantiate θ)) (Γ := Γ.subst θ) (T := T.instantiate θ))
  | @contextConvertTel n Γ t Δ =>
    simpa [Claim.instantiate, Boundary.instantiate, Tail.instantiate, List.map_ofFn, Function.comp_def, Tail.alongPath, Tail.alongPathMap,
      Tail.rootDomain, ← Tail.instantiate_total, ← Tail.instantiate_code] using
      (Rule.contextConvertTel (Ξ := Ξ.map (Declaration.instantiate θ)) (n := n) (Γ := Γ.subst θ) (t := t.subst θ) (Δ := Δ.subst θ))
  | @tailTotal Γ T =>
    simpa [Claim.instantiate, Boundary.instantiate, Tail.instantiate, List.map_ofFn, Function.comp_def, Tail.alongPath, Tail.alongPathMap,
      Tail.rootDomain, ← Tail.instantiate_total, ← Tail.instantiate_code] using
      (Rule.tailTotal (Ξ := Ξ.map (Declaration.instantiate θ)) (Γ := Γ.subst θ) (T := T.instantiate θ))
  | @branchMap Γ A x T Δ σ =>
    simpa [Claim.instantiate, Boundary.instantiate, Tail.instantiate, List.map_ofFn, Function.comp_def, Tail.alongPath, Tail.alongPathMap,
      Tail.rootDomain, ← Tail.instantiate_total, ← Tail.instantiate_code] using
      (Rule.branchMap (Ξ := Ξ.map (Declaration.instantiate θ)) (Γ := Γ.subst θ) (A := A.subst θ) (x := x.subst θ) (T := T.instantiate θ) (Δ := Δ.subst θ) (σ := σ.subst θ))
  | @branchSquare Γ A x T Δ σ =>
    simpa [Claim.instantiate, Boundary.instantiate, Tail.instantiate, List.map_ofFn, Function.comp_def, Tail.alongPath, Tail.alongPathMap,
      Tail.rootDomain, ← Tail.instantiate_total, ← Tail.instantiate_code] using
      (Rule.branchSquare (Ξ := Ξ.map (Declaration.instantiate θ)) (Γ := Γ.subst θ) (A := A.subst θ) (x := x.subst θ) (T := T.instantiate θ) (Δ := Δ.subst θ) (σ := σ.subst θ))
  | @j Γ A x T D d =>
    simpa [Claim.instantiate, Boundary.instantiate, Tail.instantiate, List.map_ofFn, Function.comp_def, Tail.alongPath, Tail.alongPathMap,
      Tail.rootDomain, ← Tail.instantiate_total, ← Tail.instantiate_code] using
      (Rule.j (Ξ := Ξ.map (Declaration.instantiate θ)) (Γ := Γ.subst θ) (A := A.subst θ) (x := x.subst θ) (T := T.instantiate θ) (D := D.subst θ) (d := d.subst θ))
  | @jBeta Γ A x T D d =>
    simpa [Claim.instantiate, Boundary.instantiate, Tail.instantiate, List.map_ofFn, Function.comp_def, Tail.alongPath, Tail.alongPathMap,
      Tail.rootDomain, ← Tail.instantiate_total, ← Tail.instantiate_code] using
      (Rule.jBeta (Ξ := Ξ.map (Declaration.instantiate θ)) (Γ := Γ.subst θ) (A := A.subst θ) (x := x.subst θ) (T := T.instantiate θ) (D := D.subst θ) (d := d.subst θ))
  | @jSub Γ A x T D d Δ σ =>
    simpa [Claim.instantiate, Boundary.instantiate, Tail.instantiate, List.map_ofFn, Function.comp_def, Tail.alongPath, Tail.alongPathMap,
      Tail.rootDomain, ← Tail.instantiate_total, ← Tail.instantiate_code] using
      (Rule.jSub (Ξ := Ξ.map (Declaration.instantiate θ)) (Γ := Γ.subst θ) (A := A.subst θ) (x := x.subst θ) (T := T.instantiate θ) (D := D.subst θ) (d := d.subst θ) (Δ := Δ.subst θ) (σ := σ.subst θ))
  | @convert Γ A t B =>
    simpa [Claim.instantiate, Boundary.instantiate, Tail.instantiate, List.map_ofFn, Function.comp_def, Tail.alongPath, Tail.alongPathMap,
      Tail.rootDomain, ← Tail.instantiate_total, ← Tail.instantiate_code] using
      (Rule.convert (Ξ := Ξ.map (Declaration.instantiate θ)) (Γ := Γ.subst θ) (A := A.subst θ) (t := t.subst θ) (B := B.subst θ))
  | @contextConvertType Γ A Δ =>
    simpa [Claim.instantiate, Boundary.instantiate, Tail.instantiate, List.map_ofFn, Function.comp_def, Tail.alongPath, Tail.alongPathMap,
      Tail.rootDomain, ← Tail.instantiate_total, ← Tail.instantiate_code] using
      (Rule.contextConvertType (Ξ := Ξ.map (Declaration.instantiate θ)) (Γ := Γ.subst θ) (A := A.subst θ) (Δ := Δ.subst θ))
  | @contextConvertTerm Γ A t Δ =>
    simpa [Claim.instantiate, Boundary.instantiate, Tail.instantiate, List.map_ofFn, Function.comp_def, Tail.alongPath, Tail.alongPathMap,
      Tail.rootDomain, ← Tail.instantiate_total, ← Tail.instantiate_code] using
      (Rule.contextConvertTerm (Ξ := Ξ.map (Declaration.instantiate θ)) (Γ := Γ.subst θ) (A := A.subst θ) (t := t.subst θ) (Δ := Δ.subst θ))
  | @contextConvertSub Δ Γ σ Δ' Γ' =>
    simpa [Claim.instantiate, Boundary.instantiate, Tail.instantiate, List.map_ofFn, Function.comp_def, Tail.alongPath, Tail.alongPathMap,
      Tail.rootDomain, ← Tail.instantiate_total, ← Tail.instantiate_code] using
      (Rule.contextConvertSub (Ξ := Ξ.map (Declaration.instantiate θ)) (Δ := Δ.subst θ) (Γ := Γ.subst θ) (σ := σ.subst θ) (Δ' := Δ'.subst θ) (Γ' := Γ'.subst θ))
  | @pathDef Γ A x =>
    simpa [Claim.instantiate, Boundary.instantiate, Tail.instantiate, List.map_ofFn, Function.comp_def, Tail.alongPath, Tail.alongPathMap,
      Tail.rootDomain, ← Tail.instantiate_total, ← Tail.instantiate_code] using
      (Rule.pathDef (Ξ := Ξ.map (Declaration.instantiate θ)) (Γ := Γ.subst θ) (A := A.subst θ) (x := x.subst θ))
  | @rootDef Γ A x =>
    simpa [Claim.instantiate, Boundary.instantiate, Tail.instantiate, List.map_ofFn, Function.comp_def, Tail.alongPath, Tail.alongPathMap,
      Tail.rootDomain, ← Tail.instantiate_total, ← Tail.instantiate_code] using
      (Rule.rootDef (Ξ := Ξ.map (Declaration.instantiate θ)) (Γ := Γ.subst θ) (A := A.subst θ) (x := x.subst θ))
  | @pairEta Γ A Δ σ =>
    simpa [Claim.instantiate, Boundary.instantiate, Tail.instantiate, List.map_ofFn, Function.comp_def, Tail.alongPath, Tail.alongPathMap,
      Tail.rootDomain, ← Tail.instantiate_total, ← Tail.instantiate_code] using
      (Rule.pairEta (Ξ := Ξ.map (Declaration.instantiate θ)) (Γ := Γ.subst θ) (A := A.subst θ) (Δ := Δ.subst θ) (σ := σ.subst θ))
  | @familyEqDecl Γ A B g0 =>
    simpa [Claim.instantiate, Boundary.instantiate, Tail.instantiate, List.map_ofFn, Function.comp_def, Tail.alongPath, Tail.alongPathMap,
      Tail.rootDomain, ← Tail.instantiate_total, ← Tail.instantiate_code] using
      (Rule.familyEqDecl (Ξ := Ξ.map (Declaration.instantiate θ)) (Γ := Γ.subst θ) (A := A.subst θ) (B := B.subst θ) (List.mem_map.mpr ⟨_, g0, rfl⟩))
  | @termEqDecl Γ A s t g0 =>
    simpa [Claim.instantiate, Boundary.instantiate, Tail.instantiate, List.map_ofFn, Function.comp_def, Tail.alongPath, Tail.alongPathMap,
      Tail.rootDomain, ← Tail.instantiate_total, ← Tail.instantiate_code] using
      (Rule.termEqDecl (Ξ := Ξ.map (Declaration.instantiate θ)) (Γ := Γ.subst θ) (A := A.subst θ) (s := s.subst θ) (t := t.subst θ) (List.mem_map.mpr ⟨_, g0, rfl⟩))
  | @pairComp Γ A Δ σ t Θ τ =>
    simpa [Claim.instantiate, Boundary.instantiate, Tail.instantiate, List.map_ofFn, Function.comp_def, Tail.alongPath, Tail.alongPathMap,
      Tail.rootDomain, ← Tail.instantiate_total, ← Tail.instantiate_code] using
      (Rule.pairComp (Ξ := Ξ.map (Declaration.instantiate θ)) (Γ := Γ.subst θ) (A := A.subst θ) (Δ := Δ.subst θ) (σ := σ.subst θ) (t := t.subst θ) (Θ := Θ.subst θ) (τ := τ.subst θ))
  | @subTyId Γ A =>
    simpa [Claim.instantiate, Boundary.instantiate, Tail.instantiate, List.map_ofFn, Function.comp_def, Tail.alongPath, Tail.alongPathMap,
      Tail.rootDomain, ← Tail.instantiate_total, ← Tail.instantiate_code] using
      (Rule.subTyId (Ξ := Ξ.map (Declaration.instantiate θ)) (Γ := Γ.subst θ) (A := A.subst θ))
  | @subTyComp Γ A Δ σ Θ τ =>
    simpa [Claim.instantiate, Boundary.instantiate, Tail.instantiate, List.map_ofFn, Function.comp_def, Tail.alongPath, Tail.alongPathMap,
      Tail.rootDomain, ← Tail.instantiate_total, ← Tail.instantiate_code] using
      (Rule.subTyComp (Ξ := Ξ.map (Declaration.instantiate θ)) (Γ := Γ.subst θ) (A := A.subst θ) (Δ := Δ.subst θ) (σ := σ.subst θ) (Θ := Θ.subst θ) (τ := τ.subst θ))
  | @subTmId Γ A t =>
    simpa [Claim.instantiate, Boundary.instantiate, Tail.instantiate, List.map_ofFn, Function.comp_def, Tail.alongPath, Tail.alongPathMap,
      Tail.rootDomain, ← Tail.instantiate_total, ← Tail.instantiate_code] using
      (Rule.subTmId (Ξ := Ξ.map (Declaration.instantiate θ)) (Γ := Γ.subst θ) (A := A.subst θ) (t := t.subst θ))
  | @subTmComp Γ A t Δ σ Θ τ =>
    simpa [Claim.instantiate, Boundary.instantiate, Tail.instantiate, List.map_ofFn, Function.comp_def, Tail.alongPath, Tail.alongPathMap,
      Tail.rootDomain, ← Tail.instantiate_total, ← Tail.instantiate_code] using
      (Rule.subTmComp (Ξ := Ξ.map (Declaration.instantiate θ)) (Γ := Γ.subst θ) (A := A.subst θ) (t := t.subst θ) (Δ := Δ.subst θ) (σ := σ.subst θ) (Θ := Θ.subst θ) (τ := τ.subst θ))
  | @subIdLeft Δ Γ σ =>
    simpa [Claim.instantiate, Boundary.instantiate, Tail.instantiate, List.map_ofFn, Function.comp_def, Tail.alongPath, Tail.alongPathMap,
      Tail.rootDomain, ← Tail.instantiate_total, ← Tail.instantiate_code] using
      (Rule.subIdLeft (Ξ := Ξ.map (Declaration.instantiate θ)) (Δ := Δ.subst θ) (Γ := Γ.subst θ) (σ := σ.subst θ))
  | @subIdRight Δ Γ σ =>
    simpa [Claim.instantiate, Boundary.instantiate, Tail.instantiate, List.map_ofFn, Function.comp_def, Tail.alongPath, Tail.alongPathMap,
      Tail.rootDomain, ← Tail.instantiate_total, ← Tail.instantiate_code] using
      (Rule.subIdRight (Ξ := Ξ.map (Declaration.instantiate θ)) (Δ := Δ.subst θ) (Γ := Γ.subst θ) (σ := σ.subst θ))
  | @subAssoc Δ Γ σ Θ τ Λ υ =>
    simpa [Claim.instantiate, Boundary.instantiate, Tail.instantiate, List.map_ofFn, Function.comp_def, Tail.alongPath, Tail.alongPathMap,
      Tail.rootDomain, ← Tail.instantiate_total, ← Tail.instantiate_code] using
      (Rule.subAssoc (Ξ := Ξ.map (Declaration.instantiate θ)) (Δ := Δ.subst θ) (Γ := Γ.subst θ) (σ := σ.subst θ) (Θ := Θ.subst θ) (τ := τ.subst θ) (Λ := Λ.subst θ) (υ := υ.subst θ))
  | @weakenPair Γ A Δ σ t =>
    simpa [Claim.instantiate, Boundary.instantiate, Tail.instantiate, List.map_ofFn, Function.comp_def, Tail.alongPath, Tail.alongPathMap,
      Tail.rootDomain, ← Tail.instantiate_total, ← Tail.instantiate_code] using
      (Rule.weakenPair (Ξ := Ξ.map (Declaration.instantiate θ)) (Γ := Γ.subst θ) (A := A.subst θ) (Δ := Δ.subst θ) (σ := σ.subst θ) (t := t.subst θ))
  | @genericPair Γ A Δ σ t =>
    simpa [Claim.instantiate, Boundary.instantiate, Tail.instantiate, List.map_ofFn, Function.comp_def, Tail.alongPath, Tail.alongPathMap,
      Tail.rootDomain, ← Tail.instantiate_total, ← Tail.instantiate_code] using
      (Rule.genericPair (Ξ := Ξ.map (Declaration.instantiate θ)) (Γ := Γ.subst θ) (A := A.subst θ) (Δ := Δ.subst θ) (σ := σ.subst θ) (t := t.subst θ))
  | @identitySubLaw Γ A x y Δ σ =>
    simpa [Claim.instantiate, Boundary.instantiate, Tail.instantiate, List.map_ofFn, Function.comp_def, Tail.alongPath, Tail.alongPathMap,
      Tail.rootDomain, ← Tail.instantiate_total, ← Tail.instantiate_code] using
      (Rule.identitySubLaw (Ξ := Ξ.map (Declaration.instantiate θ)) (Γ := Γ.subst θ) (A := A.subst θ) (x := x.subst θ) (y := y.subst θ) (Δ := Δ.subst θ) (σ := σ.subst θ))
  | @reflexivitySubLaw Γ A x Δ σ =>
    simpa [Claim.instantiate, Boundary.instantiate, Tail.instantiate, List.map_ofFn, Function.comp_def, Tail.alongPath, Tail.alongPathMap,
      Tail.rootDomain, ← Tail.instantiate_total, ← Tail.instantiate_code] using
      (Rule.reflexivitySubLaw (Ξ := Ξ.map (Declaration.instantiate θ)) (Γ := Γ.subst θ) (A := A.subst θ) (x := x.subst θ) (Δ := Δ.subst θ) (σ := σ.subst θ))
  | @eqRefl b t =>
    simpa [Claim.instantiate, Boundary.instantiate, Tail.instantiate, List.map_ofFn, Function.comp_def, Tail.alongPath, Tail.alongPathMap,
      Tail.rootDomain, ← Tail.instantiate_total, ← Tail.instantiate_code] using
      (Rule.eqRefl (Ξ := Ξ.map (Declaration.instantiate θ)) (b := b.instantiate θ) (t := t.subst θ))
  | @eqSymm b s t =>
    simpa [Claim.instantiate, Boundary.instantiate, Tail.instantiate, List.map_ofFn, Function.comp_def, Tail.alongPath, Tail.alongPathMap,
      Tail.rootDomain, ← Tail.instantiate_total, ← Tail.instantiate_code] using
      (Rule.eqSymm (Ξ := Ξ.map (Declaration.instantiate θ)) (b := b.instantiate θ) (s := s.subst θ) (t := t.subst θ))
  | @eqTrans b r s t =>
    simpa [Claim.instantiate, Boundary.instantiate, Tail.instantiate, List.map_ofFn, Function.comp_def, Tail.alongPath, Tail.alongPathMap,
      Tail.rootDomain, ← Tail.instantiate_total, ← Tail.instantiate_code] using
      (Rule.eqTrans (Ξ := Ξ.map (Declaration.instantiate θ)) (b := b.instantiate θ) (r := r.subst θ) (s := s.subst θ) (t := t.subst θ))
  | @congruence b op bs args args' =>
    simpa [Term.subst, Term.app, FinitaryTerm.bind_node_apply, Claim.instantiate, Boundary.instantiate, Tail.instantiate, List.map_ofFn, Function.comp_def, Tail.alongPath, Tail.alongPathMap,
      Tail.rootDomain, ← Tail.instantiate_total, ← Tail.instantiate_code] using
      (Rule.congruence (Ξ := Ξ.map (Declaration.instantiate θ)) (b := b.instantiate θ) op (fun i => (bs i).instantiate θ) (args := fun i => (args i).subst θ) (args' := fun i => (args' i).subst θ))

abbrev Proof (Ξ : List (Declaration V)) (c : Claim V) :=
  DependentTheoryMaps.Derivation (rules Ξ) (fun _ => Empty) c

/-- Recover the independent calculus by primitive inference reconstruction. -/
noncomputable def decode {Ξ : List (Declaration V)} {c : Claim V} : Proof Ξ c → Derives Ξ c
  | .hyp h => h.elim
  | .rule r ds => applyRule r.2.2 (fun i => decode (ds i))

/-- The syntax-directed presentation retains every primitive proof occurrence. -/
noncomputable def encode {Ξ : List (Declaration V)} {c : Claim V} : Derives Ξ c → Proof Ξ c
  | .empty => .rule (R := rules Ξ) ⟨_, _, .empty⟩ (fun i => Fin.elim0 i)
  | .extend h0 => .rule (R := rules Ξ) ⟨_, _, .extend⟩ (Fin.cases (encode h0) (fun i => Fin.elim0 i))
  | .familyDecl g0 h0 => .rule (R := rules Ξ) ⟨_, _, .familyDecl g0⟩ (Fin.cases (encode h0) (fun i => Fin.elim0 i))
  | .termDecl g0 h0 => .rule (R := rules Ξ) ⟨_, _, .termDecl g0⟩ (Fin.cases (encode h0) (fun i => Fin.elim0 i))
  | .typeContext h0 => .rule (R := rules Ξ) ⟨_, _, .typeContext⟩ (Fin.cases (encode h0) (fun i => Fin.elim0 i))
  | .termFamily h0 => .rule (R := rules Ξ) ⟨_, _, .termFamily⟩ (Fin.cases (encode h0) (fun i => Fin.elim0 i))
  | .subTy h0 h1 => .rule (R := rules Ξ) ⟨_, _, .subTy⟩ (Fin.cases (encode h0) (Fin.cases (encode h1) (fun i => Fin.elim0 i)))
  | .subTm h0 h1 => .rule (R := rules Ξ) ⟨_, _, .subTm⟩ (Fin.cases (encode h0) (Fin.cases (encode h1) (fun i => Fin.elim0 i)))
  | .identitySub h0 => .rule (R := rules Ξ) ⟨_, _, .identitySub⟩ (Fin.cases (encode h0) (fun i => Fin.elim0 i))
  | .comp h0 h1 => .rule (R := rules Ξ) ⟨_, _, .comp⟩ (Fin.cases (encode h0) (Fin.cases (encode h1) (fun i => Fin.elim0 i)))
  | .weaken h0 => .rule (R := rules Ξ) ⟨_, _, .weaken⟩ (Fin.cases (encode h0) (fun i => Fin.elim0 i))
  | .generic h0 => .rule (R := rules Ξ) ⟨_, _, .generic⟩ (Fin.cases (encode h0) (fun i => Fin.elim0 i))
  | .pair h0 h1 h2 => .rule (R := rules Ξ) ⟨_, _, .pair⟩ (Fin.cases (encode h0) (Fin.cases (encode h1) (Fin.cases (encode h2) (fun i => Fin.elim0 i))))
  | .identity h0 h1 => .rule (R := rules Ξ) ⟨_, _, .identity⟩ (Fin.cases (encode h0) (Fin.cases (encode h1) (fun i => Fin.elim0 i)))
  | .reflexivity h0 => .rule (R := rules Ξ) ⟨_, _, .reflexivity⟩ (Fin.cases (encode h0) (fun i => Fin.elim0 i))
  | .path h0 => .rule (R := rules Ξ) ⟨_, _, .path⟩ (Fin.cases (encode h0) (fun i => Fin.elim0 i))
  | .root h0 => .rule (R := rules Ξ) ⟨_, _, .root⟩ (Fin.cases (encode h0) (fun i => Fin.elim0 i))
  | .pathSub h0 h1 => .rule (R := rules Ξ) ⟨_, _, .pathSub⟩ (Fin.cases (encode h0) (Fin.cases (encode h1) (fun i => Fin.elim0 i)))
  | .nil h0 => .rule (R := rules Ξ) ⟨_, _, .nil⟩ (Fin.cases (encode h0) (fun i => Fin.elim0 i))
  | .cons h0 h1 => .rule (R := rules Ξ) ⟨_, _, .cons⟩ (Fin.cases (encode h0) (Fin.cases (encode h1) (fun i => Fin.elim0 i)))
  | .tailCode h0 => .rule (R := rules Ξ) ⟨_, _, .tailCode⟩ (Fin.cases (encode h0) (fun i => Fin.elim0 i))
  | .contextConvertTel h0 h1 => .rule (R := rules Ξ) ⟨_, _, .contextConvertTel⟩ (Fin.cases (encode h0) (Fin.cases (encode h1) (fun i => Fin.elim0 i)))
  | .tailTotal h0 => .rule (R := rules Ξ) ⟨_, _, .tailTotal⟩ (Fin.cases (encode h0) (fun i => Fin.elim0 i))
  | .branchMap h0 h1 h2 h3 h4 => .rule (R := rules Ξ) ⟨_, _, .branchMap⟩ (Fin.cases (encode h0) (Fin.cases (encode h1) (Fin.cases (encode h2) (Fin.cases (encode h3) (Fin.cases (encode h4) (fun i => Fin.elim0 i))))))
  | .branchSquare h0 h1 h2 h3 h4 => .rule (R := rules Ξ) ⟨_, _, .branchSquare⟩ (Fin.cases (encode h0) (Fin.cases (encode h1) (Fin.cases (encode h2) (Fin.cases (encode h3) (Fin.cases (encode h4) (fun i => Fin.elim0 i))))))
  | .j h0 h1 h2 h3 => .rule (R := rules Ξ) ⟨_, _, .j⟩ (Fin.cases (encode h0) (Fin.cases (encode h1) (Fin.cases (encode h2) (Fin.cases (encode h3) (fun i => Fin.elim0 i)))))
  | .jBeta h0 h1 h2 h3 h4 => .rule (R := rules Ξ) ⟨_, _, .jBeta⟩ (Fin.cases (encode h0) (Fin.cases (encode h1) (Fin.cases (encode h2) (Fin.cases (encode h3) (Fin.cases (encode h4) (fun i => Fin.elim0 i))))))
  | .jSub h0 h1 h2 h3 h4 h5 h6 => .rule (R := rules Ξ) ⟨_, _, .jSub⟩ (Fin.cases (encode h0) (Fin.cases (encode h1) (Fin.cases (encode h2) (Fin.cases (encode h3) (Fin.cases (encode h4) (Fin.cases (encode h5) (Fin.cases (encode h6) (fun i => Fin.elim0 i))))))))
  | .convert h0 h1 => .rule (R := rules Ξ) ⟨_, _, .convert⟩ (Fin.cases (encode h0) (Fin.cases (encode h1) (fun i => Fin.elim0 i)))
  | .contextConvertType h0 h1 => .rule (R := rules Ξ) ⟨_, _, .contextConvertType⟩ (Fin.cases (encode h0) (Fin.cases (encode h1) (fun i => Fin.elim0 i)))
  | .contextConvertTerm h0 h1 => .rule (R := rules Ξ) ⟨_, _, .contextConvertTerm⟩ (Fin.cases (encode h0) (Fin.cases (encode h1) (fun i => Fin.elim0 i)))
  | .contextConvertSub h0 h1 h2 => .rule (R := rules Ξ) ⟨_, _, .contextConvertSub⟩ (Fin.cases (encode h0) (Fin.cases (encode h1) (Fin.cases (encode h2) (fun i => Fin.elim0 i))))
  | .pathDef h0 => .rule (R := rules Ξ) ⟨_, _, .pathDef⟩ (Fin.cases (encode h0) (fun i => Fin.elim0 i))
  | .rootDef h0 h1 => .rule (R := rules Ξ) ⟨_, _, .rootDef⟩ (Fin.cases (encode h0) (Fin.cases (encode h1) (fun i => Fin.elim0 i)))
  | .pairEta h0 h1 h2 => .rule (R := rules Ξ) ⟨_, _, .pairEta⟩ (Fin.cases (encode h0) (Fin.cases (encode h1) (Fin.cases (encode h2) (fun i => Fin.elim0 i))))
  | .familyEqDecl g0 h0 h1 => .rule (R := rules Ξ) ⟨_, _, .familyEqDecl g0⟩ (Fin.cases (encode h0) (Fin.cases (encode h1) (fun i => Fin.elim0 i)))
  | .termEqDecl g0 h0 h1 => .rule (R := rules Ξ) ⟨_, _, .termEqDecl g0⟩ (Fin.cases (encode h0) (Fin.cases (encode h1) (fun i => Fin.elim0 i)))
  | .pairComp h0 h1 h2 h3 => .rule (R := rules Ξ) ⟨_, _, .pairComp⟩ (Fin.cases (encode h0) (Fin.cases (encode h1) (Fin.cases (encode h2) (Fin.cases (encode h3) (fun i => Fin.elim0 i)))))
  | .subTyId h0 => .rule (R := rules Ξ) ⟨_, _, .subTyId⟩ (Fin.cases (encode h0) (fun i => Fin.elim0 i))
  | .subTyComp h0 h1 h2 => .rule (R := rules Ξ) ⟨_, _, .subTyComp⟩ (Fin.cases (encode h0) (Fin.cases (encode h1) (Fin.cases (encode h2) (fun i => Fin.elim0 i))))
  | .subTmId h0 => .rule (R := rules Ξ) ⟨_, _, .subTmId⟩ (Fin.cases (encode h0) (fun i => Fin.elim0 i))
  | .subTmComp h0 h1 h2 => .rule (R := rules Ξ) ⟨_, _, .subTmComp⟩ (Fin.cases (encode h0) (Fin.cases (encode h1) (Fin.cases (encode h2) (fun i => Fin.elim0 i))))
  | .subIdLeft h0 => .rule (R := rules Ξ) ⟨_, _, .subIdLeft⟩ (Fin.cases (encode h0) (fun i => Fin.elim0 i))
  | .subIdRight h0 => .rule (R := rules Ξ) ⟨_, _, .subIdRight⟩ (Fin.cases (encode h0) (fun i => Fin.elim0 i))
  | .subAssoc h0 h1 h2 => .rule (R := rules Ξ) ⟨_, _, .subAssoc⟩ (Fin.cases (encode h0) (Fin.cases (encode h1) (Fin.cases (encode h2) (fun i => Fin.elim0 i))))
  | .weakenPair h0 h1 h2 => .rule (R := rules Ξ) ⟨_, _, .weakenPair⟩ (Fin.cases (encode h0) (Fin.cases (encode h1) (Fin.cases (encode h2) (fun i => Fin.elim0 i))))
  | .genericPair h0 h1 h2 h3 => .rule (R := rules Ξ) ⟨_, _, .genericPair⟩ (Fin.cases (encode h0) (Fin.cases (encode h1) (Fin.cases (encode h2) (Fin.cases (encode h3) (fun i => Fin.elim0 i)))))
  | .identitySubLaw h0 h1 h2 => .rule (R := rules Ξ) ⟨_, _, .identitySubLaw⟩ (Fin.cases (encode h0) (Fin.cases (encode h1) (Fin.cases (encode h2) (fun i => Fin.elim0 i))))
  | .reflexivitySubLaw h0 h1 => .rule (R := rules Ξ) ⟨_, _, .reflexivitySubLaw⟩ (Fin.cases (encode h0) (Fin.cases (encode h1) (fun i => Fin.elim0 i)))
  | .eqRefl h0 => .rule (R := rules Ξ) ⟨_, _, .eqRefl⟩ (Fin.cases (encode h0) (fun i => Fin.elim0 i))
  | .eqSymm h0 => .rule (R := rules Ξ) ⟨_, _, .eqSymm⟩ (Fin.cases (encode h0) (fun i => Fin.elim0 i))
  | .eqTrans h0 h1 => .rule (R := rules Ξ) ⟨_, _, .eqTrans⟩ (Fin.cases (encode h0) (Fin.cases (encode h1) (fun i => Fin.elim0 i)))
  | .congruence op bs h0 h1 h2 =>
      .rule (R := rules Ξ) ⟨_, _, .congruence op bs⟩
        (Fin.cases (encode h0) (Fin.cases (encode h1) (fun i => by
          simpa using encode (h2 ⟨i.val, by simpa using i.isLt⟩))))

/-- A leaf template induces local certificates at every primitive rule.
Object substitution and its dependent tail remain explicit typed syntax. -/
def templateMap (Ξ : List (Declaration V)) (θ : V → Expression W) :
    DependentTheoryMaps.TheoryMap (rules Ξ) (rules (Ξ.map (Declaration.instantiate θ)))
      (Claim.instantiate θ) where
  certificate r := by
    let r' := r.2.2.instantiate θ
    apply DependentTheoryMaps.Derivation.rule
      (R := rules (Ξ.map (Declaration.instantiate θ))) ⟨_, _, r'⟩
    intro i
    apply DependentTheoryMaps.Derivation.hyp
    exact ⟨⟨i.val, by simpa using i.isLt⟩, by simp⟩

/-- Whole-proof translation follows from the reused local-certificate induction. -/
def transport {Ξ : List (Declaration V)} {c : Claim V}
    (θ : V → Expression W) (p : Proof Ξ c) :
    Proof (Ξ.map (Declaration.instantiate θ)) (c.instantiate θ) :=
  (templateMap Ξ θ).transport (fun _ => id) p

/-- Composition acts on actual proof trees, not only their inhabitedness. -/
theorem transport_comp {Ξ : List (Declaration V)} {c : Claim V}
    (θ : V → Expression W) (υ : W → Expression X) (p : Proof Ξ c) :
    ((templateMap Ξ θ).comp (templateMap (Ξ.map (Declaration.instantiate θ)) υ)).transport
      (H' := fun _ => Empty) (fun _ => id) p = transport υ (transport θ p) := by
  exact DependentTheoryMaps.TheoryMap.comp_transport _ _
    (B := fun _ => Empty) (C := fun _ => Empty) (fun _ => id) (fun _ => id) p

end RulePresentation
end SquareKit.Internal.DependentJudgments.Contextual.Reference
