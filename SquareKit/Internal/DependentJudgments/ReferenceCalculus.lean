import SquareKit.Internal.DependentJudgments.FiniteTailTranslation

/-! A bounded contextual explicit-substitution calculus. Its inference rules
are specified independently of guarded derivations. Context extension binds a
new variable; weakening and the generic term are its elimination operations.
The same raw tree mechanics are used only to avoid a second substitution engine. -/
namespace SquareKit.Internal.DependentJudgments.Contextual.Reference
open GuardedTheory
variable {V : Type}

inductive Boundary (V : Type) where
  | ctx
  | ty (Γ : Expression V)
  | tm (Γ A : Expression V)
  | sub (Δ Γ : Expression V)
  | tel (length : Nat) (Γ : Expression V)

inductive Claim (V : Type) where
  | has (boundary : Boundary V) (expression : Expression V)
  | eq (boundary : Boundary V) (left right : Expression V)
  | tail (Γ : Expression V) (T : Tail V)

/-- The closed structural policy admits family and term declarations, and
explicit equations at such boundaries. No primitive context or substitution
declarations are admitted. Each use checks its presuppositions below. -/
inductive Declaration (V : Type) where
  | family (Γ A : Expression V)
  | term (Γ A t : Expression V)
  | familyEq (Γ A B : Expression V)
  | termEq (Γ A s t : Expression V)

inductive Derives (Ξ : List (Declaration V)) : Claim V → Type where
  | empty : Derives Ξ (.has .ctx empty)
  | extend : Derives Ξ (.has (.ty Γ) A) → Derives Ξ (.has .ctx (extend Γ A))
  | familyDecl : Declaration.family Γ A ∈ Ξ → Derives Ξ (.has .ctx Γ) →
      Derives Ξ (.has (.ty Γ) A)
  | termDecl : Declaration.term Γ A t ∈ Ξ → Derives Ξ (.has (.ty Γ) A) →
      Derives Ξ (.has (.tm Γ A) t)
  | typeContext : Derives Ξ (.has (.ty Γ) A) → Derives Ξ (.has .ctx Γ)
  | termFamily : Derives Ξ (.has (.tm Γ A) t) → Derives Ξ (.has (.ty Γ) A)
  | subTy : Derives Ξ (.has (.ty Γ) A) → Derives Ξ (.has (.sub Δ Γ) σ) →
      Derives Ξ (.has (.ty Δ) (subTy A σ))
  | subTm : Derives Ξ (.has (.tm Γ A) t) → Derives Ξ (.has (.sub Δ Γ) σ) →
      Derives Ξ (.has (.tm Δ (subTy A σ)) (subTm t σ))
  | identitySub : Derives Ξ (.has .ctx Γ) → Derives Ξ (.has (.sub Γ Γ) (identitySub Γ))
  | comp : Derives Ξ (.has (.sub Δ Γ) σ) → Derives Ξ (.has (.sub Θ Δ) τ) →
      Derives Ξ (.has (.sub Θ Γ) (comp σ τ))
  | weaken : Derives Ξ (.has (.ty Γ) A) → Derives Ξ (.has (.sub (extend Γ A) Γ) (weaken Γ A))
  | generic : Derives Ξ (.has (.ty Γ) A) →
      Derives Ξ (.has (.tm (extend Γ A) (subTy A (weaken Γ A))) (generic Γ A))
  | pair : Derives Ξ (.has (.ty Γ) A) → Derives Ξ (.has (.sub Δ Γ) σ) →
      Derives Ξ (.has (.tm Δ (subTy A σ)) t) →
      Derives Ξ (.has (.sub Δ (extend Γ A)) (pair A σ t))
  | identity : Derives Ξ (.has (.tm Γ A) x) → Derives Ξ (.has (.tm Γ A) y) →
      Derives Ξ (.has (.ty Γ) (identity A x y))
  | reflexivity : Derives Ξ (.has (.tm Γ A) x) →
      Derives Ξ (.has (.tm Γ (identity A x x)) (reflexivity A x))
  | path : Derives Ξ (.has (.tm Γ A) x) → Derives Ξ (.has .ctx (path A x))
  | root : Derives Ξ (.has (.tm Γ A) x) → Derives Ξ (.has (.sub Γ (path A x)) (root A x))
  | pathSub : Derives Ξ (.has (.tm Γ A) x) → Derives Ξ (.has (.sub Δ Γ) σ) →
      Derives Ξ (.has (.sub (path (subTy A σ) (subTm x σ)) (path A x)) (pathSub A x σ))
  | nil : Derives Ξ (.has .ctx Γ) → Derives Ξ (.tail Γ .nil)
  | cons : Derives Ξ (.has (.ty Γ) A) → Derives Ξ (.tail (extend Γ A) T) →
      Derives Ξ (.tail Γ (.cons A T))
  | tailCode : Derives Ξ (.tail Γ T) →
      Derives Ξ (.has (.tel T.length Γ) (T.code Γ))
  | contextConvertTel : Derives Ξ (.has (.tel n Γ) t) → Derives Ξ (.eq .ctx Γ Δ) →
      Derives Ξ (.has (.tel n Δ) t)
  | tailTotal : Derives Ξ (.tail Γ T) → Derives Ξ (.has .ctx (T.total Γ))
  | branchMap : Derives Ξ (.has (.tm Γ A) x) → Derives Ξ (.tail (path A x) T) →
      Derives Ξ (.has (.sub Δ Γ) σ) →
      Derives Ξ (.has .ctx ((T.alongPath A x σ).rootDomain Δ (subTy A σ) (subTm x σ))) →
      Derives Ξ (.has .ctx (T.rootDomain Γ A x)) →
      Derives Ξ (.has (.sub ((T.alongPath A x σ).rootDomain Δ (subTy A σ) (subTm x σ))
        (T.rootDomain Γ A x)) (branchMap A x (T.code (path A x)) σ))
  | branchSquare : Derives Ξ (.has (.tm Γ A) x) → Derives Ξ (.tail (path A x) T) →
      Derives Ξ (.has (.sub Δ Γ) σ) →
      Derives Ξ (.has (.sub ((T.alongPath A x σ).rootDomain Δ (subTy A σ) (subTm x σ))
        (T.total (path A x))) (comp (T.alongPathMap A x σ)
          ((T.alongPath A x σ).map Δ (root (subTy A σ) (subTm x σ))))) →
      Derives Ξ (.has (.sub ((T.alongPath A x σ).rootDomain Δ (subTy A σ) (subTm x σ))
        (T.total (path A x))) (comp (T.map Γ (root A x)) (branchMap A x (T.code (path A x)) σ))) →
      Derives Ξ (.eq (.sub ((T.alongPath A x σ).rootDomain Δ (subTy A σ) (subTm x σ))
        (T.total (path A x))) (comp (T.alongPathMap A x σ)
          ((T.alongPath A x σ).map Δ (root (subTy A σ) (subTm x σ))))
        (comp (T.map Γ (root A x)) (branchMap A x (T.code (path A x)) σ)))
  | j : Derives Ξ (.has (.tm Γ A) x) → Derives Ξ (.tail (path A x) T) →
      Derives Ξ (.has (.ty (T.total (path A x))) D) →
      Derives Ξ (.has (.tm ((T.reindex Γ (root A x)).total Γ)
        (subTy D (T.map Γ (root A x)))) d) →
      Derives Ξ (.has (.tm (T.total (path A x)) D) (j A x (T.code (path A x)) D d))
  | jBeta : Derives Ξ (.has (.tm Γ A) x) → Derives Ξ (.tail (path A x) T) →
      Derives Ξ (.has (.ty (T.total (path A x))) D) →
      Derives Ξ (.has (.tm ((T.reindex Γ (root A x)).total Γ)
        (subTy D (T.map Γ (root A x)))) d) →
      Derives Ξ (.has (.tm ((T.reindex Γ (root A x)).total Γ)
        (subTy D (T.map Γ (root A x))))
        (subTm (j A x (T.code (path A x)) D d) (T.map Γ (root A x)))) →
      Derives Ξ (.eq (.tm ((T.reindex Γ (root A x)).total Γ)
        (subTy D (T.map Γ (root A x))))
        (subTm (j A x (T.code (path A x)) D d) (T.map Γ (root A x))) d)
  | jSub : Derives Ξ (.has (.tm Γ A) x) → Derives Ξ (.tail (path A x) T) →
      Derives Ξ (.has (.ty (T.total (path A x))) D) →
      Derives Ξ (.has (.tm (T.rootDomain Γ A x) (subTy D (T.map Γ (root A x)))) d) →
      Derives Ξ (.has (.sub Δ Γ) σ) →
      Derives Ξ (.has (.tm ((T.alongPath A x σ).total (path (subTy A σ) (subTm x σ)))
        (subTy D (T.alongPathMap A x σ)))
        (subTm (j A x (T.code (path A x)) D d) (T.alongPathMap A x σ))) →
      Derives Ξ (.has (.tm ((T.alongPath A x σ).total (path (subTy A σ) (subTm x σ)))
        (subTy D (T.alongPathMap A x σ)))
        (j (subTy A σ) (subTm x σ) ((T.alongPath A x σ).code (path (subTy A σ) (subTm x σ)))
          (subTy D (T.alongPathMap A x σ)) (subTm d (branchMap A x (T.code (path A x)) σ)))) →
      Derives Ξ (.eq (.tm ((T.alongPath A x σ).total (path (subTy A σ) (subTm x σ)))
        (subTy D (T.alongPathMap A x σ)))
        (subTm (j A x (T.code (path A x)) D d) (T.alongPathMap A x σ))
        (j (subTy A σ) (subTm x σ) ((T.alongPath A x σ).code (path (subTy A σ) (subTm x σ)))
          (subTy D (T.alongPathMap A x σ)) (subTm d (branchMap A x (T.code (path A x)) σ))))
  | convert : Derives Ξ (.has (.tm Γ A) t) → Derives Ξ (.eq (.ty Γ) A B) →
      Derives Ξ (.has (.tm Γ B) t)
  | contextConvertType : Derives Ξ (.has (.ty Γ) A) → Derives Ξ (.eq .ctx Γ Δ) →
      Derives Ξ (.has (.ty Δ) A)
  | contextConvertTerm : Derives Ξ (.has (.tm Γ A) t) → Derives Ξ (.eq .ctx Γ Δ) →
      Derives Ξ (.has (.tm Δ A) t)
  | contextConvertSub : Derives Ξ (.has (.sub Δ Γ) σ) →
      Derives Ξ (.eq .ctx Δ Δ') → Derives Ξ (.eq .ctx Γ Γ') →
      Derives Ξ (.has (.sub Δ' Γ') σ)
  | pathDef : Derives Ξ (.has (.tm Γ A) x) →
      Derives Ξ (.eq .ctx (path A x) (extend (extend Γ A) (pathFamily Γ A x)))
  | rootDef : Derives Ξ (.has (.tm Γ A) x) →
      Derives Ξ (.has (.sub Γ (path A x))
        (pair (pathFamily Γ A x) (sectionSub Γ A x) (reflexivity A x))) →
      Derives Ξ (.eq (.sub Γ (path A x)) (root A x)
        (pair (pathFamily Γ A x) (sectionSub Γ A x) (reflexivity A x)))
  | pairEta : Derives Ξ (.has (.ty Γ) A) →
      Derives Ξ (.has (.sub Δ (extend Γ A)) σ) →
      Derives Ξ (.has (.sub Δ (extend Γ A))
        (pair A (comp (weaken Γ A) σ) (subTm (generic Γ A) σ))) →
      Derives Ξ (.eq (.sub Δ (extend Γ A))
        (pair A (comp (weaken Γ A) σ) (subTm (generic Γ A) σ)) σ)
  | familyEqDecl : Declaration.familyEq Γ A B ∈ Ξ →
      Derives Ξ (.has (.ty Γ) A) → Derives Ξ (.has (.ty Γ) B) →
      Derives Ξ (.eq (.ty Γ) A B)
  | termEqDecl : Declaration.termEq Γ A s t ∈ Ξ →
      Derives Ξ (.has (.tm Γ A) s) → Derives Ξ (.has (.tm Γ A) t) →
      Derives Ξ (.eq (.tm Γ A) s t)
  | pairComp : Derives Ξ (.has (.ty Γ) A) → Derives Ξ (.has (.sub Δ Γ) σ) →
      Derives Ξ (.has (.tm Δ (subTy A σ)) t) → Derives Ξ (.has (.sub Θ Δ) τ) →
      Derives Ξ (.eq (.sub Θ (extend Γ A)) (comp (pair A σ t) τ)
        (pair A (comp σ τ) (subTm t τ)))
  | subTyId : Derives Ξ (.has (.ty Γ) A) →
      Derives Ξ (.eq (.ty Γ) (subTy A (identitySub Γ)) A)
  | subTyComp : Derives Ξ (.has (.ty Γ) A) → Derives Ξ (.has (.sub Δ Γ) σ) →
      Derives Ξ (.has (.sub Θ Δ) τ) →
      Derives Ξ (.eq (.ty Θ) (subTy (subTy A σ) τ) (subTy A (comp σ τ)))
  | subTmId : Derives Ξ (.has (.tm Γ A) t) →
      Derives Ξ (.eq (.tm Γ A) (subTm t (identitySub Γ)) t)
  | subTmComp : Derives Ξ (.has (.tm Γ A) t) → Derives Ξ (.has (.sub Δ Γ) σ) →
      Derives Ξ (.has (.sub Θ Δ) τ) →
      Derives Ξ (.eq (.tm Θ (subTy A (comp σ τ)))
        (subTm (subTm t σ) τ) (subTm t (comp σ τ)))
  | subIdLeft : Derives Ξ (.has (.sub Δ Γ) σ) →
      Derives Ξ (.eq (.sub Δ Γ) (comp (identitySub Γ) σ) σ)
  | subIdRight : Derives Ξ (.has (.sub Δ Γ) σ) →
      Derives Ξ (.eq (.sub Δ Γ) (comp σ (identitySub Δ)) σ)
  | subAssoc : Derives Ξ (.has (.sub Δ Γ) σ) → Derives Ξ (.has (.sub Θ Δ) τ) →
      Derives Ξ (.has (.sub Λ Θ) υ) →
      Derives Ξ (.eq (.sub Λ Γ) (comp (comp σ τ) υ) (comp σ (comp τ υ)))
  | weakenPair : Derives Ξ (.has (.ty Γ) A) → Derives Ξ (.has (.sub Δ Γ) σ) →
      Derives Ξ (.has (.tm Δ (subTy A σ)) t) →
      Derives Ξ (.eq (.sub Δ Γ) (comp (weaken Γ A) (pair A σ t)) σ)
  | genericPair : Derives Ξ (.has (.ty Γ) A) → Derives Ξ (.has (.sub Δ Γ) σ) →
      Derives Ξ (.has (.tm Δ (subTy A σ)) t) →
      Derives Ξ (.has (.tm Δ (subTy A σ)) (subTm (generic Γ A) (pair A σ t))) →
      Derives Ξ (.eq (.tm Δ (subTy A σ)) (subTm (generic Γ A) (pair A σ t)) t)
  | identitySubLaw : Derives Ξ (.has (.tm Γ A) x) → Derives Ξ (.has (.tm Γ A) y) →
      Derives Ξ (.has (.sub Δ Γ) σ) →
      Derives Ξ (.eq (.ty Δ) (subTy (identity A x y) σ)
        (identity (subTy A σ) (subTm x σ) (subTm y σ)))
  | reflexivitySubLaw : Derives Ξ (.has (.tm Γ A) x) → Derives Ξ (.has (.sub Δ Γ) σ) →
      Derives Ξ (.eq (.tm Δ (identity (subTy A σ) (subTm x σ) (subTm x σ)))
        (subTm (reflexivity A x) σ) (reflexivity (subTy A σ) (subTm x σ)))
  | eqRefl : Derives Ξ (.has b t) → Derives Ξ (.eq b t t)
  | eqSymm : Derives Ξ (.eq b s t) → Derives Ξ (.eq b t s)
  | eqTrans : Derives Ξ (.eq b r s) → Derives Ξ (.eq b s t) → Derives Ξ (.eq b r t)
  | congruence (op : signature.Operation) (bs : Fin (signature.arity op) → Boundary V)
      {args args' : Fin (signature.arity op) → Expression V} :
      Derives Ξ (.has b (.app op args)) → Derives Ξ (.has b (.app op args')) →
      (∀ i, Derives Ξ (.eq (bs i) (args i) (args' i))) →
      Derives Ξ (.eq b (.app op args) (.app op args'))

end SquareKit.Internal.DependentJudgments.Contextual.Reference
