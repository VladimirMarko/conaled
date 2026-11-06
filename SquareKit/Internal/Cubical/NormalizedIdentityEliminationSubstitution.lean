import SquareKit.Internal.Cubical.NormalizedIdentitySingletonSubstitution
import SquareKit.Internal.Cubical.IdentityEliminationSubstitution
import SquareKit.Internal.Cubical.ContextIsoSectionSquares

namespace SquareKit.Cubical.Presheaf
open CategoryTheory
universe u

private theorem compositionReindex_heq {Γ Δ : Context.{u}} {A : Family Γ} (G : Composition A)
    {σ τ : Δ ⟶ Γ} (e : σ = τ) : HEq (G.reindex σ) (G.reindex τ) := by cases e; rfl

private theorem eliminate_heq {Γ : Context.{u}} (A : Family Γ) (a : Term A)
    {C D : Family (IdentitySingleton.context A a)} (e : C = D)
    {d : Term (reindex C (IdentitySingleton.reflexivity A a))}
    {d' : Term (reindex D (IdentitySingleton.reflexivity A a))} (hd : HEq d d')
    {G : Composition C} {G' : Composition D} (hG : HEq G G') :
    HEq (IdentityElimination.eliminate A a C d G) (IdentityElimination.eliminate A a D d' G') := by
  cases e
  cases hd
  cases hG
  rfl

private theorem eliminate_square {Γ Ω Ξ Ξ' : Context.{u}} (A : Family Γ) (a : Term A)
    (C : Family Ω) (s : IdentitySingleton.context A a ⟶ Ξ) (σ : Ξ ⟶ Ω)
    (t : IdentitySingleton.context A a ⟶ Ξ') (τ : Ξ' ⟶ Ω) (hs : s ≫ σ = t ≫ τ)
    (d : Term (reindex (reindex C σ) (IdentitySingleton.reflexivity A a ≫ s)))
    (d' : Term (reindex (reindex (reindex C τ) t) (IdentitySingleton.reflexivity A a)))
    (hd : HEq d d') (G : Composition C) :
    HEq (IdentityElimination.eliminate A a (reindex (reindex C σ) s) d ((G.reindex σ).reindex s))
      (IdentityElimination.eliminate A a (reindex (reindex C τ) t) d' ((G.reindex τ).reindex t)) :=
  eliminate_heq A a (congrArg (reindex C) hs) hd (compositionReindex_heq G hs)

namespace NormalizedIdentityElimination
set_option backward.isDefEq.respectTransparency true
set_option backward.isDefEq.respectTransparency.types true
set_option backward.defeqAttrib.useBackward false
open NormalizedIdentitySingleton
variable {Γ Δ : Context.{u}} (A : Family Γ) (a : Term A)
  (C : Family (context A a)) (d : Term (reindex C (reflexivity A a)))

def branchReindex (σ : Δ ⟶ Γ) :
    Term (reindex (reindex C (reindexMap A a σ)) (reflexivity (reindex A σ) (a.reindex σ))) :=
  Term.reindexSquare C (reflexivity A a) σ
    (reflexivity (reindex A σ) (a.reindex σ)) (reindexMap A a σ)
    (reindexMap_reflexivity A a σ) d

theorem eliminate_reindex (G : Composition C) (hG : G.Lawful) (σ : Δ ⟶ Γ) :
    eliminate (reindex A σ) (a.reindex σ) (reindex C (reindexMap A a σ))
      (branchReindex A a C d σ) (G.reindex (reindexMap A a σ)) =
      (eliminate A a C d G).reindex (reindexMap A a σ) := by
  let e := presentation A a
  let e' := presentation (reindex A σ) (a.reindex σ)
  let τ := reindexMap A a σ
  let τ₀ := IdentitySingleton.reindexMap A a σ
  have hs := presentation_reindexMap A a σ
  have hd : HEq (branchReindex A a C d σ)
      (IdentityElimination.branchReindex A a (reindex C e.hom) d σ) :=
    (Term.reindexSquare_heq C (reflexivity A a) σ
      (reflexivity (reindex A σ) (a.reindex σ)) (reindexMap A a σ)
      (reindexMap_reflexivity A a σ) d).trans (IdentityElimination.branchReindex_heq A a (reindex C e.hom) d σ).symm
  have hj := eliminate_square (Γ := Δ) (Ω := context A a)
    (Ξ := context (reindex A σ) (a.reindex σ)) (Ξ' := IdentitySingleton.context A a) (reindex A σ) (a.reindex σ) C e'.hom τ τ₀ e.hom hs
    (branchReindex A a C d σ) (IdentityElimination.branchReindex A a (reindex C e.hom) d σ) hd G
  have hu := IdentityElimination.eliminate_reindex A a (reindex C e.hom) d
    (G.reindex e.hom) (hG.reindex e.hom) σ
  have hu' := heq_of_eq hu
  run_tac Lean.Elab.Tactic.withMainContext do
    let h₁ ← Lean.Meta.getLocalDeclFromUserName `hj
    let h₂ ← Lean.Meta.getLocalDeclFromUserName `hu'
    let t₁ ← Lean.instantiateMVars h₁.type
    let t₂ ← Lean.instantiateMVars h₂.type
    let a := t₁.getAppArgs
    let b := t₂.getAppArgs
    let proof := Lean.mkAppN (Lean.mkConst ``HEq.trans t₁.getAppFn.constLevels!)
      #[a[0]!,a[2]!,b[2]!,a[1]!,a[3]!,b[3]!,h₁.toExpr,h₂.toExpr]
    let ty ← Lean.Meta.inferType proof
    let goal ← Lean.Elab.Tactic.getMainGoal
    let goal ← goal.assert `hv ty proof
    let (_,goal) ← goal.intro1P
    Lean.Elab.Tactic.replaceMainGoal [goal]
  unfold eliminate
  run_tac Lean.Elab.Tactic.withMainContext do
    let e ← Lean.Meta.getLocalDeclFromUserName `e
    let e' ← Lean.Meta.getLocalDeclFromUserName `e'
    let τ ← Lean.Meta.getLocalDeclFromUserName `τ
    let τ₀ ← Lean.Meta.getLocalDeclFromUserName `τ₀
    let hs ← Lean.Meta.getLocalDeclFromUserName `hs
    let C ← Lean.Meta.getLocalDeclFromUserName `C
    let hv ← Lean.Meta.getLocalDeclFromUserName `hv
    let ht ← Lean.instantiateMVars hv.type
    let hargs := ht.getAppArgs
    let right := hargs[3]!.getAppArgs
    let et := (← Lean.instantiateMVars e.type).getAppArgs
    let et' := (← Lean.instantiateMVars e'.type).getAppArgs
    unless et.size ≥ 2 && et'.size ≥ 2 && right.size ≥ 2 do
      throwError "argument sizes {et.size} {et'.size} {right.size}; right {hargs[3]!}"
    let proof := Lean.mkAppN (Lean.mkConst ``Term.descendIso_naturality [Lean.Level.param `u])
      #[et[et.size-2]!, et'[et'.size-2]!, et[et.size-1]!, et'[et'.size-1]!,
        e.toExpr,e'.toExpr,τ.toExpr,τ₀.toExpr,hs.toExpr,C.toExpr,
        right[right.size-2]!,hargs[1]!,hv.toExpr]
    Lean.Elab.Tactic.closeMainGoal `exact proof

end NormalizedIdentityElimination
end SquareKit.Cubical.Presheaf
