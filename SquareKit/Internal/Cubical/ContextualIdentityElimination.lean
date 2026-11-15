import SquareKit.Internal.Cubical.ContextualTelescopeIdentity
import SquareKit.Internal.Cubical.ContextIsoBoundaries

namespace SquareKit.Cubical.Contextual
open CategoryTheory Presheaf SquareKit.Internal.PathTransport.Typed
universe u
variable (Base : LawfulFamily terminal.{u}) (Fiber : LawfulFamily (total Base.family))
local notation "M" => structuralModel Base Fiber
namespace IdentityElimination
set_option backward.isDefEq.respectTransparency false

noncomputable def branch {Γ : (M).Context} (A : (M).Family Γ) (a : (M).Section Γ A) {n : Nat} (T : StructuralModel.Telescope M ((M).pathContext A a) n)
    (C : (M).Family T.total)
    (d : Term (reindex C.family ((M).rootTail A a T).down)) :=
  Term.reindexSquare
    (Γ := (StructuralModel.Telescope.pullback M T ((M).rootSub A a)).total)
    (Δ := ((Telescope.realize Base Fiber T).reindex (NormalizedIdentitySingleton.reflexivity A.family a.down)).context)
    (Ω := T.total) (Ξ := (Telescope.realize Base Fiber T).context) C.family ((M).rootTail A a T).down
    (Telescope.branchIso Base Fiber A a T).hom
    ((Telescope.realize Base Fiber T).map (NormalizedIdentitySingleton.reflexivity A.family a.down))
    (Telescope.totalIso Base Fiber T).hom (Telescope.branch_square Base Fiber A a T).symm d

noncomputable def assembled {Γ : (M).Context} (A : (M).Family Γ) (a : (M).Section Γ A) {n : Nat}
    (T : StructuralModel.Telescope M ((M).pathContext A a) n) (C : (M).Family T.total)
    (d : Term (reindex C.family ((M).rootTail A a T).down)) :=
  NormalizedTelescopeIdentityElimination.eliminate A.family a.down (Telescope.realize Base Fiber T)
    (reindex C.family (Telescope.totalIso Base Fiber T).hom) (branch Base Fiber A a T C d)
    (Telescope.fillers Base Fiber T) (Telescope.fillers_lawful Base Fiber T)
    (C.filling.reindex (Telescope.totalIso Base Fiber T).hom)

theorem assembled_beta {Γ : (M).Context} (A : (M).Family Γ) (a : (M).Section Γ A) {n : Nat}
    (T : StructuralModel.Telescope M ((M).pathContext A a) n) (C : (M).Family T.total)
    (d : Term (reindex C.family ((M).rootTail A a T).down)) :
    (assembled Base Fiber A a T C d).reindex
      ((Telescope.realize Base Fiber T).map (NormalizedIdentitySingleton.reflexivity A.family a.down)) =
        branch Base Fiber A a T C d :=
  NormalizedTelescopeIdentityElimination.eliminate_beta A.family a.down
    (Telescope.realize Base Fiber T) (reindex C.family (Telescope.totalIso Base Fiber T).hom)
    (branch Base Fiber A a T C d) (Telescope.fillers Base Fiber T)
    (Telescope.fillers_lawful Base Fiber T) (C.filling.reindex (Telescope.totalIso Base Fiber T).hom)
    (C.lawful.reindex (Telescope.totalIso Base Fiber T).hom)

noncomputable def eliminate {Γ : (M).Context} (A : (M).Family Γ) (a : (M).Section Γ A) {n : Nat}
    (T : StructuralModel.Telescope M ((M).pathContext A a) n) (C : (M).Family T.total)
    (d : Term (reindex C.family ((M).rootTail A a T).down)) : Term C.family :=
  (assembled Base Fiber A a T C d).descendIso (Telescope.totalIso Base Fiber T)

theorem eliminate_beta {Γ : (M).Context} (A : (M).Family Γ) (a : (M).Section Γ A) {n : Nat}
    (T : StructuralModel.Telescope M ((M).pathContext A a) n) (C : (M).Family T.total)
    (d : Term (reindex C.family ((M).rootTail A a T).down)) :
    (eliminate Base Fiber A a T C d).reindex ((M).rootTail A a T).down = d := by
  apply Term.descendIso_boundary (Telescope.totalIso Base Fiber T) (Telescope.branchIso Base Fiber A a T)
    ((Telescope.realize Base Fiber T).map (NormalizedIdentitySingleton.reflexivity A.family a.down))
    ((M).rootTail A a T).down (Telescope.branch_square Base Fiber A a T)
  have h₁ := heq_of_eq (assembled_beta Base Fiber A a T C d)
  have h₂ := Term.reindexSquare_heq C.family ((M).rootTail A a T).down
    (Telescope.branchIso Base Fiber A a T).hom
    ((Telescope.realize Base Fiber T).map (NormalizedIdentitySingleton.reflexivity A.family a.down))
    (Telescope.totalIso Base Fiber T).hom (Telescope.branch_square Base Fiber A a T).symm d
  run_tac Lean.Elab.Tactic.withMainContext do
    let h₁ ← Lean.Meta.getLocalDeclFromUserName `h₁
    let h₂ ← Lean.Meta.getLocalDeclFromUserName `h₂
    let t₁ ← Lean.instantiateMVars h₁.type
    let t₂ ← Lean.instantiateMVars h₂.type
    let a := t₁.getAppArgs
    let b := t₂.getAppArgs
    let proof := Lean.mkAppN (Lean.mkConst ``HEq.trans t₁.getAppFn.constLevels!)
      #[a[0]!,a[2]!,b[2]!,a[1]!,a[3]!,b[3]!,h₁.toExpr,h₂.toExpr]
    Lean.Elab.Tactic.closeMainGoal `exact proof

end IdentityElimination
end SquareKit.Cubical.Contextual
