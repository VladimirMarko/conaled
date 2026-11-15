import SquareKit.DependentTheoryTemplates

namespace SquareKit.DependentTheoryMaps.TemplateMap

variable {U : Signature} {M N : Metavariables} {X Y V : Type}

/-- Add ambient metavariables without changing the template's argument metavariables. -/
def includeBody (M : Metavariables) {X : Type} : Expr (extend U N) X → Expr (extend (extend U M) N) X
  | .var x => .var x
  | .app (.inl u) es => .app (.inl (.inl u)) (fun i => includeBody M (es i))
  | .app (.inr n) es => .app (.inr n) (fun i => includeBody M (es i))

theorem instantiate_shift (ρ : X → Expr U V) (a : Assignment U M V)
    (e : Expr (extend U M) (Fin n ⊕ X)) :
    instantiate (Expr.lift (n := n) (Expr.lift (n := k) ρ)) ((a.weaken k).weaken n)
      (Expr.rename (Sum.map id Sum.inr) e) =
      Expr.rename (Sum.map id Sum.inr) (instantiate (Expr.lift ρ) (a.weaken n) e) := by
  rw [instantiate_rename, ← Expr.subst_vars, instantiate_subst]
  congr 1
  · funext x
    cases x with
    | inl => rfl
    | inr x => simp [Expr.lift, Expr.subst_vars, Expr.rename_comp, Function.comp_def]
  · funext i
    simp only [Assignment.subst, Assignment.weaken, Expr.subst_rename, Expr.rename_comp]
    rw [← Expr.subst_vars]
    congr 1
    funext x
    cases x <;> rfl

theorem instantiate_includeBody (b : Expr (extend U N) Y)
    (η : Y → Expr (extend U M) X) (args : Assignment (extend U M) N X)
    (ρ : X → Expr U V) (a : Assignment U M V) :
    instantiate ρ a (instantiate η args (includeBody M b)) =
      instantiate (fun y => instantiate ρ a (η y))
        (fun n => instantiate (Expr.lift (n := N.arguments n) ρ)
          (a.weaken (N.arguments n)) (args n)) b := by
  induction b generalizing X V with
  | var y => rfl
  | app s es ih =>
    cases s with
    | inl u =>
      simp only [includeBody, instantiate]
      congr 1
      funext i
      rw [ih i]
      congr 1
      · funext z
        cases z with
        | inl => rfl
        | inr => exact instantiate_weaken ρ a _
      · funext n
        exact instantiate_shift ρ a (args n)
    | inr n =>
      simp only [includeBody, instantiate]
      refine (instantiate_bound ρ a (args n) _).trans ?_
      congr 1
      funext z
      cases z with
      | inl i =>
        refine (ih i (Sum.elim Fin.elim0 η) args ρ a).trans ?_
        congr 1
        funext v
        cases v with
        | inl v => exact Fin.elim0 v
        | inr => rfl
      | inr => rfl

theorem instantiate_includeBody_closed (b : Expr (extend U N) Empty)
    (args : Assignment (extend U M) N X) (ρ : X → Expr U V) (a : Assignment U M V) :
    instantiate ρ a (instantiate Empty.elim args (includeBody M b)) =
      instantiate Empty.elim
        (fun n => instantiate (Expr.lift (n := N.arguments n) ρ)
          (a.weaken (N.arguments n)) (args n)) b := by
  rw [instantiate_includeBody]
  congr 1
  funext e
  exact Empty.elim e

end SquareKit.DependentTheoryMaps.TemplateMap
