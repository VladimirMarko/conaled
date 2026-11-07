import SquareKit.DependentTemplateInjection

/-! Composition of finite symbol templates. Added metavariables are kept fixed
while the ordinary target symbols are expanded by the second template map. -/
namespace SquareKit.DependentTheoryMaps

namespace SyntaxMap
variable {S T : Signature}

theorem act_lift (F : SyntaxMap S T) (ρ : X → Expr S V) :
    (fun x : Fin n ⊕ X => F.act (Expr.lift ρ x)) =
      Expr.lift (fun x => F.act (ρ x)) := by
  funext x
  cases x with
  | inl => exact F.on_var _
  | inr => exact F.rename _ _

theorem act_weaken (F : SyntaxMap S T) (a : Assignment S M V) :
    (fun m => F.act (a.weaken n m)) =
      Assignment.weaken (fun m => F.act (a m)) n := by
  funext m
  exact F.rename _ _
end SyntaxMap

namespace TemplateMap
variable {S T U : Signature}

/-- Extend a template interpretation by leaving the additional metavariables
fixed. Only ordinary symbols are expanded by the finite template body. -/
def liftedOperations (G : TemplateMap T U) (M : Metavariables) :
    OperationMap (extend T M) (extend U M) where
  operation := fun s args => match s with
    | .inl t => instantiate Empty.elim args (includeBody M (G t))
    | .inr m => Expr.app (.inr m) args
  natural := by
    intro V W f s args
    cases s with
    | inl t =>
      erw [instantiate_subst]
      congr 1
      funext x
      exact x.elim
    | inr m => rfl

def liftedSyntax (G : TemplateMap T U) (M : Metavariables) :
    SyntaxMap (extend T M) (extend U M) := .ofOperations (liftedOperations G M)

/-- Interpreting a lifted template commutes with instantiating its metavariables.
The same selected bodies and free-variable substitution appear on both routes. -/
theorem instantiate_lifted (G : TemplateMap T U) (ρ : X → Expr T V)
    (a : Assignment T M V) (e : Expr (extend T M) X) :
    instantiate (fun x => (toSyntax G).act (ρ x))
      (fun m => (toSyntax G).act (a m)) ((liftedSyntax G M).act e) =
      (toSyntax G).act (instantiate ρ a e) := by
  induction e generalizing V with
  | var => rfl
  | @app X s es ih =>
    cases s with
    | inl t =>
      change instantiate _ _ (instantiate Empty.elim
        (fun i => (liftedSyntax G M).act (es i)) (includeBody M (G t))) = _
      rw [instantiate_includeBody_closed]
      change instantiate Empty.elim _ (G t) =
        instantiate Empty.elim (fun i => (toSyntax G).act
          (instantiate (Expr.lift ρ) (a.weaken (T.binds t i)) (es i))) (G t)
      congr 1
      funext i
      simpa only [SyntaxMap.act_lift, SyntaxMap.act_weaken] using
        ih i (Expr.lift ρ) (a.weaken (T.binds t i))
    | inr m =>
      change Expr.subst _ ((toSyntax G).act (a m)) =
        (toSyntax G).act (Expr.subst _ (a m))
      erw [(toSyntax G).substitution]
      congr 1
      funext x
      cases x with
      | inl i =>
        change instantiate (Sum.elim Fin.elim0 (fun x => (toSyntax G).act (ρ x)))
          (fun m => (toSyntax G).act (a m)) ((liftedSyntax G M).act (es i)) =
            (toSyntax G).act (instantiate (Sum.elim Fin.elim0 ρ) a (es i))
        have hz : (fun x : Fin 0 ⊕ X => (toSyntax G).act (Sum.elim Fin.elim0 ρ x)) =
            Sum.elim Fin.elim0 (fun x => (toSyntax G).act (ρ x)) := by
          funext x
          cases x with
          | inl z => exact Fin.elim0 z
          | inr => rfl
        simpa only [hz] using ih i (Sum.elim Fin.elim0 ρ) a
      | inr v => exact ((toSyntax G).on_var v).symm

/-- Composite images are finite closed expressions over exactly the original
symbol's argument metavariables, rather than arbitrary expression functions. -/
def comp (F : TemplateMap S T) (G : TemplateMap T U) : TemplateMap S U :=
  fun s => (liftedSyntax G (symbolMetavariables S s)).act (F s)

/-- Interpreting the composed closed templates agrees on every expression with
successive interpretation. This includes symbols with dependent binding scopes. -/
theorem comp_act (F : TemplateMap S T) (G : TemplateMap T U) (e : Expr S V) :
    (toSyntax (comp F G)).act e = (toSyntax G).act ((toSyntax F).act e) := by
  induction e with
  | var => rfl
  | @app V s es ih =>
    change instantiate Empty.elim (fun i => (toSyntax (comp F G)).act (es i))
      ((liftedSyntax G (symbolMetavariables S s)).act (F s)) =
        (toSyntax G).act (instantiate Empty.elim (fun i => (toSyntax F).act (es i)) (F s))
    have hn := instantiate_lifted G Empty.elim
      (fun i => (toSyntax F).act (es i)) (F s)
    have he : (fun x : Empty => (toSyntax G).act (Empty.elim x : Expr T V)) = Empty.elim :=
      funext (fun x => x.elim)
    rw [he] at hn
    rw [← hn]
    congr 1
    funext i
    exact ih i

theorem comp_identity_act (F : TemplateMap S T) (e : Expr S V) :
    (toSyntax (comp F (identity T))).act e = (toSyntax F).act e := by
  rw [comp_act, identity_act]

theorem identity_comp_act (F : TemplateMap S T) (e : Expr S V) :
    (toSyntax (comp (identity S) F)).act e = (toSyntax F).act e := by
  rw [comp_act, identity_act]

theorem comp_assoc_act {Z : Signature} (F : TemplateMap S T) (G : TemplateMap T U)
    (H : TemplateMap U Z) (e : Expr S V) :
    (toSyntax (comp (comp F G) H)).act e =
      (toSyntax (comp F (comp G H))).act e := by
  simp only [comp_act]

end TemplateMap
end SquareKit.DependentTheoryMaps
