import SquareKit.DependentTheoryMaps

/-! Explicit metavariable templates for finite binding signatures. -/
namespace SquareKit.DependentTheoryMaps

structure Metavariables where
  count : Nat
  arguments : Fin count → Nat

abbrev extend (S : Signature) (M : Metavariables) : Signature where
  Symbol := S.Symbol ⊕ Fin M.count
  arity := Sum.elim S.arity M.arguments
  binds := fun s => match s with
    | .inl s => S.binds s
    | .inr _ => fun _ => 0

/-- Metavariable bodies have exactly their argument variables and the ambient scope. -/
abbrev Assignment (S : Signature) (M : Metavariables) (V : Type) :=
  (i : Fin M.count) → Expr S (Fin (M.arguments i) ⊕ V)

namespace Assignment

def weaken (a : Assignment S M V) (n : Nat) : Assignment S M (Fin n ⊕ V) :=
  fun i => Expr.rename (Sum.map id Sum.inr) (a i)

def subst (f : V → Expr S W) (a : Assignment S M V) : Assignment S M W :=
  fun i => Expr.subst (Expr.lift f) (a i)
end Assignment

/-- Simultaneous substitution for free variables and application of metavariables.
A metavariable application instantiates its body with its translated arguments. -/
def instantiate {S : Signature} {M : Metavariables} :
    {X V : Type} → (X → Expr S V) → Assignment S M V → Expr (extend S M) X → Expr S V
  | _, _, ρ, _, .var x => ρ x
  | _, _, ρ, a, .app (.inl s) es => .app s (fun i =>
      instantiate (Expr.lift ρ) (a.weaken (S.binds s i)) (es i))
  | _, _, ρ, a, .app (.inr m) es => Expr.subst
      (Sum.elim (fun i => instantiate (Sum.elim Fin.elim0 ρ) a (es i)) Expr.var) (a m)

namespace Expr
variable {S : Signature} {V W : Type}

@[simp] theorem rename_weaken_lift (f : V → Expr S W) (e : Expr S (Fin n ⊕ V)) :
    Expr.rename (Sum.map id Sum.inr) (Expr.subst (Expr.lift f) e) =
      Expr.subst (Expr.lift (Expr.lift (n := k) f))
        (Expr.rename (Sum.map id Sum.inr) e) := by
  simp only [rename_subst, subst_rename]
  congr 1
  funext v
  cases v with
  | inl => rfl
  | inr => simp [lift, Function.comp_def]
end Expr

@[simp] theorem instantiate_subst {S : Signature} {M : Metavariables}
    (ρ : X → Expr S V) (a : Assignment S M V) (f : V → Expr S W)
    (e : Expr (extend S M) X) :
    Expr.subst f (instantiate ρ a e) =
      instantiate (fun x => Expr.subst f (ρ x)) (a.subst f) e := by
  induction e generalizing V W with
  | var => rfl
  | app s es ih =>
    cases s with
    | inl s =>
      dsimp only [extend, Sum.elim] at es ih
      simp only [instantiate, Expr.subst]
      congr 1
      funext i
      rw [ih]
      congr 1
      · funext v
        cases v with
        | inl => rfl
        | inr => simp [Expr.lift, Expr.subst_rename, Expr.rename_subst, Function.comp_def]
      · funext m
        exact (Expr.rename_weaken_lift f (a m)).symm
    | inr m =>
      dsimp only [extend, Sum.elim] at es ih
      simp only [instantiate, Assignment.subst]
      dsimp only [Sum.elim]
      simp only [Expr.subst_comp]
      congr 1
      funext v
      cases v with
      | inl i =>
        simp only [Expr.lift, Expr.subst_var]
        simp only [Sum.elim_inl]
        erw [ih i]
        congr 1
        funext x
        cases x with
        | inl x => exact Fin.elim0 x
        | inr => rfl
      | inr v =>
        simp only [Expr.lift, Expr.subst_rename]
        change f v = Expr.subst Expr.var (f v)
        exact (Expr.subst_id _).symm

@[simp] theorem instantiate_rename {S : Signature} {M : Metavariables}
    (ρ : Y → Expr S V) (a : Assignment S M V) (f : X → Y)
    (e : Expr (extend S M) X) :
    instantiate ρ a (Expr.rename f e) = instantiate (ρ ∘ f) a e := by
  induction e generalizing Y V with
  | var => rfl
  | app s es ih =>
    cases s with
    | inl s =>
      dsimp only [extend, Sum.elim] at es ih
      simp only [Expr.rename, instantiate]
      congr 1
      funext i
      erw [ih i]
      congr 1
      funext x
      cases x <;> rfl
    | inr m =>
      dsimp only [extend, Sum.elim] at es ih
      simp only [Expr.rename, instantiate]
      congr 1
      funext v
      cases v with
      | inl i =>
        simp only [Sum.elim_inl]
        erw [ih i]
        congr 1
        funext x
        cases x with
        | inl x => exact Fin.elim0 x
        | inr => rfl
      | inr => rfl

@[simp] theorem instantiate_weaken {S : Signature} {M : Metavariables}
    (ρ : X → Expr S V) (a : Assignment S M V) (e : Expr (extend S M) X) :
    instantiate (Expr.lift (n := n) ρ) (a.weaken n) (Expr.rename Sum.inr e) =
      Expr.rename Sum.inr (instantiate ρ a e) := by
  rw [instantiate_rename]
  rw [← Expr.subst_vars, instantiate_subst]
  congr 1
  · funext x
    simp [Expr.lift, Expr.subst_vars]
  funext i
  simp only [Assignment.subst, Assignment.weaken]
  have h : Expr.lift (fun v : V => Expr.var (S := S) (Sum.inr (α := Fin n) v)) =
      (fun x : Fin (M.arguments i) ⊕ V => Expr.var (Sum.map id Sum.inr x)) := by
    funext x; cases x <;> rfl
  rw [h, Expr.subst_vars]

@[simp] theorem instantiate_input_subst {S : Signature} {M : Metavariables}
    (ρ : Y → Expr S V) (a : Assignment S M V) (σ : X → Expr (extend S M) Y)
    (e : Expr (extend S M) X) :
    instantiate ρ a (Expr.subst σ e) =
      instantiate (fun x => instantiate ρ a (σ x)) a e := by
  induction e generalizing Y V with
  | var => rfl
  | app s es ih =>
    cases s with
    | inl s =>
      dsimp only [extend, Sum.elim] at es ih
      simp only [Expr.subst, instantiate]
      congr 1
      funext i
      erw [ih i]
      congr 1
      funext x
      cases x with
      | inl => rfl
      | inr x => exact instantiate_weaken ρ a (σ x)
    | inr m =>
      dsimp only [extend, Sum.elim] at es ih
      simp only [Expr.subst, instantiate]
      congr 1
      funext v
      cases v with
      | inl i =>
        simp only [Sum.elim_inl]
        erw [ih i]
        congr 1
        funext x
        cases x with
        | inl x => exact Fin.elim0 x
        | inr x =>
          simp only [Expr.lift, instantiate_rename]
          congr 1
      | inr => rfl

/-- Instantiating a bound template commutes with substituting its bound argument. -/
theorem instantiate_bound {S : Signature} {M : Metavariables}
    (ρ : X → Expr S V) (a : Assignment S M V)
    (e : Expr (extend S M) (Fin n ⊕ X)) (args : Fin n → Expr (extend S M) X) :
    instantiate ρ a (Expr.subst (Sum.elim args Expr.var) e) =
      Expr.subst (Sum.elim (fun i => instantiate ρ a (args i)) Expr.var)
        (instantiate (Expr.lift ρ) (a.weaken n) e) := by
  rw [instantiate_input_subst, instantiate_subst]
  congr 1
  · funext x
    cases x with
    | inl => rfl
    | inr x =>
      simp only [Expr.lift, Expr.subst_rename]
      change ρ x = Expr.subst Expr.var (ρ x)
      exact (Expr.subst_id _).symm
  · funext i
    simp only [Assignment.subst, Assignment.weaken, Expr.subst_rename]
    have h : Expr.lift (Sum.elim (fun j => instantiate ρ a (args j)) Expr.var) ∘
        Sum.map id Sum.inr = (Expr.var (S := S) : Fin (M.arguments i) ⊕ V → _) := by
      funext x
      cases x with
      | inl => rfl
      | inr => rfl
    rw [h, Expr.subst_id]

abbrev symbolMetavariables (S : Signature) (s : S.Symbol) : Metavariables :=
  ⟨S.arity s, S.binds s⟩

/-- BHL-style symbol images: actual finite expressions over the target extended
by the source symbol's argument metavariables, with empty external scope. -/
abbrev TemplateMap (S T : Signature) :=
  (s : S.Symbol) → Expr (extend T (symbolMetavariables S s)) Empty

/-- The generic application of an argument metavariable to its bound variables. -/
def metaApplication {S : Signature} {M : Metavariables} (m : Fin M.count) :
    Expr (extend S M) (Fin (M.arguments m) ⊕ Empty) :=
  .app (.inr m) (fun i => Expr.rename Sum.inr (.var (.inl i)))

@[simp] theorem instantiate_metaApplication {S : Signature} {M : Metavariables}
    (a : Assignment S M V) (m : Fin M.count) :
    instantiate (Expr.lift (n := M.arguments m) Empty.elim)
      (a.weaken (M.arguments m)) (metaApplication m) = a m := by
  simp only [metaApplication, instantiate, instantiate_rename, Assignment.weaken]
  have h : Sum.elim (fun i => Expr.var (S := S) (Sum.inl i)) Expr.var ∘ Sum.map id Sum.inr =
      (Expr.var : Fin (M.arguments m) ⊕ V → Expr S _) := by
    funext v; cases v <;> rfl
  change Expr.subst (Sum.elim (fun i => Expr.var (Sum.inl i)) Expr.var)
    (Expr.rename (Sum.map id Sum.inr) (a m)) = _
  rw [Expr.subst_rename, h, Expr.subst_id]

namespace TemplateMap
variable {S T : Signature}

def operations (F : TemplateMap S T) : OperationMap S T where
  operation := fun s a => instantiate Empty.elim a (F s)
  natural := by
    intro V W f s a
    rw [instantiate_subst]
    congr 1
    funext v
    exact v.elim

def toSyntax (F : TemplateMap S T) : SyntaxMap S T := .ofOperations (operations F)

/-- The action follows by recursion; its substitution law is derived from
explicit template instantiation, with no client theorem supplied as a field. -/
theorem substitution (F : TemplateMap S T) (f : V → Expr S W) (e : Expr S V) :
    (toSyntax F).act (Expr.subst f e) =
      Expr.subst (fun v => (toSyntax F).act (f v)) ((toSyntax F).act e) := (toSyntax F).substitution f e
def identity (S : Signature) : TemplateMap S S :=
  fun s => .app (.inl s) (fun i => metaApplication (M := symbolMetavariables S s) i)

@[simp] theorem identity_operation (s : S.Symbol)
    (a : Assignment S (symbolMetavariables S s) V) :
    (operations (identity S)).operation s a = Expr.app s a := by
  change Expr.app s (fun i => instantiate (Expr.lift Empty.elim)
    (a.weaken (S.binds s i)) (metaApplication (M := symbolMetavariables S s) i)) = Expr.app s a
  congr 1
  funext i
  exact instantiate_metaApplication a i

@[simp] theorem identity_act (e : Expr S V) : (toSyntax (identity S)).act e = e := by
  induction e with
  | var => rfl
  | app s es ih =>
    change (operations (identity S)).operation s
      (fun i => (toSyntax (identity S)).act (es i)) = Expr.app s es
    rw [identity_operation]
    congr 1
    funext i
    exact ih i
end TemplateMap

end SquareKit.DependentTheoryMaps
