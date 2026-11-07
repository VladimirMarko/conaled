import SquareKit.DependentTheoryTemplates
import SquareKit.DependentPairPresentations

/-! The projection-to-eliminator map as explicit, closed BHL-style templates. -/
namespace SquareKit.DependentPairPresentations
open DependentTheoryMaps
namespace Templates
abbrev Raw (M : Metavariables) := Expr (extend eliminationSignature M)
variable {M : Metavariables} {X V : Type}

def generic (m : Fin M.count) : Raw M (Fin (M.arguments m) ⊕ Empty) :=
  .app (.inr m) (fun i => zero (.var (.inl i)))

def S (A : Raw M X) (B : Raw M (Fin 1 ⊕ X)) : Raw M X :=
  .app (.inl .S) (Fin.cases (zero A) (Fin.cases B (fun i => nomatch i)))

def pack (A : Raw M X) (B : Raw M (Fin 1 ⊕ X)) (a b : Raw M X) : Raw M X :=
  .app (.inl .pack) (Fin.cases (zero A) (Fin.cases B
    (Fin.cases (zero a) (Fin.cases (zero b) (fun i => nomatch i)))))

def split (A : Raw M X) (B D : Raw M (Fin 1 ⊕ X)) (e : Raw M (Fin 2 ⊕ X))
    (p : Raw M X) : Raw M X :=
  .app (.inl .split) (Fin.cases (zero A) (Fin.cases B (Fin.cases D
    (Fin.cases e (Fin.cases (zero p) (fun i => nomatch i))))))

def first (A : Raw M X) (B : Raw M (Fin 1 ⊕ X)) (p : Raw M X) : Raw M X :=
  split A B (Expr.rename Sum.inr A) (.var (.inl 0)) p

def second (A : Raw M X) (B : Raw M (Fin 1 ⊕ X)) (p : Raw M X) : Raw M X :=
  split A B
    (Elimination.instantiate (Expr.rename (Sum.map id Sum.inr) B)
      (first (Expr.rename Sum.inr A) (Expr.rename (Sum.map id Sum.inr) B) (.var (.inl 0))))
    (.var (.inl 1)) p

@[simp] theorem eval_zero (ρ : X → EExpr V) (a : Assignment eliminationSignature M V)
    (e : Raw M X) :
    instantiate (Expr.lift (n := 0) ρ) (a.weaken 0) (zero e) =
      zero (instantiate ρ a e) := instantiate_weaken ρ a e

@[simp] theorem eval_S (ρ : X → EExpr V) (a : Assignment eliminationSignature M V)
    (A : Raw M X) (B : Raw M (Fin 1 ⊕ X)) :
    instantiate ρ a (S A B) =
      Elimination.S (instantiate ρ a A) (instantiate (Expr.lift ρ) (a.weaken 1) B) := by
  simp only [S, instantiate, Elimination.S]
  congr 1
  funext i
  change Fin 2 at i
  fin_cases i <;> first | exact eval_zero ρ a _ | rfl

@[simp] theorem eval_pack (ρ : X → EExpr V) (a : Assignment eliminationSignature M V)
    (A : Raw M X) (B : Raw M (Fin 1 ⊕ X)) (x y : Raw M X) :
    instantiate ρ a (pack A B x y) =
      Elimination.pack (instantiate ρ a A) (instantiate (Expr.lift ρ) (a.weaken 1) B)
        (instantiate ρ a x) (instantiate ρ a y) := by
  simp only [pack, instantiate, Elimination.pack]
  congr 1
  funext i
  change Fin 4 at i
  fin_cases i <;> first | exact eval_zero ρ a _ | rfl

@[simp] theorem eval_split (ρ : X → EExpr V) (a : Assignment eliminationSignature M V)
    (A : Raw M X) (B D : Raw M (Fin 1 ⊕ X)) (e : Raw M (Fin 2 ⊕ X)) (p : Raw M X) :
    instantiate ρ a (split A B D e p) =
      Elimination.split (instantiate ρ a A) (instantiate (Expr.lift ρ) (a.weaken 1) B)
        (instantiate (Expr.lift ρ) (a.weaken 1) D)
        (instantiate (Expr.lift ρ) (a.weaken 2) e) (instantiate ρ a p) := by
  simp only [split, instantiate, Elimination.split]
  congr 1
  funext i
  change Fin 5 at i
  fin_cases i <;> first | exact eval_zero ρ a _ | rfl

@[simp] theorem eval_first (ρ : X → EExpr V) (a : Assignment eliminationSignature M V)
    (A : Raw M X) (B : Raw M (Fin 1 ⊕ X)) (p : Raw M X) :
    instantiate ρ a (first A B p) =
      Elimination.first (instantiate ρ a A) (instantiate (Expr.lift ρ) (a.weaken 1) B)
        (instantiate ρ a p) := by
  simp only [first, eval_split, instantiate_weaken, instantiate, Expr.lift, Elimination.first]

theorem eval_shift (ρ : X → EExpr V) (a : Assignment eliminationSignature M V)
    (B : Raw M (Fin 1 ⊕ X)) :
    instantiate (Expr.lift (Expr.lift (n := 1) ρ)) ((a.weaken 1).weaken 1)
      (Expr.rename (Sum.map id Sum.inr) B) =
      Expr.rename (Sum.map id Sum.inr) (instantiate (Expr.lift ρ) (a.weaken 1) B) := by
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

@[simp] theorem eval_second (ρ : X → EExpr V) (a : Assignment eliminationSignature M V)
    (A : Raw M X) (B : Raw M (Fin 1 ⊕ X)) (p : Raw M X) :
    instantiate ρ a (second A B p) =
      Elimination.second (instantiate ρ a A) (instantiate (Expr.lift ρ) (a.weaken 1) B)
        (instantiate ρ a p) := by
  simp only [second, eval_split, Elimination.instantiate, instantiate_bound,
    eval_first, instantiate_weaken, eval_shift, instantiate, Expr.lift, Elimination.second]

theorem eval_generic (m : Fin M.count)
    (ρ : Fin (M.arguments m) ⊕ Empty → EExpr V) (a : Assignment eliminationSignature M V) :
    instantiate ρ a (generic m) =
      Expr.subst (Sum.elim (fun i => ρ (.inl i)) Expr.var) (a m) := by
  simp only [generic, instantiate, zero, instantiate_rename]
  rfl

@[simp] theorem eval_generic_bound (a : Assignment eliminationSignature M V) (m : Fin M.count) :
    instantiate (Expr.lift (n := M.arguments m) Empty.elim)
      (a.weaken (M.arguments m)) (generic m) = a m := by
  rw [eval_generic]
  simp only [Assignment.weaken, Expr.subst_rename]
  have h : Sum.elim (fun i => Expr.lift (n := M.arguments m)
      (S := eliminationSignature) (W := V) Empty.elim (.inl i)) Expr.var ∘ Sum.map id Sum.inr =
      (Expr.var : Fin (M.arguments m) ⊕ V → EExpr _) := by
    funext v; cases v <;> rfl
  rw [h, Expr.subst_id]

@[simp] theorem eval_generic_free (a : Assignment eliminationSignature M V) (m : Fin M.count)
    (hm : M.arguments m = 0) :
    instantiate Empty.elim a (Expr.rename (Sum.elim (fun i => (hm ▸ i).elim0) id) (generic m)) =
      Expr.rename (Sum.elim (fun i => (hm ▸ i).elim0) id) (a m) := by
  rw [instantiate_rename, eval_generic, ← Expr.subst_vars]
  congr 1
  funext v
  cases v with
  | inl i => exact (hm ▸ i).elim0
  | inr => rfl

/-- No free ambient variables occur in these symbol images. Metavariables
stand only for the symbol's declared arguments, including their binders. -/
def Gtemplate : TemplateMap projectionSignature eliminationSignature
  | .P => S (unzero (generic 0)) (generic 1)
  | .pair => pack (unzero (generic 0)) (generic 1) (unzero (generic 2)) (unzero (generic 3))
  | .fst => first (unzero (generic 0)) (generic 1) (unzero (generic 2))
  | .snd => second (unzero (generic 0)) (generic 1) (unzero (generic 2))
  | .declaration decl => .app (.inl (.declaration decl)) (fun i => generic (M := symbolMetavariables projectionSignature (.declaration decl)) i)

theorem Gtemplate_operation (s : ProjectionSymbol)
    (a : Assignment eliminationSignature (symbolMetavariables projectionSignature s) V) :
    (TemplateMap.operations Gtemplate).operation s a = Goperation s a := by
  change instantiate Empty.elim a (Gtemplate s) = _
  cases s with
  | P =>
    simp only [Gtemplate, Goperation, eval_S]
    congr 1
    · exact eval_generic_free a 0 rfl
    · exact eval_generic_bound a 1
  | pair =>
    simp only [Gtemplate, Goperation, eval_pack]
    congr 1
    · exact eval_generic_free a 0 rfl
    · exact eval_generic_bound a 1
    · exact eval_generic_free a 2 rfl
    · exact eval_generic_free a 3 rfl
  | fst =>
    simp only [Gtemplate, Goperation, eval_first]
    congr 1
    · exact eval_generic_free a 0 rfl
    · exact eval_generic_bound a 1
    · exact eval_generic_free a 2 rfl
  | snd =>
    simp only [Gtemplate, Goperation, eval_second]
    congr 1
    · exact eval_generic_free a 0 rfl
    · exact eval_generic_bound a 1
    · exact eval_generic_free a 2 rfl
  | declaration decl =>
    simp only [Gtemplate, Goperation, instantiate]
    congr 1
    funext i
    exact eval_generic_bound a i

theorem Gtemplate_act (e : PExpr V) : (TemplateMap.toSyntax Gtemplate).act e = G.act e := by
  induction e with
  | var => rfl
  | app s es ih =>
    change (TemplateMap.operations Gtemplate).operation s
      (fun i => (TemplateMap.toSyntax Gtemplate).act (es i)) =
      Goperation s (fun i => G.act (es i))
    rw [Gtemplate_operation]
    congr 1
    funext i
    exact ih i

end Templates
end SquareKit.DependentPairPresentations
