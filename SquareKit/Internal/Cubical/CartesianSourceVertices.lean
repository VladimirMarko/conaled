import SquareKit.Internal.Cubical.DimensionModels
import SquareKit.Internal.Cubical.CubeProducts

/-! Boolean vertices of De Morgan cubes, without identifying dimension expressions
with their Boolean observations. -/
set_option autoImplicit false
set_option warningAsError true
namespace SquareKit.Cubical
open CategoryTheory

namespace SourceVertexExpr
variable {α β : Type}

def eval (v : α → Bool) : Expr α → Bool
  | .zero => false
  | .one => true
  | .var i => v i
  | .neg a => !(eval v a)
  | .meet a b => eval v a && eval v b
  | .join a b => eval v a || eval v b

theorem four_diagonal (v : α → Bool) (a : Expr α) :
    Four.eval (fun i => (v i, v i)) a = (eval v a, eval v a) := by
  induction a <;> simp_all [Four.eval, Four.neg, Four.meet, Four.join, eval]

theorem sound (v : α → Bool) {a b : Expr α} (h : Expr.Conv a b) :
    eval v a = eval v b := by
  have hh := Four.sound (fun i => (v i, v i)) h
  simpa only [four_diagonal] using congrArg Prod.fst hh

@[simp] theorem eval_subst (v : β → Bool) (f : α → Expr β) (a : Expr α) :
    eval v (a.subst f) = eval (fun i => eval v (f i)) a := by
  induction a <;> simp_all [Expr.subst, eval]

def endpoint (b : Bool) : Expr α := if b then .one else .zero

@[simp] theorem eval_endpoint (v : α → Bool) (b : Bool) : eval v (endpoint b) = b := by
  cases b <;> rfl

def line (v w : Bool) (t : Expr α) : Expr α :=
  if v then (if w then .one else .neg t) else (if w then t else .zero)

@[simp] theorem line_zero (v w : Bool) :
    Expr.Conv (line v w (.zero : Expr α)) (endpoint v) := by
  cases v <;> cases w <;> first | exact .refl _ | exact .neg_zero

@[simp] theorem line_one (v w : Bool) :
    Expr.Conv (line v w (.one : Expr α)) (endpoint w) := by
  cases v <;> cases w <;> first | exact .refl _ | exact .neg_one

@[simp] theorem subst_line (f : α → Expr β) (v w : Bool) (t : Expr α) :
    (line v w t).subst f = line v w (t.subst f) := by
  cases v <;> cases w <;> rfl

theorem subst_endpoints (v : α → Bool) (a : Expr α) :
    Expr.Conv (a.subst (fun i => (endpoint (v i) : Expr β))) (endpoint (eval v a)) := by
  induction a with
  | zero => exact .refl _
  | one => exact .refl _
  | var i => exact .refl _
  | neg a ih =>
    apply Expr.Conv.trans (.neg ih)
    simp only [eval]
    cases eval v a <;> first | exact .neg_zero | exact .neg_one
  | meet a b ia ib =>
    apply Expr.Conv.trans (.meet ia ib)
    simp only [eval]
    cases eval v a <;> cases eval v b <;>
      first | exact .meet_zero _ | exact .meet_one _
  | join a b ia ib =>
    apply Expr.Conv.trans (.join ia ib)
    simp only [eval]
    cases eval v a <;> cases eval v b <;>
      first | exact .join_zero _ | exact .join_one _

/-- Relative interpolation valid in every De Morgan algebra. -/
def conditional (s p q : Expr α) : Expr α :=
  .meet (.meet (.join s p) (.join (.neg s) q)) (.join p q)

theorem conditional_zero (p q : Expr α) : Expr.Conv (conditional .zero p q) p := by
  apply Expr.Conv.trans (Expr.Conv.meet (Expr.Conv.meet
    ((Expr.Conv.join_comm _ _).trans (.join_zero _))
    ((Expr.Conv.join .neg_zero (.refl _)).trans
      ((Expr.Conv.join_comm _ _).trans (.join_one _)))) (.refl _))
  exact (Expr.Conv.meet (.meet_one _) (.refl _)).trans (.absorb_meet _ _)

theorem conditional_one (p q : Expr α) : Expr.Conv (conditional .one p q) q := by
  apply Expr.Conv.trans (Expr.Conv.meet (Expr.Conv.meet
    ((Expr.Conv.join_comm _ _).trans (.join_one _))
    ((Expr.Conv.join .neg_one (.refl _)).trans
      ((Expr.Conv.join_comm _ _).trans (.join_zero _)))) (.refl _))
  apply Expr.Conv.trans (Expr.Conv.meet
    ((Expr.Conv.meet_comm _ _).trans (.meet_one _)) (.join_comm _ _))
  exact .absorb_meet _ _

theorem conditional_same (s p : Expr α) : Expr.Conv (conditional s p p) p := by
  apply Expr.Conv.trans (Expr.Conv.meet (.refl _) (.join_idem _))
  apply Expr.Conv.trans (Expr.Conv.meet_comm _ _)
  apply Expr.Conv.trans (Expr.Conv.meet_assoc _ _ _).symm
  apply Expr.Conv.trans (Expr.Conv.meet
    ((Expr.Conv.meet (.refl _) (.join_comm _ _)).trans (.absorb_meet _ _))
    (.join_comm _ _))
  exact .absorb_meet _ _

theorem conditional_endpoints (s : Expr α) (v w : Bool) :
    Expr.Conv (conditional s (endpoint v) (endpoint w)) (line v w s) := by
  cases v <;> cases w
  · exact (Expr.Conv.meet (.refl _) (.join_zero _)).trans (.meet_zero _)
  · exact (Expr.Conv.meet (Expr.Conv.meet (.join_zero _) (.join_one _))
      (.join_one _)).trans ((Expr.Conv.meet (.meet_one _) (.refl _)).trans (.meet_one _))
  · exact (Expr.Conv.meet (Expr.Conv.meet (.join_one _) (.join_zero _))
      (.join_zero _)).trans ((Expr.Conv.meet
        ((Expr.Conv.meet_comm _ _).trans (.meet_one _)) (.refl _)).trans (.meet_one _))
  · exact (Expr.Conv.meet (Expr.Conv.meet (.join_one _) (.join_one _))
      (.join_one _)).trans ((Expr.Conv.meet (.meet_one _) (.refl _)).trans (.meet_one _))

theorem conditional_congr {s s' p p' q q' : Expr α}
    (hs : Expr.Conv s s') (hp : Expr.Conv p p') (hq : Expr.Conv q q') :
    Expr.Conv (conditional s p q) (conditional s' p' q') :=
  .meet (.meet (.join hs hp) (.join (.neg hs) hq)) (.join hp hq)

@[simp] theorem subst_conditional (f : α → Expr β) (s p q : Expr α) :
    (conditional s p q).subst f = conditional (s.subst f) (p.subst f) (q.subst f) := rfl

/-- A common boundary of the two paths stays fixed during interpolation. -/
theorem conditional_relative (f : α → Expr β) (s p q : Expr α) (a : Expr β)
    (hp : Expr.Conv (p.subst f) a) (hq : Expr.Conv (q.subst f) a) :
    Expr.Conv ((conditional s p q).subst f) a :=
  (conditional_congr (.refl _) hp hq).trans (conditional_same _ _)

end SourceVertexExpr

namespace Cartesian

def dmVertices {I J : SquareKit.Cubical.Cube} (f : I ⟶ J)
    (v : Fin I.dimension → Bool) : Fin J.dimension → Bool :=
  Quotient.liftOn f (fun f i => SourceVertexExpr.eval v (f i))
    (fun _ _ h => funext (fun i => SourceVertexExpr.sound v (h i)))

@[simp] theorem dmVertices_ofRaw {I J : SquareKit.Cubical.Cube}
    (f : SquareKit.Cubical.Cube.Raw I J) (v : Fin I.dimension → Bool) (i : Fin J.dimension) :
    dmVertices (SquareKit.Cubical.Cube.ofRaw f) v i = SourceVertexExpr.eval v (f i) := rfl

@[simp] theorem dmVertices_id (I : SquareKit.Cubical.Cube) (v : Fin I.dimension → Bool) :
    dmVertices (𝟙 I) v = v := rfl

@[simp] theorem dmVertices_comp {I J K : SquareKit.Cubical.Cube} (f : I ⟶ J) (g : J ⟶ K)
    (v : Fin I.dimension → Bool) : dmVertices (f ≫ g) v = dmVertices g (dmVertices f v) := by
  refine Quotient.inductionOn₂ f g ?_
  intro f g
  funext i
  exact SourceVertexExpr.eval_subst v f (g i)

@[simp] theorem dmVertices_drop (I : SquareKit.Cubical.Cube)
    (v : Fin (I.dimension + 1) → Bool) :
    dmVertices (SquareKit.Cubical.Cube.drop I) v = fun i => v i.succ := rfl

@[simp] theorem dmVertices_fresh (I : SquareKit.Cubical.Cube)
    (v : Fin (I.dimension + 1) → Bool) :
    dmVertices (SquareKit.Cubical.Cube.fresh I) v = fun _ => v 0 := rfl

@[simp] theorem dmVertices_pair {I J : SquareKit.Cubical.Cube}
    (f : I ⟶ J) (r : I ⟶ (⟨1⟩ : SquareKit.Cubical.Cube))
    (v : Fin I.dimension → Bool) :
    dmVertices (SquareKit.Cubical.Cube.pair f r) v =
      Fin.cases (dmVertices r v 0) (dmVertices f v) := by
  refine Quotient.inductionOn₂ f r ?_
  intro f r
  funext i
  cases i using Fin.cases <;> rfl

def dmVertex {I : SquareKit.Cubical.Cube} (v : Fin I.dimension → Bool) :
    (⟨0⟩ : SquareKit.Cubical.Cube) ⟶ I :=
  SquareKit.Cubical.Cube.ofRaw (fun i => SourceVertexExpr.endpoint (v i))

theorem dmVertex_comp {I J : SquareKit.Cubical.Cube}
    (v : Fin I.dimension → Bool) (f : I ⟶ J) :
    dmVertex v ≫ f = dmVertex (dmVertices f v) := by
  refine Quotient.inductionOn f ?_
  intro f
  apply Quotient.sound
  intro i
  exact SourceVertexExpr.subst_endpoints v (f i)

def dmCanonicalPath {I : SquareKit.Cubical.Cube} (v w : Fin I.dimension → Bool) :
    (⟨1⟩ : SquareKit.Cubical.Cube) ⟶ I :=
  SquareKit.Cubical.Cube.ofRaw (fun i => SourceVertexExpr.line (v i) (w i) (.var 0))

theorem dmCanonicalPath_zero {I : SquareKit.Cubical.Cube} (v w : Fin I.dimension → Bool) :
    dmVertex (I := ⟨1⟩) (fun _ => false) ≫ dmCanonicalPath v w = dmVertex v := by
  apply Quotient.sound
  intro i
  simpa only [SourceVertexExpr.subst_line, Expr.subst, SourceVertexExpr.endpoint, Bool.false_eq_true, ite_false, ite_true] using SourceVertexExpr.line_zero (v i) (w i)

theorem dmCanonicalPath_one {I : SquareKit.Cubical.Cube} (v w : Fin I.dimension → Bool) :
    dmVertex (I := ⟨1⟩) (fun _ => true) ≫ dmCanonicalPath v w = dmVertex w := by
  apply Quotient.sound
  intro i
  simpa only [SourceVertexExpr.subst_line, Expr.subst, SourceVertexExpr.endpoint, Bool.false_eq_true, ite_false, ite_true] using SourceVertexExpr.line_one (v i) (w i)

/-- Interpolate two raw paths, with the interpolation coordinate first. -/
def dmPathSquare {I : SquareKit.Cubical.Cube}
    (p q : SquareKit.Cubical.Cube.Raw ⟨1⟩ I) :
    (⟨2⟩ : SquareKit.Cubical.Cube) ⟶ I :=
  SquareKit.Cubical.Cube.ofRaw (fun i => SourceVertexExpr.conditional (.var 0)
    ((p i).subst (fun _ => .var 1)) ((q i).subst (fun _ => .var 1)))

/-- Fix the interpolation coordinate and retain the path coordinate. -/
def dmSquareHorizontal (b : Bool) :
    (⟨1⟩ : SquareKit.Cubical.Cube) ⟶ (⟨2⟩ : SquareKit.Cubical.Cube) :=
  SquareKit.Cubical.Cube.ofRaw (Fin.cases (SourceVertexExpr.endpoint b) (fun _ => .var 0))

/-- Fix the path coordinate and retain the interpolation coordinate. -/
def dmSquareVertical (b : Bool) :
    (⟨1⟩ : SquareKit.Cubical.Cube) ⟶ (⟨2⟩ : SquareKit.Cubical.Cube) :=
  SquareKit.Cubical.Cube.ofRaw (Fin.cases (.var 0) (fun _ => SourceVertexExpr.endpoint b))

private theorem subst_single_var (a : Expr (Fin 1)) :
    a.subst (fun _ => .var 0) = a := by
  have h : (fun _ : Fin 1 => (Expr.var 0 : Expr (Fin 1))) = Expr.var := by
    funext i
    rw [Fin.eq_zero i]
  rw [h, Expr.subst_var]

theorem dmPathSquare_zero {I : SquareKit.Cubical.Cube}
    (p q : SquareKit.Cubical.Cube.Raw ⟨1⟩ I) :
    dmSquareHorizontal false ≫ dmPathSquare p q = SquareKit.Cubical.Cube.ofRaw p := by
  apply Quotient.sound
  intro i
  simp only [SourceVertexExpr.subst_conditional, Expr.subst_subst]
  change Expr.Conv (SourceVertexExpr.conditional .zero
    ((p i).subst (fun _ => .var 0)) ((q i).subst (fun _ => .var 0))) (p i)
  rw [subst_single_var, subst_single_var]
  exact SourceVertexExpr.conditional_zero _ _

theorem dmPathSquare_one {I : SquareKit.Cubical.Cube}
    (p q : SquareKit.Cubical.Cube.Raw ⟨1⟩ I) :
    dmSquareHorizontal true ≫ dmPathSquare p q = SquareKit.Cubical.Cube.ofRaw q := by
  apply Quotient.sound
  intro i
  simp only [SourceVertexExpr.subst_conditional, Expr.subst_subst]
  change Expr.Conv (SourceVertexExpr.conditional .one
    ((p i).subst (fun _ => .var 0)) ((q i).subst (fun _ => .var 0))) (q i)
  rw [subst_single_var, subst_single_var]
  exact SourceVertexExpr.conditional_one _ _

theorem dmPathSquare_relative {I : SquareKit.Cubical.Cube}
    (p q : SquareKit.Cubical.Cube.Raw ⟨1⟩ I) (b : Bool) (v : Fin I.dimension → Bool)
    (hp : ∀ i, Expr.Conv ((p i).subst (fun _ => SourceVertexExpr.endpoint b))
      (SourceVertexExpr.endpoint (v i) : Expr (Fin 1)))
    (hq : ∀ i, Expr.Conv ((q i).subst (fun _ => SourceVertexExpr.endpoint b))
      (SourceVertexExpr.endpoint (v i) : Expr (Fin 1))) :
    dmSquareVertical b ≫ dmPathSquare p q =
      SquareKit.Cubical.Cube.ofRaw (fun i => SourceVertexExpr.endpoint (v i)) := by
  apply Quotient.sound
  intro i
  simp only [SourceVertexExpr.subst_conditional, Expr.subst_subst, Expr.subst,
    Fin.cases_zero]
  exact (SourceVertexExpr.conditional_congr (.refl _) (hp i) (hq i)).trans
    (SourceVertexExpr.conditional_same _ _)

theorem dmPathSquare_vertical {I : SquareKit.Cubical.Cube}
    (p q : SquareKit.Cubical.Cube.Raw ⟨1⟩ I) (b : Bool) :
    dmSquareVertical b ≫ dmPathSquare p q = dmCanonicalPath
      (fun i => SourceVertexExpr.eval (fun _ => b) (p i))
      (fun i => SourceVertexExpr.eval (fun _ => b) (q i)) := by
  apply Quotient.sound
  intro i
  simp only [SourceVertexExpr.subst_conditional, Expr.subst_subst, Expr.subst,
    Fin.cases_zero]
  exact (SourceVertexExpr.conditional_congr (.refl _)
    (SourceVertexExpr.subst_endpoints _ _) (SourceVertexExpr.subst_endpoints _ _)).trans
    (SourceVertexExpr.conditional_endpoints _ _ _)

theorem dmPathSquare_relative_vertices {I : SquareKit.Cubical.Cube}
    (p q : SquareKit.Cubical.Cube.Raw ⟨1⟩ I) (b : Bool)
    (h : ∀ i, SourceVertexExpr.eval (fun _ => b) (p i) =
      SourceVertexExpr.eval (fun _ => b) (q i)) :
    dmSquareVertical b ≫ dmPathSquare p q = SquareKit.Cubical.Cube.ofRaw
      (fun i => SourceVertexExpr.endpoint (SourceVertexExpr.eval (fun _ => b) (p i))) := by
  apply dmPathSquare_relative p q b _
  · intro i
    exact SourceVertexExpr.subst_endpoints _ _
  · intro i
    rw [h i]
    exact SourceVertexExpr.subst_endpoints _ _

/-- The non-Boolean excluded-middle path can be deformed to one relative to
its two endpoints, without equating the original dimension expressions. -/
theorem dmExcludedMiddleSquare_boundary (b : Bool) :
    dmSquareVertical b ≫ dmPathSquare
      (I := ⟨1⟩) (fun _ => .join (.var 0) (.neg (.var 0))) (fun _ => .one) =
      SquareKit.Cubical.Cube.ofRaw (fun _ => .one) := by
  have h : ∀ i : Fin 1,
      SourceVertexExpr.eval (fun _ => b)
        ((fun _ : Fin 1 => Expr.join (.var 0) (.neg (.var 0))) i) =
      SourceVertexExpr.eval (fun _ : Fin 1 => b) ((fun _ : Fin 1 => Expr.one) i) := by
    intro i
    cases b <;> rfl
  have hh := dmPathSquare_relative_vertices
    (I := ⟨1⟩) (fun _ => .join (.var 0) (.neg (.var 0))) (fun _ => .one) b h
  cases b <;> simpa only [SourceVertexExpr.eval, SourceVertexExpr.endpoint,
    Bool.not_false, Bool.not_true, Bool.false_or, Bool.true_or, ite_true] using hh

theorem dmExcludedMiddle_ne_one :
    SquareKit.Cubical.Cube.ofRaw (a := ⟨1⟩) (b := ⟨1⟩)
      (fun _ => .join (.var 0) (.neg (.var 0))) ≠
    SquareKit.Cubical.Cube.ofRaw (fun _ => .one) := by
  intro h
  have bad := Four.sound (fun _ => (false, true)) (Quotient.exact h 0)
  cases bad

@[simp] theorem dmVertices_reversal (v : Fin 1 → Bool) :
    dmVertices SquareKit.Cubical.Cube.reversal v 0 = !(v 0) := rfl

end Cartesian
end SquareKit.Cubical
