import Applications.AD.Compiler
import SquareKit.Relations

/-!
# Generalized AD calculated from derivative-representation squares

Unlike constructing a `DMap` and converting its derivative afterwards,
`Program` stores only a primal/represented-derivative computation. Its actual
Fréchet derivative is existentially quantified in `Prop`. The representation
interface has local relational squares for linear operations. Both supplied
instances discharge those squares: direct continuous linear maps, and reversed
continuous-linear continuations. Thus the same existing source compiler
constructs either mode directly, while the analytic witness is erased.
-/

noncomputable section

namespace Applications.AD.Generalized

open Applications.AD.FirstOrder

abbrev Ty := FirstOrderCompiler.Ty
abbrev Obj (a : Ty) := FirstOrderCompiler.Val ℝ a
abbrev LMap (a b : Ty) := Obj a →L[ℝ] Obj b

structure LinearModel where
  Code : Ty → Ty → Type
  Rel : {a b : Ty} → Code a b → LMap a b → Prop
  ident : {a : Ty} → Code a a
  comp : {a b c : Ty} → Code b c → Code a b → Code a c
  fst : {a b : Ty} → Code (.prod a b) a
  snd : {a b : Ty} → Code (.prod a b) b
  pair : {a b c : Ty} → Code a b → Code a c → Code a (.prod b c)
  zero : {a b : Ty} → Code a b
  add : {a b : Ty} → Code a b → Code a b → Code a b
  scale : {a b : Ty} → ℝ → Code a b → Code a b
  ident_rel : ∀ {a}, Rel (ident (a := a)) (ContinuousLinearMap.id ℝ (Obj a))
  comp_rel : ∀ {a b c} {g : Code b c} {f : Code a b} {G : LMap b c} {F : LMap a b},
    Rel g G → Rel f F → Rel (comp g f) (G.comp F)
  fst_rel : ∀ {a b}, Rel (fst (a := a) (b := b)) (ContinuousLinearMap.fst ℝ (Obj a) (Obj b))
  snd_rel : ∀ {a b}, Rel (snd (a := a) (b := b)) (ContinuousLinearMap.snd ℝ (Obj a) (Obj b))
  pair_rel : ∀ {a b c} {f : Code a b} {g : Code a c} {F : LMap a b} {G : LMap a c},
    Rel f F → Rel g G → Rel (pair f g) (F.prod G)
  zero_rel : ∀ {a b}, Rel (zero (a := a) (b := b)) 0
  add_rel : ∀ {a b} {f g : Code a b} {F G : LMap a b},
    Rel f F → Rel g G → Rel (add f g) (F + G)
  scale_rel : ∀ {a b} (s : ℝ) {f : Code a b} {F : LMap a b},
    Rel f F → Rel (scale s f) (s • F)

def LinearModel.homRep (K : LinearModel) (a b : Ty) : Relational.RelRep :=
  ⟨K.Code a b, LMap a b, K.Rel⟩

def LinearModel.compositionSquare (K : LinearModel) (a b c : Ty) :
    Relational.RelSquare
      (Relational.product (K.homRep b c) (K.homRep a b)) (K.homRep a c) where
  impl p := K.comp p.1 p.2
  spec p := p.1.comp p.2
  preserves h := K.comp_rel h.1 h.2

def LinearModel.pairSquare (K : LinearModel) (a b c : Ty) :
    Relational.RelSquare
      (Relational.product (K.homRep a b) (K.homRep a c)) (K.homRep a (.prod b c)) where
  impl p := K.pair p.1 p.2
  spec p := p.1.prod p.2
  preserves h := K.pair_rel h.1 h.2

/-- The derivative witness lives only in `Prop`; it is absent from runtime data. -/
structure Program (K : LinearModel) (a b : Ty) where
  run : Obj a → Obj b × K.Code a b
  correct : ∀ x, ∃ L : LMap a b,
    HasFDerivAt (fun y => (run y).1) L x ∧ K.Rel (run x).2 L

namespace Program

variable {K : LinearModel} {a b c d : Ty}

def ident : Program K a a where
  run x := (x, K.ident)
  correct x := ⟨_, hasFDerivAt_id x, K.ident_rel⟩

def comp (g : Program K b c) (f : Program K a b) : Program K a c where
  run x :=
    let r := f.run x
    let s := g.run r.1
    (s.1, K.comp s.2 r.2)
  correct x := by
    obtain ⟨F, hF, rF⟩ := f.correct x
    obtain ⟨G, hG, rG⟩ := g.correct (f.run x).1
    have hcomp := hG.comp x hF
    exact ⟨G.comp F, hcomp, K.comp_rel rG rF⟩

def constant (y : Obj b) : Program K a b where
  run _ := (y, K.zero)
  correct x := ⟨0, hasFDerivAt_const y x, K.zero_rel⟩

def fst : Program K (.prod a b) a where
  run p := (p.1, K.fst)
  correct _ := ⟨_, hasFDerivAt_fst, K.fst_rel⟩

def snd : Program K (.prod a b) b where
  run p := (p.2, K.snd)
  correct _ := ⟨_, hasFDerivAt_snd, K.snd_rel⟩

def pair (f : Program K a b) (g : Program K a c) : Program K a (.prod b c) where
  run x :=
    let (y, df) := f.run x
    let (z, dg) := g.run x
    ((y, z), K.pair df dg)
  correct x := by
    obtain ⟨F, hF, rF⟩ := f.correct x
    obtain ⟨G, hG, rG⟩ := g.correct x
    exact ⟨F.prod G, hF.prodMk hG, K.pair_rel rF rG⟩

def add : Program K (.prod .base .base) .base where
  run p := (p.1 + p.2, K.add K.fst K.snd)
  correct p := ⟨_, (hasFDerivAt_fst (p := p)).add hasFDerivAt_snd,
    K.add_rel K.fst_rel K.snd_rel⟩

def mul : Program K (.prod .base .base) .base where
  run p := (p.1 * p.2, K.add (K.scale p.1 K.snd) (K.scale p.2 K.fst))
  correct p := ⟨_, (hasFDerivAt_fst (p := p)).mul hasFDerivAt_snd,
    K.add_rel (K.scale_rel p.1 K.snd_rel) (K.scale_rel p.2 K.fst_rel)⟩

end Program

@[reducible] def direct : LinearModel where
  Code := LMap
  Rel c L := c = L
  ident := ContinuousLinearMap.id ℝ _
  comp := ContinuousLinearMap.comp
  fst := ContinuousLinearMap.fst ℝ _ _
  snd := ContinuousLinearMap.snd ℝ _ _
  pair := ContinuousLinearMap.prod
  zero := 0
  add f g := f + g
  scale s f := s • f
  ident_rel := rfl
  comp_rel hf hg := by cases hf; cases hg; rfl
  fst_rel := rfl
  snd_rel := rfl
  pair_rel hf hg := by cases hf; cases hg; rfl
  zero_rel := rfl
  add_rel hf hg := by cases hf; cases hg; rfl
  scale_rel := by
    intro a b s f F hf
    cases hf
    rfl

/-- The reverse-mode representation constructs only pullback code. -/
@[reducible] def continuations : LinearModel where
  Code a b := Continuation (Obj a) (Obj b) ℝ
  Rel c L := ∀ k, c k = k.comp L
  ident := ContinuousLinearMap.id ℝ _
  comp g f := f.comp g
  fst := continuation (ContinuousLinearMap.fst ℝ _ _)
  snd := continuation (ContinuousLinearMap.snd ℝ _ _)
  pair f g :=
    f.comp (continuation (ContinuousLinearMap.inl ℝ _ _)) +
    g.comp (continuation (ContinuousLinearMap.inr ℝ _ _))
  zero := 0
  add f g := f + g
  scale s f := s • f
  ident_rel := by intro a k; rfl
  comp_rel := by
    intro a b c g f G F hg hf k
    change f (g k) = k.comp (G.comp F)
    rw [hg, hf]
    rfl
  fst_rel := by intros; rfl
  snd_rel := by intros; rfl
  pair_rel := by
    intro a b c f g F G hf hg k
    ext x
    change f (k.comp (ContinuousLinearMap.inl ℝ _ _)) x +
      g (k.comp (ContinuousLinearMap.inr ℝ _ _)) x = k (F x, G x)
    rw [hf, hg]
    change k (F x, 0) + k (0, G x) = k (F x, G x)
    rw [← k.map_add]
    simp
  zero_rel := by intro a b k; ext x; simp
  add_rel := by
    intro a b f g F G hf hg k
    ext x
    change f k x + g k x = k (F x + G x)
    rw [hf, hg]
    exact (k.map_add _ _).symm
  scale_rel := by
    intro a b s f F hf k
    ext x
    change s • f k x = k (s • F x)
    rw [hf]
    exact (k.map_smul s (F x)).symm

def primitives (K : LinearModel) {a b : Ty} (p : FirstOrder.RealPrim a b) : Program K a b :=
  match p with
  | .constant c => Program.constant c
  | .add => Program.add
  | .mul => Program.mul

def target (K : LinearModel) : FirstOrderCompiler.Target FirstOrder.RealPrim where
  Hom := Program K
  ident := Program.ident
  comp := Program.comp
  terminal := Program.constant ()
  fst := Program.fst
  snd := Program.snd
  pair := Program.pair
  primitive := primitives K

def sound (K : LinearModel) : FirstOrderCompiler.Sound ℝ (target K)
    (FirstOrder.meaning FirstOrder.realPrimitives) where
  denote f x := (f.run x).1
  ident _ := rfl
  comp _ _ _ := rfl
  terminal _ := rfl
  fst _ := rfl
  snd _ := rfl
  pair _ _ _ := rfl
  primitive p _ := by cases p <;> rfl

def compile (K : LinearModel) (t : FirstOrderCompiler.Term FirstOrder.RealPrim Γ a) :
    Program K (FirstOrderCompiler.context Γ) a := FirstOrderCompiler.compile (target K) t

theorem compile_primal (K : LinearModel) (t : FirstOrderCompiler.Term FirstOrder.RealPrim Γ a)
    (ρ : Obj (FirstOrderCompiler.context Γ)) :
    ((compile K t).run ρ).1 =
      FirstOrderCompiler.eval (FirstOrder.meaning FirstOrder.realPrimitives) t ρ :=
  FirstOrderCompiler.compile_sound (target K) (sound K) t ρ

theorem compile_differentiable (K : LinearModel)
    (t : FirstOrderCompiler.Term FirstOrder.RealPrim Γ a) :
    Differentiable ℝ
      (FirstOrderCompiler.eval (FirstOrder.meaning FirstOrder.realPrimitives) t) := by
  intro ρ
  obtain ⟨L, hL, _⟩ := (compile K t).correct ρ
  have heq : (fun y => ((compile K t).run y).1) =
      FirstOrderCompiler.eval (FirstOrder.meaning FirstOrder.realPrimitives) t :=
    funext (compile_primal K t)
  rw [heq] at hL
  exact hL.differentiableAt

/-- The representation relation holds of the *actual* derivative, for every source term. -/
theorem compile_derivative (K : LinearModel)
    (t : FirstOrderCompiler.Term FirstOrder.RealPrim Γ a)
    (ρ : Obj (FirstOrderCompiler.context Γ)) :
    K.Rel ((compile K t).run ρ).2
      (fderiv ℝ (FirstOrderCompiler.eval (FirstOrder.meaning FirstOrder.realPrimitives) t) ρ) := by
  obtain ⟨L, hL, rL⟩ := (compile K t).correct ρ
  have heq : (fun y => ((compile K t).run y).1) =
      FirstOrderCompiler.eval (FirstOrder.meaning FirstOrder.realPrimitives) t :=
    funext (compile_primal K t)
  rw [heq] at hL
  rw [hL.fderiv]
  exact rL

theorem compile_reverse_correct (t : FirstOrderCompiler.Term FirstOrder.RealPrim Γ a)
    (ρ v : Obj (FirstOrderCompiler.context Γ)) (k : Obj a →L[ℝ] ℝ) :
    ((compile continuations t).run ρ).2 k v =
      k (fderiv ℝ (FirstOrderCompiler.eval
        (FirstOrder.meaning FirstOrder.realPrimitives) t) ρ v) := by
  exact congrArg (fun L : Obj (FirstOrderCompiler.context Γ) →L[ℝ] ℝ => L v)
    (compile_derivative continuations t ρ k)

/-- Both independently constructed backends agree on every directional observation. -/
theorem modes_agree (t : FirstOrderCompiler.Term FirstOrder.RealPrim Γ a)
    (ρ v : Obj (FirstOrderCompiler.context Γ)) (k : Obj a →L[ℝ] ℝ) :
    ((compile continuations t).run ρ).2 k v = k (((compile direct t).run ρ).2 v) := by
  rw [compile_reverse_correct]
  have h := compile_derivative direct t ρ
  change ((compile direct t).run ρ).2 = _ at h
  rw [h]

/-- This is a directly compiled continuation, not a conversion of an existing derivative. -/
theorem sharedPolynomial_reverse (x y dx dy : ℝ) :
    ((compile continuations FirstOrder.sharedPolynomial).run ((), (x, y))).2
        (ContinuousLinearMap.id ℝ ℝ) ((), (dx, dy)) =
      (2 * x * y * y + 1) * dx + (2 * x * x * y) * dy := by
  rw [compile_reverse_correct]
  change fderiv ℝ (FirstOrderCompiler.eval (FirstOrder.meaning FirstOrder.realPrimitives)
    FirstOrder.sharedPolynomial) ((), (x, y)) ((), (dx, dy)) = _
  rw [← FirstOrder.compile_derivative]
  exact FirstOrder.sharedPolynomial_derivative x y dx dy

end Applications.AD.Generalized
