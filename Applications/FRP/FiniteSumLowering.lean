import Applications.FRP.FiniteSum

/-! Finite case lowering evaluates the scrutinee once, then both total arms,
and selects their finite result with Boolean gates. -/
namespace FRPSpec.FiniteSum
open Applications.Circuits
open FirstOrderCompiler (context)

/-- Canonical zero uses existing constant gates, including inactive payloads. -/
def zeroCircuit (a b : FirstOrderCompiler.Ty) : Circuit a b :=
  match b with
  | .base => .compose (.gate (.constant false)) .terminate
  | .unit => .terminate
  | .prod b c => .pair (zeroCircuit a b) (zeroCircuit a c)

@[simp] theorem zeroCircuit_execute (a b : FirstOrderCompiler.Ty)
    (x : FirstOrderCompiler.Val Bool a) : (zeroCircuit a b).execute x = zero b := by
  induction b with
  | base => rfl
  | unit => rfl
  | prod b c hb hc => simp [zeroCircuit, Circuit.execute, zero, hb, hc]

/-- False chooses the left value. All gates and both inputs are evaluated. -/
def boolMux : Circuit (.prod .base (.prod .base .base)) .base :=
  .compose Circuit.or
    (.pair
      (.compose Circuit.and (.pair (.compose Circuit.not .first) (.compose .first .second)))
      (.compose Circuit.and (.pair .first (.compose .second .second))))

theorem boolMux_execute (tag l r : Bool) : boolMux.execute (tag,(l,r)) =
    if tag then r else l := by
  cases tag <;> cases l <;> cases r <;> rfl

def mux : (a : FirstOrderCompiler.Ty) → Circuit (.prod .base (.prod a a)) a
  | .base => boolMux
  | .unit => .terminate
  | .prod a b => .pair
      (.compose (mux a) (.pair .first (.pair
        (.compose .first (.compose .first .second))
        (.compose .first (.compose .second .second)))))
      (.compose (mux b) (.pair .first (.pair
        (.compose .second (.compose .first .second))
        (.compose .second (.compose .second .second)))))

@[simp] theorem mux_execute (a : FirstOrderCompiler.Ty) (tag : Bool)
    (l r : FirstOrderCompiler.Val Bool a) :
    (mux a).execute (tag,(l,r)) = if tag then r else l := by
  induction a with
  | base => exact boolMux_execute tag l r
  | unit => cases tag <;> cases l <;> cases r <;> rfl
  | prod a b ha hb =>
    simp only [mux, Circuit.execute, ha, hb]
    cases tag <;> rfl

def lowerVar : Var Γ a → Circuit (context (storageContext Γ)) a.storage
  | .here => .second
  | .there v => .compose (lowerVar v) .first

@[simp] theorem lowerVar_execute (v : Var Γ a) (ρ : Env Γ) :
    (lowerVar v).execute (encodeEnv ρ) = encode (CategoricalCompiler.lookup v.source ρ) := by
  induction v with
  | here => rfl
  | there v ih => exact ih ρ.1

/-- The context and evaluated tagged value enter this block together. -/
def caseCircuit {γ a b c : FirstOrderCompiler.Ty}
    (l : Circuit (.prod γ a) c) (r : Circuit (.prod γ b) c) :
    Circuit (.prod γ (.prod .base (.prod a b))) c :=
  .compose (mux c)
    (.pair (.compose .first .second)
      (.pair
        (.compose l (.pair .first (.compose .first (.compose .second .second))))
        (.compose r (.pair .first (.compose .second (.compose .second .second))))))

theorem caseCircuit_execute {γ a b c : FirstOrderCompiler.Ty}
    (l : Circuit (.prod γ a) c) (r : Circuit (.prod γ b) c)
    (ρ : FirstOrderCompiler.Val Bool γ) (tag : Bool)
    (x : FirstOrderCompiler.Val Bool a) (y : FirstOrderCompiler.Val Bool b) :
    (caseCircuit l r).execute (ρ,(tag,(x,y))) =
      if tag then r.execute (ρ,y) else l.execute (ρ,x) := by
  simp only [caseCircuit, Circuit.execute]
  exact mux_execute c tag _ _

/-- Work includes both arms and the componentwise mux, even for a fixed tag. -/
theorem caseCircuit_work {γ a b c : FirstOrderCompiler.Ty}
    (l : Circuit (.prod γ a) c) (r : Circuit (.prod γ b) c) :
    (caseCircuit l r).work = l.work + r.work + (mux c).work + 22 := by
  simp only [caseCircuit, Circuit.work]
  omega

def lower : Term Γ a → Circuit (context (storageContext Γ)) a.storage
  | .var v => lowerVar v
  | .unit => .terminate
  | .pair t u => .pair (lower t) (lower u)
  | .fst t => .compose .first (lower t)
  | .snd t => .compose .second (lower t)
  | .letE t u => .compose (lower u) (.pair .identity (lower t))
  | .inl (a := a) (b := b) t =>
      .pair (.compose (.gate (.constant false)) .terminate)
        (.pair (lower t) (zeroCircuit _ b.storage))
  | .inr (a := a) (b := b) t =>
      .pair (.compose (.gate (.constant true)) .terminate)
        (.pair (zeroCircuit _ a.storage) (lower t))
  | .caseE s l r => .compose (caseCircuit (lower l) (lower r)) (.pair .identity (lower s))
  | .constant b => .compose (.gate (.constant b)) .terminate
  | .test t => .pair (lower t) (.pair .terminate .terminate)
  | .not t => .compose Circuit.not (lower t)
  | .nand t => .compose Circuit.nand (lower t)

/-- Structural preservation includes open contexts, both binders and nested sums. -/
theorem lower_correct (t : Term Γ a) (ρ : Env Γ) :
    (lower t).execute (encodeEnv ρ) = encode (eval t ρ) := by
  induction t with
  | var v => exact lowerVar_execute v ρ
  | unit => rfl
  | pair t u ht hu => simp [lower, Circuit.execute, ht, hu, eval, Term.source,
      CategoricalCompiler.eval, encode]
  | fst t ht =>
    simp only [lower, Circuit.execute]
    rw [ht ρ]
    rfl
  | snd t ht =>
    simp only [lower, Circuit.execute]
    rw [ht ρ]
    rfl
  | letE t u ht hu =>
    simp only [lower, Circuit.execute, ht]
    exact hu (ρ,eval t ρ)
  | inl t ht =>
    simp [lower, Circuit.execute, ht, eval, Term.source, CategoricalCompiler.eval, encode,
      Gate.meaning]
  | inr t ht =>
    simp [lower, Circuit.execute, ht, eval, Term.source, CategoricalCompiler.eval, encode,
      Gate.meaning]
  | caseE s l r hs hl hr =>
    simp only [lower, Circuit.execute]
    rw [hs ρ]
    cases h : eval s ρ with
    | inl x =>
      simp only [encode]
      rw [caseCircuit_execute]
      change (lower l).execute (encodeEnv (ρ,x)) = _
      rw [hl]
      simp [eval, Term.source, CategoricalCompiler.eval] at h ⊢
      rw [h]
    | inr y =>
      simp only [encode]
      rw [caseCircuit_execute]
      change (lower r).execute (encodeEnv (ρ,y)) = _
      rw [hr]
      simp [eval, Term.source, CategoricalCompiler.eval] at h ⊢
      rw [h]
  | constant b => rfl
  | test t ht =>
    simp only [lower, Circuit.execute]
    rw [ht ρ]
    change (eval t ρ,((),())) = encode (a := .sum .unit .unit) (if eval t ρ then Sum.inr () else Sum.inl ())
    cases eval t ρ <;> rfl
  | not t ht => simp only [lower, Circuit.execute]; rw [ht ρ]; rfl
  | nand t ht => simp only [lower, Circuit.execute]; rw [ht ρ]; rfl

end FRPSpec.FiniteSum
