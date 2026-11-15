import SquareKit.ListFoldCompiler
import Applications.Resources.Workload

/-! A writer interpretation of the finite fold source. Wiring is uncharged;
primitive costs and one visit per consumed list cell are explicit observations.
Only value denotation is cartesian-sound. -/
namespace Resources.FoldCompiler
open FirstOrderCompiler
variable {Prim : Ty → Ty → Type} {B : Type}
variable (meaning : {a b : Ty} → Prim a b → Val B a → Val B b)
variable (charge : {a b : Ty} → Prim a b → Nat)

def scalar : FirstOrderCompiler.Target Prim where
  Hom a b := Val B a → Measured (Val B b) Nat
  ident := pure
  comp g f x := bind (f x) g
  terminal _ := pure ()
  fst x := pure x.1
  snd x := pure x.2
  pair f g x := bind (f x) (fun y => bind (g x) (fun z => pure (y,z)))
  primitive p x := (meaning p x,charge p)

def scalarSound : FirstOrderCompiler.Sound B (scalar meaning charge) meaning where
  denote f x := (f x).1
  ident _ := rfl
  comp _ _ _ := rfl
  terminal _ := rfl
  fst _ := rfl
  snd _ := rfl
  pair _ _ _ := rfl
  primitive _ _ := rfl

def bodyCost : Term Prim Γ a → Nat
  | .var _ => 0
  | .unit => 0
  | .pair t u => bodyCost t + bodyCost u
  | .fst t => bodyCost t
  | .snd t => bodyCost t
  | .letE t u => bodyCost t + bodyCost u
  | .prim p t => bodyCost t + charge p

theorem variable_cost (v : Var Γ a) (ρ : Val B (context Γ)) :
    (compileVar (scalar meaning charge) v ρ).2 = 0 := by
  induction v with
  | here => rfl
  | there v ih => simpa [compileVar,scalar,bind,pure] using ih ρ.1

theorem scalar_cost (t : Term Prim Γ a) (ρ : Val B (context Γ)) :
    (FirstOrderCompiler.compile (scalar meaning charge) t ρ).2 = bodyCost charge t := by
  induction t with
  | var v => exact variable_cost meaning charge v ρ
  | unit => rfl
  | pair t u ih jh =>
    change (FirstOrderCompiler.compile (scalar meaning charge) t ρ).2 +
      ((FirstOrderCompiler.compile (scalar meaning charge) u ρ).2 + 0) = _
    rw [ih,jh]; simp [bodyCost]
  | fst t ih =>
    change (FirstOrderCompiler.compile (scalar meaning charge) t ρ).2 + 0 = _
    rw [ih]; simp [bodyCost]
  | snd t ih =>
    change (FirstOrderCompiler.compile (scalar meaning charge) t ρ).2 + 0 = _
    rw [ih]; simp [bodyCost]
  | letE t u ih jh =>
    change 0 + ((FirstOrderCompiler.compile (scalar meaning charge) t ρ).2 + 0) +
      (FirstOrderCompiler.compile (scalar meaning charge) u
        (ρ,(FirstOrderCompiler.compile (scalar meaning charge) t ρ).1)).2 = _
    rw [ih,jh]; simp [bodyCost]
  | prim p t ih =>
    change (FirstOrderCompiler.compile (scalar meaning charge) t ρ).2 + charge p = _
    rw [ih]; rfl

def target : ListFoldCompiler.Target Prim where
  scalar := scalar meaning charge
  Hom a b := List (Val B a) → Measured (Val B b) Nat
  fold seed body xs := bind (seed ()) (fun s =>
    run (fun x s => let r := body (((),s),x); (r.1,1+r.2)) xs s)
  post body p xs := bind (p xs) (fun s => body ((),s))

def sound : ListFoldCompiler.Sound B (target meaning charge) meaning where
  scalar := scalarSound meaning charge
  denote f xs := (f xs).1
  fold seed body xs := by
    simpa only [target,bind,scalarSound,id_eq] using
      (run_value_fusion (fun x s => let r := body (((),s),x); (r.1,1+r.2))
        (fun x s => (body (((),s),x)).1) id (fun _ => True)
        (fun _ _ _ => True.intro) (fun _ _ _ => rfl) xs (seed ()).1 True.intro)
  post _ _ _ := rfl

/-- Counts come from the executed transitions; no value-only transport infers them. -/
theorem run_constant_cost {ι σ : Type} (step : ι → σ → Measured σ Nat)
    (k : Nat) (cost : ∀ i s, (step i s).2 = k) (xs : List ι) (s : σ) :
    (run step xs s).2 = xs.length*k := by
  induction xs generalizing s with
  | nil => simp [run,pure]
  | cons x xs ih => simp [run_cons,cost,ih,Nat.succ_mul,Nat.add_comm]

/-- Syntax determines these costs because each supplied primitive has constant
modeled charge. Input-dependent primitive charges would need a richer analysis. -/
def programCost (charge : {a b : Ty} → Prim a b → Nat) :
    ListFoldCompiler.Program Prim a b → Nat → Nat
  | .fold seed body, n => bodyCost charge seed + n*(1+bodyCost charge body)
  | .post p body, n => programCost charge p n + bodyCost charge body

theorem compile_cost (p : ListFoldCompiler.Program Prim a b) (xs : List (Val B a)) :
    (ListFoldCompiler.compile (target meaning charge) p xs).2 = programCost charge p xs.length := by
  induction p with
  | fold seed body =>
    change (FirstOrderCompiler.compile (scalar meaning charge) seed ()).2 +
      (run (fun x s => let r := FirstOrderCompiler.compile (scalar meaning charge) body (((),s),x)
        ; (r.1,1+r.2)) xs _).2 = _
    rw [scalar_cost,run_constant_cost (k := 1+bodyCost charge body)
      (cost := fun x s => by simp [scalar_cost])]
    rfl
  | post p body ih =>
    change (ListFoldCompiler.compile (target meaning charge) p xs).2 +
      (FirstOrderCompiler.compile (scalar meaning charge) body ((),_)).2 = _
    rw [ih,scalar_cost]
    rfl

def erasure (p : ListFoldCompiler.Program Prim a b) :
    Squares.Square ⟨List (Val B a),List (Val B a),id⟩
      ⟨Measured (Val B b) Nat,Val B b,Prod.fst⟩ :=
  erasureSquare (ListFoldCompiler.compile (target meaning charge) p)
    (ListFoldCompiler.eval meaning p)
    (ListFoldCompiler.compile_sound _ (sound meaning charge) p)

end Resources.FoldCompiler
