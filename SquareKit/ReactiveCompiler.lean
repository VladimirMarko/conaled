import SquareKit.ListFoldCompiler
import Applications.Progress.Reactive

/-! Compile initialized transition bodies once using the existing first-order
compiler. Execution consumes stored target morphisms, not source terms. -/
namespace ReactiveCompiler
open FirstOrderCompiler Progress.Feedback
variable {Prim : Ty → Ty → Type} {a b s : Ty} {B : Type}

structure Compiled (K : Target Prim) (a b s : Ty) where
  seed : K.Hom .unit s
  body : K.Hom (context [a,s]) (.prod b s)

def compile (K : Target Prim) (seed : Term Prim [] s)
    (body : Term Prim [a,s] (.prod b s)) : Compiled K a b s :=
  ⟨FirstOrderCompiler.compile K seed,FirstOrderCompiler.compile K body⟩

def realize (K : Target Prim)
    (denote : {a b : Ty} → K.Hom a b → Val B a → Val B b)
    (p : Compiled K a b s) : Initialized (Val B a) (Val B b) (Val B s) where
  initial := denote p.seed ()
  step := fun (x,state) => denote p.body (((),state),x)

/-- Independent source meaning uses the term evaluator only on this side. -/
def source (meaning : {a b : Ty} → Prim a b → Val B a → Val B b)
    (seed : Term Prim [] s) (body : Term Prim [a,s] (.prod b s)) :
    Initialized (Val B a) (Val B b) (Val B s) where
  initial := FirstOrderCompiler.eval meaning seed ()
  step := fun (x,state) => FirstOrderCompiler.eval meaning body (((),state),x)

theorem initial_sound (K : Target Prim)
    {meaning : {a b : Ty} → Prim a b → Val B a → Val B b}
    (S : Sound B K meaning) (seed : Term Prim [] s) (body : Term Prim [a,s] (.prod b s)) :
    (realize K S.denote (compile K seed body)).initial = (source meaning seed body).initial :=
  FirstOrderCompiler.compile_sound K S seed ()

theorem step_sound (K : Target Prim)
    {meaning : {a b : Ty} → Prim a b → Val B a → Val B b}
    (S : Sound B K meaning) (seed : Term Prim [] s) (body : Term Prim [a,s] (.prod b s))
    (x : Val B a) (state : Val B s) :
    (realize K S.denote (compile K seed body)).step (x,state) =
      (source meaning seed body).step (x,state) :=
  FirstOrderCompiler.compile_sound K S body (((),state),x)

theorem realize_compile (K : Target Prim)
    {meaning : {a b : Ty} → Prim a b → Val B a → Val B b}
    (S : Sound B K meaning) (seed : Term Prim [] s) (body : Term Prim [a,s] (.prod b s)) :
    realize K S.denote (compile K seed body) = source meaning seed body := by
  have hs : (realize K S.denote (compile K seed body)).step =
      (source meaning seed body).step := funext (fun (x,state) => step_sound K S seed body x state)
  have hi := initial_sound K S seed body
  cases h : realize K S.denote (compile K seed body)
  cases h' : source meaning seed body
  simp_all

theorem run_sound (K : Target Prim)
    {meaning : {a b : Ty} → Prim a b → Val B a → Val B b}
    (S : Sound B K meaning) (seed : Term Prim [] s) (body : Term Prim [a,s] (.prod b s))
    (xs : List (Val B a)) :
    let compiled := realize K S.denote (compile K seed body)
    run compiled.mealy compiled.initial xs =
      run (source meaning seed body).mealy (source meaning seed body).initial xs := by
  simp only [realize_compile K S]

/-- Pure syntax also compiles before runtime inputs are supplied. -/
def compileMap (K : Target Prim) (t : Term Prim [a] b) : K.Hom (context [a]) b :=
  FirstOrderCompiler.compile K t

def realizeMap (K : Target Prim)
    (denote : {a b : Ty} → K.Hom a b → Val B a → Val B b)
    (f : K.Hom (context [a]) b) : Val B a → Val B b := fun x => denote f ((),x)

theorem map_sound (K : Target Prim)
    {meaning : {a b : Ty} → Prim a b → Val B a → Val B b}
    (S : Sound B K meaning) (t : Term Prim [a] b) (x : Val B a) :
    realizeMap K S.denote (compileMap K t) x = FirstOrderCompiler.eval meaning t ((),x) :=
  FirstOrderCompiler.compile_sound K S t ((),x)

end ReactiveCompiler
