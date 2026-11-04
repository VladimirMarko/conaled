import SquareKit.GuardedStreams
import Squares

/-! Compilation of a finite guarded stream-body language. Translation recurses
on syntax; solution construction separately recurses on observation coordinates.
There is one recursive stream variable and no unrestricted fixed-point primitive. -/
namespace SquareKit.GuardedStreamCompiler
open GuardedStreams

inductive Body (Const Param Ref Op Bin : Type) where
  | recur
  | param : Param → Body Const Param Ref Op Bin
  | ref : Ref → Body Const Param Ref Op Bin
  | delay : Const → Body Const Param Ref Op Bin → Body Const Param Ref Op Bin
  | app : Op → Body Const Param Ref Op Bin → Body Const Param Ref Op Bin
  | zip : Bin → Body Const Param Ref Op Bin → Body Const Param Ref Op Bin →
      Body Const Param Ref Op Bin

variable {Const Param Ref Op Bin A B : Type}
local notation "Syntax" => Body Const Param Ref Op Bin

/-- References are already available streams. Extending this environment with a
constructed solution cannot introduce a forward reference or a recursive cycle. -/
structure Meaning (Const Param Ref Op Bin A : Type) where
  constant : Const → A
  parameter : Param → Stream A
  reference : Ref → Stream A
  operation : Op → Stream A → Stream A
  causal : ∀ o, Causal (operation o)
  binary : Bin → A → A → A

def denote (M : Meaning Const Param Ref Op Bin A) : Syntax → Stream A → Stream A
  | .recur => id
  | .param p => fun _ => M.parameter p
  | .ref r => fun _ => M.reference r
  | .delay c t => cons (M.constant c) ∘ denote M t
  | .app o t => M.operation o ∘ denote M t
  | .zip o t u => fun s n => M.binary o (denote M t s n) (denote M u s n)

/-- Every recursive occurrence must cross a delay. This sufficient check is
conservative: a constant-valued admitted operation can hide an unused occurrence. -/
def guarded : Syntax → Bool
  | .recur => false
  | .param _ | .ref _ => true
  | .delay _ _ => true
  | .app _ t => guarded t
  | .zip _ t u => guarded t && guarded u

theorem denote_causal (M : Meaning Const Param Ref Op Bin A) (t : Syntax) :
    Causal (denote M t) := by
  induction t with
  | recur => exact causal_id
  | param | ref => intro n s t h; rfl
  | delay c t ih =>
    intro n s u h
    cases n with
    | zero => rfl
    | succ n => exact ih n s u (fun i hi => h i (Nat.le_trans hi (Nat.le_succ n)))
  | app o t ih => exact causal_comp (M.causal o) ih
  | zip o t u ih ih' =>
    intro n s v h
    exact congrArg₂ (M.binary o) (ih n s v h) (ih' n s v h)

theorem denote_guarded (M : Meaning Const Param Ref Op Bin A) (t : Syntax)
    (h : guarded t = true) : Guarded (denote M t) := by
  induction t with
  | recur => cases h
  | param | ref => intro n s t h; rfl
  | delay c t => exact guarded_comp_causal (cons_guarded _) (denote_causal M t)
  | app o t ih => exact causal_comp_guarded (M.causal o) (ih h)
  | zip o t u ih ih' =>
    have hs := Bool.and_eq_true_iff.mp h
    intro n s v h
    exact congrArg₂ (M.binary o) (ih hs.1 n s v h) (ih' hs.2 n s v h)

/-- A target supplies body constructors, not a whole recursive client. -/
structure Target (Const Param Ref Op Bin : Type) where
  Code : Type
  recur : Code
  param : Param → Code
  ref : Ref → Code
  delay : Const → Code → Code
  app : Op → Code → Code
  zip : Bin → Code → Code → Code

def compile (K : Target Const Param Ref Op Bin) : Syntax → K.Code
  | .recur => K.recur
  | .param p => K.param p
  | .ref r => K.ref r
  | .delay c t => K.delay c (compile K t)
  | .app o t => K.app o (compile K t)
  | .zip o t u => K.zip o (compile K t) (compile K u)

structure Sound (K : Target Const Param Ref Op Bin)
    (M : Meaning Const Param Ref Op Bin A) where
  interpret : K.Code → Stream A → Stream A
  recur : interpret K.recur = id
  param : ∀ p, interpret (K.param p) = fun _ => M.parameter p
  ref : ∀ r, interpret (K.ref r) = fun _ => M.reference r
  delay : ∀ c t, interpret (K.delay c t) = cons (M.constant c) ∘ interpret t
  app : ∀ o t, interpret (K.app o t) = M.operation o ∘ interpret t
  zip : ∀ o t u, interpret (K.zip o t u) =
    fun s n => M.binary o (interpret t s n) (interpret u s n)

theorem compile_sound (K : Target Const Param Ref Op Bin)
    (M : Meaning Const Param Ref Op Bin A) (S : Sound K M) (t : Syntax) :
    S.interpret (compile K t) = denote M t := by
  induction t with
  | recur => exact S.recur
  | param p => exact S.param p
  | ref r => exact S.ref r
  | delay c t ih => simp only [compile, S.delay, ih, denote]
  | app o t ih => simp only [compile, S.app, ih, denote]
  | zip o t u ih ih' => simp only [compile, S.zip, ih, ih', denote]

theorem compile_guarded (K : Target Const Param Ref Op Bin)
    (M : Meaning Const Param Ref Op Bin A) (S : Sound K M) (t : Syntax)
    (h : guarded t = true) : Guarded (S.interpret (compile K t)) := by
  rw [compile_sound]
  exact denote_guarded M t h

/-- Only certified bodies enter the recursive compiler interface. -/
def solution (K : Target Const Param Ref Op Bin)
    (M : Meaning Const Param Ref Op Bin A) (S : Sound K M) (t : Syntax)
    (_h : guarded t = true) (seed : A) : Stream A :=
  solve (S.interpret (compile K t)) seed

theorem solution_fixed (K : Target Const Param Ref Op Bin)
    (M : Meaning Const Param Ref Op Bin A) (S : Sound K M) (t : Syntax)
    (h : guarded t = true) (seed : A) :
    solution K M S t h seed = denote M t (solution K M S t h seed) := by
  have fixed := solve_fixed (compile_guarded K M S t h) seed
  rw [compile_sound] at fixed
  simpa only [solution, compile_sound] using fixed

/-- Independent meanings are candidate streams satisfying the source equation.
No solution or uniqueness assumption is supplied by a target. -/
theorem solution_meaning (K : Target Const Param Ref Op Bin)
    (M : Meaning Const Param Ref Op Bin A) (S : Sound K M) (t : Syntax)
    (h : guarded t = true) (seed : A) (expected : Stream A)
    (equation : expected = denote M t expected) :
    solution K M S t h seed = expected := by
  apply Eq.symm
  apply unique (compile_guarded K M S t h) seed
  rw [compile_sound]
  exact equation

def functionTarget (M : Meaning Const Param Ref Op Bin A) : Target Const Param Ref Op Bin where
  Code := Stream A → Stream A
  recur := id
  param p _ := M.parameter p
  ref r _ := M.reference r
  delay c t := cons (M.constant c) ∘ t
  app o t := M.operation o ∘ t
  zip o t u s n := M.binary o (t s n) (u s n)

def functionSound (M : Meaning Const Param Ref Op Bin A) : Sound (functionTarget M) M where
  interpret := id
  recur := rfl
  param _ := rfl
  ref _ := rfl
  delay _ _ := rfl
  app _ _ := rfl
  zip _ _ _ := rfl

/-- Constructor-local interpretation obligations. No law mentions a solution
or quantifies over a composite body. -/
structure Interpretation (M : Meaning Const Param Ref Op Bin A)
    (N : Meaning Const Param Ref Op Bin B) (f : A → B) : Prop where
  constant : ∀ c, f (M.constant c) = N.constant c
  parameter : ∀ p, f ∘ M.parameter p = N.parameter p
  reference : ∀ r, f ∘ M.reference r = N.reference r
  operation : ∀ o s, f ∘ M.operation o s = N.operation o (f ∘ s)
  binary : ∀ o a b, f (M.binary o a b) = N.binary o (f a) (f b)

def streamRep (f : A → B) : Squares.Rep := ⟨Stream A, Stream B, fun s => f ∘ s⟩

/-- Shared square composition and pairing lift the local laws through syntax. -/
def bodySquare (M : Meaning Const Param Ref Op Bin A)
    (N : Meaning Const Param Ref Op Bin B) (f : A → B) (I : Interpretation M N f) :
    Syntax → Squares.Square (streamRep f) (streamRep f)
  | .recur => Squares.identity _
  | .param p => ⟨fun _ => M.parameter p, fun _ => N.parameter p, fun _ => I.parameter p⟩
  | .ref r => ⟨fun _ => M.reference r, fun _ => N.reference r, fun _ => I.reference r⟩
  | .delay c t => Squares.compose
      ⟨cons (M.constant c), cons (N.constant c), by
        intro s; funext n; cases n with
        | zero => exact I.constant c
        | succ n => rfl⟩ (bodySquare M N f I t)
  | .app o t => Squares.compose
      ⟨M.operation o, N.operation o, I.operation o⟩ (bodySquare M N f I t)
  | .zip o t u => Squares.compose (B := Squares.product (streamRep f) (streamRep f))
      ⟨fun p n => M.binary o (p.1 n) (p.2 n),
       fun p n => N.binary o (p.1 n) (p.2 n),
       fun p => funext (fun n => I.binary o (p.1 n) (p.2 n))⟩
      (Squares.pair (bodySquare M N f I t) (bodySquare M N f I u))

theorem bodySquare_arrows (M : Meaning Const Param Ref Op Bin A)
    (N : Meaning Const Param Ref Op Bin B) (f : A → B) (I : Interpretation M N f)
    (t : Syntax) :
    (bodySquare M N f I t).impl = denote M t ∧
    (bodySquare M N f I t).spec = denote N t := by
  induction t with
  | recur | param | ref => exact ⟨rfl, rfl⟩
  | delay c t ih | app c t ih =>
    simp only [bodySquare, Squares.compose, ih.1, ih.2, denote, Function.comp_def]
    exact ⟨rfl, rfl⟩
  | zip o t u ih ih' =>
    simp only [bodySquare, Squares.compose, Squares.pair, ih.1, ih.2, ih'.1, ih'.2, denote]
    exact ⟨rfl, rfl⟩

theorem denote_interpretation (M : Meaning Const Param Ref Op Bin A)
    (N : Meaning Const Param Ref Op Bin B) (f : A → B) (I : Interpretation M N f)
    (t : Syntax) (s : Stream A) : f ∘ denote M t s = denote N t (f ∘ s) := by
  have h := (bodySquare M N f I t).commutes s
  change f ∘ (bodySquare M N f I t).impl s = (bodySquare M N f I t).spec (f ∘ s) at h
  rw [(bodySquare_arrows M N f I t).1, (bodySquare_arrows M N f I t).2] at h
  exact h

theorem solution_interpretation (K L : Target Const Param Ref Op Bin)
    (M : Meaning Const Param Ref Op Bin A) (N : Meaning Const Param Ref Op Bin B)
    (S : Sound K M) (T : Sound L N) (f : A → B) (I : Interpretation M N f)
    (t : Syntax) (h : guarded t = true) (a : A) (b : B) :
    f ∘ solution K M S t h a = solution L N T t h b := by
  apply map_solution (compile_guarded K M S t h) (compile_guarded L N T t h) f a b
  intro s
  rw [compile_sound, compile_sound]
  exact denote_interpretation M N f I t s

end SquareKit.GuardedStreamCompiler
