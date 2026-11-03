import Applications.Progress.Feedback

/-! Feed-forward wiring of initialized machines with explicit retained states.
These operations do not solve instantaneous feedback or identify state types. -/
namespace Progress.Feedback
universe u
variable {A B C D S T : Type u}

def pure (f : A → B) : Initialized A B PUnit where
  initial := PUnit.unit
  step p := (f p.1, PUnit.unit)

def seq (f : Initialized A B S) (g : Initialized B C T) : Initialized A C (S × T) where
  initial := (f.initial,g.initial)
  step := fun (a,s,t) =>
    let first := f.step (a,s)
    let second := g.step (first.1,t)
    (second.1,(first.2,second.2))

def par (f : Initialized A B S) (g : Initialized C D T) :
    Initialized (A × C) (B × D) (S × T) where
  initial := (f.initial,g.initial)
  step := fun ((a,c),s,t) =>
    let first := f.step (a,s)
    let second := g.step (c,t)
    ((first.1,second.1),(first.2,second.2))

theorem pure_output (f : A → B) (a : Stream A) : output (pure f) a = fun n => f (a n) := rfl

theorem seq_solution (f : Initialized A B S) (g : Initialized B C T) (a : Stream A) :
    Solution (seq f g) a (fun n => (state f a n,state g (output f a) n))
      (output g (output f a)) := ⟨rfl,fun _ => rfl,fun _ => rfl⟩

theorem seq_state (f : Initialized A B S) (g : Initialized B C T) (a : Stream A) :
    state (seq f g) a = fun n => (state f a n,state g (output f a) n) :=
  (unique (seq_solution f g a)).1.symm

theorem seq_output (f : Initialized A B S) (g : Initialized B C T) (a : Stream A) :
    output (seq f g) a = output g (output f a) := (unique (seq_solution f g a)).2.symm

theorem par_solution (f : Initialized A B S) (g : Initialized C D T) (a : Stream (A × C)) :
    Solution (par f g) a
      (fun n => (state f (fun k => (a k).1) n,state g (fun k => (a k).2) n))
      (fun n => (output f (fun k => (a k).1) n,output g (fun k => (a k).2) n)) :=
  ⟨rfl,fun _ => rfl,fun _ => rfl⟩

theorem par_state (f : Initialized A B S) (g : Initialized C D T) (a : Stream (A × C)) :
    state (par f g) a =
      fun n => (state f (fun k => (a k).1) n,state g (fun k => (a k).2) n) :=
  (unique (par_solution f g a)).1.symm

theorem par_output (f : Initialized A B S) (g : Initialized C D T) (a : Stream (A × C)) :
    output (par f g) a =
      fun n => (output f (fun k => (a k).1) n,output g (fun k => (a k).2) n) :=
  (unique (par_solution f g a)).2.symm

theorem run_pure (f : A → B) (xs : List A) :
    run (pure f).mealy PUnit.unit xs = (xs.map f,PUnit.unit) := by
  induction xs with
  | nil => rfl
  | cons x xs ih =>
    simp only [run]
    rw [ih]
    rfl

theorem run_seq (f : Initialized A B S) (g : Initialized B C T) (s : S) (t : T) (xs : List A) :
    run (seq f g).mealy (s,t) xs =
      let first := run f.mealy s xs
      let second := run g.mealy t first.1
      (second.1,(first.2,second.2)) := by
  induction xs generalizing s t with
  | nil => rfl
  | cons x xs ih =>
    simp only [run]
    rw [ih]
    rfl

theorem run_par (f : Initialized A B S) (g : Initialized C D T) (s : S) (t : T)
    (xs : List (A × C)) :
    run (par f g).mealy (s,t) xs =
      let first := run f.mealy s (xs.map Prod.fst)
      let second := run g.mealy t (xs.map Prod.snd)
      (first.1.zip second.1,(first.2,second.2)) := by
  induction xs generalizing s t with
  | nil => rfl
  | cons x xs ih =>
    simp only [List.map_cons,run]
    rw [ih]
    rfl

/-- Finite counterpart of `transport`, including both output lists and retained
final states. It uses the existing runner rather than a second evaluator. -/
theorem run_related {A' B' T : Type u} (f : Mealy S A B) (g : Mealy T A' B')
    (I : A → A' → Prop) (R : S → T → Prop) (O : B → B' → Prop)
    (step : ∀ a a' s t, I a a' → R s t →
      O (f s a).1 (g t a').1 ∧ R (f s a).2 (g t a').2)
    {xs : List A} {ys : List A'} (inputs : List.Forall₂ I xs ys)
    {s : S} {t : T} (initial : R s t) :
    List.Forall₂ O (run f s xs).1 (run g t ys).1 ∧ R (run f s xs).2 (run g t ys).2 := by
  induction inputs generalizing s t with
  | nil => exact ⟨.nil,initial⟩
  | cons h hs ih =>
    have hstep :=  step _ _ _ _ h initial
    have rest := ih hstep.2
    exact ⟨.cons hstep.1 rest.1,rest.2⟩

end Progress.Feedback
