import Applications.Progress.Feedback

namespace Progress.Feedback
universe u
variable {A X Y : Type u}

/-- Both initial states are visible. Left reads old right; right reads the new
left value. The right-to-left edge therefore crosses a state delay. -/
def CoupledSolution (p : A → Y → X → X) (q : A → X → Y → Y)
    (x₀ : X) (y₀ : Y) (a : Stream A) (x : Stream X) (y : Stream Y) : Prop :=
  x 0 = x₀ ∧ y 0 = y₀ ∧ (∀ n, x (n+1) = p (a n) (y n) (x n)) ∧
    ∀ n, y (n+1) = q (a n) (x (n+1)) (y n)

def joint (p : A → Y → X → X) (q : A → X → Y → Y) (x₀ : X) (y₀ : Y) :
    Initialized A (X × Y) (X × Y) where
  initial := (x₀,y₀)
  step := fun (a,x,y) => let x' := p a y x; let y' := q a x' y; ((x',y'),(x',y'))

def leftStage (p : A → Y → X → X) : Mealy X (A × Y) X :=
  fun x (a,y) => let x' := p a y x; (x',x')
def rightStage (q : A → X → Y → Y) : Mealy Y (A × X) Y :=
  fun y (a,x') => let y' := q a x' y; (y',y')

/-- Sequential stage execution, with an explicit intermediate and separate
component states. It does not call the joint interpreter. -/
def wired (p : A → Y → X → X) (q : A → X → Y → Y) (x : X) (y : Y) :
    List A → List (X × Y) × (X × Y)
  | [] => ([],(x,y))
  | a::as =>
    let l := leftStage p x (a,y)
    let r := rightStage q y (a,l.1)
    let rest := wired p q l.2 r.2 as
    ((l.1,r.1)::rest.1,rest.2)

theorem factorization (p : A → Y → X → X) (q : A → X → Y → Y)
    (x : X) (y : Y) (as : List A) :
    run (joint p q x y).mealy (x,y) as = wired p q x y as := by
  induction as generalizing x y with
  | nil => rfl
  | cons a as ih =>
    change ((p a y x,q a (p a y x) y) ::
      (run (joint p q x y).mealy (p a y x,q a (p a y x) y) as).1,
      (run (joint p q x y).mealy (p a y x,q a (p a y x) y) as).2) = _
    exact congrArg (fun z : List (X × Y) × (X × Y) =>
      ((p a y x,q a (p a y x) y)::z.1,z.2))
      (ih (p a y x) (q a (p a y x) y))

theorem joint_solves (p : A → Y → X → X) (q : A → X → Y → Y)
    (x : X) (y : Y) (a : Stream A) :
    CoupledSolution p q x y a (fun n => (state (joint p q x y) a n).1)
      (fun n => (state (joint p q x y) a n).2) :=
  ⟨rfl,rfl,fun _ => rfl,fun _ => rfl⟩

theorem coupled_unique {p : A → Y → X → X} {q : A → X → Y → Y}
    {x₀ : X} {y₀ : Y} {a : Stream A} {x : Stream X} {y : Stream Y}
    (h : CoupledSolution p q x₀ y₀ a x y) :
    (fun n => (x n,y n)) = state (joint p q x₀ y₀) a := by
  apply (unique (f := joint p q x₀ y₀) (a := a)
    (s := fun n => (x n,y n)) (b := fun n => (x (n+1),y (n+1))) ?_).1
  refine ⟨by simp [joint,h.1,h.2.1],?_,?_⟩ <;>
    intro n <;> simp [joint,h.2.2.1 n,h.2.2.2 n]

/-- The first separately stateful stage realizes its part of any solution. -/
theorem left_stream {p : A → Y → X → X} {q : A → X → Y → Y}
    {x₀ : X} {y₀ : Y} {a : Stream A} {x : Stream X} {y : Stream Y}
    (h : CoupledSolution p q x₀ y₀ a x y) :
    (fun n => x (n+1)) = runStream (leftStage p) x₀ (fun n => (a n,y n)) := by
  let f : Initialized (A × Y) X X := ⟨fun (ay,x) => leftStage p x ay,x₀⟩
  have sol : Solution f (fun n => (a n,y n)) x (fun n => x (n+1)) :=
    ⟨h.1,h.2.2.1,h.2.2.1⟩
  exact (unique sol).2.trans (output_mealy f _)

theorem right_stream {p : A → Y → X → X} {q : A → X → Y → Y}
    {x₀ : X} {y₀ : Y} {a : Stream A} {x : Stream X} {y : Stream Y}
    (h : CoupledSolution p q x₀ y₀ a x y) :
    (fun n => y (n+1)) = runStream (rightStage q) y₀ (fun n => (a n,x (n+1))) := by
  let f : Initialized (A × X) Y Y := ⟨fun (ax,y) => rightStage q y ax,y₀⟩
  have sol : Solution f (fun n => (a n,x (n+1))) y (fun n => y (n+1)) :=
    ⟨h.2.1,h.2.2.2,h.2.2.2⟩
  exact (unique sol).2.trans (output_mealy f _)

theorem coupled_prefix (p : A → Y → X → X) (q : A → X → Y → Y)
    (x : X) (y : Y) (a : Stream A) (n : Nat) :
    prefixOf (output (joint p q x y) a) n = (wired p q x y (prefixOf a n)).1 := by
  rw [output_prefix, ← run_outputs]
  exact congrArg Prod.fst (factorization p q x y (prefixOf a n))

end Progress.Feedback
