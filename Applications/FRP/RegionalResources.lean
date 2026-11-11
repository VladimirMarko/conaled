import Applications.FRP.RegionalPlans

/-! Explicit operational accounting for the local regional catalog. Units are
node dispatches and copied Boolean cells/frames, not host allocation or time. -/
namespace FRPSpec.Regional
open Progress Progress.Feedback Applications.Circuits
namespace Rich
open CategoricalCompiler

/-- Maximum finite representation width. Arrow types require another analysis. -/
def width : Ty → Nat
  | .base => 1
  | .unit => 0
  | .prod a b => width a + width b
  | .sum a b => 1 + max (width a) (width b)
  | .arr _ _ => 0

def firstOrder : Ty → Bool
  | .arr _ _ => false
  | .prod a b | .sum a b => firstOrder a && firstOrder b
  | _ => true

/-- No bound is returned for applying an arbitrary host function. -/
def analyzable {a b : Ty} (c : Code Prim a b) : Bool :=
  match c with
  | .curry _ | .apply => false
  | .comp g f | .pair f g | .copair f g =>
      firstOrder a && firstOrder b && analyzable f && analyzable g
  | _ => firstOrder a && firstOrder b

/-- The actual recursive dispatch count. Closure application has no resource
certificate; its apparent unit here must never be used as a service bound. -/
def dispatches : Code Prim a b → Val Bool a → Nat
  | .comp g f, x => dispatches f x + dispatches g (run meaning f x) + 1
  | .pair f g, x => dispatches f x + dispatches g x + 1
  | .copair f _, .inl x => dispatches f x + 1
  | .copair _ g, .inr x => dispatches g x + 1
  | _, _ => 1

def workBound : Code Prim a b → Nat
  | .comp g f | .pair f g => workBound f + workBound g + 1
  | .copair f g => max (workBound f) (workBound g) + 1
  | _ => 1

theorem dispatches_le (c : Code Prim a b) (x : Val Bool a) :
    dispatches c x ≤ workBound c := by
  induction c with
  | comp g f hg hf => simp only [dispatches, workBound]; exact Nat.add_le_add_right (Nat.add_le_add (hf _) (hg _)) _
  | pair f g hf hg => simp only [dispatches, workBound]; exact Nat.add_le_add_right (Nat.add_le_add (hf _) (hg _)) _
  | copair f g hf hg =>
    cases x with
    | inl x => exact Nat.add_le_add_right ((hf x).trans (Nat.le_max_left _ _)) _
    | inr x => exact Nat.add_le_add_right ((hg x).trans (Nat.le_max_right _ _)) _
  | _ => exact Nat.le_refl _

/-- Each node has a preallocated frame and input/output copies. Reserving both
case arms bounds the selected arm without allocating during interpretation. -/
def arena {a b : Ty} (c : Code Prim a b) : Nat :=
  match c with
  | .comp g f | .pair f g | .copair f g =>
      arena f + arena g + 1 + width a + width b
  | .curry f => arena f + 1 + width a + width b
  | _ => 1 + width a + width b

/-- Operational derivation for the analyzed raw subset. Composition follows
actual evaluation order; case enters just the selected arm. -/
inductive Executes : {a b : Ty} → Code Prim a b → Val Bool a → Val Bool b → Nat → Prop where
  | ident (x : Val Bool a) : Executes .ident x x 1
  | terminal (x : Val Bool a) : Executes .terminal x () 1
  | fst (x : Val Bool (.prod a b)) : Executes .fst x x.1 1
  | snd (x : Val Bool (.prod a b)) : Executes .snd x x.2 1
  | primitive (p : Prim a b) (x : Val Bool a) : Executes (.primitive p) x (meaning p x) 1
  | inl (x : Val Bool a) : Executes (.inl (b := b)) x (.inl x) 1
  | inr (x : Val Bool b) : Executes (.inr (a := a)) x (.inr x) 1
  | dist (x : Val Bool (.prod a (.sum b c))) : Executes .dist x (distribute x) 1
  | comp (hf : Executes f x y wf) (hg : Executes g y z wg) :
      Executes (.comp g f) x z (wf + wg + 1)
  | pair (hf : Executes f x y wf) (hg : Executes g x z wg) :
      Executes (.pair f g) x (y,z) (wf + wg + 1)
  | left (hf : Executes f x y w) : Executes (.copair f g) (.inl x) y (w+1)
  | right (hg : Executes g x y w) : Executes (.copair f g) (.inr x) y (w+1)

theorem executes (c : Code Prim a b) (h : analyzable c = true) (x : Val Bool a) :
    Executes c x (run meaning c x) (dispatches c x) := by
  induction c with
  | comp g f hg hf =>
    simp only [analyzable, Bool.and_eq_true] at h
    exact .comp (hf h.1.2 x) (hg h.2 _)
  | pair f g hf hg =>
    simp only [analyzable, Bool.and_eq_true] at h
    exact .pair (hf h.1.2 x) (hg h.2 x)
  | copair f g hf hg =>
    simp only [analyzable, Bool.and_eq_true] at h
    cases x with
    | inl x => exact .left (hf h.1.2 x)
    | inr x => exact .right (hg h.2 x)
  | curry => simp [analyzable] at h
  | apply => simp [analyzable] at h
  | ident => exact .ident x
  | terminal => exact .terminal x
  | fst => exact .fst x
  | snd => exact .snd x
  | primitive p => exact .primitive p x
  | inl => exact .inl x
  | inr => exact .inr x
  | dist => exact .dist x

theorem code_analyzable : analyzable code = true := rfl

theorem regional_execution (x : Input) :
    Executes code ((),x) (oracle x) (dispatches code ((),x)) := by
  rw [← correct]
  exact executes code code_analyzable ((),x)

end Rich

namespace Plan
/-- Retained payload cells; unit state occupies no payload cell. -/
def retained : Plan A B → Nat
  | .delay | .direct | .fused => 1
  | .seq p q | .par p q => p.retained + q.retained
  | _ => 0

def outputCells : Plan A B → Nat
  | .encode => 2
  | .duplicate => 6
  | .seq _ q => q.outputCells
  | .par p q => p.outputCells + q.outputCells
  | _ => 1

def inputCells : Plan A B → Nat
  | .rich | .direct | .duplicate => 3
  | .decode => 2
  | .seq p _ => p.inputCells
  | .par p q => p.inputCells + q.inputCells
  | _ => 1

/-- Dispatch plus explicit copy/validation operations. The native reference is
not analyzed by this routine; admission below keeps that absence explicit. -/
def work : Plan A B → Nat
  | .rich => Rich.workBound Rich.code
  | .delay => Indefinite.delay.body.work
  | .negate => negateProgram.body.work
  | .bareNegate => Circuit.not.work
  | .fused => fusedProgram.body.work
  | .encode => 3 -- read, complement, pair copy
  | .decode => 4 -- complement, equality, branch, projection copy
  | .side => 1
  | .duplicate => 6
  | .direct => 1
  | .seq p q | .par p q => p.work + q.work + 1 + p.outputCells

/-- Region arenas are reclaimed after copying their output. The right region
runs with that output live. All retained states are accounted outside this list.
A composition frame is live throughout. Parallel nodes run left before right. -/
def checkpoints : Plan A B → List Nat
  | .rich => [Rich.arena Rich.code]
  | .delay => [Indefinite.delay.body.arena]
  | .negate => [negateProgram.body.arena]
  | .bareNegate => [Circuit.not.arena]
  | .fused => [fusedProgram.body.arena]
  | .encode => [1+1+2] -- frame, input, redundant output
  | .decode => [1+2+1+1] -- frame, pair, validation bit, decoded value
  | .side => [1+1+1]
  | .duplicate => [1+3+6]
  | .direct => []
  | .seq p q =>
      (p.checkpoints.map (1 + p.outputCells + ·)) ++
        [1 + p.outputCells] ++
        (q.checkpoints.map (1 + p.outputCells + ·)) ++
        [1 + p.outputCells + q.outputCells]
  | .par p q =>
      (p.checkpoints.map (1 + q.inputCells + p.outputCells + ·)) ++
        [1 + q.inputCells + p.outputCells] ++
        (q.checkpoints.map (1 + p.outputCells + ·)) ++
        [1 + p.outputCells + q.outputCells]

def peak (xs : List Nat) : Nat := xs.foldr max 0

theorem le_peak (xs : List Nat) (n : Nat) (h : n ∈ xs) : n ≤ peak xs := by
  induction xs with
  | nil => simp at h
  | cons x xs ih =>
    simp only [List.mem_cons] at h
    cases h with
    | inl h => subst n; exact Nat.le_max_left _ _
    | inr h => exact (ih h).trans (Nat.le_max_right _ _)

def storage (p : Plan A B) := p.retained + peak p.checkpoints

def analyzed : Plan A B → Bool
  | .direct => false
  | .seq p q | .par p q => p.analyzed && q.analyzed
  | _ => true

/-- A checkpoint bound includes every retained region state, even while its
arena is inactive. The live list describes the declared reclaim/copy schedule. -/
theorem checkpoint_bound (p : Plan A B) (n : Nat) (h : n ∈ p.checkpoints) :
    p.retained + n ≤ p.storage := Nat.add_le_add_left (le_peak _ _ h) _

/-- Actual regional dispatch accounting for this input and continuation. -/
def stepWork : (p : Plan A B) → A → p.State → Nat
  | .rich, x, _ => Rich.dispatches Rich.code ((),x)
  | .seq p q, x, s =>
      p.stepWork x s.1 + q.stepWork (p.machine.step (x,s.1)).1 s.2 + 1 + p.outputCells
  | .par p q, x, s =>
      p.stepWork x.1 s.1 + q.stepWork x.2 s.2 + 1 + p.outputCells
  | p, _, _ => p.work

theorem stepWork_le (p : Plan A B) (x : A) (s : p.State) : p.stepWork x s ≤ p.work := by
  induction p with
  | rich => exact Rich.dispatches_le _ _
  | seq p q hp hq =>
    simp only [stepWork, work]
    exact Nat.add_le_add_right (Nat.add_le_add_right (Nat.add_le_add (hp _ _) (hq _ _)) _) _
  | par p q hp hq =>
    simp only [stepWork, work]
    exact Nat.add_le_add_right (Nat.add_le_add_right (Nat.add_le_add (hp _ _) (hq _ _)) _) _
  | _ => exact Nat.le_refl _

/-- Local evaluation evidence follows the actual selected leaves. Native direct
execution has no resource derivation in this analyzer. -/
def Operational : (p : Plan A B) → A → p.State → Prop
  | .rich, x, _ => Rich.Executes Rich.code ((),x) (Rich.execute x)
      (Rich.dispatches Rich.code ((),x))
  | .delay, x, s => Circuit.Executes Indefinite.delay.body (x,s)
      (Indefinite.delay.machine.step (x,s)) Indefinite.delay.body.work Indefinite.delay.body.arena
  | .negate, x, s => Circuit.Executes negateProgram.body (x,s)
      (negateProgram.machine.step (x,s)) negateProgram.body.work negateProgram.body.arena
  | .bareNegate, x, _ => Circuit.Executes Circuit.not x (Circuit.not.execute x)
      Circuit.not.work Circuit.not.arena
  | .fused, x, s => Circuit.Executes fusedProgram.body (x,s)
      (fusedProgram.machine.step (x,s)) fusedProgram.body.work fusedProgram.body.arena
  | .encode, x, _ => (Regional.encode x).val = (x,!x)
  | .decode, x, _ => MigrationPair.reverse x.val = some (Regional.decode x)
  | .side, x, _ => id x = x
  | .duplicate, x, _ => (x,x) = (x,x)
  | .direct, _, _ => False
  | .seq p q, x, s => p.Operational x s.1 ∧
      q.Operational (p.machine.step (x,s.1)).1 s.2
  | .par p q, x, s => p.Operational x.1 s.1 ∧ q.Operational x.2 s.2

theorem operates (p : Plan A B) (h : p.analyzed = true) (x : A) (s : p.State) :
    p.Operational x s := by
  induction p with
  | rich => exact Rich.executes _ Rich.code_analyzable _
  | delay => exact Indefinite.delay.body.executes _
  | negate => exact negateProgram.body.executes _
  | bareNegate => exact Circuit.not.executes _
  | fused => exact fusedProgram.body.executes _
  | encode => rfl
  | decode => rw [Operational, decode_correct]; exact MigrationPair.reverse_valid _ x.property
  | side => rfl
  | duplicate => rfl
  | direct => simp [analyzed] at h
  | seq p q hp hq =>
    simp only [analyzed, Bool.and_eq_true] at h
    exact ⟨hp h.1 _ _,hq h.2 _ _⟩
  | par p q hp hq =>
    simp only [analyzed, Bool.and_eq_true] at h
    exact ⟨hp h.1 _ _,hq h.2 _ _⟩

/-- These logical times are proof data, never retained by the executor. -/
def duration (p : Plan A B) (env : Indefinite.Program.Environment) (n : Nat) : Nat :=
  env.inputWait n + env.schedulerWait n + p.work + env.sinkWait n + 1

def starts (p : Plan A B) (env : Indefinite.Program.Environment) : Nat → Nat
  | 0 => 0
  | n+1 => p.starts env n + p.duration env n

theorem starts_grow (p : Plan A B) (env : Indefinite.Program.Environment) (n : Nat) :
    n ≤ p.starts env n := by
  induction n with
  | zero => exact Nat.zero_le _
  | succ n ih => simp only [starts, duration]; omega

/-- A round executes the selected regions and releases the output within the
reserved work budget. Unused budget may be idle time; it is not measured work. -/
inductive Round (p : Plan A B) (env : Indefinite.Program.Environment) (n : Nat)
    (x : A) (s : p.State) : Nat → B × p.State → Nat → Prop where
  | service (execution : p.Operational x s) (budget : p.stepWork x s ≤ p.work) :
      Round p env n x s start (p.machine.step (x,s)) (start + p.duration env n)

theorem scheduled (p : Plan A B) (h : p.analyzed = true)
    (env : Indefinite.Program.Environment) (input : Stream A) (n : Nat) :
    Round p env n (input n) (state p.machine input n) (p.starts env n)
      (output p.machine input n,state p.machine input (n+1)) (p.starts env (n+1)) :=
  .service (p.operates h _ _) (p.stepWork_le _ _)

/-- Uniform for arbitrary prefixes and internal schedule checkpoints. Resource
admission is a separate premise: semantic function execution supplies no bound. -/
theorem uniform (p : Plan A B) (_h : p.analyzed = true) (input : Stream A) (n : Nat) :
    p.stepWork (input n) (state p.machine input n) ≤ p.work ∧
    ∀ live ∈ p.checkpoints, p.retained + live ≤ p.storage :=
  ⟨p.stepWork_le _ _,p.checkpoint_bound⟩

end Plan
end FRPSpec.Regional
