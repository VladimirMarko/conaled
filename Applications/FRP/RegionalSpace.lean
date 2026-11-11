import Applications.FRP.RegionalResources

/-! Allocation derivations for actual raw and regional executions. Raw arenas
retain entered frames until region return; regional composition copies the result
before releasing that arena. All counts describe the logical copied-value model. -/
namespace FRPSpec.Regional
open Progress Progress.Feedback Applications.Circuits
namespace Rich
open CategoricalCompiler

def frame (a b : Ty) := 1 + width a + width b

/-- Allocations follow actual evaluation, including only the selected case arm. -/
def allocations {a b : Ty} (c : Code Prim a b) (x : Val Bool a) : List Nat :=
  match c with
  | .comp g f => frame a b :: (allocations f x ++ allocations g (run meaning f x))
  | .pair f g => frame a b :: (allocations f x ++ allocations g x)
  | .copair f g => frame a b :: (match x with
      | .inl y => allocations f y
      | .inr y => allocations g y)
  | _ => [frame a b]

/-- The arena trace is part of the execution judgment, not an unrelated budget.
Each constructor allocates a frame and copies its typed input/output values. -/
inductive Allocates : {a b : Ty} → Code Prim a b → Val Bool a → Val Bool b → List Nat → Prop where
  | ident (x : Val Bool a) : Allocates .ident x x [frame a a]
  | terminal (x : Val Bool a) : Allocates .terminal x () [frame a .unit]
  | fst (x : Val Bool (.prod a b)) : Allocates .fst x x.1 [frame (.prod a b) a]
  | snd (x : Val Bool (.prod a b)) : Allocates .snd x x.2 [frame (.prod a b) b]
  | primitive (p : Prim a b) (x : Val Bool a) :
      Allocates (.primitive p) x (meaning p x) [frame a b]
  | inl (x : Val Bool a) : Allocates (.inl (b := b)) x (.inl x) [frame a (.sum a b)]
  | inr (x : Val Bool b) : Allocates (.inr (a := a)) x (.inr x) [frame b (.sum a b)]
  | dist (x : Val Bool (.prod a (.sum b c))) :
      Allocates .dist x (distribute x) [frame (.prod a (.sum b c)) (.sum (.prod a b) (.prod a c))]
  | comp {f : Code Prim a b} {g : Code Prim b c}
      (hf : Allocates f x y af) (hg : Allocates g y z ag) :
      Allocates (.comp g f) x z (frame a c :: (af ++ ag))
  | pair {f : Code Prim a b} {g : Code Prim a c}
      (hf : Allocates f x y af) (hg : Allocates g x z ag) :
      Allocates (.pair f g) x (y,z) (frame a (.prod b c) :: (af ++ ag))
  | left {f : Code Prim a c} {g : Code Prim b c} (hf : Allocates f x y af) :
      Allocates (.copair f g) (.inl x) y (frame (.sum a b) c :: af)
  | right {f : Code Prim a c} {g : Code Prim b c} (hg : Allocates g x y ag) :
      Allocates (.copair f g) (.inr x) y (frame (.sum a b) c :: ag)

theorem Allocates.result (h : Allocates c x y trace) : y = run meaning c x := by
  induction h <;> simp_all [CategoricalCompiler.run]

theorem allocates (c : Code Prim a b) (h : analyzable c = true) (x : Val Bool a) :
    Allocates c x (run meaning c x) (allocations c x) := by
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

theorem allocations_le (c : Code Prim a b) (x : Val Bool a) :
    (allocations c x).sum ≤ arena c := by
  induction c with
  | comp g f hg hf =>
    simp only [allocations, List.sum_cons, List.sum_append, arena, frame]
    have := hf x; have := hg (run meaning f x); omega
  | pair f g hf hg =>
    simp only [allocations, List.sum_cons, List.sum_append, arena, frame]
    have := hf x; have := hg x; omega
  | copair f g hf hg =>
    cases x with
    | inl x =>
      simp only [allocations, List.sum_cons, arena, frame]
      have := hf x; omega
    | inr x =>
      simp only [allocations, List.sum_cons, arena, frame]
      have := hg x; omega
  | curry => simp only [allocations, List.sum_cons, List.sum_nil, arena, frame]; omega
  | _ => simp [allocations, arena, frame]

end Rich

/-- Running arena occupancies before regional reclamation. Every allocation
prefix occurs, including the empty prefix. This is proof data. -/
def occupancies (allocations : List Nat) : List Nat :=
  (List.range (allocations.length + 1)).map (fun n => (allocations.take n).sum)

theorem take_sum_le (xs : List Nat) (n : Nat) : (xs.take n).sum ≤ xs.sum := by
  induction xs generalizing n with
  | nil => simp
  | cons x xs ih =>
    cases n with
    | zero => simp
    | succ n => simpa using Nat.add_le_add_left (ih n) x

/-- Every actual live observation has a dominating static checkpoint. -/
def Dominated (actual bound : List Nat) : Prop :=
  ∀ n ∈ actual, ∃ m ∈ bound, n ≤ m

theorem occupancies_dominated (xs : List Nat) (b : Nat) (h : xs.sum ≤ b) :
    Dominated (occupancies xs) [b] := by
  intro n hn
  obtain ⟨k,_,rfl⟩ := List.mem_map.mp hn
  exact ⟨b,by simp,(take_sum_le xs k).trans h⟩

theorem dominated_refl (xs : List Nat) : Dominated xs xs := fun n hn => ⟨n,hn,Nat.le_refl _⟩

theorem dominated_map (k : Nat) (h : Dominated xs ys) :
    Dominated (xs.map (k + ·)) (ys.map (k + ·)) := by
  intro n hn
  obtain ⟨x,hx,rfl⟩ := List.mem_map.mp hn
  obtain ⟨y,hy,hxy⟩ := h x hx
  exact ⟨k+y,List.mem_map.mpr ⟨y,hy,rfl⟩,Nat.add_le_add_left hxy _⟩

theorem dominated_append (h : Dominated xs ys) (h' : Dominated xs' ys') :
    Dominated (xs ++ xs') (ys ++ ys') := by
  intro n hn
  cases List.mem_append.mp hn with
  | inl hn => obtain ⟨m,hm,hle⟩ := h n hn; exact ⟨m,List.mem_append_left _ hm,hle⟩
  | inr hn => obtain ⟨m,hm,hle⟩ := h' n hn; exact ⟨m,List.mem_append_right _ hm,hle⟩

namespace Plan
/-- Left buffer is reserved during left evaluation. Right input is additionally
retained during a parallel left branch. Left arena is then reclaimed; right runs
with the copied left value; both outputs coexist before returning. -/
def wireTrace (heldInput leftOutput rightOutput : Nat) (left right : List Nat) : List Nat :=
  left.map (1 + heldInput + leftOutput + ·) ++
    [1 + heldInput + leftOutput] ++ right.map (1 + leftOutput + ·) ++
    [1 + leftOutput + rightOutput]

theorem wire_dominated (h : Dominated xs ys) (h' : Dominated xs' ys') :
    Dominated (wireTrace i o r xs xs') (wireTrace i o r ys ys') :=
  dominated_append
    (dominated_append (dominated_append (dominated_map _ h) (dominated_refl _))
      (dominated_map _ h')) (dominated_refl _)

/-- Space execution exposes the executed values and continuation. Leaf allocation
judgments are composed in exactly the same order as the value executor. -/
inductive SpaceRuns : {A B : Type} → (p : Plan A B) → A → p.State → B × p.State → List Nat → Prop where
  | rich (h : Rich.Allocates Rich.code ((),x) y alloc) :
      SpaceRuns .rich x s (y,⟨⟩) (occupancies alloc)
  | delay (h : Circuit.Executes Indefinite.delay.body (x,s) result nodeWork arenaSize) :
      SpaceRuns .delay x s result (occupancies Indefinite.delay.body.allocations)
  | negate (h : Circuit.Executes negateProgram.body (x,s) result nodeWork arenaSize) :
      SpaceRuns .negate x s result (occupancies negateProgram.body.allocations)
  | bareNegate (h : Circuit.Executes Circuit.not x y nodeWork arenaSize) :
      SpaceRuns .bareNegate x s (y,⟨⟩) (occupancies Circuit.not.allocations)
  | fused (h : Circuit.Executes fusedProgram.body (x,s) result nodeWork arenaSize) :
      SpaceRuns .fused x s result (occupancies fusedProgram.body.allocations)
  | encode (x : Bool) : SpaceRuns .encode x s (Regional.encode x,⟨⟩) [2,3,4]
  | decode (x : Redundant) (h : MigrationPair.reverse x.val = some y) :
      SpaceRuns .decode x s (y,⟨⟩) [3,4,5]
  | side (x : Bool) : SpaceRuns .side x s (x,⟨⟩) [2,3]
  | duplicate (x : Input) : SpaceRuns .duplicate x s ((x,x),⟨⟩) [4,10]
  | seq {p : Plan A B} {q : Plan B C} {s s' : p.State} {t t' : q.State}
      {leftTrace rightTrace : List Nat}
      (hp : SpaceRuns p x s (y,s') leftTrace) (hq : SpaceRuns q y t (z,t') rightTrace) :
      SpaceRuns (.seq p q) x (s,t) (z,(s',t'))
        (wireTrace 0 p.outputCells q.outputCells leftTrace rightTrace)
  | par {p : Plan A B} {q : Plan C D} {s s' : p.State} {t t' : q.State}
      {leftTrace rightTrace : List Nat}
      (hp : SpaceRuns p x s (y,s') leftTrace) (hq : SpaceRuns q z t (v,t') rightTrace) :
      SpaceRuns (.par p q) (x,z) (s,t) ((y,v),(s',t'))
        (wireTrace q.inputCells p.outputCells q.outputCells leftTrace rightTrace)

theorem SpaceRuns.result {p : Plan A B} {x : A} {s : p.State}
    {result : B × p.State} {trace : List Nat} (h : SpaceRuns p x s result trace) : result = p.machine.step (x,s) := by
  induction h with
  | rich h => exact Prod.ext h.result rfl
  | delay h => exact h.result.1
  | negate h => exact h.result.1
  | bareNegate h => exact Prod.ext h.result.1 rfl
  | fused h => exact h.result.1
  | encode => rfl
  | decode x h => simp [machine, Feedback.pure, Regional.decode, h]; rfl
  | side => rfl
  | duplicate => rfl
  | seq hp hq ihp ihq => simp only [machine, Feedback.seq, ← ihp, ← ihq]; rfl
  | par hp hq ihp ihq => simp only [machine, Feedback.par, ← ihp, ← ihq]; rfl

/-- The trace is input-sensitive for raw cases and follows executed intermediate
values. No budget is used to manufacture this trace. -/
def liveTrace : (p : Plan A B) → A → p.State → List Nat
  | .rich, x, _ => occupancies (Rich.allocations Rich.code ((),x))
  | .delay, _, _ => occupancies Indefinite.delay.body.allocations
  | .negate, _, _ => occupancies negateProgram.body.allocations
  | .bareNegate, _, _ => occupancies Circuit.not.allocations
  | .fused, _, _ => occupancies fusedProgram.body.allocations
  | .encode, _, _ => [2,3,4]
  | .decode, _, _ => [3,4,5]
  | .side, _, _ => [2,3]
  | .duplicate, _, _ => [4,10]
  | .direct, _, _ => []
  | .seq p q, x, s => wireTrace 0 p.outputCells q.outputCells
      (p.liveTrace x s.1) (q.liveTrace (p.machine.step (x,s.1)).1 s.2)
  | .par p q, x, s => wireTrace q.inputCells p.outputCells q.outputCells
      (p.liveTrace x.1 s.1) (q.liveTrace x.2 s.2)

theorem space_runs (p : Plan A B) (h : p.analyzed = true) (x : A) (s : p.State) :
    SpaceRuns p x s (p.machine.step (x,s)) (p.liveTrace x s) := by
  induction p with
  | rich => exact .rich (Rich.allocates _ Rich.code_analyzable _)
  | delay => exact .delay (Indefinite.delay.body.executes _)
  | negate => exact .negate (negateProgram.body.executes _)
  | bareNegate => exact .bareNegate (Circuit.not.executes _)
  | fused => exact .fused (fusedProgram.body.executes _)
  | encode => exact .encode x
  | decode => exact .decode x (by rw [decode_correct]; exact MigrationPair.reverse_valid _ x.property)
  | side => exact .side x
  | duplicate => exact .duplicate x
  | direct => simp [analyzed] at h
  | seq p q hp hq =>
    simp only [analyzed, Bool.and_eq_true] at h
    exact .seq (hp h.1 _ _) (hq h.2 _ _)
  | par p q hp hq =>
    simp only [analyzed, Bool.and_eq_true] at h
    exact .par (hp h.1 _ _) (hq h.2 _ _)

theorem live_dominated (p : Plan A B) (x : A) (s : p.State) :
    Dominated (p.liveTrace x s) p.checkpoints := by
  induction p with
  | rich => exact occupancies_dominated _ _ (Rich.allocations_le _ _)
  | delay => exact occupancies_dominated _ _ (Nat.le_of_eq Indefinite.delay.body.allocations_sum)
  | negate => exact occupancies_dominated _ _ (Nat.le_of_eq negateProgram.body.allocations_sum)
  | bareNegate => exact occupancies_dominated _ _ (Nat.le_of_eq Circuit.not.allocations_sum)
  | fused => exact occupancies_dominated _ _ (Nat.le_of_eq fusedProgram.body.allocations_sum)
  | encode | decode | side | duplicate => simp [liveTrace, checkpoints, Dominated]
  | direct => simp [liveTrace, Dominated]
  | seq p q hp hq => exact wire_dominated (hp _ _) (hq _ _)
  | par p q hp hq => exact wire_dominated (hp _ _) (hq _ _)

theorem live_bound (p : Plan A B) (x : A) (s : p.State) (n : Nat)
    (hn : n ∈ p.liveTrace x s) : p.retained + n ≤ p.storage := by
  obtain ⟨m,hm,hnm⟩ := p.live_dominated x s n hn
  exact (Nat.add_le_add_left hnm _).trans (p.checkpoint_bound m hm)

/-- Capacity now bounds a trace whose derivation evaluates the actual plan. -/
theorem sufficient_storage (p : Plan A B) (h : p.analyzed = true) (capacity : Nat)
    (fits : p.storage ≤ capacity) (x : A) (s : p.State) :
    ∃ trace, SpaceRuns p x s (p.machine.step (x,s)) trace ∧
      ∀ live ∈ trace, p.retained + live ≤ capacity :=
  ⟨p.liveTrace x s,p.space_runs h x s,fun live hlive => (p.live_bound x s live hlive).trans fits⟩

/-- Every stream prefix has a sufficient-space derivation for its next tick. -/
theorem uniform (p : Plan A B) (h : p.analyzed = true) (input : Stream A) (n : Nat) :
    SpaceRuns p (input n) (state p.machine input n)
      (output p.machine input n,state p.machine input (n+1))
      (p.liveTrace (input n) (state p.machine input n)) ∧
    ∀ live ∈ p.liveTrace (input n) (state p.machine input n),
      p.retained + live ≤ p.storage :=
  ⟨p.space_runs h _ _,p.live_bound _ _⟩

/-- Work and space derivations describe the same transition. -/
inductive Round (p : Plan A B) (env : Indefinite.Program.Environment) (n : Nat)
    (x : A) (s : p.State) : Nat → B × p.State → Nat → Prop where
  | service (execution : p.Operational x s) (budget : p.stepWork x s ≤ p.work)
      (space : SpaceRuns p x s (p.machine.step (x,s)) (p.liveTrace x s)) :
      Round p env n x s start (p.machine.step (x,s)) (start + p.duration env n)

theorem scheduled (p : Plan A B) (h : p.analyzed = true)
    (env : Indefinite.Program.Environment) (input : Stream A) (n : Nat) :
    Round p env n (input n) (state p.machine input n) (p.starts env n)
      (output p.machine input n,state p.machine input (n+1)) (p.starts env (n+1)) :=
  .service (p.operates h _ _) (p.stepWork_le _ _) (p.space_runs h _ _)

end Plan
end FRPSpec.Regional
