import Applications.Incremental.VectorSumCost
import Applications.Resources.FoldCompiler

/-! Compiled scalar maps with retained contributions. Indexed storage has the
owned-store meaning of `VectorSum.Cost`, not a Lean runtime complexity claim. -/
namespace Incremental.MappedAggregate
open Resources VectorSum
open FirstOrderCompiler

/-- A scalar source and its primitive interpretation. Compilation itself is
outside the execution tariff; `cost` counts execution of the compiled body. -/
structure Scalar (G : Type) where
  Prim : Ty → Ty → Type
  meaning : {a b : Ty} → Prim a b → Val G a → Val G b
  charge : {a b : Ty} → Prim a b → Nat
  body : Term Prim [.base] .base

namespace Scalar
variable {G : Type}
def eval (g : Scalar G) (x : G) : G := FirstOrderCompiler.eval g.meaning g.body ((), x)
def exec (g : Scalar G) (x : G) : Measured G Nat :=
  FirstOrderCompiler.compile (FoldCompiler.scalar g.meaning g.charge) g.body ((), x)
def cost (g : Scalar G) : Nat := FoldCompiler.bodyCost g.charge g.body
@[simp] theorem exec_value (g : Scalar G) (x : G) : (g.exec x).1 = g.eval x :=
  FirstOrderCompiler.compile_sound _ (FoldCompiler.scalarSound g.meaning g.charge) g.body _
@[simp] theorem exec_cost (g : Scalar G) (x : G) : (g.exec x).2 = g.cost :=
  FoldCompiler.scalar_cost g.meaning g.charge g.body _
end Scalar

variable {G : Type} [AddCommGroup G] {n : Nat}

def mapped (g : G → G) (v : Values G n) : Values G n := g ∘ v
def mappedPatch (g : G → G) (p : Patch G n) : Patch G n := p.map (fun a => (a.1, g a.2))

omit [AddCommGroup G] in
theorem mapped_assign (g : G → G) (v : Values G n) (a : Assignment G n) :
    mapped g (assign v a) = assign (mapped g v) (a.1, g a.2) := by
  funext i
  by_cases h : i = a.1 <;> simp [mapped, assign, Function.update_apply, h]

omit [AddCommGroup G] in
theorem mapped_applyPatch (g : G → G) (v : Values G n) (p : Patch G n) :
    mapped g (applyPatch v p) = applyPatch (mapped g v) (mappedPatch g p) := by
  induction p generalizing v with
  | nil => rfl
  | cons a p ih => simpa [applyPatch, mappedPatch, mapped_assign] using ih (assign v a)

def specification (g : G → G) (v : Values G n) : G := total (mapped g v)
def Valid (g : G → G) (v : Values G n) (s : State G n) : Prop := VectorSum.Valid (mapped g v) s

@[reducible] def realization (g : G → G) (n : Nat) : Stateful.Ops (object G n) (additive G) where
  State := State G n
  init v := VectorSum.init (mapped g v)
  repair s p := (VectorSum.realization G n).repair s (mappedPatch g p)
  observe := State.sum

theorem realization_laws (g : G → G) :
    Stateful.Laws (specification g) (realization g n) (Valid g) where
  init v := VectorSum.realization_laws.init (mapped g v)
  repair v s p h := by
    simpa only [Valid, object, mapped_applyPatch] using
      VectorSum.realization_laws.repair (mapped g v) s (mappedPatch g p) h
  observe v s h := VectorSum.realization_laws.observe (mapped g v) s h
  boundary v s p h := VectorSum.realization_laws.boundary (mapped g v) s (mappedPatch g p) h

/-- The downstream scalar retains its input and output. Evaluating it again on
an updated scalar is intentional; it never rescans the original vector. -/
@[reducible] def post (h : G → G) : Stateful.Ops (additive G) (additive G) where
  State := G × G
  init x := (x, h x)
  repair s d := let y := h (s.1 + d); ((s.1 + d, y), y - s.2)
  observe := Prod.snd

def PostValid (h : G → G) (x : G) (s : G × G) : Prop := s = (x, h x)

theorem post_laws (h : G → G) : Stateful.Laws h (post h) (PostValid h) where
  init _ := rfl
  repair x s d hs := by cases hs; rfl
  observe x s hs := by cases hs; rfl
  boundary _ _ _ _ := by dsimp [post, additive]; abel

@[reducible] def composed (g h : G → G) (n : Nat) := Stateful.comp (post h) (realization g n)

theorem composed_laws (g h : G → G) :
    Stateful.Laws (h ∘ specification g) (composed g h n)
      (Stateful.CompValid (realization g n) (post h) (Valid g) (PostValid h)) :=
  (realization_laws g).comp (post_laws h)

theorem after_patch (g h : G → G) (v : Values G n) (p : Patch G n) :
    (composed g h n).observe ((composed g h n).repair ((composed g h n).init v) p).1 =
      h (specification g (applyPatch v p)) :=
  (composed_laws g h).observe _ _ ((composed_laws g h).repair _ _ _ ((composed_laws g h).init v))

namespace Cost
open VectorSum.Cost

/-- Read, execute the compiled scalar, and allocate each contribution cell. -/
def materialize (g : Scalar G) : {n : Nat} → Values G n → Measured (Values G n) Nat
  | 0, v => Resources.pure v
  | _ + 1, v => Resources.bind (read v 0) fun x =>
      Resources.bind (g.exec x) fun y =>
      Resources.bind (materialize g (fun i => v i.succ)) fun t => prepend y t

omit [AddCommGroup G] in
theorem materialize_value (g : Scalar G) (v : Values G n) :
    (materialize g v).1 = mapped g.eval v := by
  induction n with
  | zero => funext i; exact Fin.elim0 i
  | succ n ih =>
    simp only [materialize, Resources.bind, VectorSum.Cost.read, prepend, Scalar.exec_value, ih]
    exact Fin.cons_self_tail (mapped g.eval v)

omit [AddCommGroup G] in
theorem materialize_cost (g : Scalar G) (v : Values G n) :
    (materialize g v).2 = n * (g.cost + 2) := by
  induction n with
  | zero => simp [materialize, Resources.pure]
  | succ n ih => simp [materialize, Resources.bind, VectorSum.Cost.read, prepend, ih, Nat.succ_mul]; omega

def init (g : Scalar G) (v : Values G n) : Measured (State G n) Nat :=
  Resources.bind (materialize g v) VectorSum.Cost.init

def step (g : Scalar G) (a : Assignment G n) (s : State G n) : Measured (State G n) Nat :=
  Resources.bind (g.exec a.2) fun y => VectorSum.Cost.step (a.1, y) s

def repair (g : Scalar G) (s : State G n) (p : Patch G n) : Measured (State G n × G) Nat :=
  Resources.bind (run (step g) p s) fun t =>
    Resources.bind (sub t.sum s.sum) fun d => Resources.pure (t, d)

@[simp] theorem init_value (g : Scalar G) (v : Values G n) :
    (init g v).1 = (realization g.eval n).init v := by
  simp [init, Resources.bind, materialize_value, VectorSum.Cost.init_value]

@[simp] theorem init_cost (g : Scalar G) (v : Values G n) :
    (init g v).2 = n * (g.cost + 4) + 1 := by
  simp [init, Resources.bind, materialize_cost, VectorSum.Cost.init_cost, Nat.mul_add]; omega

@[simp] theorem step_value (g : Scalar G) (a : Assignment G n) (s : State G n) :
    (step g a s).1 = VectorSum.step s (a.1, g.eval a.2) := by
  simp [step, Resources.bind]

@[simp] theorem step_cost (g : Scalar G) (a : Assignment G n) (s : State G n) :
    (step g a s).2 = g.cost + 5 := by simp [step, Resources.bind]

theorem patch_value (g : Scalar G) (s : State G n) (p : Patch G n) :
    (run (step g) p s).1 = VectorSum.patch s (mappedPatch g.eval p) := by
  induction p generalizing s with
  | nil => rfl
  | cons a p ih => simp [run_cons, ih, mappedPatch, VectorSum.patch]

@[simp] theorem repair_value (g : Scalar G) (s : State G n) (p : Patch G n) :
    (repair g s p).1 = (realization g.eval n).repair s p := by
  simp [repair, Resources.bind, sub, Resources.pure, patch_value]

@[simp] theorem repair_cost (g : Scalar G) (s : State G n) (p : Patch G n) :
    (repair g s p).2 = p.length * (g.cost + 5) + 1 := by
  simp [repair, Resources.bind, sub, Resources.pure,
    FoldCompiler.run_constant_cost (step g) (g.cost + 5) (step_cost g)]

def postInit (h : Scalar G) (x : G) : Measured (G × G) Nat :=
  Resources.bind (store x) fun u => Resources.bind (h.exec u) fun y =>
    Resources.bind (store y) fun z => Resources.pure (u, z)

def postRepair (h : Scalar G) (s : G × G) (d : G) : Measured ((G × G) × G) Nat :=
  Resources.bind (add s.1 d) fun x => Resources.bind (store x) fun u =>
  Resources.bind (h.exec u) fun y => Resources.bind (store y) fun z =>
  Resources.bind (sub z s.2) fun e => Resources.pure ((u, z), e)

def composedInit (g h : Scalar G) (v : Values G n) : Measured (State G n × (G × G)) Nat :=
  Resources.bind (init g v) fun s => Resources.bind (observe s) fun x =>
  Resources.bind (postInit h x) fun t => Resources.pure (s, t)

def composedRepair (g h : Scalar G) (s : State G n × (G × G)) (p : Patch G n) :
    Measured ((State G n × (G × G)) × G) Nat :=
  Resources.bind (repair g s.1 p) fun t => Resources.bind (postRepair h s.2 t.2) fun u =>
    Resources.pure ((t.1, u.1), u.2)

@[simp] theorem composedInit_value (g h : Scalar G) (v : Values G n) :
    (composedInit g h v).1 = (composed g.eval h.eval n).init v := by
  simp [composedInit, postInit, Resources.bind, Resources.pure, store, observe, emit, post]

@[simp] theorem composedInit_cost (g h : Scalar G) (v : Values G n) :
    (composedInit g h v).2 = n * (g.cost + 4) + h.cost + 4 := by
  simp [composedInit, postInit, Resources.bind, Resources.pure, store, observe, emit]; omega

@[simp] theorem composedRepair_value (g h : Scalar G) (s : State G n × (G × G)) (p : Patch G n) :
    (composedRepair g h s p).1 = (composed g.eval h.eval n).repair s p := by
  simp [composedRepair, postRepair, Resources.bind, Resources.pure, store, VectorSum.Cost.add, sub, post]

@[simp] theorem composedRepair_cost (g h : Scalar G) (s : State G n × (G × G)) (p : Patch G n) :
    (composedRepair g h s p).2 = p.length * (g.cost + 5) + h.cost + 5 := by
  simp [composedRepair, postRepair, Resources.bind, Resources.pure, store, VectorSum.Cost.add, sub]; omega

/-- Publish both the boundary delta and the scalar output after every patch.
The initial output is also published, including for the empty workload. -/
def batch (g h : Scalar G) (p : Patch G n) (s : State G n × (G × G)) :
    Measured (State G n × (G × G)) Nat :=
  Resources.bind (composedRepair g h s p) fun t =>
  Resources.bind (emit t.2) fun _ => Resources.bind (emit t.1.2.2) fun _ => Resources.pure t.1

def workload (g h : Scalar G) (v : Values G n) (ps : List (Patch G n)) :
    Measured (State G n × (G × G)) Nat :=
  Resources.bind (composedInit g h v) fun s =>
  Resources.bind (emit s.2.2) fun _ => run (batch g h) ps s

theorem batches_cost (g h : Scalar G) (s : State G n × (G × G)) (ps : List (Patch G n)) :
    (run (batch g h) ps s).2 = assignments ps * (g.cost + 5) + ps.length * (h.cost + 7) := by
  induction ps generalizing s with
  | nil => simp [assignments]
  | cons p ps ih =>
    simp [run_cons, batch, Resources.bind, emit, Resources.pure, ih, assignments,
      Nat.add_mul, Nat.succ_mul]; omega

theorem workload_cost (g h : Scalar G) (v : Values G n) (ps : List (Patch G n)) :
    (workload g h v ps).2 = n * (g.cost + 4) + h.cost + 5 +
      assignments ps * (g.cost + 5) + ps.length * (h.cost + 7) := by
  simp [workload, Resources.bind, emit, batches_cost]; omega

theorem workload_valid (g h : Scalar G) (v : Values G n) (ps : List (Patch G n)) :
    Stateful.CompValid (realization g.eval n) (post h.eval) (Valid g.eval) (PostValid h.eval)
      (ps.foldl applyPatch v) (workload g h v ps).1 := by
  have aux : ∀ ps (v : Values G n) s,
      Stateful.CompValid (realization g.eval n) (post h.eval) (Valid g.eval) (PostValid h.eval) v s →
      Stateful.CompValid (realization g.eval n) (post h.eval) (Valid g.eval) (PostValid h.eval)
        (ps.foldl applyPatch v) (run (batch g h) ps s).1 := by
    intro ps
    induction ps with
    | nil => intro v s hs; exact hs
    | cons p ps ih =>
      intro v s hs
      apply ih
      simp only [batch, Resources.bind, emit, Resources.pure]
      rw [composedRepair_value]
      exact (composed_laws g.eval h.eval).repair v s p hs
  simpa [workload, Resources.bind, emit] using aux ps v _ ((composed_laws g.eval h.eval).init v)

theorem workload_output (g h : Scalar G) (v : Values G n) (ps : List (Patch G n)) :
    (workload g h v ps).1.2.2 = h.eval (specification g.eval (ps.foldl applyPatch v)) :=
  (composed_laws g.eval h.eval).observe _ _ (workload_valid g h v ps)

/-- The measured repair publishes the same exact finite change as the retained
semantic implementation, for every state satisfying its input relation. -/
theorem composedRepair_boundary (g h : Scalar G) (v : Values G n)
    (s : State G n × (G × G)) (p : Patch G n)
    (hs : Stateful.CompValid (realization g.eval n) (post h.eval)
      (Valid g.eval) (PostValid h.eval) v s) :
    s.2.2 + (composedRepair g h s p).1.2 = (composedRepair g h s p).1.1.2.2 := by
  rw [composedRepair_value]
  exact (composed_laws g.eval h.eval).boundary v s p hs

/-- A recomputation scan executes the same compiled map and scalar tariff,
without allocating a contribution cache. -/
def scan (g : Scalar G) : {n : Nat} → Values G n → Measured G Nat
  | 0, _ => Resources.pure 0
  | _ + 1, v => Resources.bind (read v 0) fun x =>
    Resources.bind (g.exec x) fun y => Resources.bind (scan g (fun i => v i.succ)) fun z =>
    VectorSum.Cost.add y z

theorem scan_value (g : Scalar G) (v : Values G n) :
    (scan g v).1 = specification g.eval v := by
  induction n with
  | zero => simp [scan, Resources.pure, specification, total]
  | succ n ih =>
    simp [scan, Resources.bind, VectorSum.Cost.read, VectorSum.Cost.add, ih,
      specification, total, mapped, Fin.sum_univ_succ]

theorem scan_cost (g : Scalar G) (v : Values G n) :
    (scan g v).2 = n * (g.cost + 2) := by
  induction n with
  | zero => simp [scan, Resources.pure]
  | succ n ih =>
    simp [scan, Resources.bind, VectorSum.Cost.read, VectorSum.Cost.add, ih, Nat.succ_mul]; omega

/-- The baseline owns a copied raw store and retains the previous output for
emitting a boundary delta. It rebuilds the scalar sum after each patch. -/
def recomputeInit (g h : Scalar G) (v : Values G n) : Measured (Values G n × G) Nat :=
  Resources.bind (copy v) fun w => Resources.bind (scan g w) fun x =>
  Resources.bind (h.exec x) fun y => Resources.bind (store y) fun z =>
  Resources.bind (emit z) fun _ => Resources.pure (w, z)

def rawStep (a : Assignment G n) (v : Values G n) : Measured (Values G n) Nat :=
  write v a.1 a.2

omit [AddCommGroup G] in
theorem rawPatch_value (v : Values G n) (p : Patch G n) :
    (run rawStep p v).1 = applyPatch v p := by rw [run_state]; rfl

def recomputeBatch (g h : Scalar G) (p : Patch G n) (s : Values G n × G) :
    Measured (Values G n × G) Nat :=
  Resources.bind (run rawStep p s.1) fun v =>
  Resources.bind (scan g v) fun x => Resources.bind (h.exec x) fun y =>
  Resources.bind (store y) fun z => Resources.bind (sub z s.2) fun d =>
  Resources.bind (emit d) fun _ => Resources.bind (emit z) fun _ => Resources.pure (v, z)

def recompute (g h : Scalar G) (v : Values G n) (ps : List (Patch G n)) :
    Measured (Values G n × G) Nat :=
  Resources.bind (recomputeInit g h v) (run (recomputeBatch g h) ps)

theorem recomputeInit_value (g h : Scalar G) (v : Values G n) :
    (recomputeInit g h v).1 = (v, h.eval (specification g.eval v)) := by
  simp [recomputeInit, Resources.bind, Resources.pure, copy_value, scan_value, store, emit]

theorem recomputeBatch_value (g h : Scalar G) (p : Patch G n) (s : Values G n × G) :
    (recomputeBatch g h p s).1 =
      (applyPatch s.1 p, h.eval (specification g.eval (applyPatch s.1 p))) := by
  simp [recomputeBatch, Resources.bind, Resources.pure, rawPatch_value, scan_value, store, emit, sub]

theorem recompute_output (g h : Scalar G) (v : Values G n) (ps : List (Patch G n)) :
    (recompute g h v ps).1 = (ps.foldl applyPatch v,
      h.eval (specification g.eval (ps.foldl applyPatch v))) := by
  have aux : ∀ ps (v : Values G n),
      (run (recomputeBatch g h) ps (v, h.eval (specification g.eval v))).1 =
      (ps.foldl applyPatch v, h.eval (specification g.eval (ps.foldl applyPatch v))) := by
    intro ps
    induction ps with
    | nil => intro v; rfl
    | cons p ps ih => intro v; simpa only [run_cons, recomputeBatch_value, List.foldl_cons] using ih (applyPatch v p)
  simpa only [recompute, Resources.bind, recomputeInit_value] using aux ps v

theorem recomputeInit_cost (g h : Scalar G) (v : Values G n) :
    (recomputeInit g h v).2 = n * (g.cost + 4) + h.cost + 2 := by
  simp [recomputeInit, Resources.bind, Resources.pure, copy_cost, scan_cost, store, emit, Nat.mul_add]; omega

theorem recomputeBatch_cost (g h : Scalar G) (p : Patch G n) (s : Values G n × G) :
    (recomputeBatch g h p s).2 = p.length + n * (g.cost + 2) + h.cost + 4 := by
  have rawCost : (run rawStep p s.1).2 = p.length := by
    simpa using FoldCompiler.run_constant_cost rawStep 1 (fun _ _ => rfl) p s.1
  simp [recomputeBatch, Resources.bind, Resources.pure, rawCost, scan_cost, store, emit, sub]; omega

theorem recompute_cost (g h : Scalar G) (v : Values G n) (ps : List (Patch G n)) :
    (recompute g h v ps).2 = n * (g.cost + 4) + h.cost + 2 + assignments ps +
      ps.length * (n * (g.cost + 2) + h.cost + 4) := by
  have aux : ∀ ps (s : Values G n × G), (run (recomputeBatch g h) ps s).2 =
      assignments ps + ps.length * (n * (g.cost + 2) + h.cost + 4) := by
    intro ps
    induction ps with
    | nil => intro s; simp [assignments]
    | cons p ps ih =>
      intro s
      simp [run_cons, recomputeBatch_cost, ih, assignments, Nat.succ_mul]; omega
  simp [recompute, Resources.bind, recomputeInit_cost, aux]; omega

/-- Complete workload comparison, including setup and all observations. The
right side is the exact workload condition, not an asymptotic promise. -/
theorem repair_le_recompute_iff (g h : Scalar G) (v : Values G n) (ps : List (Patch G n)) :
    (workload g h v ps).2 ≤ (recompute g h v ps).2 ↔
      3 + assignments ps * (g.cost + 4) + 3 * ps.length ≤ ps.length * (n * (g.cost + 2)) := by
  rw [workload_cost, recompute_cost]
  simp only [Nat.mul_add]
  omega

theorem equal_outputs (g h : Scalar G) (v : Values G n) (ps : List (Patch G n)) :
    (workload g h v ps).1.2.2 = (recompute g h v ps).1.2 := by
  rw [workload_output, recompute_output]

end Cost
end Incremental.MappedAggregate
