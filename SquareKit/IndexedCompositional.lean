import SquareKit.CompositionalCoalgebra

/-! Finite derivative templates in families over a fixed index type.
Both constructors and transitions may change fibers. Output types remain indexed
by the semantic sort; no state indices or selected witnesses are erased. -/
namespace SquareKit.IndexedCompositional
universe i o a x y z d

structure Signature (I : Type i) where
  Op : I → Type o
  arity : {j : I} → Op j → Nat
  child : {j : I} → (op : Op j) → Fin (arity op) → I

inductive Term {I : Type i} (S : Signature.{i,o} I) (X : I → Type x) : I → Type (max i o x)
  | leaf {j} : X j → Term S X j
  | node {j} (op : S.Op j) : ((k : Fin (S.arity op)) → Term S X (S.child op k)) → Term S X j

namespace Term
variable {I : Type i} {S : Signature.{i,o} I} {X : I → Type x}
  {Y : I → Type y} {Z : I → Type z} {D : I → Type d}

def bind (f : ∀ j, X j → Term S Y j) : {j : I} → Term S X j → Term S Y j
  | _, .leaf x => f _ x
  | _, .node op ts => .node op (fun k => bind f (ts k))

def map (f : ∀ j, X j → Y j) : Term S X j → Term S Y j := bind (fun j x => .leaf (f j x))

def fold (alg : ∀ {j} (op : S.Op j), (∀ k, D (S.child op k)) → D j)
    (f : ∀ j, X j → D j) : {j : I} → Term S X j → D j
  | _, .leaf x => f _ x
  | _, .node op ts => alg op (fun k => fold alg f (ts k))

@[simp] theorem bind_leaf (t : Term S X j) : bind (fun _ => leaf) t = t := by
  induction t with
  | leaf => rfl
  | node op ts ih => simp only [bind]; congr 1; funext k; exact ih k

theorem bind_assoc (t : Term S X j) (f : ∀ j, X j → Term S Y j)
    (g : ∀ j, Y j → Term S Z j) :
    bind g (bind f t) = bind (fun j x => bind g (f j x)) t := by
  induction t with
  | leaf => rfl
  | node op ts ih => simp only [bind]; congr 1; funext k; exact ih k

theorem map_id (t : Term S X j) : map (fun _ x => x) t = t := bind_leaf t

theorem map_comp (t : Term S X j) (f : ∀ j, X j → Y j) (g : ∀ j, Y j → Z j) :
    map g (map f t) = map (fun j x => g j (f j x)) t := by
  exact bind_assoc t _ _

theorem fold_bind (alg : ∀ {j} (op : S.Op j), (∀ k, D (S.child op k)) → D j)
    (f : ∀ j, X j → Term S Y j) (g : ∀ j, Y j → D j) (t : Term S X j) :
    fold alg g (bind f t) = fold alg (fun j x => fold alg g (f j x)) t := by
  induction t with
  | leaf => rfl
  | node op ts ih => simp only [bind, fold]; congr 1; funext k; exact ih k

theorem fold_node (f : ∀ j, X j → Term S Y j) (t : Term S X j) :
    fold node f t = bind f t := by
  induction t with
  | leaf => rfl
  | node op ts ih => simp only [fold, bind]; congr 1; funext k; exact ih k
end Term

structure Behavior (I : Type i) where
  Output : I → Type o
  Request : I → Type a
  next : (j : I) → Request j → I

namespace Behavior
variable {I : Type i} (B : Behavior.{i,o,a} I)
abbrev Layer (X : I → Type x) (j : I) := B.Output j × ((r : B.Request j) → X (B.next j r))
abbrev Coalgebra (X : I → Type x) := ∀ j, X j → B.Layer X j
variable {X : I → Type x} {Y : I → Type y} {Z : I → Type z}

def map (f : ∀ j, X j → Y j) (v : B.Layer X j) : B.Layer Y j :=
  (v.1, fun r => f _ (v.2 r))
theorem map_id (v : B.Layer X j) : B.map (fun _ x => x) v = v := rfl
theorem map_comp (f : ∀ j, X j → Y j) (g : ∀ j, Y j → Z j) (v : B.Layer X j) :
    B.map g (B.map f v) = B.map (fun j x => g j (f j x)) v := rfl

structure Morphism {X : I → Type x} {Y : I → Type y}
    (c : B.Coalgebra X) (d : B.Coalgebra Y) (f : ∀ j, X j → Y j) : Prop where
  output : ∀ j x, (d j (f j x)).1 = (c j x).1
  next : ∀ j x r, (d j (f j x)).2 r = f _ ((c j x).2 r)

/-- A finite typed path records its final sort, and therefore its output type. -/
inductive Path : I → I → Type (max i a)
  | stop {j} : Path j j
  | step {j k} (r : B.Request j) : Path (B.next j r) k → Path j k

def observe (c : B.Coalgebra X) {j k} (p : B.Path j k) (v : X j) : B.Output k :=
  match p with
  | .stop => (c _ v).1
  | .step r p => observe c p ((c _ v).2 r)

theorem observe_morphism (c : B.Coalgebra X) (d : B.Coalgebra Y)
    (f : ∀ j, X j → Y j) (h : B.Morphism c d f) (p : B.Path j k) (v : X j) :
    B.observe d p (f j v) = B.observe c p v := by
  induction p with
  | stop => exact h.output _ _
  | step r p ih => simp only [observe, h.next]; exact ih _
end Behavior

inductive Slot {I : Type i} (S : Signature.{i,o} I) (B : Behavior.{i,z,a} I)
    {j} (op : S.Op j) : I → Type (max i a) where
  | ret (k : Fin (S.arity op)) : Slot S B op (S.child op k)
  | succ (k : Fin (S.arity op)) (r : B.Request (S.child op k)) :
      Slot S B op (B.next (S.child op k) r)

structure Rule {I : Type i} (S : Signature I) (B : Behavior I) where
  out : ∀ {j} (op : S.Op j), (∀ k, B.Output (S.child op k)) → B.Output j
  step : ∀ {j} (op : S.Op j), (∀ k, B.Output (S.child op k)) →
    (r : B.Request j) → Term S (Slot S B op) (B.next j r)

namespace Rule
variable {I : Type i} {S : Signature I} {B : Behavior I} (r : Rule S B)
  {X : I → Type x} {Y : I → Type y} {D : I → Type d}

def slots {j} (op : S.Op j) (xs : ∀ k, X (S.child op k))
    (ns : ∀ k (a : B.Request (S.child op k)), X (B.next (S.child op k) a)) :
    ∀ j, Slot S B op j → X j
  | _, .ret k => xs k
  | _, .succ k a => ns k a

def layer {j} (op : S.Op j) (xs : ∀ k, X (S.child op k))
    (bs : ∀ k, B.Layer X (S.child op k)) : B.Layer (Term S X) j :=
  (r.out op (fun k => (bs k).1), fun a =>
    (r.step op (fun k => (bs k).1) a).map (slots op xs (fun k => (bs k).2)))

theorem layer_natural (f : ∀ j, X j → Y j) {j} (op : S.Op j)
    (xs : ∀ k, X (S.child op k)) (bs : ∀ k, B.Layer X (S.child op k)) :
    r.layer op (fun k => f _ (xs k)) (fun k => B.map f (bs k)) =
      B.map (fun _ => Term.map f) (r.layer op xs bs) := by
  apply Prod.ext
  · rfl
  · funext a
    simp only [layer, Behavior.map, Term.map_comp]
    congr 1
    funext j s; cases s <;> rfl

def output (c : B.Coalgebra X) : {j : I} → Term S X j → B.Output j
  | _, .leaf x => (c _ x).1
  | _, .node op ts => r.out op (fun k => output c (ts k))

def next (c : B.Coalgebra X) : {j : I} → Term S X j → (a : B.Request j) → Term S X (B.next j a)
  | _, .leaf x, a => .leaf ((c _ x).2 a)
  | _, .node op ts, a =>
    Term.bind (slots op ts (fun k b => next c (ts k) b))
      (r.step op (fun k => output r c (ts k)) a)

def lift (c : B.Coalgebra X) : B.Coalgebra (Term S X) := fun _ t => (r.output c t, r.next c t)

structure Compatible (alg : ∀ {j} (op : S.Op j), (∀ k, D (S.child op k)) → D j)
    (d : B.Coalgebra D) : Prop where
  output : ∀ j (op : S.Op j) xs, (d _ (alg op xs)).1 = r.out op (fun k => (d _ (xs k)).1)
  next : ∀ j (op : S.Op j) xs a, (d _ (alg op xs)).2 a =
    Term.fold alg (slots op xs (fun k b => (d _ (xs k)).2 b))
      (r.step op (fun k => (d _ (xs k)).1) a)

theorem fold_morphism (alg : ∀ {j} (op : S.Op j), (∀ k, D (S.child op k)) → D j)
    (d : B.Coalgebra D) (hc : r.Compatible alg d) (c : B.Coalgebra X)
    (f : ∀ j, X j → D j) (hf : B.Morphism c d f) :
    B.Morphism (r.lift c) d (fun _ => Term.fold alg f) := by
  have ho : ∀ j (t : Term S X j), (d _ (Term.fold alg f t)).1 = r.output c t := by
    intro j t
    induction t with
    | leaf x => exact hf.output _ x
    | node op ts ih =>
      simp only [Term.fold, output]
      rw [hc.output]
      congr 1; funext k; exact ih k
  refine ⟨ho, ?_⟩
  intro j t a
  change (d _ (Term.fold alg f t)).2 a = Term.fold alg f (r.next c t a)
  induction t with
  | leaf x => exact hf.next _ x a
  | node op ts ih =>
    simp only [Term.fold, next, Term.fold_bind]
    rw [hc.next]
    have he : (fun k => (d _ (Term.fold alg f (ts k))).1) =
        (fun k => r.output c (ts k)) := funext (fun k => ho _ (ts k))
    rw [he]
    congr 1
    funext j s; cases s with
    | ret k => rfl
    | succ k b => exact ih k b

theorem compatible_lift (c : B.Coalgebra X) : r.Compatible Term.node (r.lift c) where
  output _ _ _ := rfl
  next _ op xs a := by rw [Term.fold_node]; rfl

theorem bind_morphism (c : B.Coalgebra X) (d : B.Coalgebra Y)
    (f : ∀ j, X j → Term S Y j) (hf : B.Morphism c (r.lift d) f) :
    B.Morphism (r.lift c) (r.lift d) (fun _ => Term.bind f) := by
  have h := r.fold_morphism Term.node (r.lift d) (r.compatible_lift d) c f hf
  have he : (fun j => Term.fold (S := S) Term.node f (j := j)) =
      (fun j => Term.bind f (j := j)) := by
    funext j t; exact Term.fold_node f t
  rw [he] at h
  exact h

theorem leaf_morphism (c : B.Coalgebra X) : B.Morphism c (r.lift c) (fun _ => Term.leaf) :=
  ⟨fun _ _ => rfl, fun _ _ _ => rfl⟩

theorem join_morphism (c : B.Coalgebra X) :
    B.Morphism (r.lift (r.lift c)) (r.lift c) (fun _ => Term.bind (fun _ x => x)) :=
  r.bind_morphism (r.lift c) c (fun _ x => x) ⟨fun _ _ => rfl, fun _ _ _ => rfl⟩

theorem map_morphism (c : B.Coalgebra X) (d : B.Coalgebra Y)
    (f : ∀ j, X j → Y j) (hf : B.Morphism c d f) :
    B.Morphism (r.lift c) (r.lift d) (fun _ => Term.map f) :=
  r.bind_morphism c d (fun j x => .leaf (f j x))
    ⟨hf.output, fun j x a => congrArg Term.leaf (hf.next j x a)⟩
end Rule
end SquareKit.IndexedCompositional
