import Mathlib.Logic.Relation

/-!
# State/exception interpretations

Experimental bounded comparison for #373. Catch has a separate scope; it is
not an algebraic operation commuting with arbitrary continuation substitution.
-/
namespace StateException

abbrev Keep (S E A : Type) := S → Except E A × S
abbrev Undo (S E A : Type) := S → Except E (A × S)

namespace Keep
variable {S E A B C : Type}
def ret (a : A) : Keep S E A := fun s => (.ok a, s)
def bind (m : Keep S E A) (k : A → Keep S E B) : Keep S E B := fun s =>
  match m s with
  | (.ok a, t) => k a t
  | (.error e, t) => (.error e, t)
def get : Keep S E S := fun s => (.ok s, s)
def put (t : S) : Keep S E Unit := fun _ => (.ok (), t)
def throw (e : E) : Keep S E A := fun s => (.error e, s)
def handle (m : Keep S E A) (h : E → Keep S E A) : Keep S E A := fun s =>
  match m s with
  | (.ok a, t) => (.ok a, t)
  | (.error e, t) => h e t

theorem bind_ret (m : Keep S E A) : bind m ret = m := by
  funext s; cases hm : m s with | mk r t => cases r <;> simp [bind, ret, hm]

theorem bind_assoc (m : Keep S E A) (f : A → Keep S E B)
    (g : B → Keep S E C) : bind (bind m f) g = bind m (fun a => bind (f a) g) := by
  funext s; cases hm : m s with | mk r t => cases r <;> simp [bind, hm]

theorem catch_put (t : S) (m : Keep S E A) (h : E → Keep S E A) :
    bind (put t) (fun _ => handle m h) = handle (bind (put t) (fun _ => m)) h := by
  rfl

theorem catch_ret (a : A) (h : E → Keep S E A) : handle (ret a) h = ret a := rfl
theorem catch_throw (e : E) (h : E → Keep S E A) : handle (throw e) h = h e := rfl
end Keep

namespace Undo
variable {S E A B C : Type}
def ret (a : A) : Undo S E A := fun s => .ok (a, s)
def bind (m : Undo S E A) (k : A → Undo S E B) : Undo S E B := fun s =>
  match m s with
  | .ok (a, t) => k a t
  | .error e => .error e
def get : Undo S E S := fun s => .ok (s, s)
def put (t : S) : Undo S E Unit := fun _ => .ok ((), t)
def throw (e : E) : Undo S E A := fun _ => .error e
def handle (m : Undo S E A) (h : E → Undo S E A) : Undo S E A := fun s =>
  match m s with
  | .ok (a, t) => .ok (a, t)
  | .error e => h e s

theorem bind_ret (m : Undo S E A) : bind m ret = m := by
  funext s; cases hm : m s with
  | ok p => cases p; simp [bind, ret, hm]
  | error e => simp [bind, hm]

theorem bind_assoc (m : Undo S E A) (f : A → Undo S E B)
    (g : B → Undo S E C) : bind (bind m f) g = bind m (fun a => bind (f a) g) := by
  funext s; cases hm : m s with
  | ok p => cases p; simp [bind, hm]
  | error e => simp [bind, hm]

theorem catch_put (t : S) (m : Undo S E A) (h : E → Undo S E A) :
    bind (put t) (fun _ => handle m h) =
      handle (bind (put t) (fun _ => m)) (fun e => bind (put t) (fun _ => h e)) := by
  funext s; cases hm : m t <;> simp [bind, put, handle, hm]

theorem catch_ret (a : A) (h : E → Undo S E A) : handle (ret a) h = ret a := rfl
theorem catch_throw (e : E) (h : E → Undo S E A) : handle (throw e) h = h e := rfl

theorem put_throw (t : S) (e : E) :
    bind (put t) (fun _ => throw e) = (throw e : Undo S E A) := rfl
end Undo

/-- Unquotiented well-founded syntax. Branching may be infinite for arbitrary `S`;
the Boolean specialization is finite. Equations require semantic proofs. -/
inductive Tree (S E A : Type) where
  | ret : A → Tree S E A
  | read : (S → Tree S E A) → Tree S E A
  | write : S → Tree S E A → Tree S E A
  | raise : E → Tree S E A

namespace Tree
variable {S E A B : Type}
def bind (p : Tree S E A) (k : A → Tree S E B) : Tree S E B :=
  match p with
  | .ret a => k a
  | .read f => .read (fun s => bind (f s) k)
  | .write s p => .write s (bind p k)
  | .raise e => .raise e
end Tree

/-- Operations are separate from laws. No global fold law is a field. -/
structure Algebra (S E : Type) (M : Type → Type) where
  ret : {A : Type} → A → M A
  read : {A : Type} → (S → M A) → M A
  write : {A : Type} → S → M A → M A
  raise : {A : Type} → E → M A
  bind : {A B : Type} → M A → (A → M B) → M B

/-- Local constructor obligations suffice for interpretation of substitution. -/
structure LocalLaws {S E : Type} {M : Type → Type} (a : Algebra S E M) : Prop where
  ret_bind : ∀ {A B} (v : A) (k : A → M B), a.bind (a.ret v) k = k v
  read_bind : ∀ {A B} (f : S → M A) (k : A → M B),
    a.bind (a.read f) k = a.read (fun s => a.bind (f s) k)
  write_bind : ∀ {A B} s (m : M A) (k : A → M B),
    a.bind (a.write s m) k = a.write s (a.bind m k)
  raise_bind : ∀ {A B} e (k : A → M B), a.bind (a.raise e) k = a.raise e

def fold {S E A : Type} {M : Type → Type} (a : Algebra S E M) : Tree S E A → M A
  | .ret v => a.ret v
  | .read f => a.read (fun s => fold a (f s))
  | .write s p => a.write s (fold a p)
  | .raise e => a.raise e

theorem fold_bind {S E A B : Type} {M : Type → Type} (a : Algebra S E M)
    (laws : LocalLaws a) (p : Tree S E A) (k : A → Tree S E B) :
    fold a (p.bind k) = a.bind (fold a p) (fun v => fold a (k v)) := by
  induction p with
  | ret v => exact (laws.ret_bind v (fun v => fold a (k v))).symm
  | read f ih => simp only [Tree.bind, fold, laws.read_bind]; exact congrArg a.read (funext ih)
  | write s p ih => simp only [Tree.bind, fold, laws.write_bind, ih]
  | raise e => exact (laws.raise_bind _ _).symm

def keepAlgebra (S E : Type) : Algebra S E (Keep S E) where
  ret := Keep.ret
  read f := fun s => f s s
  write t m := fun _ => m t
  raise := Keep.throw
  bind := Keep.bind

def undoAlgebra (S E : Type) : Algebra S E (Undo S E) where
  ret := Undo.ret
  read f := fun s => f s s
  write t m := fun _ => m t
  raise := Undo.throw
  bind := Undo.bind

theorem keep_local (S E : Type) : LocalLaws (keepAlgebra S E) :=
  ⟨fun _ _ => rfl, fun _ _ => rfl, fun _ _ _ => rfl, fun _ _ => rfl⟩
theorem undo_local (S E : Type) : LocalLaws (undoAlgebra S E) :=
  ⟨fun _ _ => rfl, fun _ _ => rfl, fun _ _ _ => rfl, fun _ _ => rfl⟩

/-- The ordinary single-cell equations, independent of the exception policy. -/
structure StateLaws {S E : Type} {M : Type → Type} (a : Algebra S E M) : Prop where
  write_write : ∀ {A} s t (m : M A), a.write s (a.write t m) = a.write t m
  write_read : ∀ {A} s (f : S → M A), a.write s (a.read f) = a.write s (f s)
  read_write : ∀ {A} (m : M A), a.read (fun s => a.write s m) = m
  read_read : ∀ {A} (f : S → S → M A),
    a.read (fun s => a.read (f s)) = a.read (fun s => f s s)

theorem keep_state (S E : Type) : StateLaws (keepAlgebra S E) :=
  ⟨fun _ _ _ => rfl, fun _ _ => rfl, fun _ => rfl, fun _ => rfl⟩
theorem undo_state (S E : Type) : StateLaws (undoAlgebra S E) :=
  ⟨fun _ _ _ => rfl, fun _ _ => rfl, fun _ => rfl, fun _ => rfl⟩

/-- Read commutes with a constant exception; write commutation distinguishes policies. -/
theorem undo_read_raise {S E A : Type} (e : E) :
    (undoAlgebra S E).read (fun _ => (Undo.throw e : Undo S E A)) = Undo.throw e := rfl

/-- Well-founded nested handler scopes. Continuations in each leaf use Tree.bind. -/
inductive Scoped (S E A : Type) where
  | body : Tree S E A → Scoped S E A
  | handle : Scoped S E A → (E → Scoped S E A) → Scoped S E A

def scopedFold {S E A : Type} {M : Type → Type} (a : Algebra S E M)
    (handle : M A → (E → M A) → M A) : Scoped S E A → M A
  | .body p => fold a p
  | .handle p h => handle (scopedFold a handle p) (fun e => scopedFold a handle (h e))

/-- Semantic equality of a protected scope and each handler is sufficient. -/
theorem scoped_congr {S E A : Type} {M : Type → Type} (a : Algebra S E M)
    (handle : M A → (E → M A) → M A) (p q : Scoped S E A)
    (h k : E → Scoped S E A) (hp : scopedFold a handle p = scopedFold a handle q)
    (hh : ∀ e, scopedFold a handle (h e) = scopedFold a handle (k e)) :
    scopedFold a handle (.handle p h) = scopedFold a handle (.handle q k) := by
  simp only [scopedFold, hp, funext hh]

end StateException
