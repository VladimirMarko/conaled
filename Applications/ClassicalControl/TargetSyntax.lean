import Applications.ClassicalControl.Certificate

/-! Scoped mixed lambda/control syntax. Saved stacks are closed runtime constants;
renaming and substitution descend into both scanner continuation arguments. -/
namespace ClassicalControl
namespace Target

mutual
inductive Term : Nat → Type where
  | var : Fin n → Term n
  | lam : Term (n+1) → Term n
  | app : Term n → Term n → Term n
  | cc : Term n
  | saved : Stack → Term n
  | walk : Term n → List Nat → Nat → List Nat → Term n
  | test : Term n → List Nat → Nat → List Nat → Term n
  | ret : Value → Term n
  | stuck : Term n
inductive Stack where
  | halt
  | out : List Nat → Stack
  | arg : Term 0 → Stack → Stack
  | next : Term 0 → List Nat → Nat → List Nat → Stack → Stack
end

/-- Induction on open mixed terms treats saved closed stacks as constants. -/
@[elab_as_elim] theorem Term.induct {P : ∀ n, Term n → Prop}
    (var : ∀ {n} (i : Fin n), P n (.var i))
    (lam : ∀ {n} (b : Term (n+1)), P (n+1) b → P n (.lam b))
    (app : ∀ {n} (a b : Term n), P n a → P n b → P n (.app a b))
    (cc : ∀ {n}, P n .cc)
    (saved : ∀ {n} s, P n (.saved s))
    (walk : ∀ {n} (k : Term n) L j O, P n k → P n (.walk k L j O))
    (test : ∀ {n} (k : Term n) L j O, P n k → P n (.test k L j O))
    (ret : ∀ {n} v, P n (.ret v))
    (stuck : ∀ {n}, P n .stuck) {n} (t : Term n) : P n t :=
  @Term.rec P (fun _ => True) var lam app cc (fun s _ => saved s)
    walk test ret stuck trivial (fun _ => trivial)
    (fun _ _ _ _ => trivial) (fun _ _ _ _ _ _ _ => trivial) _ t

def liftRen (f : Fin n → Fin m) : Fin (n+1) → Fin (m+1) :=
  Fin.cases 0 (fun i => (f i).succ)

def Term.rename (f : Fin n → Fin m) : Term n → Term m
 | .var i => .var (f i)
 | .lam b => .lam (b.rename (liftRen f))
 | .app a b => .app (a.rename f) (b.rename f)
 | .cc => .cc
 | .saved s => .saved s
 | .walk k l j o => .walk (k.rename f) l j o
 | .test k l j o => .test (k.rename f) l j o
 | .ret v => .ret v
 | .stuck => .stuck

@[simp] theorem liftRen_id : @liftRen n n id = id := by
  funext i; refine Fin.cases ?_ (fun i => ?_) i <;> rfl

theorem liftRen_comp (f : Fin m → Fin k) (g : Fin n → Fin m) :
    liftRen (f ∘ g) = liftRen f ∘ liftRen g := by
  funext i; refine Fin.cases ?_ (fun i => ?_) i <;> rfl

@[simp] theorem Term.rename_id (t : Term n) : t.rename id = t := by
  induction t using Term.induct <;> simp_all [rename]

theorem Term.rename_comp (t : Term n) (f : Fin m → Fin k) (g : Fin n → Fin m) :
    (t.rename g).rename f = t.rename (f ∘ g) := by
  induction t using Term.induct generalizing m k <;> simp_all [rename, liftRen_comp]

def liftSub (σ : Fin n → Term m) : Fin (n+1) → Term (m+1) :=
  Fin.cases (.var 0) (fun i => (σ i).rename Fin.succ)

def Term.subst (σ : Fin n → Term m) : Term n → Term m
 | .var i => σ i
 | .lam b => .lam (b.subst (liftSub σ))
 | .app a b => .app (a.subst σ) (b.subst σ)
 | .cc => .cc
 | .saved s => .saved s
 | .walk k l j o => .walk (k.subst σ) l j o
 | .test k l j o => .test (k.subst σ) l j o
 | .ret v => .ret v
 | .stuck => .stuck

theorem Term.subst_rename (t : Term n) (σ : Fin m → Term k) (f : Fin n → Fin m) :
    (t.rename f).subst σ = t.subst (σ ∘ f) := by
  induction t using Term.induct generalizing m k with
  | lam b ih =>
    have h : liftSub σ ∘ liftRen f = liftSub (σ ∘ f) := by
      funext i; refine Fin.cases ?_ (fun i => ?_) i <;> rfl
    simp only [rename, subst, ih, h]
  | _ => simp_all [rename, subst]

theorem Term.rename_subst (t : Term n) (f : Fin m → Fin k) (σ : Fin n → Term m) :
    (t.subst σ).rename f = t.subst (fun i => (σ i).rename f) := by
  induction t using Term.induct generalizing m k with
  | lam b ih =>
    have h : (fun i => (liftSub σ i).rename (liftRen f)) =
        liftSub (fun i => (σ i).rename f) := by
      funext i
      refine Fin.cases ?_ (fun i => ?_) i
      · rfl
      · simp only [liftSub, Fin.cases_succ, rename_comp]; rfl
    simp only [subst, rename, ih, h]
  | _ => simp_all [rename, subst]

theorem Term.subst_shift (t : Term n) (σ : Fin n → Term m) :
    (t.rename Fin.succ).subst (liftSub σ) = (t.subst σ).rename Fin.succ := by
  rw [subst_rename, rename_subst]; rfl

theorem Term.subst_comp (t : Term n) (σ : Fin n → Term m) (τ : Fin m → Term k) :
    (t.subst σ).subst τ = t.subst (fun i => (σ i).subst τ) := by
  induction t using Term.induct generalizing m k with
  | lam b ih =>
    have h : (fun i => (liftSub σ i).subst (liftSub τ)) =
        liftSub (fun i => (σ i).subst τ) := by
      funext i
      refine Fin.cases ?_ (fun i => ?_) i
      · rfl
      · exact subst_shift _ _
    simp only [subst, ih, h]
  | _ => simp_all [subst]

@[simp] theorem Term.subst_id (t : Term n) : t.subst .var = t := by
  have h : ∀ n, @liftSub n n Term.var = Term.var := by
    intro n; funext i; refine Fin.cases ?_ (fun i => ?_) i <;> rfl
  induction t using Term.induct <;> simp_all [subst]

def single (u : Term n) : Fin (n+1) → Term n := Fin.cases u Term.var

/-- Beta commutes with closing a body; the shifted replacements contain no free variables. -/
theorem Term.close_beta (b : Term (n+1)) (σ : Fin n → Term 0) (u : Term 0) :
    (b.subst (liftSub σ)).subst (single u) = b.subst (Fin.cases u σ) := by
  rw [subst_comp]
  congr 1
  funext i
  refine Fin.cases ?_ (fun i => ?_) i
  · rfl
  · simp only [liftSub, Fin.cases_succ, subst_rename]
    exact subst_id _

end Target
end ClassicalControl
