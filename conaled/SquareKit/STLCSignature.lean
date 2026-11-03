import SquareKit.STLCNaturality

/-! Primitive-signature changes retain the existing types and binding structure.
Interpretation commutes with restriction; new preservation obligations are local. -/
namespace SquareKit.STLCSignature
open CategoricalCompiler STLCNaturality
universe u v w z
variable {P Q R : Ty → Ty → Type}

/-- Relabel primitives without changing variables, types or term constructors. -/
def map (f : {a b : Ty} → P a b → Q a b) : Term P Γ a → Term Q Γ a
  | .var v => .var v
  | .unit => .unit
  | .pair t u => .pair (map f t) (map f u)
  | .fst t => .fst (map f t)
  | .snd t => .snd (map f t)
  | .lam t => .lam (map f t)
  | .app t u => .app (map f t) (map f u)
  | .letE t u => .letE (map f t) (map f u)
  | .inl t => .inl (map f t)
  | .inr t => .inr (map f t)
  | .caseE s l r => .caseE (map f s) (map f l) (map f r)
  | .prim p t => .prim (f p) (map f t)

theorem map_id (t : Term P Γ a) : map (fun p => p) t = t := by
  induction t <;> simp_all [map]

theorem map_comp (f : {a b : Ty} → P a b → Q a b)
    (g : {a b : Ty} → Q a b → R a b) (t : Term P Γ a) :
    map g (map f t) = map (fun p => g (f p)) t := by
  induction t <;> simp_all [map]

variable {O : Type u} {C : CategoryOps.{u,v} O} {A : Ty → O}

def restrict (f : {a b : Ty} → P a b → Q a b) (M : Model C Q A) : Model C P A :=
  { M with primitive := fun p => M.primitive (f p) }

theorem compileVar_restrict (f : {a b : Ty} → P a b → Q a b)
    (M : Model C Q A) (v : Var Γ a) :
    compileVar M v = compileVar (restrict f M) v := by
  induction v with
  | here => rfl
  | there v ih => exact congrArg (fun k => C.comp k M.fst) ih

/-- Old terms keep exactly their interpretation, with no law on new operations. -/
theorem compile_map (f : {a b : Ty} → P a b → Q a b)
    (M : Model C Q A) (t : Term P Γ a) :
    STLCNaturality.compile M (map f t) = STLCNaturality.compile (restrict f M) t := by
  induction t <;> first | exact compileVar_restrict f M _ | simp_all [map, STLCNaturality.compile, restrict]

def restrictTarget (f : {a b : Ty} → P a b → Q a b) (K : Target Q) : Target P :=
  { K with primitive := fun p => K.primitive (f p) }

theorem compile_target (f : {a b : Ty} → P a b → Q a b)
    (K : Target Q) (t : Term P Γ a) :
    CategoricalCompiler.compile K (map f t) = CategoricalCompiler.compile (restrictTarget f K) t := by
  have h := compile_map f (ofTarget K) t
  rw [compile_ofTarget] at h
  exact h.trans (compile_ofTarget (restrictTarget f K) t)

theorem eval_map (f : {a b : Ty} → P a b → Q a b) (B : Type)
    (meaning : {a b : Ty} → Q a b → Val B a → Val B b) (t : Term P Γ a)
    (ρ : Val B (context Γ)) :
    eval meaning (map f t) ρ = eval (fun p => meaning (f p)) t ρ := by
  have h := congrFun (compile_map f (semantics B meaning) t) ρ
  rw [semantics_compile] at h
  exact h.trans (semantics_compile B (fun p => meaning (f p)) t ρ)

abbrev Add (P Q : Ty → Ty → Type) (a b : Ty) := Sum (P a b) (Q a b)

def extend (M : Model C P A) (q : {a b : Ty} → Q a b → C.Hom (A a) (A b)) :
    Model C (Add P Q) A := { M with primitive := Sum.elim M.primitive q }

/-- With structural operations fixed, only the added primitive square is new. -/
theorem preserves_extend {O' : Type w} {D : CategoryOps.{w,z} O'}
    {F : RawMap C D} {H : HomEquiv D}
    {M : Model C P A} {N : Model D P (F.obj ∘ A)}
    (s : Preserves F H M N)
    (q : {a b : Ty} → Q a b → C.Hom (A a) (A b))
    (r : {a b : Ty} → Q a b → D.Hom (F.obj (A a)) (F.obj (A b)))
    (h : ∀ {a b} (p : Q a b), H.Rel (F.map (q p)) (r p)) :
    Preserves F H (extend M q) (extend N r) :=
  { s with primitive := by intro a b p; cases p with
           | inl p => exact s.primitive p
           | inr p => exact h p }

end SquareKit.STLCSignature
