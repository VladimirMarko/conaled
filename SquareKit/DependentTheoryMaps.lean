import Mathlib.Data.Fin.Basic

/-! Experimental finite-binding syntax and local-certificate theory maps (#344).
The construction adapts BHL v1 §6.5; it does not claim their acceptability metatheorems. -/
namespace SquareKit.DependentTheoryMaps

structure Signature where
  Symbol : Type
  arity : Symbol → Nat
  binds : (s : Symbol) → Fin (arity s) → Nat

inductive Expr (S : Signature) : Type → Type 1 where
  | var {V} : V → Expr S V
  | app {V} (s : S.Symbol) : ((i : Fin (S.arity s)) →
      Expr S (Fin (S.binds s i) ⊕ V)) → Expr S V

namespace Expr
variable {S : Signature} {V W X : Type}

def rename : {V W : Type} → (V → W) → Expr S V → Expr S W
  | _, _, f, .var v => .var (f v)
  | _, _, f, .app s a => .app s (fun i => rename (Sum.map id f) (a i))

@[simp] theorem rename_var (f : V → W) (v : V) : rename f (.var v : Expr S V) = .var (f v) := rfl

@[simp] theorem rename_id (e : Expr S V) : rename id e = e := by
  induction e with
  | var => rfl
  | app s a ih =>
    simp only [rename]
    congr 1
    funext i
    simpa only [Sum.map_id_id] using ih i

@[simp] theorem rename_comp (f : V → W) (g : W → X) (e : Expr S V) :
    rename g (rename f e) = rename (g ∘ f) e := by
  induction e generalizing W X with
  | var => rfl
  | app s a ih =>
    simp only [rename]
    congr 1
    funext i
    rw [ih]
    congr 1
    funext v
    cases v <;> rfl

def lift (f : V → Expr S W) : Fin n ⊕ V → Expr S (Fin n ⊕ W)
  | .inl i => .var (.inl i)
  | .inr v => rename Sum.inr (f v)

def subst : {V W : Type} → (V → Expr S W) → Expr S V → Expr S W
  | _, _, f, .var v => f v
  | _, _, f, .app s a => .app s (fun i => subst (lift f) (a i))

@[simp] theorem subst_var (f : V → Expr S W) (v : V) : subst f (.var v) = f v := rfl

@[simp] theorem subst_rename (f : V → W) (g : W → Expr S X) (e : Expr S V) :
    subst g (rename f e) = subst (g ∘ f) e := by
  induction e generalizing W X with
  | var => rfl
  | app s a ih =>
    simp only [rename, subst]
    congr 1
    funext i
    rw [ih]
    congr 1
    funext v
    cases v <;> rfl

@[simp] theorem rename_subst (f : V → Expr S W) (g : W → X) (e : Expr S V) :
    rename g (subst f e) = subst (fun v => rename g (f v)) e := by
  induction e generalizing W X with
  | var => rfl
  | app s a ih =>
    simp only [rename, subst]
    congr 1
    funext i
    rw [ih]
    congr 1
    funext v
    cases v with
    | inl => rfl
    | inr => simp [lift, Function.comp_def]

@[simp] theorem subst_comp (f : V → Expr S W) (g : W → Expr S X) (e : Expr S V) :
    subst g (subst f e) = subst (fun v => subst g (f v)) e := by
  induction e generalizing W X with
  | var => rfl
  | app s a ih =>
    simp only [subst]
    congr 1
    funext i
    rw [ih]
    congr 1
    funext v
    cases v with
    | inl => rfl
    | inr v => simp [lift, Function.comp_def]

@[simp] theorem subst_id (e : Expr S V) : subst .var e = e := by
  induction e with
  | var => rfl
  | @app V' s a ih =>
    simp only [subst]
    congr 1
    funext i
    have h : lift (S := S) (V := V') (n := S.binds s i) .var = Expr.var := by
      funext v; cases v <;> rfl
    rw [h, ih]

@[simp] theorem subst_vars (f : V → W) (e : Expr S V) :
    subst (fun v => .var (f v)) e = rename f e := by
  change subst (Expr.var ∘ f) e = rename f e
  rw [← Expr.subst_rename, Expr.subst_id]

end Expr

/-- A binding operation template, natural in substitution of its free variables.
The law is local to one symbol; it does not assume transport of derivations. -/
structure OperationMap (S T : Signature) where
  operation : {V : Type} → (s : S.Symbol) →
    ((i : Fin (S.arity s)) → Expr T (Fin (S.binds s i) ⊕ V)) → Expr T V
  natural : ∀ {V W : Type} (f : V → Expr T W) (s : S.Symbol)
    (a : (i : Fin (S.arity s)) → Expr T (Fin (S.binds s i) ⊕ V)),
    Expr.subst f (operation s a) =
      operation s (fun i => Expr.subst (Expr.lift f) (a i))

namespace OperationMap
variable {S T U : Signature}

def act (F : OperationMap S T) : {V : Type} → Expr S V → Expr T V
  | _, .var v => .var v
  | _, .app s a => F.operation s (fun i => F.act (a i))

@[simp] theorem act_var (F : OperationMap S T) (v : V) : F.act (.var v) = .var v := rfl

theorem operation_rename (F : OperationMap S T) (f : V → W) (s : S.Symbol)
    (a : (i : Fin (S.arity s)) → Expr T (Fin (S.binds s i) ⊕ V)) :
    Expr.rename f (F.operation s a) =
      F.operation s (fun i => Expr.rename (Sum.map id f) (a i)) := by
  rw [← Expr.subst_vars, F.natural]
  congr 1
  funext i
  have h : Expr.lift (fun v => Expr.var (S := T) (f v)) =
      (fun v : Fin (S.binds s i) ⊕ V => Expr.var (Sum.map id f v)) := by
    funext v; cases v <;> rfl
  rw [h, Expr.subst_vars]

@[simp] theorem act_rename (F : OperationMap S T) (f : V → W) (e : Expr S V) :
    F.act (Expr.rename f e) = Expr.rename f (F.act e) := by
  induction e generalizing W with
  | var => rfl
  | app s a ih =>
    simp only [Expr.rename, act, F.operation_rename]
    congr 1
    funext i
    exact ih i _

@[simp] theorem act_subst (F : OperationMap S T) (f : V → Expr S W) (e : Expr S V) :
    F.act (Expr.subst f e) = Expr.subst (fun v => F.act (f v)) (F.act e) := by
  induction e generalizing W with
  | var => rfl
  | app s a ih =>
    simp only [Expr.subst, act, F.natural]
    congr 1
    funext i
    rw [ih]
    congr 1
    funext v
    cases v with
    | inl => rfl
    | inr => simp [Expr.lift, act_rename]

def identity (S : Signature) : OperationMap S S where
  operation := Expr.app
  natural := fun _ _ _ => rfl

@[simp] theorem identity_act (e : Expr S V) : (identity S).act e = e := by
  induction e with
  | var => rfl
  | app s a ih => simp only [act, identity]; congr 1; funext i; exact ih i

end OperationMap
/-- Maps of scoped term monads. Local operation templates generate these maps;
composition does not require pulling target expressions back to the source. -/
structure SyntaxMap (S T : Signature) where
  act : {V : Type} → Expr S V → Expr T V
  on_var : ∀ {V : Type} (v : V), act (.var v) = .var v
  substitution : ∀ {V W : Type} (f : V → Expr S W) (e : Expr S V),
    act (Expr.subst f e) = Expr.subst (fun v => act (f v)) (act e)

namespace SyntaxMap
variable {S T U : Signature}

def ofOperations (F : OperationMap S T) : SyntaxMap S T where
  act := F.act
  on_var := F.act_var
  substitution := F.act_subst

def identity (S : Signature) : SyntaxMap S S where
  act := id
  on_var := fun _ => rfl
  substitution := fun _ _ => rfl

def comp (F : SyntaxMap S T) (G : SyntaxMap T U) : SyntaxMap S U where
  act := fun e => G.act (F.act e)
  on_var := by intros; rw [F.on_var, G.on_var]
  substitution := by intros; rw [F.substitution, G.substitution]

@[simp] theorem comp_act (F : SyntaxMap S T) (G : SyntaxMap T U) (e : Expr S V) :
    (F.comp G).act e = G.act (F.act e) := rfl

@[simp] theorem rename (F : SyntaxMap S T) (f : V → W) (e : Expr S V) :
    F.act (Expr.rename f e) = Expr.rename f (F.act e) := by
  rw [← Expr.subst_vars, F.substitution]
  simp only [F.on_var, Expr.subst_vars]
end SyntaxMap

/-- A finitary inference signature. The judgment type may contain contexts,
types, and terms; the syntax map is supplied separately. -/
structure Rules (J : Type u) where
  Label : Type v
  count : Label → Nat
  premise : (r : Label) → Fin (count r) → J
  conclusion : Label → J

/-- Actual proof trees, including a typed family of open assumptions. -/
inductive Derivation {J : Type u} (R : Rules.{u,v} J) (H : J → Type w) : J → Type (max u v w) where
  | hyp {j} : H j → Derivation R H j
  | rule (r : R.Label) : ((i : Fin (R.count r)) → Derivation R H (R.premise r i)) →
      Derivation R H (R.conclusion r)

namespace Derivation
variable {J : Type u} {R : Rules.{u,v} J} {H K L : J → Type w}

def graft (f : ∀ j, H j → Derivation R K j) : {j : J} → Derivation R H j → Derivation R K j
  | _, .hyp h => f _ h
  | _, .rule r ds => .rule r (fun i => graft f (ds i))

@[simp] theorem graft_hyp (f : ∀ j, H j → Derivation R K j) (h : H j) :
    graft f (.hyp h) = f j h := rfl

@[simp] theorem graft_identity (d : Derivation R H j) :
    graft (fun _ => .hyp) d = d := by
  induction d with
  | hyp => rfl
  | rule r ds ih => simp only [graft]; congr 1; funext i; exact ih i

@[simp] theorem graft_comp (f : ∀ j, H j → Derivation R K j)
    (g : ∀ j, K j → Derivation R L j) (d : Derivation R H j) :
    graft g (graft f d) = graft (fun j h => graft g (f j h)) d := by
  induction d with
  | hyp => rfl
  | rule r ds ih => simp only [graft]; congr 1; funext i; exact ih i
end Derivation

/-- Local rule certificates over the images of their own premises. An index
in the premise family retains repeated occurrences of the same judgment. -/
structure TheoryMap {J : Type u} {K : Type u} (R : Rules.{u,v} J) (Q : Rules.{u,v} K)
    (f : J → K) where
  certificate : (r : R.Label) → Derivation Q
    (fun k => {i : Fin (R.count r) // f (R.premise r i) = k}) (f (R.conclusion r))

namespace TheoryMap
variable {J K : Type u} {R : Rules.{u,v} J} {Q : Rules.{u,v} K} {f : J → K}

def transport (F : TheoryMap R Q f) {H : J → Type} {H' : K → Type}
    (h : ∀ j, H j → H' (f j)) : {j : J} → Derivation R H j → Derivation Q H' (f j)
  | _, .hyp p => .hyp (h _ p)
  | _, .rule r ds => (F.certificate r).graft (fun _ p =>
      p.property ▸ transport F h (ds p.val))

theorem transport_graft (F : TheoryMap R Q f)
    {H A : J → Type} {A' B : K → Type}
    (h : ∀ j, H j → A' (f j)) (a : ∀ j, A j → B (f j))
    (k : ∀ j, H j → Derivation R A j) (l : ∀ j, A' j → Derivation Q B j)
    (hl : ∀ j p, F.transport a (k j p) = l (f j) (h j p))
    (d : Derivation R H j) :
    F.transport a (d.graft k) = (F.transport h d).graft l := by
  induction d with
  | hyp p => exact hl _ p
  | rule r ds ih =>
    simp only [Derivation.graft, transport, Derivation.graft_comp]
    congr 1
    funext j p
    rcases p with ⟨i, hi⟩
    cases hi
    exact ih i

def identity (R : Rules.{u,v} J) : TheoryMap R R id where
  certificate := fun r => .rule r (fun i => .hyp ⟨i, rfl⟩)

@[simp] theorem identity_transport {H : J → Type} (d : Derivation R H j) :
    (identity R).transport (fun _ => id) d = d := by
  induction d with
  | hyp => rfl
  | rule r ds ih =>
    simp only [transport, identity, Derivation.graft]
    congr 1
    funext i
    exact ih i

variable {L : Type u} {P : Rules.{u,v} L} {g : K → L}

def comp (F : TheoryMap R Q f) (G : TheoryMap Q P g) : TheoryMap R P (g ∘ f) where
  certificate := fun r => G.transport
    (fun _ p => ⟨p.val, congrArg g p.property⟩) (F.certificate r)

theorem comp_transport (F : TheoryMap R Q f) (G : TheoryMap Q P g)
    {A : J → Type} {B : K → Type} {C : L → Type}
    (a : ∀ j, A j → B (f j)) (b : ∀ k, B k → C (g k))
    (d : Derivation R A j) :
    (F.comp G).transport (fun j p => b (f j) (a j p)) d =
      G.transport b (F.transport a d) := by
  induction d with
  | hyp => rfl
  | rule r ds ih =>
    simp only [transport, comp]
    symm
    apply transport_graft
    intro j p
    rcases p with ⟨i, hi⟩
    cases hi
    exact (ih i).symm

end TheoryMap
/-- A boundary lists the judgments presupposed by a judgment. -/
structure Boundary (J : Type u) where
  count : J → Nat
  judgment : (j : J) → Fin (count j) → J

/-- Presuppositions are certified at primitive rules, not assumed for complete proofs. -/
structure Presuppositive {J : Type u} (R : Rules.{u,v} J) (B : Boundary J) where
  certificate : (r : R.Label) → (i : Fin (B.count (R.conclusion r))) →
    Derivation R (fun j => {p : Fin (R.count r) // R.premise r p = j})
      (B.judgment (R.conclusion r) i)

def presuppositions {J : Type u} {R : Rules.{u,v} J} {B : Boundary J}
    (P : Presuppositive R B) {H : J → Type} {j : J}
    (boundaryHyp : ∀ j, H j → ∀ i : Fin (B.count j), Derivation R H (B.judgment j i))
    (d : Derivation R H j) (i : Fin (B.count j)) : Derivation R H (B.judgment j i) := by
  cases d with
  | hyp h => exact boundaryHyp _ h i
  | rule r ds =>
    exact (P.certificate r i).graft (fun _ p => p.property ▸ ds p.val)

/-- Predecessor restriction used to check boundaries before admitting a rule. -/
def Rules.before {J : Type u} (R : Rules.{u,v} J) (rank : R.Label → Nat) (n : Nat) : Rules J where
  Label := {r : R.Label // rank r < n}
  count := fun r => R.count r.val
  premise := fun r => R.premise r.val
  conclusion := fun r => R.conclusion r.val

/-- Earlier-rule certificates embed into the complete presentation by a local map. -/
def Rules.includeBefore {J : Type u} (R : Rules.{u,v} J) (rank : R.Label → Nat) (n : Nat) :
    TheoryMap (R.before rank n) R id where
  certificate := fun r => .rule r.val (fun i => .hyp ⟨i, rfl⟩)

structure SequentialBoundaries {J : Type u} (R : Rules.{u,v} J) (B : Boundary J)
    (rank : R.Label → Nat) where
  certificate : (r : R.Label) → (i : Fin (B.count (R.conclusion r))) →
    Derivation (R.before rank (rank r))
      (fun j => {p : Fin (R.count r) // R.premise r p = j})
      (B.judgment (R.conclusion r) i)

def SequentialBoundaries.presuppositive {J : Type u} {R : Rules.{u,v} J} {B : Boundary J}
    {rank : R.Label → Nat} (P : SequentialBoundaries R B rank) : Presuppositive R B where
  certificate := fun r i => (R.includeBefore rank (rank r)).transport
    (fun _ => id) (P.certificate r i)

end SquareKit.DependentTheoryMaps
