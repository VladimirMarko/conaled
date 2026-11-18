import SquareKit.Lawvere.Sums
import Mathlib.Logic.Equiv.Fin.Basic

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
noncomputable section
namespace SquareKit.Lawvere.Operations
universe u
variable {O : Operations.{u}}
/-- All rectangular substitutions interchange, including empty rectangles. -/
def Commutes {n m} (f : O.Op n) (g : O.Op m) : Prop :=
  ∀ k (x : Fin n → Fin m → O.Op k),
    O.subst f (fun i => O.subst g (x i)) =
      O.subst g (fun j => O.subst f (fun i => x i j))

theorem Commutes.symm {n m} {f : O.Op n} {g : O.Op m}
    (h : Commutes f g) : Commutes g f := by
  intro k x
  exact (h k (fun i j => x j i)).symm

theorem commutes_var {n m} (i : Fin n) (g : O.Op m) : Commutes (O.var i) g := by
  intro k x
  simp only [O.var_subst]

theorem Commutes.subst {n m r} {f : O.Op n} {g : O.Op m}
    (h : Commutes f g) (σ : Fin n → O.Op r)
    (hs : ∀ i, Commutes (σ i) g) : Commutes (O.subst f σ) g := by
  intro k x
  simp only [O.subst_assoc]
  calc
    O.subst f (fun i => O.subst (σ i) (fun j => O.subst g (x j))) =
        O.subst f (fun i => O.subst g (fun j => O.subst (σ i) (fun a => x a j))) :=
      congrArg (O.subst f) (funext (fun i => hs i k x))
    _ = _ := h k _
end SquareKit.Lawvere.Operations

namespace SquareKit.Lawvere.Presentation
universe u v
open Operations
variable (P Q : Presentation.{u})
def crossLeft (s : P.Symbol) (t : Q.Symbol) :
    (sum P Q).Term (P.arity s * Q.arity t) :=
  .node (.inl s) (fun i => .node (.inr t) (fun j => .leaf (finProdFinEquiv (i,j))))
def crossRight (s : P.Symbol) (t : Q.Symbol) :
    (sum P Q).Term (P.arity s * Q.arity t) :=
  .node (.inr t) (fun j => .node (.inl s) (fun i => .leaf (finProdFinEquiv (i,j))))

def tensor : Presentation.{u} where
  Symbol := (sum P Q).Symbol
  arity := (sum P Q).arity
  Equation := (sum P Q).Equation ⊕ (P.Symbol × Q.Symbol)
  variableCount := Sum.elim (sum P Q).variableCount (fun st => P.arity st.1 * Q.arity st.2)
  lhs := Sum.rec (sum P Q).lhs (fun st => crossLeft P Q st.1 st.2)
  rhs := Sum.rec (sum P Q).rhs (fun st => crossRight P Q st.1 st.2)

theorem cross_equation_iff {O : Operations.{v}}
    (op : (s : (sum P Q).Symbol) → O.Op ((sum P Q).arity s)) (s : P.Symbol) (t : Q.Symbol) :
    (sum P Q).evaluate op (crossLeft P Q s t) =
      (sum P Q).evaluate op (crossRight P Q s t) ↔ Commutes (op (.inl s)) (op (.inr t)) := by
  constructor
  · intro h k x
    have hh := congrArg (fun a => O.subst a (fun ij => x ((finProdFinEquiv (m := P.arity s) (n := Q.arity t)).symm ij).1 ((finProdFinEquiv (m := P.arity s) (n := Q.arity t)).symm ij).2)) h
    have hx (i : Fin (P.arity s)) (j : Fin (Q.arity t)) :
        x (finProdFinEquiv.symm (finProdFinEquiv (i,j))).1
          (finProdFinEquiv.symm (finProdFinEquiv (i,j))).2 = x i j := by
      rw [Equiv.symm_apply_apply]
    simpa only [evaluate, crossLeft, crossRight, FinitaryTerm.fold, O.subst_assoc,
      O.var_subst, hx] using hh
  · intro h
    exact h _ (fun i j => O.var (finProdFinEquiv (i,j)))

theorem evaluate_commutes {O : Operations.{v}}
    (a : P.Assignment O) {m} (g : O.Op m) (h : ∀ s, Commutes (a.op s) g)
    {n} (t : P.Term n) : Commutes (P.evaluate a.op t) g := by
  induction t with
  | leaf i => exact commutes_var i g
  | node s ts ih => exact (h s).subst _ ih

theorem maps_commute_iff {O : Operations.{v}} (F : P.operations.Map O) (G : Q.operations.Map O) :
    (∀ n m (f : P.operations.Op n) (g : Q.operations.Op m), Commutes (F.map f) (G.map g)) ↔
      ∀ s t, Commutes (F.map (P.symbol s)) (G.map (Q.symbol t)) := by
  constructor
  · intro h s t; exact h _ _ _ _
  · intro h n m f g
    refine Quotient.inductionOn₂ f g ?_
    intro f g
    rw [P.map_mk, Q.map_mk]
    apply P.evaluate_commutes (P.assignment F)
    intro s
    exact (Q.evaluate_commutes (Q.assignment G) _ (fun t => (h s t).symm) g).symm
end SquareKit.Lawvere.Presentation

namespace SquareKit.Lawvere.Presentation
universe u v
open Operations
variable (P Q : Presentation.{u})
def CommutingAssignments (O : Operations.{v}) :=
  {a : P.Assignment O × Q.Assignment O // ∀ s t, Commutes (a.1.op s) (a.2.op t)}

def tensorAssignmentEquiv (O : Operations.{v}) :
    (tensor P Q).Assignment O ≃ CommutingAssignments P Q O where
  toFun a :=
    ⟨sumAssignmentEquiv P Q O ⟨a.op, fun e => a.laws (.inl e)⟩,
     fun s t => (cross_equation_iff P Q a.op s t).mp (a.laws (.inr (s,t)))⟩
  invFun a :=
    ⟨((sumAssignmentEquiv P Q O).symm a.val).op, by
      intro e
      cases e with
      | inl e => exact ((sumAssignmentEquiv P Q O).symm a.val).laws e
      | inr st => exact (cross_equation_iff P Q _ st.1 st.2).mpr (a.property st.1 st.2)⟩
  left_inv a := by apply Assignment.ext; funext s; cases s <;> rfl
  right_inv a := by apply Subtype.ext; rfl

def CommutingMaps (O : Operations.{v}) :=
  {fg : P.operations.Map O × Q.operations.Map O //
    ∀ n m (f : P.operations.Op n) (g : Q.operations.Op m), Commutes (fg.1.map f) (fg.2.map g)}

def commutingAssignmentEquiv (O : Operations.{v}) :
    CommutingAssignments P Q O ≃ CommutingMaps P Q O where
  toFun a := ⟨((P.assignmentEquiv O) a.val.1, (Q.assignmentEquiv O) a.val.2), by
    apply (maps_commute_iff P Q _ _).mpr
    intro s t
    simpa only [assignmentEquiv, Equiv.coe_fn_mk, interpretation_symbol] using a.property s t⟩
  invFun fg := ⟨(P.assignment fg.val.1, Q.assignment fg.val.2),
    (maps_commute_iff P Q _ _).mp fg.property⟩
  left_inv a := by
    apply Subtype.ext
    exact (Equiv.prodCongr (P.assignmentEquiv O) (Q.assignmentEquiv O)).left_inv a.val
  right_inv fg := by
    apply Subtype.ext
    exact (Equiv.prodCongr (P.assignmentEquiv O) (Q.assignmentEquiv O)).right_inv fg.val

/-- The universal commuting combination, for all finite arities including zero. -/
def tensorMapEquiv (O : Operations.{v}) :
    (tensor P Q).operations.Map O ≃ CommutingMaps P Q O :=
  ((tensor P Q).assignmentEquiv O).symm |>.trans
    ((tensorAssignmentEquiv P Q O).trans (commutingAssignmentEquiv P Q O))
end SquareKit.Lawvere.Presentation

namespace SquareKit.Lawvere.Presentation
universe u v
open Operations
variable (P Q : Presentation.{u})
def tensorInl : P.operations.Map (tensor P Q).operations :=
  ((tensorMapEquiv P Q _) (Map.id _)).val.1

def tensorInr : Q.operations.Map (tensor P Q).operations :=
  ((tensorMapEquiv P Q _) (Map.id _)).val.2

@[simp] theorem tensorInl_symbol (s : P.Symbol) :
    (tensorInl P Q).map (P.symbol s) = (tensor P Q).symbol (.inl s) :=
  P.interpretation_symbol _ s

@[simp] theorem tensorInr_symbol (s : Q.Symbol) :
    (tensorInr P Q).map (Q.symbol s) = (tensor P Q).symbol (.inr s) :=
  Q.interpretation_symbol _ s

theorem tensorMapEquiv_apply {O : Operations.{v}} (F : (tensor P Q).operations.Map O) :
    (tensorMapEquiv P Q O F).val = ((tensorInl P Q).comp F, (tensorInr P Q).comp F) := by
  apply Prod.ext
  · apply (P.assignmentEquiv O).symm.injective
    apply Assignment.ext
    funext s
    change (P.interpretation ((tensorAssignmentEquiv P Q O) ((tensor P Q).assignment F)).val.1.op
      ((tensorAssignmentEquiv P Q O) ((tensor P Q).assignment F)).val.1.laws).map (P.symbol s) =
      F.map ((tensorInl P Q).map (P.symbol s))
    rw [tensorInl_symbol]
    exact P.interpretation_symbol _ s
  · apply (Q.assignmentEquiv O).symm.injective
    apply Assignment.ext
    funext s
    change (Q.interpretation ((tensorAssignmentEquiv P Q O) ((tensor P Q).assignment F)).val.2.op
      ((tensorAssignmentEquiv P Q O) ((tensor P Q).assignment F)).val.2.laws).map (Q.symbol s) =
      F.map ((tensorInr P Q).map (Q.symbol s))
    rw [tensorInr_symbol]
    exact Q.interpretation_symbol _ s

theorem tensor_injections_commute :
    ∀ n m (f : P.operations.Op n) (g : Q.operations.Op m),
      Commutes ((tensorInl P Q).map f) ((tensorInr P Q).map g) :=
  ((tensorMapEquiv P Q _) (Map.id _)).property
end SquareKit.Lawvere.Presentation

namespace SquareKit.Lawvere.Operations
universe u v
variable (O R : Operations.{u})
def tensor : Operations.{u} := (Presentation.tensor O.canonicalPresentation R.canonicalPresentation).operations

def CommutingMaps (A : Operations.{v}) :=
  {fg : O.Map A × R.Map A // ∀ n m (f : O.Op n) (g : R.Op m), Commutes (fg.1.map f) (fg.2.map g)}

def canonicalCommutingMapEquiv (A : Operations.{v}) :
    Presentation.CommutingMaps O.canonicalPresentation R.canonicalPresentation A ≃ CommutingMaps O R A where
  toFun fg := ⟨(O.canonicalMapEquiv A fg.val.1, R.canonicalMapEquiv A fg.val.2),
    fun n m f g => fg.property n m (O.encode.map f) (R.encode.map g)⟩
  invFun fg := ⟨((O.canonicalMapEquiv A).symm fg.val.1, (R.canonicalMapEquiv A).symm fg.val.2),
    fun n m f g => fg.property n m (O.decode.map f) (R.decode.map g)⟩
  left_inv fg := by
    apply Subtype.ext
    exact (Equiv.prodCongr (O.canonicalMapEquiv A) (R.canonicalMapEquiv A)).left_inv fg.val
  right_inv fg := by
    apply Subtype.ext
    exact (Equiv.prodCongr (O.canonicalMapEquiv A) (R.canonicalMapEquiv A)).right_inv fg.val

def tensorMapEquiv (A : Operations.{v}) : (tensor O R).Map A ≃ CommutingMaps O R A :=
  (Presentation.tensorMapEquiv O.canonicalPresentation R.canonicalPresentation A).trans
    (canonicalCommutingMapEquiv O R A)

def tensorInl : O.Map (tensor O R) := O.encode.comp (Presentation.tensorInl _ _)
def tensorInr : R.Map (tensor O R) := R.encode.comp (Presentation.tensorInr _ _)

theorem tensorMapEquiv_apply {A : Operations.{v}} (F : (tensor O R).Map A) :
    (tensorMapEquiv O R A F).val = ((tensorInl O R).comp F, (tensorInr O R).comp F) := by
  change ((O.canonicalMapEquiv A) (Presentation.tensorMapEquiv _ _ _ F).val.1,
    (R.canonicalMapEquiv A) (Presentation.tensorMapEquiv _ _ _ F).val.2) = _
  rw [Presentation.tensorMapEquiv_apply]
  rfl

theorem tensor_injections_commute : ∀ n m (f : O.Op n) (g : R.Op m),
    Commutes ((tensorInl O R).map f) ((tensorInr O R).map g) := by
  intro n m f g
  exact Presentation.tensor_injections_commute _ _ n m (O.encode.map f) (R.encode.map g)
end SquareKit.Lawvere.Operations
