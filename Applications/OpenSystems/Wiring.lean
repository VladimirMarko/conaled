import Mathlib.Analysis.Calculus.ContDiff.Operations
import Mathlib.Analysis.Calculus.FDeriv.Linear
import Mathlib.Tactic

/-! Experimental finite wiring fragment of Vagner–Spivak–Lerman 1408.1598v2.
Every port has type ℝ. Wires preserve that type and never copy a supplier.
The state-only readout is the admissibility boundary, not a feedback solver. -/
noncomputable section
open scoped ContDiff
namespace Applications.OpenSystems

/-- Routing data separated from its bijection obligation. -/
structure Routing (I O J P : Type) where
  input : I → O ⊕ J
  output : P → O

namespace Routing
variable {I O J P K Q : Type}
def wires (w : Routing I O J P) : I ⊕ P → O ⊕ J :=
  Sum.elim w.input (Sum.inl ∘ w.output)

def Admissible (w : Routing I O J P) : Prop := Function.Bijective w.wires

def identity : Routing I O I O := ⟨Sum.inr, id⟩

def comp (w : Routing I O J P) (v : Routing J P K Q) : Routing I O K Q where
  input i := match w.input i with
    | .inl o => .inl o
    | .inr j => match v.input j with
      | .inl p => .inl (w.output p)
      | .inr k => .inr k
  output q := w.output (v.output q)

@[simp] theorem identity_admissible : (identity : Routing I O I O).Admissible :=
  (Equiv.sumComm I O).bijective

theorem comp_admissible (w : Routing I O J P) (v : Routing J P K Q)
    (hw : w.Admissible) (hv : v.Admissible) : (w.comp v).Admissible := by
  have wi : Function.Injective w.input := by
    intro a b h; exact Sum.inl.inj (hw.1 (show w.wires (.inl a) = w.wires (.inl b) from h))
  have wo : Function.Injective w.output := by
    intro a b h; exact Sum.inr.inj (hw.1 (show w.wires (.inr a) = w.wires (.inr b) from congrArg Sum.inl h))
  have wd (i : I) (p : P) : w.input i ≠ .inl (w.output p) := by
    intro h; exact Sum.inl_ne_inr (hw.1 (show w.wires (.inl i) = w.wires (.inr p) from h))
  have vi : Function.Injective v.input := by
    intro a b h; exact Sum.inl.inj (hv.1 (show v.wires (.inl a) = v.wires (.inl b) from h))
  have vo : Function.Injective v.output := by
    intro a b h; exact Sum.inr.inj (hv.1 (show v.wires (.inr a) = v.wires (.inr b) from congrArg Sum.inl h))
  have vd (j : J) (q : Q) : v.input j ≠ .inl (v.output q) := by
    intro h; exact Sum.inl_ne_inr (hv.1 (show v.wires (.inl j) = v.wires (.inr q) from h))
  have wj (j : J) : ∃ i, w.input i = .inr j := by
    obtain ⟨a, ha⟩ := hw.2 (.inr j)
    cases a with
    | inl i => exact ⟨i, ha⟩
    | inr p => simp [wires] at ha
  constructor
  · intro a b h
    cases a with
    | inl a =>
      cases b with
      | inl b =>
        simp only [wires, Sum.elim_inl] at h
        cases ha : w.input a with
        | inl o =>
          cases hb : w.input b with
          | inl o' =>
            simp [comp, ha, hb] at h
            exact congrArg Sum.inl (wi (ha.trans (h ▸ hb.symm)))
          | inr j =>
            cases hj : v.input j <;> simp [comp, ha, hb, hj] at h
            exact False.elim (wd a _ (ha.trans (congrArg Sum.inl h)))
        | inr j =>
          cases hb : w.input b with
          | inl o =>
            cases hj : v.input j <;> simp [comp, ha, hb, hj] at h
            exact False.elim (wd b _ (hb.trans (congrArg Sum.inl h.symm)))
          | inr j' =>
            have hjj : j = j' := by
              apply vi
              cases hj : v.input j <;> cases hj' : v.input j' <;>
                simp [comp, ha, hb, hj, hj'] at h ⊢
              · exact wo h
              · exact h
            exact congrArg Sum.inl (wi (ha.trans (hjj ▸ hb.symm)))
      | inr q =>
        cases ha : w.input a with
        | inl o =>
          simp [wires, comp, ha] at h
          exact False.elim (wd a _ (ha.trans (congrArg Sum.inl h)))
        | inr j =>
          cases hj : v.input j <;> simp [wires, comp, ha, hj] at h
          exact False.elim (vd j q (hj.trans (congrArg Sum.inl (wo h))))
    | inr q =>
      cases b with
      | inl b =>
        cases hb : w.input b with
        | inl o =>
          simp [wires, comp, hb] at h
          exact False.elim (wd b _ (hb.trans (congrArg Sum.inl h.symm)))
        | inr j =>
          cases hj : v.input j <;> simp [wires, comp, hb, hj] at h
          exact False.elim (vd j q (hj.trans (congrArg Sum.inl (wo h.symm))))
      | inr q' =>
        simp [wires, comp] at h
        exact congrArg Sum.inr (vo (wo h))
  · intro target
    cases target with
    | inl o =>
      obtain ⟨a, ha⟩ := hw.2 (.inl o)
      cases a with
      | inl i => exact ⟨.inl i, by simp [wires, comp, show w.input i = .inl o from ha]⟩
      | inr p =>
        have hop : w.output p = o := Sum.inl.inj ha
        obtain ⟨b, hb⟩ := hv.2 (.inl p)
        cases b with
        | inl j =>
          obtain ⟨i, hi⟩ := wj j
          exact ⟨.inl i, by simp [wires, comp, hi, show v.input j = .inl p from hb, hop]⟩
        | inr q =>
          exact ⟨.inr q, by simp [wires, comp, show v.output q = p from Sum.inl.inj hb, hop]⟩
    | inr k =>
      obtain ⟨b, hb⟩ := hv.2 (.inr k)
      cases b with
      | inl j =>
        obtain ⟨i, hi⟩ := wj j
        exact ⟨.inl i, by simp [wires, comp, hi, show v.input j = .inr k from hb]⟩
      | inr q => simp [wires] at hb

/-- A routing certificate is an actual port equivalence, not just cardinality. -/
def equivalence (w : Routing I O J P) (h : w.Admissible) : I ⊕ P ≃ O ⊕ J :=
  Equiv.ofBijective w.wires h

def supply (w : Routing I O J P) (o : O → ℝ) (j : J → ℝ) : I → ℝ :=
  fun i => Sum.elim o j (w.input i)
def read (w : Routing I O J P) (o : O → ℝ) : P → ℝ := o ∘ w.output

@[simp] theorem supply_identity (o : O → ℝ) (i : I → ℝ) :
    identity.supply o i = i := rfl
@[simp] theorem read_identity (o : O → ℝ) : (identity : Routing I O I O).read o = o := rfl

/-- Local substitution law: no system preservation theorem is assumed. -/
theorem supply_comp (w : Routing I O J P) (v : Routing J P K Q)
    (o : O → ℝ) (k : K → ℝ) :
    (w.comp v).supply o k = w.supply o (v.supply (w.read o) k) := by
  funext i
  cases hw : w.input i with
  | inl a => simp [supply, comp, hw]
  | inr j => cases hv : v.input j <;> simp [supply, comp, hw, hv, read]

theorem read_comp (w : Routing I O J P) (v : Routing J P K Q) (o : O → ℝ) :
    (w.comp v).read o = v.read (w.read o) := rfl
end Routing

/-- Finite scalar-typed ports with a certified no-passing bijection. -/
structure Wiring (I O J P : Type) [Fintype I] [Fintype O] [Fintype J] [Fintype P]
    extends Routing I O J P where
  admissible : toRouting.Admissible

namespace Wiring
variable {I O J P K Q : Type} [Fintype I] [Fintype O] [Fintype J] [Fintype P]
  [Fintype K] [Fintype Q]
def identity : Wiring I O I O := ⟨Routing.identity, Routing.identity_admissible⟩
def comp (w : Wiring I O J P) (v : Wiring J P K Q) : Wiring I O K Q :=
  ⟨w.toRouting.comp v.toRouting, Routing.comp_admissible _ _ w.admissible v.admissible⟩
end Wiring

/-- Velocities in a vector-space state chart; readouts never consume inputs. -/
structure System (S I O : Type) where
  field : S → (I → ℝ) → S
  readout : S → (O → ℝ)

namespace System
variable {S T I O J P K Q I' O' : Type}
def wire (w : Routing I O J P) (f : System S I O) : System S J P where
  field s j := f.field s (w.supply (f.readout s) j)
  readout s := w.read (f.readout s)

def parallel (f : System S I O) (g : System T I' O') :
    System (S × T) (I ⊕ I') (O ⊕ O') where
  field s i := (f.field s.1 (i ∘ Sum.inl), g.field s.2 (i ∘ Sum.inr))
  readout s := Sum.elim (f.readout s.1) (g.readout s.2)

theorem wire_identity (f : System S I O) : f.wire Routing.identity = f := by cases f; rfl

theorem wire_comp (f : System S I O) (w : Routing I O J P) (v : Routing J P K Q) :
    (f.wire w).wire v = f.wire (w.comp v) := by
  cases f
  simp only [wire, Routing.supply_comp, Routing.read_comp]

theorem wire_field (w : Routing I O J P) (f : System S I O) (s : S) (j : J → ℝ) :
    (f.wire w).field s j = f.field s (w.supply (f.readout s) j) := rfl

theorem wire_readout (w : Routing I O J P) (f : System S I O) (s : S) :
    (f.wire w).readout s = w.read (f.readout s) := rfl

/-- Smoothness is a separate analytic property of the complete field/readout. -/
def Smooth [NormedAddCommGroup S] [NormedSpace ℝ S] [Fintype I] [Fintype O]
    (f : System S I O) : Prop :=
  ContDiff ℝ ∞ (fun p : S × (I → ℝ) => f.field p.1 p.2) ∧
  ContDiff ℝ ∞ f.readout
theorem Smooth.wire [NormedAddCommGroup S] [NormedSpace ℝ S]
    [Fintype I] [Fintype O] [Fintype J] [Fintype P]
    {f : System S I O} (hf : f.Smooth) (w : Routing I O J P) : (f.wire w).Smooth := by
  constructor
  · apply hf.1.comp (f := fun p : S × (J → ℝ) => (p.1, w.supply (f.readout p.1) p.2))
    apply contDiff_fst.prodMk
    apply contDiff_pi.mpr
    intro i
    cases h : w.input i with
    | inl o =>
      change ContDiff ℝ ∞ (fun p : S × (J → ℝ) => w.supply (f.readout p.1) p.2 i)
      simp only [Routing.supply, h, Sum.elim_inl]
      exact (contDiff_pi.mp hf.2 o).comp contDiff_fst
    | inr j =>
      change ContDiff ℝ ∞ (fun p : S × (J → ℝ) => w.supply (f.readout p.1) p.2 i)
      simp only [Routing.supply, h, Sum.elim_inr]
      fun_prop
  · exact contDiff_pi.mpr (fun p => contDiff_pi.mp hf.2 (w.output p))

theorem Smooth.parallel [NormedAddCommGroup S] [NormedSpace ℝ S]
    [NormedAddCommGroup T] [NormedSpace ℝ T]
    [Fintype I] [Fintype O] [Fintype I'] [Fintype O']
    {f : System S I O} {g : System T I' O'} (hf : f.Smooth) (hg : g.Smooth) :
    (f.parallel g).Smooth := by
  constructor
  · apply ContDiff.prodMk
    · apply hf.1.comp (f := fun p : (S × T) × ((I ⊕ I') → ℝ) => (p.1.1, p.2 ∘ Sum.inl))
      apply ContDiff.prodMk
      · fun_prop
      · apply contDiff_pi.mpr; intro i; fun_prop
    · apply hg.1.comp (f := fun p : (S × T) × ((I ⊕ I') → ℝ) => (p.1.2, p.2 ∘ Sum.inr))
      apply ContDiff.prodMk
      · fun_prop
      · apply contDiff_pi.mpr; intro i; fun_prop
  · apply contDiff_pi.mpr
    intro o
    cases o with
    | inl o => exact (contDiff_pi.mp hf.2 o).comp contDiff_fst
    | inr o => exact (contDiff_pi.mp hg.2 o).comp contDiff_snd

end System
end Applications.OpenSystems
