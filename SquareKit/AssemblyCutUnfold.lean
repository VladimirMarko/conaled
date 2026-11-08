import SquareKit.AssemblyCutStructure
import SquareKit.AssemblyCutLength

/-! Finite observations for the final coalgebra mediator. -/
universe u
namespace Realizability.Assembly
open Encodable Denumerable
open Nat.Partrec (Code)

def unfoldSteps {α : Type u} (c : α → Option α) : Nat → α → Option α
  | 0, x => some x
  | n + 1, x => (unfoldSteps c n x).bind c

theorem unfoldSteps_succ_left {α : Type u} (c : α → Option α) (n : Nat) (x : α) :
    unfoldSteps c (n + 1) x = (c x).bind (unfoldSteps c n) := by
  induction n with
  | zero => simp [unfoldSteps]
  | succ n ih =>
    change (unfoldSteps c (n + 1) x).bind c = _
    rw [ih, Option.bind_assoc]
    rfl

def unfoldObserves {α : Type u} (c : α → Option α) (x : α) (k : Nat) : Prop :=
  ∃ y, unfoldSteps c (k + 1) x = some y

theorem unfoldObserves_down {α : Type u} (c : α → Option α) (x : α) (k : Nat) :
    unfoldObserves c x (k + 1) → unfoldObserves c x k := by
  rintro ⟨y, hy⟩
  unfold unfoldSteps at hy
  cases hs : unfoldSteps c (k + 1) x with
  | none => simp [hs] at hy
  | some z => exact ⟨z, hs⟩

noncomputable def unfoldLength {α : Type u} (c : α → Option α) (x : α) : Option Nat :=
  cutLength (unfoldObserves c x)

theorem unfoldLength_test {α : Type u} (c : α → Option α) (x : α) (k : Nat) :
    cutTest (unfoldLength c x) k ↔ unfoldObserves c x k :=
  cutLength_test _ (unfoldObserves_down c x) k

/-- One internal unfolding first runs the coalgebra tracker, then the lifted output. -/
def unfoldProgramStep (q : Code) (e : Nat) : Part Nat := (q.eval e).bind run

theorem unfoldProgramStep_recursive (q : Code) : Partrec (unfoldProgramStep q) :=
  (Code.eval_part.comp (Computable.const q) Computable.id).bind
    ((Partrec.nat_iff.mpr run_partrec).comp Computable.snd).to₂

def unfoldProgram (q : Code) (e : Nat) : Nat → Part Nat
  | 0 => Part.some e
  | n + 1 => (unfoldProgram q e n).bind (unfoldProgramStep q)

theorem unfoldProgram_recursive (q : Code) : Partrec₂ (unfoldProgram q) := by
  apply (Partrec.nat_rec Computable.snd Computable.fst
    ((unfoldProgramStep_recursive q).comp (Computable.snd.comp Computable.snd)).to₂).of_eq
  intro p
  induction p.2 with
  | zero => rfl
  | succ n ih => exact congrArg (fun t => t.bind (unfoldProgramStep q)) ih

/-- Partial output realizes its selected value, or is undefined at bottom. -/
def PartialRealizes (A : Assembly.{u}) (p : Part Nat) (x : Option A.Carrier) : Prop :=
  match x with
  | none => ¬ p.Dom
  | some x => ∃ e, e ∈ p ∧ A.realizes e x

theorem PartialRealizes.dom {A : Assembly.{u}} {p : Part Nat} {x : Option A.Carrier}
    (h : PartialRealizes A p x) : p.Dom ↔ ∃ y, x = some y := by
  cases x with
  | none => exact ⟨fun hd => (h hd).elim, by simp⟩
  | some x =>
    obtain ⟨e, he, _⟩ := h
    exact ⟨fun _ => ⟨x, rfl⟩, fun _ => Part.dom_iff_mem.mpr ⟨e, he⟩⟩

theorem PartialRealizes.bind {A : Assembly.{u}} {p : Part Nat} {x : Option A.Carrier}
    (h : PartialRealizes A p x) (c : A.Carrier → Option A.Carrier) (φ : Nat → Part Nat)
    (ht : ∀ a e, A.realizes e a → PartialRealizes A (φ e) (c a)) :
    PartialRealizes A (p.bind φ) (x.bind c) := by
  cases x with
  | none => exact fun hd => h hd.1
  | some x =>
    obtain ⟨e, he, hx⟩ := h
    have hp : p = Part.some e := Part.eq_some_iff.mpr he
    rw [hp, Part.bind_some]
    exact ht x e hx

theorem unfoldProgramStep_realizes {A : Assembly.{u}} (c : Hom A (programLift A))
    (q : Code) (hq : Tracks A (programLift A) q.eval c.toFun)
    (x : A.Carrier) (e : Nat) (he : A.realizes e x) :
    PartialRealizes A (unfoldProgramStep q e) (c.toFun x) := by
  obtain ⟨m, hm, hy⟩ := hq x e he
  have hp : q.eval e = Part.some m := Part.eq_some_iff.mpr hm
  unfold unfoldProgramStep
  rw [hp, Part.bind_some]
  cases hh : c.toFun x <;> simpa only [hh, programLift, PartialRealizes] using hy

theorem unfoldProgram_realizes {A : Assembly.{u}} (c : Hom A (programLift A))
    (q : Code) (hq : Tracks A (programLift A) q.eval c.toFun)
    (x : A.Carrier) (e : Nat) (he : A.realizes e x) (k : Nat) :
    PartialRealizes A (unfoldProgram q e k) (unfoldSteps c.toFun k x) := by
  induction k with
  | zero => exact ⟨e, by simp [unfoldProgram], he⟩
  | succ k ih =>
    exact ih.bind c.toFun (unfoldProgramStep q) (unfoldProgramStep_realizes c q hq)

noncomputable def cutUnfold {A : Assembly.{u}} (c : Hom A (programLift A)) : Hom A finalCuts where
  toFun x := ⟨unfoldLength c.toFun x⟩
  tracked := by
    obtain ⟨q, hq⟩ := c.has_code
    have hp : Partrec₂ (fun e k => unfoldProgram q e (k + 1)) :=
      ((unfoldProgram_recursive q).comp Computable.fst (Computable.succ.comp Computable.snd)).to₂
    let d := templateCode _ hp
    have hd : Computable (fun e => encode (d.curry e)) :=
      Computable.encode.comp (Code.primrec₂_curry.to_comp.comp (Computable.const d) Computable.id)
    refine ⟨fun e => Part.some (encode (d.curry e)), Partrec.nat_iff.mp hd, ?_⟩
    intro x e he
    refine ⟨encode (d.curry e), by simp, ?_⟩
    have ht : ∀ k, ((d.curry e).eval k).Dom ↔ cutTest (unfoldLength c.toFun x) k := by
      intro k
      rw [Code.eval_curry, templateCode_eval]
      exact (unfoldProgram_realizes c q hq x e he (k + 1)).dom.trans
        (unfoldLength_test c.toFun x k).symm
    dsimp only [finalCuts]
    cases hh : unfoldLength c.toFun x with
    | none => intro k; simpa [hh, cutTest] using (ht k).mpr (by simp [hh, cutTest])
    | some n => intro k; simpa [hh, cutTest] using ht k

end Realizability.Assembly
