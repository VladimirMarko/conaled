import SquareKit.AssemblyCutComplete

/-! Finite/full observations, uniform iteration and conditional selection cases. -/
namespace InternalIteration
open Realizability Realizability.Assembly CategoryTheory Encodable Denumerable
open Nat.Partrec (Code)

example : Cut (encode (cutCode 0)) 0 := cutCode_realizes 0
example : Cut (encode (cutCode 3)) 3 := cutCode_realizes 3

/-- Returned enumeration labels are unrestricted, not fixed to the canonical zero. -/
theorem alternative_cut_labels : Cut (encode (Code.comp (Code.const 99) (cutCode 3))) 3 := by
  intro k
  simp only [Denumerable.ofNat_encode, Code.eval]
  change (((cutCode 3).eval k).bind (fun n => (Code.const 99).eval n)).Dom ↔ k < 3
  simp_rw [Code.eval_const]
  rw [Part.bind_some_eq_map]
  simp

theorem full_not_finite (n : Nat) : ¬ Cut (encode (Code.const 0)) n := by
  intro h
  exact Nat.lt_irrefl n ((h n).mp (by simp [Code.eval_const]))

/-- The final mediator recovers each finite cut without reading its length from a realizer. -/
theorem finite_unfold_is_inclusion : cutUnfold cutUnroll = cutInclusion.{0} := by
  symm
  apply cutUnfold_unique
  apply Hom.ext
  rintro ⟨n⟩
  cases n <;> rfl

example : (cutUnfold cutUnroll).toFun (⟨3⟩ : iterationCuts.{0}.Carrier) = ⟨some 3⟩ :=
  congrArg (fun h => h.toFun ⟨3⟩) finite_unfold_is_inclusion

abbrev N := encoded Nat

/-- A coalgebra which always continues has the full cut as its unique unfolding. -/
theorem always_unfolds_to_infinity :
    (cutUnfold (programLiftUnit N)).toFun (17 : Nat) = ⟨none⟩ := by
  apply ULift.ext
  apply cutTest_ext
  intro k
  refine (unfoldLength_test (programLiftUnit N).toFun (17 : Nat) k).trans ?_
  have hs : ∀ n, unfoldSteps (programLiftUnit N).toFun n (17 : Nat) = some (17 : Nat) := by
    intro n
    induction n with
    | zero => rfl
    | succ n ih => exact congrArg (fun t => t.bind (programLiftUnit N).toFun) ih
  exact ⟨fun _ => trivial, fun _ => ⟨(17 : Nat), hs (k + 1)⟩⟩

/-- The free strict algebra is supplied by the checked lifting monad. -/
def liftedNaturals : Monad.Algebra programLiftMonad where
  A := programLift N
  a := programLiftMul N
  unit := programLiftMul_left_unit N
  assoc := (programLiftMul_assoc N).symm

def chooseParameter : Hom (prod N (programLift N)) (programLift N) :=
  (fst _ _).comp (programLiftUnit N)

theorem parameter_iteration_zero :
    (strictIteration liftedNaturals chooseParameter).toFun ((17 : Nat), ⟨0⟩) = none := rfl

theorem parameter_iteration_one :
    (strictIteration liftedNaturals chooseParameter).toFun ((17 : Nat), ⟨1⟩) = some (17 : Nat) :=
  strictIteration_succ _ _ _ 0

theorem parameter_iteration_four :
    (strictIteration liftedNaturals chooseParameter).toFun ((17 : Nat), ⟨4⟩) = some (17 : Nat) :=
  strictIteration_succ _ _ _ 3

example : ∃ q : Code, Tracks (prod N iterationCuts) (programLift N) q.eval
    (strictIteration liftedNaturals chooseParameter).toFun :=
  (strictIteration liftedNaturals chooseParameter).has_code

def successor : Hom N N := ofComputable Nat.succ Computable.succ

def successorLiftHom : Monad.Algebra.Hom liftedNaturals liftedNaturals :=
  ⟨programLiftMap successor, programLiftMul_natural successor⟩

def chooseNextParameter : Hom (prod N (programLift N)) (programLift N) :=
  chooseParameter.comp (programLiftMap successor)

theorem parameter_intertwines : chooseParameter.comp successorLiftHom.f =
    (pair (fst _ _) ((snd _ _).comp successorLiftHom.f)).comp chooseNextParameter :=
  Hom.ext fun _ => rfl

example : (strictIteration liftedNaturals chooseParameter).comp successorLiftHom.f =
    strictIteration liftedNaturals chooseNextParameter :=
  strictIteration_transport _ _ successorLiftHom _ _ parameter_intertwines

theorem shifted_iteration_keeps_eighteen :
    (strictIteration liftedNaturals ((contextMap successor (programLift N)).comp chooseParameter)).toFun
      ((17 : Nat), ⟨2⟩) = some (18 : Nat) := strictIteration_succ _ _ _ 1

example : (contextMap successor iterationCuts).comp (strictIteration liftedNaturals chooseParameter) =
    strictIteration liftedNaturals ((contextMap successor (programLift N)).comp chooseParameter) :=
  strictIteration_substitution _ _ _

theorem parameter_selected_keeps_seventeen (hc : CutComplete (programLift N)) :
    (cutSelected liftedNaturals hc chooseParameter).toFun (17 : Nat) = some (17 : Nat) :=
  (congrArg (fun f => f.toFun (17 : Nat)) (cutSelected_fixed liftedNaturals hc chooseParameter)).symm

example (hc : CutComplete (programLift N)) :
    (cutSelected liftedNaturals hc chooseParameter).comp successorLiftHom.f =
      cutSelected liftedNaturals hc chooseNextParameter :=
  cutSelected_transport _ _ hc hc successorLiftHom _ _ parameter_intertwines

example (hc : CutComplete (programLift N)) :
    successor.comp (cutSelected liftedNaturals hc chooseParameter) =
      cutSelected liftedNaturals hc ((contextMap successor (programLift N)).comp chooseParameter) :=
  cutSelected_substitution _ hc _ _

abbrev U := encoded Unit

local instance : Subsingleton U.Carrier := inferInstanceAs (Subsingleton Unit)

def terminalMap (A : Assembly.{0}) : Hom A U where
  toFun _ := ()
  tracked := by
    refine ⟨fun _ => Part.some (encode ()), Nat.Partrec.of_primrec (Nat.Primrec.const _), ?_⟩
    intro x e h
    exact ⟨encode (), by simp, rfl⟩

theorem terminal_complete : CutComplete U := by
  intro Γ
  constructor
  · intro f g h
    exact Hom.ext fun _ => Subsingleton.elim _ _
  · intro h
    exact ⟨terminalMap _, Hom.ext fun _ => Subsingleton.elim _ _⟩

def terminalAlgebra : Monad.Algebra programLiftMonad where
  A := U
  a := terminalMap _
  unit := Hom.ext fun _ => Subsingleton.elim _ _
  assoc := Hom.ext fun _ => Subsingleton.elim _ _

example : ∃ q : Code, Tracks U U q.eval
    (cutSelected terminalAlgebra terminal_complete (terminalMap _)).toFun :=
  (cutSelected terminalAlgebra terminal_complete (terminalMap _)).has_code

/-- This is conditional on the genuine all-context completeness obligation
owned by P4. The fixed-point equations alone admit other answers. -/
theorem identity_selection_is_bottom (hc : CutComplete (programLift N)) :
    (cutSelected liftedNaturals hc (snd U (programLift N))).toFun () = none :=
  cutSelected_identity (Γ := U) liftedNaturals hc ()

theorem identity_has_distinct_fixed_points :
    (Hom.id (programLift N)).toFun none = none ∧
    (Hom.id (programLift N)).toFun (some (17 : Nat)) = some (17 : Nat) ∧
    (none : (programLift N).Carrier) ≠ some (17 : Nat) :=
  ⟨rfl, rfl, by intro h; cases h⟩

def booleanNot : Hom (encoded Bool) (encoded Bool) :=
  ofComputable Bool.not (Primrec.dom_bool _).to_comp

/-- A tracked endomap alone does not provide complete strict-algebra structure. -/
theorem boolean_not_complete_strict (a : Hom (programLift (encoded Bool)) (encoded Bool))
    (hu : (programLiftUnit (encoded Bool)).comp a = Hom.id (encoded Bool))
    (ha : (programLiftMul (encoded Bool)).comp a = (programLiftMap a).comp a)
    (hc : CutComplete (encoded Bool)) : False := by
  let X : Monad.Algebra programLiftMonad := ⟨encoded Bool, a, hu, ha⟩
  let g : Hom (prod U (encoded Bool)) (encoded Bool) := (snd _ _).comp booleanNot
  have h := congrArg (fun f => f.toFun ()) (cutSelected_fixed X hc g)
  change Bool.not ((cutSelected X hc g).toFun ()) = (cutSelected X hc g).toFun () at h
  have no : ∀ b : Bool, Bool.not b ≠ b := by intro b; cases b <;> decide
  exact no _ h

end InternalIteration
