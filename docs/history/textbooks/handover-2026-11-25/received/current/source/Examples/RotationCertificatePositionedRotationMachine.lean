import Applications.Resources.RotationCertificate.PositionedRotationMachine

/-!
# Connected clients of finite positioned rotation

The literal cases were fixed independently before implementation. Execution
contracts below refer to the actual finite program and its physical stores.
Source-event work, machine clocks, first live return, caller steps, present halt
and outer none are separate observations. A genuine one-input initializer does
not install a physical path. The general represented contract retains arbitrary
old saved words and untouched suffixes.

The universal contracts cover dirty phase execution, shared inclusive prefixes,
exact first-return timing, dependent cell bounds, represented source semantics
and physical caller composition. Literal boundary and malformed-word fixtures
consume the same public execution interfaces.
-/

namespace Examples.RotationCertificatePositionedRotationMachine

open Trees Resources.RotationCertificate
open Search.SharedTree (Branch)
open Trees.Rotations (RotationDirection RotationMove)
open Resources.RotationCertificate.PositionedRotationMachine

def ProtectedAlphabet : Fin 2 → Type := Fin.cases Tag (fun _ => Unit)

instance protectedAlphabetFintype (k : Fin 2) : Fintype (ProtectedAlphabet k) :=
  Fin.cases (motive := fun k : Fin 2 => Fintype (ProtectedAlphabet k))
    (inferInstance : Fintype Tag) (fun _ => (inferInstance : Fintype Unit)) k

def protectedWords (tags : Word) (units : List Unit) :
    ∀ k, List (ProtectedAlphabet k) := Fin.cases tags (fun _ => units)

def ordinaryContext : ∀ k, List (ProtectedAlphabet k) :=
  protectedWords [15, 2, 7, 10, 3] [(), ()]

def emptyContext : ∀ k, List (ProtectedAlphabet k) := protectedWords [] []
def stale (flag : Bool) : Registers Bool :=
  ((some .right, (some (15 : Tag), some ())), flag)
def clean (flag : Bool) : Registers Bool := ((none, (none, none)), flag)

abbrev ExampleCfg := Cfg ProtectedAlphabet Unit Bool
abbrev ExampleCaller := External Unit → Statement ProtectedAlphabet Unit Bool

def data (X F S : Word) (H : List Unit) (P : List Branch) : LocalData :=
  { source := X, saved := F, scratch := S, pending := H, path := P }

def atPhase (q : Phase) (flag : Bool) (D : LocalData) : ExampleCfg :=
  cfg (some (phaseLabel q)) (stale flag) D ordinaryContext
def atResult (r : Result) (flag : Bool) (D : LocalData) : ExampleCfg :=
  cfg (some (resultLabel r)) (clean flag) D ordinaryContext
def cleanEntry (d : RotationDirection) (flag : Bool)
    (w : Word) (p : List Branch) : ExampleCfg :=
  atPhase (.seek d) flag (data w [] [] [] p)

def nilTree : BinaryTree Unit := .nil
def oneTree : BinaryTree Unit := .node () nilTree nilTree
def rightTwo : BinaryTree Unit := .node () nilTree oneTree
def leftTwo : BinaryTree Unit := .node () oneTree nilTree
def balancedThree : BinaryTree Unit := .node () oneTree oneTree
def leftContext : BinaryTree Unit := .node () rightTwo nilTree
def rightContext : BinaryTree Unit := .node () oneTree rightTwo
def twoRightTwos : BinaryTree Unit := .node () rightTwo rightTwo
def afterLeftContext : BinaryTree Unit := .node () leftTwo nilTree

def dirtyData : LocalData := data [15, 0] [12, 3] [8, 5] [(), ()] [.right, .left]
def dirtyPhaseA : LocalData := data [1, 1, 0, 0, 0, 14] [15, 2] [3, 1] [] [.right, .left]
def dirtyPhaseB : LocalData := data [15, 0, 1] [15, 2] [3, 1] [(), ()] [.right, .left]

def Runs {K Λ R : Type} {Γ : K → Type} [DecidableEq K]
    (caller : External Λ → Statement Γ Λ R) (start : Cfg Γ Λ R) (n : Nat)
    (finish : Cfg Γ Λ R) : Prop :=
  (next caller)^[n] (some start) = some finish

def FirstRun {K Λ R : Type} {Γ : K → Type} [DecidableEq K]
    (caller : External Λ → Statement Γ Λ R) (start : Cfg Γ Λ R) (n : Nat)
    (finish : Cfg Γ Λ R) : Prop :=
  Runs caller start n finish ∧ ¬ Owned finish.l ∧
    ∀ k, k < n → ∃ reached,
      Runs caller start k reached ∧ Owned reached.l

structure RunFixture where
  phase : Phase
  before : LocalData
  result : Result
  after : LocalData
  ticks : Nat

def RunFixture.Expected (c : RunFixture) (caller : ExampleCaller)
    (flag : Bool) : Prop :=
  FirstRun caller (atPhase c.phase flag c.before) c.ticks
    (atResult c.result flag c.after)

def CarrierExpected : Prop :=
  Fintype.card LocalStack = 5 ∧ Fintype.card Phase = 16 ∧
  Fintype.card Result = 2 ∧ Fintype.card Temporaries = 102 ∧
  Fintype.card (StackId (Fin 2)) = 7 ∧ Fintype.card (Label Unit) = 19 ∧
  Fintype.card (Registers Bool) = 204 ∧
  Fintype.card (OwnedLabel Unit) = 16 ∧
  Fintype.card (OwnedLabel Nat) = 16 ∧ contextCells ordinaryContext = 7

def transferFixtures : List RunFixture :=
  [ ⟨.restoreScratch .successLeft, dirtyData, .success,
      data [3,12,1,1,5,8,15,0] [] [] [(),()] [.right,.left], 6⟩,
    ⟨.restoreScratch .successRight, dirtyData, .success,
      data [3,12,1,5,8,15,0] [] [] [(),()] [.right,.left], 6⟩,
    ⟨.restoreScratch .failureLeft, dirtyData, .failure,
      data [3,12,1,5,8,15,0] [] [] [] [.right,.left], 9⟩,
    ⟨.restoreScratch .failureRight, dirtyData, .failure,
      data [3,12,1,1,5,8,15,0] [] [] [] [.right,.left], 9⟩,
    ⟨.dropPending, dirtyData, .failure,
      data [3,12,15,0] [] [8,5] [] [.right,.left], 6⟩,
    ⟨.restorePrefix .success, dirtyData, .success,
      data [3,12,15,0] [] [8,5] [(),()] [.right,.left], 3⟩,
    ⟨.restorePrefix .failure, dirtyData, .failure,
      data [3,12,15,0] [] [8,5] [(),()] [.right,.left], 3⟩ ]

def ScratchSplitExpected (caller : ExampleCaller) (flag : Bool)
    (mode : RestoreMode) (X F A B : Word) (H : List Unit) (P : List Branch) : Prop :=
  Runs caller (atPhase (.restoreScratch mode) flag (data X F (A ++ B) H P)) A.length
    (cfg (some (phaseLabel (.restoreScratch mode)))
      (if A = [] then stale flag else clean flag)
      (data (A.reverse ++ X) F B H P) ordinaryContext)

def SavedSplitExpected (caller : ExampleCaller) (flag : Bool)
    (r : Result) (X A B S : Word) (H : List Unit) (P : List Branch) : Prop :=
  Runs caller (atPhase (.restorePrefix r) flag (data X (A ++ B) S H P)) A.length
    (cfg (some (phaseLabel (.restorePrefix r)))
      (if A = [] then stale flag else clean flag)
      (data (A.reverse ++ X) B S H P) ordinaryContext)

def PendingSplitExpected (caller : ExampleCaller) (flag : Bool)
    (X F S : Word) (A B : List Unit) (P : List Branch) : Prop :=
  Runs caller (atPhase .dropPending flag (data X F S (A ++ B) P)) A.length
    (cfg (some (phaseLabel .dropPending))
      (if A = [] then stale flag else clean flag)
      (data X F S B P) ordinaryContext)

def rawFixtures : List RunFixture :=
  [ ⟨.seek .left, data [] [] [] [] [], .failure, data [] [] [] [] [], 4⟩,
    ⟨.seek .right, data [] [] [] [] [], .failure, data [] [] [] [] [], 4⟩,
    ⟨.seek .left, data [15,0] [] [] [] [.left,.right], .failure,
      data [15,0] [] [] [] [.right], 3⟩,
    ⟨.seek .right, data [1,15,0] [] [] [] [], .failure, data [1,15,0] [] [] [] [], 4⟩,
    ⟨.seek .left, data [1,15,0] [] [] [] [], .failure, data [1,15,0] [] [] [] [], 7⟩,
    ⟨.seek .right, data [1,1,15,0] [] [] [] [], .failure, data [1,1,15,0] [] [] [] [], 7⟩,
    ⟨.seek .left, data [1,0,15,2] [] [] [] [], .failure, data [1,0,15,2] [] [] [] [], 8⟩,
    ⟨.seek .left, data [1,0,1,15] [] [] [] [], .success, data [1,1,0,15] [] [] [] [], 7⟩,
    ⟨.seek .right, data [1,1,0,15] [] [] [] [], .success, data [1,0,1,15] [] [] [] [], 6⟩,
    ⟨.seek .left, data [0] [] [] [] [.left,.right,.left], .failure,
      data [0] [] [] [] [.right,.left], 3⟩,
    ⟨.seek .right, data [0] [] [] [] [.left,.right,.left], .failure,
      data [0] [] [] [] [.right,.left], 3⟩,
    ⟨.seek .left, data [1,0,1,0,0] [] [] [()] [], .failure,
      data [1,0,1,0,0] [] [] [] [], 14⟩ ]

structure RepresentedFixture where
  tree : BinaryTree Unit
  move : RotationMove
  value : Option (BinaryTree Unit)
  sourceWork : Nat
  ticks : Nat
  remaining : List Branch

def representedFixtures : List RepresentedFixture :=
  [ ⟨nilTree, ⟨.left, []⟩, none, 3, 4, []⟩,
    ⟨nilTree, ⟨.right, []⟩, none, 3, 4, []⟩,
    ⟨oneTree, ⟨.left, []⟩, none, 3, 8, []⟩,
    ⟨oneTree, ⟨.right, []⟩, none, 3, 4, []⟩,
    ⟨rightTwo, ⟨.left, []⟩, some leftTwo, 5, 7, []⟩,
    ⟨leftTwo, ⟨.right, []⟩, some rightTwo, 5, 6, []⟩,
    ⟨leftContext, ⟨.left, [.left]⟩, some afterLeftContext, 8, 9, []⟩,
    ⟨rightContext, ⟨.left, [.right]⟩, some (.node () oneTree leftTwo), 8, 15, []⟩,
    ⟨oneTree, ⟨.right, [.left,.right,.left]⟩, none, 4, 5, [.left]⟩,
    ⟨rightTwo, ⟨.left, [.right,.left,.right]⟩, none, 6, 9, []⟩,
    ⟨leftContext, ⟨.left, []⟩, none, 3, 16, []⟩,
    ⟨twoRightTwos, ⟨.left, [.left]⟩, some (.node () leftTwo rightTwo), 8, 9, []⟩,
    ⟨twoRightTwos, ⟨.left, [.right]⟩, some (.node () rightTwo leftTwo), 8, 19, []⟩ ]

def RepresentedFixture.Expected (c : RepresentedFixture) (caller : ExampleCaller)
    (flag : Bool) (F z : Word) : Prop :=
  applyMoveRun c.move c.tree = (c.value, c.sourceWork) ∧
  representedClock c.move.direction c.move.position c.tree = c.ticks ∧
  remainingPath c.move.position c.tree = c.remaining ∧
  FirstRun caller
    (atPhase (.seek c.move.direction) flag
      (data (treeCode c.tree ++ z) F [] [] c.move.position))
    (c.ticks + F.length)
    (atResult (if c.value.isSome then .success else .failure) flag
      (data (F.reverse ++ treeCode (c.value.getD c.tree) ++ z) [] [] [] c.remaining))

def FirstSuccess {K Λ R : Type} {Γ : K → Type} [DecidableEq K]
    (caller : External Λ → Statement Γ Λ R) (start : Cfg Γ Λ R) : Prop :=
  ∃ ticks finish, FirstRun caller start ticks finish ∧
    finish.l = some (resultLabel .success)

def RootSuccessIffExpected (caller : ExampleCaller) (flag : Bool) (w : Word) : Prop :=
  (FirstSuccess caller (cleanEntry .left flag w []) ↔
    ∃ A : BinaryTree Unit, ∃ z : Word, w = [1] ++ treeCode A ++ [1] ++ z) ∧
  (FirstSuccess caller (cleanEntry .right flag w []) ↔
    ∃ A : BinaryTree Unit, ∃ z : Word, w = [1,1] ++ treeCode A ++ z)

def LeftRootPatternExpected (caller : ExampleCaller) (flag : Bool)
    (A : BinaryTree Unit) (z : Word) : Prop :=
  let w := [1] ++ treeCode A ++ [1] ++ z
  let ticks := 2 * (treeCode A).length + 5
  runSteps .left w [] = ticks ∧
    FirstRun caller (cleanEntry .left flag w []) ticks
      (atResult .success flag (data ([1,1] ++ treeCode A ++ z) [] [] [] []))

def RightRootPatternExpected (caller : ExampleCaller) (flag : Bool)
    (A : BinaryTree Unit) (z : Word) : Prop :=
  let w := [1,1] ++ treeCode A ++ z
  let ticks := 2 * (treeCode A).length + 4
  runSteps .right w [] = ticks ∧
    FirstRun caller (cleanEntry .right flag w []) ticks
      (atResult .success flag (data ([1] ++ treeCode A ++ [1] ++ z) [] [] [] []))

def PrefixExpected {K Λ R : Type} {Γ : K → Type}
    [DecidableEq K] [Fintype K]
    (caller : External Λ → Statement Γ Λ R) (start : Cfg Γ Λ R)
    (n : Nat) : Prop :=
  n ≤ remainingSteps start → ∃ reached,
    (next caller)^[n] (some start) = some reached ∧
    remainingSteps reached = remainingSteps start - n ∧
    Relation.ReflTransGen (LocalStep caller) start reached ∧
    (n < remainingSteps start ↔ Owned reached.l) ∧
    (n = 0 → reached = start) ∧
    reached.var = (if n = 0 then start.var else reset start.var) ∧
    (∀ k, reached.stk (.inr k) = start.stk (.inr k)) ∧
    tagCells reached + debt reached.l = tagCells start + debt start.l ∧
    potential reached ≤ potential start ∧ stackCells reached ≤ potential start

abbrev Boundary := Nat × (Phase ⊕ Result) × LocalData × Nat

def leftBoundaries : List Boundary :=
  [ (0, .inl (.seek .left), data [1,0,1,0,0] [] [] [] [], 5),
    (1, .inl (.start .left), data [1,0,1,0,0] [] [] [] [], 5),
    (2, .inl (.scanScratch .left), data [0,1,0,0] [] [] [()] [], 5),
    (3, .inl .checkRight, data [1,0,0] [] [0] [] [], 4),
    (4, .inl (.restoreScratch .successLeft), data [0,0] [] [0] [] [], 3),
    (5, .inl (.restoreScratch .successLeft), data [0,0,0] [] [] [] [], 3),
    (6, .inl (.restorePrefix .success), data [1,1,0,0,0] [] [] [] [], 5),
    (7, .inr .success, data [1,1,0,0,0] [] [] [] [], 5) ]

def rightBoundaries : List Boundary :=
  [ (0, .inl (.seek .right), data [1,1,0,0,0] [] [] [] [], 5),
    (1, .inl (.start .right), data [1,1,0,0,0] [] [] [] [], 5),
    (2, .inl (.scanScratch .right), data [0,0,0] [] [] [()] [], 4),
    (3, .inl (.restoreScratch .successRight), data [1,0,0] [] [0] [] [], 4),
    (4, .inl (.restoreScratch .successRight), data [0,1,0,0] [] [] [] [], 4),
    (5, .inl (.restorePrefix .success), data [1,0,1,0,0] [] [] [] [], 5),
    (6, .inr .success, data [1,0,1,0,0] [] [] [] [], 5) ]

def haltCaller : ExampleCaller := fun _ => .halt

def sentinelCaller (marker : Tag) : ExampleCaller
  | .inl _ => .push (.inr (0 : Fin 2)) (fun _ => marker) .halt
  | .inr _ => .halt

def allocatingCaller : ExampleCaller
  | .inl r => .push (.inr (1 : Fin 2)) (fun _ => ())
      (.goto (fun _ => resultLabel r))
  | .inr _ => .halt

def misleadingCaller : ExampleCaller
  | .inl .success => .goto (fun _ => resultLabel .failure)
  | .inl .failure => .goto (fun _ => resultLabel .success)
  | .inr _ => .halt

def externalCaller : ExampleCaller
  | .inl _ => .goto (fun _ => callerLabel ())
  | .inr _ => .push (.inr (0 : Fin 2)) (fun _ => (13 : Tag)) .halt

def inverseCaller (reinstall : Bool) : ExampleCaller
  | .inl .success =>
      if reinstall then
        .push (.inl .path) (fun _ => .left)
          (.goto (fun _ => phaseLabel (.seek .right)))
      else .goto (fun _ => phaseLabel (.seek .right))
  | .inl .failure => .halt
  | .inr _ => .halt

def appendTimed (caller : ExampleCaller) (start middle : ExampleCfg)
    (finish : Option ExampleCfg) (q k : Nat)
    (first : StateTransition.EvalsToInTime (step caller) start (some middle) q)
    (second : StateTransition.EvalsToInTime (step caller) middle finish k) :
    StateTransition.EvalsToInTime (step caller) start finish (k + q) :=
  StateTransition.EvalsToInTime.trans (step caller) q k start middle finish first second

def concreteMachine (d : RotationDirection) (caller : ExampleCaller)
    (initial : Bool) : Turing.FinTM2 := machine caller d initial

/-- The dimensions come from the actual finite carriers supplied to the program. -/
theorem actual_finite_carrier_counts :
    Fintype.card LocalStack = 5 ∧ Fintype.card Phase = 16 ∧
      Fintype.card Result = 2 ∧ Fintype.card Temporaries = 102 ∧
      Fintype.card (StackId (Fin 2)) = 7 ∧ Fintype.card (Label Unit) = 19 ∧
      Fintype.card (Registers Bool) = 204 := by
  refine ⟨card_localStack, card_phase, card_result, card_temporaries, ?_, ?_, ?_⟩
  · simpa using (card_stackId (K := Fin 2))
  · simpa using (card_label (Λ := Unit))
  · exact card_registers (R := Bool)

/-- An infinite external control type does not enlarge the owned phase subtype. -/
theorem owned_labels_stay_finite_with_nat_callers :
    Fintype.card (OwnedLabel Unit) = 16 ∧ Fintype.card (OwnedLabel Nat) = 16 :=
  ⟨card_ownedLabel, card_ownedLabel⟩

theorem every_actual_stack_alphabet_is_finite (k : StackId (Fin 2)) :
    Nonempty (Fintype (alphabet ProtectedAlphabet k)) := ⟨inferInstance⟩

/-- All finite observations can be stale without changing the caller projection. -/
theorem reset_all_102_temporary_values (temps : Temporaries) (flag : Bool) :
    reset (temps, flag) = clean flag ∧ (reset (temps, flag)).2 = flag := ⟨rfl, rfl⟩

theorem physical_fixture_projection (q : Option (Label Unit)) (flag : Bool)
    (D : LocalData) :
    (cfg q (stale flag) D ordinaryContext).stk (.inl .source) = D.source ∧
      (cfg q (stale flag) D ordinaryContext).stk (.inl .saved) = D.saved ∧
      (cfg q (stale flag) D ordinaryContext).stk (.inl .scratch) = D.scratch ∧
      (cfg q (stale flag) D ordinaryContext).stk (.inl .pending) = D.pending ∧
      (cfg q (stale flag) D ordinaryContext).stk (.inl .path) = D.path ∧
      (cfg q (stale flag) D ordinaryContext).stk (.inr (0 : Fin 2)) = ([15,2,7,10,3] : Word) ∧
      (cfg q (stale flag) D ordinaryContext).stk (.inr (1 : Fin 2)) = [(),()] :=
  ⟨rfl, rfl, rfl, rfl, rfl, rfl, rfl⟩

theorem literal_tree_codes :
    treeCode nilTree = [0] ∧ treeCode oneTree = [1,0,0] ∧
      treeCode rightTwo = [1,0,1,0,0] ∧ treeCode leftTwo = [1,1,0,0,0] ∧
      treeCode balancedThree = [1,1,0,0,1,0,0] ∧
      treeCode leftContext = [1,1,0,1,0,0,0] ∧
      treeCode rightContext = [1,1,0,0,1,0,1,0,0] ∧
      treeCode afterLeftContext = [1,1,1,0,0,0,0] :=
  ⟨rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl⟩

/-- The fixed source tariffs use the actual source program, independently of TM2 clocks. -/
theorem every_represented_fixture_has_its_source_result
    (c : RepresentedFixture) (member : c ∈ representedFixtures) :
    applyMoveRun c.move c.tree = (c.value, c.sourceWork) := by
  simp only [representedFixtures, List.mem_cons, List.mem_nil_iff, or_false] at member
  rcases member with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl |
    rfl | rfl | rfl <;> rfl

theorem every_represented_fixture_has_its_fixed_clock_and_remaining_path
    (c : RepresentedFixture) (member : c ∈ representedFixtures) :
    representedClock c.move.direction c.move.position c.tree = c.ticks ∧
      remainingPath c.move.position c.tree = c.remaining := by
  simp only [representedFixtures, List.mem_cons, List.mem_nil_iff, or_false] at member
  rcases member with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl |
    rfl | rfl | rfl <;> exact ⟨rfl, rfl⟩

/-- Equal path depth and equal source tariff do not determine the physical clock. -/
theorem the_same_tree_has_source_eight_but_machine_nine_and_nineteen :
    (applyMoveRun ⟨.left, [.left]⟩ twoRightTwos).2 = 8 ∧
      (applyMoveRun ⟨.left, [.right]⟩ twoRightTwos).2 = 8 ∧
      representedClock .left [.left] twoRightTwos = 9 ∧
      representedClock .left [.right] twoRightTwos = 19 ∧
      navigationLength [.left] twoRightTwos = 1 ∧
      navigationLength [.right] twoRightTwos = 6 :=
  ⟨rfl, rfl, rfl, rfl, rfl, rfl⟩

theorem the_missing_cursor_and_physical_tail_are_distinct :
    stoppedPath [.left,.right,.left] oneTree = [.right,.left] ∧
      remainingPath [.left,.right,.left] oneTree = [.left] ∧
      descentCount [.left,.right,.left] oneTree = 1 := ⟨rfl, rfl, rfl⟩

/-- Neither malformed mirror word is even an accepted complete-tree prefix. -/
theorem malformed_mirror_words_are_not_tree_codes :
    (parseTreeRun [1,0,1,15]).1 = none ∧
      (parseTreeRun [1,1,0,15]).1 = none := ⟨rfl, rfl⟩

theorem source_inverse_keeps_the_original_position :
    (RotationMove.opposite ⟨.left, [.left]⟩).position = [.left] ∧
      applyMoveRun ⟨.left, [.left]⟩ leftContext = (some afterLeftContext, 8) ∧
      applyMoveRun ⟨.right, [.left]⟩ afterLeftContext = (some leftContext, 8) ∧
      applyMoveRun ⟨.right, []⟩ afterLeftContext = (some balancedThree, 5) ∧
      balancedThree ≠ leftContext := by
  refine ⟨rfl, rfl, rfl, rfl, ?_⟩
  intro same
  have codes := congrArg treeCode same
  change ([1,1,0,0,1,0,0] : Word) = [1,1,0,1,0,0,0] at codes
  exact (by decide : ([1,1,0,0,1,0,0] : Word) ≠ [1,1,0,1,0,0,0]) codes

/-- Concatenation uses actual iterates, never a free replacement of the middle state. -/
theorem runs_trans (caller : ExampleCaller) (start middle finish : ExampleCfg)
    (q k : Nat) (first : Runs caller start q middle)
    (second : Runs caller middle k finish) : Runs caller start (q + k) finish := by
  unfold Runs at *
  rw [Nat.add_comm q k, Function.iterate_add_apply, first, second]

/-- Strict earlier control comes from an actual owned segment, not its eventual endpoint. -/
theorem local_run_has_owned_strict_prefixes {K Λ R : Type} {Γ : K → Type} [DecidableEq K]
    (caller : External Λ → Statement Γ Λ R)
    {ticks : Nat} {start finish : Cfg Γ Λ R} (segment : LocalRun caller ticks start finish) :
    ∀ k, k < ticks → ∃ reached, Runs caller start k reached ∧ Owned reached.l := by
  induction segment with
  | refl c => intro k strict; omega
  | @cons ticks before middle after head tail ih =>
      intro k strict
      cases k with
      | zero => exact ⟨before, rfl, head.1⟩
      | succ k =>
          obtain ⟨reached, executed, owned⟩ := ih k (by omega)
          refine ⟨reached, ?_, owned⟩
          exact (iterate_step caller k before middle head.2).trans executed

theorem firstRun_of_localRun {K Λ R : Type} {Γ : K → Type} [DecidableEq K]
    (caller : External Λ → Statement Γ Λ R) {ticks : Nat}
    {start finish : Cfg Γ Λ R} (segment : LocalRun caller ticks start finish)
    (external : ¬ Owned finish.l) : FirstRun caller start ticks finish :=
  ⟨LocalRun.iterate caller segment, external, local_run_has_owned_strict_prefixes caller segment⟩

/-- Uniqueness requires ownership before the proposed return, even for looping callers. -/
theorem firstRun_unique {K Λ R : Type} {Γ : K → Type} [DecidableEq K]
    (caller : External Λ → Statement Γ Λ R) {start left right : Cfg Γ Λ R}
    {m n : Nat} (first : FirstRun caller start m left)
    (second : FirstRun caller start n right) : m = n ∧ left = right := by
  have m_le_n : m ≤ n := by
    by_contra beyond
    obtain ⟨reached, executed, owned⟩ := first.2.2 n (by omega)
    have same : reached = right := Option.some.inj (executed.symm.trans second.1)
    exact second.2.1 (same ▸ owned)
  have n_le_m : n ≤ m := by
    by_contra beyond
    obtain ⟨reached, executed, owned⟩ := second.2.2 m (by omega)
    have same : reached = left := Option.some.inj (executed.symm.trans first.1)
    exact first.2.1 (same ▸ owned)
  have counts : m = n := by omega
  subst n
  exact ⟨rfl, Option.some.inj (first.1.symm.trans second.1)⟩

def localRunInTime {K Λ R : Type} {Γ : K → Type} [DecidableEq K]
    (caller : External Λ → Statement Γ Λ R) {ticks : Nat}
    {start finish : Cfg Γ Λ R} (segment : LocalRun caller ticks start finish) :
    StateTransition.EvalsToInTime (step caller) start (some finish) ticks where
  steps := ticks
  evals_in_steps := LocalRun.iterate caller segment
  steps_le_m := Nat.le_refl _

theorem append_actual_step (caller : ExampleCaller) (n : Nat)
    (start reached : ExampleCfg) (finish : Option ExampleCfg)
    (executed : (next caller)^[n] (some start) = some reached)
    (continued : step caller reached = finish) :
    (next caller)^[n + 1] (some start) = finish := by
  rw [Function.iterate_succ_apply', executed, next_some, continued]

def oneActualStepTime (caller : ExampleCaller) (start : ExampleCfg)
    (finish : Option ExampleCfg) (executed : step caller start = finish) :
    StateTransition.EvalsToInTime (step caller) start finish 1 where
  steps := 1
  evals_in_steps := executed
  steps_le_m := Nat.le_refl _

theorem a_present_halt_has_one_further_outer_none (caller : ExampleCaller)
    (regs : Registers Bool) (D : LocalData)
    (ctx : ∀ k, List (ProtectedAlphabet k)) :
    step caller (cfg none regs D ctx) = none := rfl

theorem the_zero_step_preserves_stale_registers (caller : ExampleCaller)
    (q : Phase) (flag : Bool) (D : LocalData) :
    (next caller)^[0] (some (atPhase q flag D)) = some (atPhase q flag D) ∧
      (atPhase q flag D).var = stale flag ∧ stale flag ≠ clean flag := by
  refine ⟨rfl, rfl, ?_⟩
  intro same
  have branch := congrArg (fun regs : Registers Bool => regs.1.1) same
  cases branch

/-- The caller is one real push/halt block and preserves every local store. -/
theorem sentinel_push_step (marker : Tag) (r : Result) (regs : Registers Bool)
    (D : LocalData) (tags : Word) (units : List Unit) :
    step (sentinelCaller marker)
        (cfg (some (resultLabel r)) regs D (protectedWords tags units)) =
      some (cfg none regs D (protectedWords (marker :: tags) units)) := by
  apply congrArg some
  apply cfg_ext
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · intro k
    fin_cases k <;> rfl

theorem allocation_is_an_actual_protected_unit_push (r : Result)
    (regs : Registers Bool) (D : LocalData) (tags : Word) (units : List Unit) :
    step allocatingCaller
        (cfg (some (resultLabel r)) regs D (protectedWords tags units)) =
      some (cfg (some (resultLabel r)) regs D (protectedWords tags (() :: units))) := by
  apply congrArg some
  apply cfg_ext
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · intro k
    fin_cases k <;> rfl

theorem a_caller_can_forge_the_opposite_result (regs : Registers Bool)
    (D : LocalData) (ctx : ∀ k, List (ProtectedAlphabet k)) :
    step misleadingCaller (cfg (some (resultLabel .success)) regs D ctx) =
        some (cfg (some (resultLabel .failure)) regs D ctx) ∧
      step misleadingCaller (cfg (some (resultLabel .failure)) regs D ctx) =
        some (cfg (some (resultLabel .success)) regs D ctx) := ⟨rfl, rfl⟩

theorem separate_external_label_is_reached_first (r : Result)
    (regs : Registers Bool) (D : LocalData)
    (ctx : ∀ k, List (ProtectedAlphabet k)) :
    step externalCaller (cfg (some (resultLabel r)) regs D ctx) =
      some (cfg (some (callerLabel ())) regs D ctx) := rfl

theorem external_label_executes_its_own_push_and_halt (regs : Registers Bool)
    (D : LocalData) (tags : Word) (units : List Unit) :
    step externalCaller
        (cfg (some (callerLabel ())) regs D (protectedWords tags units)) =
      some (cfg none regs D (protectedWords (13 :: tags) units)) := by
  apply congrArg some
  apply cfg_ext
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · intro k
    fin_cases k <;> rfl

/-- A goto cannot restore the consumed path. -/
theorem inverse_reentry_without_push (regs : Registers Bool) (D : LocalData)
    (ctx : ∀ k, List (ProtectedAlphabet k)) :
    step (inverseCaller false) (cfg (some (resultLabel .success)) regs D ctx) =
      some (cfg (some (phaseLabel (.seek .right))) regs D ctx) := rfl

/-- The actual push and goto together cost one outer activation. -/
theorem inverse_reentry_with_physical_push (regs : Registers Bool) (D : LocalData)
    (ctx : ∀ k, List (ProtectedAlphabet k)) :
    step (inverseCaller true) (cfg (some (resultLabel .success)) regs D ctx) =
      some (cfg (some (phaseLabel (.seek .right))) regs
        { D with path := .left :: D.path } ctx) := by
  apply congrArg some
  apply cfg_ext <;> first | rfl | exact fun _ => rfl

section FiniteTable

variable {K Λ R : Type} {Γ : K → Type} [DecidableEq K]
variable (caller : External Λ → Statement Γ Λ R)
variable (regs : Registers R) (ctx : ∀ k, List (Γ k))
variable (X F S : Word) (H : List Unit) (P : List Branch)

/-- Empty path, left descent and right descent use three different actual blocks. -/
theorem seek_path_and_node_observations (d : RotationDirection) :
    step caller (cfg (some (phaseLabel (.seek d))) regs (data X F S H []) ctx) =
        some (cfg (some (phaseLabel (.start d))) (reset regs) (data X F S H []) ctx) ∧
      step caller (cfg (some (phaseLabel (.seek d))) regs
          (data (1 :: X) F S H (.left :: P)) ctx) =
        some (cfg (some (phaseLabel (.seek d))) (reset regs) (data X (1 :: F) S H P) ctx) ∧
      step caller (cfg (some (phaseLabel (.seek d))) regs
          (data (1 :: X) F S H (.right :: P)) ctx) =
        some (cfg (some (phaseLabel (.scanPrefix d))) (reset regs)
          (data X (1 :: F) S (() :: H) P) ctx) :=
  ⟨seek_step_path_nil caller d (data X F S H []) regs ctx,
    seek_step_node_left caller d X P (data X F S H P) regs ctx,
    seek_step_node_right caller d X P (data X F S H P) regs ctx⟩

/-- The unsuccessful branch observation remains consumed even when source is restored. -/
theorem seek_failure_consumes_exactly_one_path_head (d : RotationDirection)
    (b : Branch) (a : Tag) (notNode : a ≠ nodeTag) :
    step caller (cfg (some (phaseLabel (.seek d))) regs (data [] F S H (b :: P)) ctx) =
        some (cfg (some (phaseLabel .dropPending)) (reset regs) (data [] F S H P) ctx) ∧
      step caller (cfg (some (phaseLabel (.seek d))) regs
          (data (a :: X) F S H (b :: P)) ctx) =
        some (cfg (some (phaseLabel .dropPending)) (reset regs) (data (a :: X) F S H P) ctx) :=
  ⟨seek_step_source_nil caller d b P (data X F S H P) regs ctx,
    seek_step_source_nonnode caller d b P a X (data X F S H P) regs ctx notNode⟩

/-- Zero, one and at least two old pending cells remain distinct observations. -/
theorem prefix_scanner_counts_the_peek_after_pop (d : RotationDirection) :
    step caller (cfg (some (phaseLabel (.scanPrefix d))) regs (data (1 :: X) F S H P) ctx) =
        some (cfg (some (phaseLabel (.scanPrefix d))) (reset regs)
          (data X (1 :: F) S (() :: H) P) ctx) ∧
      step caller (cfg (some (phaseLabel (.scanPrefix d))) regs (data (0 :: X) F S [] P) ctx) =
        some (cfg (some (phaseLabel (.seek d))) (reset regs) (data X (0 :: F) S [] P) ctx) ∧
      step caller (cfg (some (phaseLabel (.scanPrefix d))) regs (data (0 :: X) F S [()] P) ctx) =
        some (cfg (some (phaseLabel (.seek d))) (reset regs) (data X (0 :: F) S [] P) ctx) ∧
      step caller (cfg (some (phaseLabel (.scanPrefix d))) regs
          (data (0 :: X) F S (() :: () :: H) P) ctx) =
        some (cfg (some (phaseLabel (.scanPrefix d))) (reset regs)
          (data X (0 :: F) S (() :: H) P) ctx) :=
  ⟨scanPrefix_step_node caller d X (data X F S H P) regs ctx,
    scanPrefix_step_empty_finish caller d X (data X F S [] P) regs ctx rfl,
    scanPrefix_step_empty_finish caller d X (data X F S [()] P) regs ctx rfl,
    scanPrefix_step_empty_continue caller d X H (data X F S H P) regs ctx⟩

theorem prefix_scanner_restores_every_foreign_observation (d : RotationDirection)
    (a : Tag) (notNode : a ≠ nodeTag) (notEmpty : a ≠ emptyTag) :
    step caller (cfg (some (phaseLabel (.scanPrefix d))) regs (data [] F S H P) ctx) =
        some (cfg (some (phaseLabel .dropPending)) (reset regs) (data [] F S H P) ctx) ∧
      step caller (cfg (some (phaseLabel (.scanPrefix d))) regs (data (a :: X) F S H P) ctx) =
        some (cfg (some (phaseLabel .dropPending)) (reset regs) (data (a :: X) F S H P) ctx) :=
  ⟨scanPrefix_step_nil caller d (data X F S H P) regs ctx,
    scanPrefix_step_foreign caller d a X (data X F S H P) regs ctx notNode notEmpty⟩

theorem left_start_keeps_failed_observations (a : Tag) (notNode : a ≠ nodeTag) :
    step caller (cfg (some (phaseLabel (.start .left))) regs (data (1 :: X) F S H P) ctx) =
        some (cfg (some (phaseLabel (.scanScratch .left))) (reset regs)
          (data X F S (() :: H) P) ctx) ∧
      step caller (cfg (some (phaseLabel (.start .left))) regs (data [] F S H P) ctx) =
        some (cfg (some (phaseLabel .dropPending)) (reset regs) (data [] F S H P) ctx) ∧
      step caller (cfg (some (phaseLabel (.start .left))) regs (data (a :: X) F S H P) ctx) =
        some (cfg (some (phaseLabel .dropPending)) (reset regs) (data (a :: X) F S H P) ctx) :=
  ⟨start_left_step_node caller X (data X F S H P) regs ctx,
    start_left_step_nil caller (data X F S H P) regs ctx,
    start_left_step_nonnode caller a X (data X F S H P) regs ctx notNode⟩

/-- The two root probes and any rollback occur in the same right-start activation. -/
theorem right_start_observes_and_restores_both_heads (a : Tag) (notNode : a ≠ nodeTag) :
    step caller (cfg (some (phaseLabel (.start .right))) regs
          (data (1 :: 1 :: X) F S H P) ctx) =
        some (cfg (some (phaseLabel (.scanScratch .right))) (reset regs)
          (data X F S (() :: H) P) ctx) ∧
      step caller (cfg (some (phaseLabel (.start .right))) regs (data [] F S H P) ctx) =
        some (cfg (some (phaseLabel .dropPending)) (reset regs) (data [] F S H P) ctx) ∧
      step caller (cfg (some (phaseLabel (.start .right))) regs (data (a :: X) F S H P) ctx) =
        some (cfg (some (phaseLabel .dropPending)) (reset regs) (data (a :: X) F S H P) ctx) ∧
      step caller (cfg (some (phaseLabel (.start .right))) regs (data [1] F S H P) ctx) =
        some (cfg (some (phaseLabel .dropPending)) (reset regs) (data [1] F S H P) ctx) ∧
      step caller (cfg (some (phaseLabel (.start .right))) regs
          (data (1 :: a :: X) F S H P) ctx) =
        some (cfg (some (phaseLabel .dropPending)) (reset regs)
          (data (1 :: a :: X) F S H P) ctx) :=
  ⟨start_right_step_nodes caller X (data X F S H P) regs ctx,
    start_right_step_first_nil caller (data X F S H P) regs ctx,
    start_right_step_first_nonnode caller a X (data X F S H P) regs ctx notNode,
    start_right_step_second_nil caller (data X F S H P) regs ctx,
    start_right_step_second_nonnode caller a X (data X F S H P) regs ctx notNode⟩

theorem scratch_scanner_continues_with_literal_old_accumulators (d : RotationDirection) :
    step caller (cfg (some (phaseLabel (.scanScratch d))) regs (data (1 :: X) F S H P) ctx) =
        some (cfg (some (phaseLabel (.scanScratch d))) (reset regs)
          (data X F (1 :: S) (() :: H) P) ctx) ∧
      step caller (cfg (some (phaseLabel (.scanScratch d))) regs
          (data (0 :: X) F S (() :: () :: H) P) ctx) =
        some (cfg (some (phaseLabel (.scanScratch d))) (reset regs)
          (data X F (0 :: S) (() :: H) P) ctx) :=
  ⟨scanScratch_step_node caller d X (data X F S H P) regs ctx,
    scanScratch_step_empty_continue caller d X H (data X F S H P) regs ctx⟩

/-- Right completion has already pushed its first source node when it returns. -/
theorem scratch_finishes_with_zero_or_one_old_slot :
    step caller (cfg (some (phaseLabel (.scanScratch .left))) regs (data (0 :: X) F S [] P) ctx) =
        some (cfg (some (phaseLabel .checkRight)) (reset regs) (data X F (0 :: S) [] P) ctx) ∧
      step caller (cfg (some (phaseLabel (.scanScratch .left))) regs
          (data (0 :: X) F S [()] P) ctx) =
        some (cfg (some (phaseLabel .checkRight)) (reset regs) (data X F (0 :: S) [] P) ctx) ∧
      step caller (cfg (some (phaseLabel (.scanScratch .right))) regs
          (data (0 :: X) F S [] P) ctx) =
        some (cfg (some (phaseLabel (.restoreScratch .successRight))) (reset regs)
          (data (1 :: X) F (0 :: S) [] P) ctx) ∧
      step caller (cfg (some (phaseLabel (.scanScratch .right))) regs
          (data (0 :: X) F S [()] P) ctx) =
        some (cfg (some (phaseLabel (.restoreScratch .successRight))) (reset regs)
          (data (1 :: X) F (0 :: S) [] P) ctx) :=
  ⟨scanScratch_left_step_finish caller X (data X F S [] P) regs ctx rfl,
    scanScratch_left_step_finish caller X (data X F S [()] P) regs ctx rfl,
    scanScratch_right_step_finish caller X (data X F S [] P) regs ctx rfl,
    scanScratch_right_step_finish caller X (data X F S [()] P) regs ctx rfl⟩

theorem scratch_failure_restores_a_foreign_head (d : RotationDirection)
    (a : Tag) (notNode : a ≠ nodeTag) (notEmpty : a ≠ emptyTag) :
    step caller (cfg (some (phaseLabel (.scanScratch d))) regs (data [] F S H P) ctx) =
        some (cfg (some (phaseLabel (.restoreScratch (scratchFailure d))))
          (reset regs) (data [] F S H P) ctx) ∧
      step caller (cfg (some (phaseLabel (.scanScratch d))) regs (data (a :: X) F S H P) ctx) =
        some (cfg (some (phaseLabel (.restoreScratch (scratchFailure d))))
          (reset regs) (data (a :: X) F S H P) ctx) :=
  ⟨scanScratch_step_nil caller d (data X F S H P) regs ctx,
    scanScratch_step_foreign caller d a X (data X F S H P) regs ctx notNode notEmpty⟩

theorem right_check_keeps_failed_observations (a : Tag) (notNode : a ≠ nodeTag) :
    step caller (cfg (some (phaseLabel .checkRight)) regs (data (1 :: X) F S H P) ctx) =
        some (cfg (some (phaseLabel (.restoreScratch .successLeft)))
          (reset regs) (data X F S H P) ctx) ∧
      step caller (cfg (some (phaseLabel .checkRight)) regs (data [] F S H P) ctx) =
        some (cfg (some (phaseLabel (.restoreScratch .failureLeft)))
          (reset regs) (data [] F S H P) ctx) ∧
      step caller (cfg (some (phaseLabel .checkRight)) regs (data (a :: X) F S H P) ctx) =
        some (cfg (some (phaseLabel (.restoreScratch .failureLeft)))
          (reset regs) (data (a :: X) F S H P) ctx) :=
  ⟨checkRight_step_node caller X (data X F S H P) regs ctx,
    checkRight_step_nil caller (data X F S H P) regs ctx,
    checkRight_step_nonnode caller a X (data X F S H P) regs ctx notNode⟩

theorem every_scratch_tag_is_a_literal_transfer (mode : RestoreMode) (a : Tag) :
    step caller (cfg (some (phaseLabel (.restoreScratch mode))) regs
        (data X F (a :: S) H P) ctx) =
      some (cfg (some (phaseLabel (.restoreScratch mode))) (reset regs)
        (data (a :: X) F S H P) ctx) :=
  restoreScratch_step_cons caller mode a S (data X F S H P) regs ctx

/-- Four empty probes restore exactly the owed markers while retaining dirty pending. -/
theorem scratch_empty_probe_has_four_literal_marker_words :
    step caller (cfg (some (phaseLabel (.restoreScratch .successLeft))) regs
          (data X F [] H P) ctx) =
        some (cfg (some (phaseLabel (.restorePrefix .success))) (reset regs)
          (data (1 :: 1 :: X) F [] H P) ctx) ∧
      step caller (cfg (some (phaseLabel (.restoreScratch .successRight))) regs
          (data X F [] H P) ctx) =
        some (cfg (some (phaseLabel (.restorePrefix .success))) (reset regs)
          (data (1 :: X) F [] H P) ctx) ∧
      step caller (cfg (some (phaseLabel (.restoreScratch .failureLeft))) regs
          (data X F [] H P) ctx) =
        some (cfg (some (phaseLabel .dropPending)) (reset regs) (data (1 :: X) F [] H P) ctx) ∧
      step caller (cfg (some (phaseLabel (.restoreScratch .failureRight))) regs
          (data X F [] H P) ctx) =
        some (cfg (some (phaseLabel .dropPending)) (reset regs) (data (1 :: 1 :: X) F [] H P) ctx) :=
  ⟨restoreScratch_step_nil caller .successLeft (data X F [] H P) regs ctx,
    restoreScratch_step_nil caller .successRight (data X F [] H P) regs ctx,
    restoreScratch_step_nil caller .failureLeft (data X F [] H P) regs ctx,
    restoreScratch_step_nil caller .failureRight (data X F [] H P) regs ctx⟩

theorem cleanup_does_not_erase_unmentioned_dirty_stores (r : Result) (a : Tag) :
    step caller (cfg (some (phaseLabel .dropPending)) regs (data X F S (() :: H) P) ctx) =
        some (cfg (some (phaseLabel .dropPending)) (reset regs) (data X F S H P) ctx) ∧
      step caller (cfg (some (phaseLabel .dropPending)) regs (data X F S [] P) ctx) =
        some (cfg (some (phaseLabel (.restorePrefix .failure))) (reset regs) (data X F S [] P) ctx) ∧
      step caller (cfg (some (phaseLabel (.restorePrefix r))) regs (data X (a :: F) S H P) ctx) =
        some (cfg (some (phaseLabel (.restorePrefix r))) (reset regs) (data (a :: X) F S H P) ctx) ∧
      step caller (cfg (some (phaseLabel (.restorePrefix r))) regs (data X [] S H P) ctx) =
        some (cfg (some (resultLabel r)) (reset regs) (data X [] S H P) ctx) :=
  ⟨dropPending_step_cons caller H (data X F S H P) regs ctx,
    dropPending_step_nil caller (data X F S H P) regs ctx,
    restorePrefix_step_cons caller r a F (data X F S H P) regs ctx,
    restorePrefix_step_nil caller r (data X F S H P) regs ctx⟩

end FiniteTable

section MinimalSegments

variable {K Λ R : Type} {Γ : K → Type} [DecidableEq K]
variable (caller : External Λ → Statement Γ Λ R)
variable (regs : Registers R) (ctx : ∀ k, List (Γ k))

/-- Seven actual owned activations expose both restoration empty probes. -/
theorem minimal_left_physical_segment :
    LocalRun caller 7
      (cfg (some (phaseLabel (.seek .left))) regs (data [1,0,1,0,0] [] [] [] []) ctx)
      (cfg (some (resultLabel .success)) (reset regs) (data [1,1,0,0,0] [] [] [] []) ctx) := by
  refine LocalRun.cons ⟨True.intro, seek_step_path_nil caller .left (data [1,0,1,0,0] [] [] [] []) regs ctx⟩ ?_
  refine LocalRun.cons ⟨True.intro, start_left_step_node caller [0,1,0,0] (data [1,0,1,0,0] [] [] [] []) (reset regs) ctx⟩ ?_
  refine LocalRun.cons ⟨True.intro, scanScratch_left_step_finish caller [1,0,0] (data [0,1,0,0] [] [] [()] [])
      (reset regs) ctx rfl⟩ ?_
  refine LocalRun.cons ⟨True.intro, checkRight_step_node caller [0,0] (data [1,0,0] [] [0] [] []) (reset regs) ctx⟩ ?_
  refine LocalRun.cons ⟨True.intro, restoreScratch_step_cons caller .successLeft 0 [] (data [0,0] [] [0] [] [])
      (reset regs) ctx⟩ ?_
  refine LocalRun.cons ⟨True.intro, restoreScratch_step_nil caller .successLeft (data [0,0,0] [] [] [] []) (reset regs) ctx⟩ ?_
  refine LocalRun.cons ⟨True.intro, restorePrefix_step_nil caller .success (data [1,1,0,0,0] [] [] [] []) (reset regs) ctx⟩ ?_
  exact .refl _

/-- Right scanning inserts a node in its third activation, not a separate transition. -/
theorem minimal_right_physical_segment :
    LocalRun caller 6
      (cfg (some (phaseLabel (.seek .right))) regs (data [1,1,0,0,0] [] [] [] []) ctx)
      (cfg (some (resultLabel .success)) (reset regs) (data [1,0,1,0,0] [] [] [] []) ctx) := by
  refine LocalRun.cons ⟨True.intro, seek_step_path_nil caller .right (data [1,1,0,0,0] [] [] [] []) regs ctx⟩ ?_
  refine LocalRun.cons ⟨True.intro, start_right_step_nodes caller [0,0,0] (data [1,1,0,0,0] [] [] [] []) (reset regs) ctx⟩ ?_
  refine LocalRun.cons ⟨True.intro, scanScratch_right_step_finish caller [0,0] (data [0,0,0] [] [] [()] [])
      (reset regs) ctx rfl⟩ ?_
  refine LocalRun.cons ⟨True.intro, restoreScratch_step_cons caller .successRight 0 [] (data [1,0,0] [] [0] [] [])
      (reset regs) ctx⟩ ?_
  refine LocalRun.cons ⟨True.intro, restoreScratch_step_nil caller .successRight (data [0,1,0,0] [] [] [] []) (reset regs) ctx⟩ ?_
  refine LocalRun.cons ⟨True.intro, restorePrefix_step_nil caller .success (data [1,0,1,0,0] [] [] [] []) (reset regs) ctx⟩ ?_
  exact .refl _

/-- A missing node consumes one physical Branch and preserves its entire tail. -/
theorem missing_nil_physical_segment (d : RotationDirection) (b : Branch) (p : List Branch) :
    LocalRun caller 3
      (cfg (some (phaseLabel (.seek d))) regs (data [0] [] [] [] (b :: p)) ctx)
      (cfg (some (resultLabel .failure)) (reset regs) (data [0] [] [] [] p) ctx) := by
  refine LocalRun.cons ⟨True.intro, seek_step_source_nonnode caller d b p 0 [] (data [0] [] [] [] p)
      regs ctx (by decide)⟩ ?_
  refine LocalRun.cons ⟨True.intro, dropPending_step_nil caller (data [0] [] [] [] p) (reset regs) ctx⟩ ?_
  refine LocalRun.cons ⟨True.intro, restorePrefix_step_nil caller .failure (data [0] [] [] [] p) (reset regs) ctx⟩ ?_
  exact .refl _

theorem empty_root_physical_segment (d : RotationDirection) :
    LocalRun caller 4
      (cfg (some (phaseLabel (.seek d))) regs (data [] [] [] [] []) ctx)
      (cfg (some (resultLabel .failure)) (reset regs) (data [] [] [] [] []) ctx) := by
  refine LocalRun.cons ⟨True.intro, seek_step_path_nil caller d (data [] [] [] [] []) regs ctx⟩ ?_
  have start : step caller
      (cfg (some (phaseLabel (.start d))) (reset regs) (data [] [] [] [] []) ctx) =
      some (cfg (some (phaseLabel .dropPending)) (reset regs) (data [] [] [] [] []) ctx) := by
    cases d with
    | left => exact start_left_step_nil caller (data [] [] [] [] []) (reset regs) ctx
    | right => exact start_right_step_first_nil caller (data [] [] [] [] []) (reset regs) ctx
  refine LocalRun.cons ⟨True.intro, start⟩ ?_
  refine LocalRun.cons ⟨True.intro, dropPending_step_nil caller (data [] [] [] [] []) (reset regs) ctx⟩ ?_
  refine LocalRun.cons ⟨True.intro, restorePrefix_step_nil caller .failure (data [] [] [] [] []) (reset regs) ctx⟩ ?_
  exact .refl _

/-- A zero-slot scanner exits after the first empty child, leaving the second literal Tag. -/
theorem prefix_scan_zero_pending_stops_early (d : RotationDirection)
    (F S z : Word) (P : List Branch) :
    LocalRun caller 2
      (cfg (some (phaseLabel (.scanPrefix d))) regs (data (1 :: 0 :: 0 :: z) F S [] P) ctx)
      (cfg (some (phaseLabel (.seek d))) (reset regs) (data (0 :: z) (0 :: 1 :: F) S [] P) ctx) := by
  refine LocalRun.cons ⟨True.intro, scanPrefix_step_node caller d (0 :: 0 :: z) (data [] F S [] P) regs ctx⟩ ?_
  refine LocalRun.cons ⟨True.intro, scanPrefix_step_empty_finish caller d (0 :: z) (data [] (1 :: F) S [()] P)
      (reset regs) ctx rfl⟩ ?_
  exact .refl _

theorem prefix_scan_one_pending_consumes_the_whole_tree (d : RotationDirection)
    (F S z : Word) (P : List Branch) :
    LocalRun caller 3
      (cfg (some (phaseLabel (.scanPrefix d))) regs (data (1 :: 0 :: 0 :: z) F S [()] P) ctx)
      (cfg (some (phaseLabel (.seek d))) (reset regs)
        (data z (0 :: 0 :: 1 :: F) S [] P) ctx) := by
  refine LocalRun.cons ⟨True.intro, scanPrefix_step_node caller d (0 :: 0 :: z) (data [] F S [()] P) regs ctx⟩ ?_
  refine LocalRun.cons ⟨True.intro, scanPrefix_step_empty_continue caller d (0 :: z) []
      (data [] (1 :: F) S [(),()] P) (reset regs) ctx⟩ ?_
  refine LocalRun.cons ⟨True.intro, scanPrefix_step_empty_finish caller d z (data [] (0 :: 1 :: F) S [()] P)
      (reset regs) ctx rfl⟩ ?_
  exact .refl _

theorem prefix_scan_two_pending_retains_the_outer_slot (d : RotationDirection)
    (F S z : Word) (P : List Branch) :
    LocalRun caller 3
      (cfg (some (phaseLabel (.scanPrefix d))) regs (data (1 :: 0 :: 0 :: z) F S [(),()] P) ctx)
      (cfg (some (phaseLabel (.scanPrefix d))) (reset regs)
        (data z (0 :: 0 :: 1 :: F) S [()] P) ctx) := by
  refine LocalRun.cons ⟨True.intro, scanPrefix_step_node caller d (0 :: 0 :: z) (data [] F S [(),()] P) regs ctx⟩ ?_
  refine LocalRun.cons ⟨True.intro, scanPrefix_step_empty_continue caller d (0 :: z) [()]
      (data [] (1 :: F) S [(),(),()] P) (reset regs) ctx⟩ ?_
  refine LocalRun.cons ⟨True.intro, scanPrefix_step_empty_continue caller d z []
      (data [] (0 :: 1 :: F) S [(),()] P) (reset regs) ctx⟩ ?_
  exact .refl _

theorem scratch_left_zero_pending_stops_early (F S z : Word) (P : List Branch) :
    LocalRun caller 2
      (cfg (some (phaseLabel (.scanScratch .left))) regs (data (1 :: 0 :: 0 :: z) F S [] P) ctx)
      (cfg (some (phaseLabel .checkRight)) (reset regs) (data (0 :: z) F (0 :: 1 :: S) [] P) ctx) := by
  refine LocalRun.cons ⟨True.intro, scanScratch_step_node caller .left (0 :: 0 :: z) (data [] F S [] P) regs ctx⟩ ?_
  refine LocalRun.cons ⟨True.intro, scanScratch_left_step_finish caller (0 :: z) (data [] F (1 :: S) [()] P)
      (reset regs) ctx rfl⟩ ?_
  exact .refl _

theorem scratch_right_zero_pending_inserts_its_node_early (F S z : Word) (P : List Branch) :
    LocalRun caller 2
      (cfg (some (phaseLabel (.scanScratch .right))) regs (data (1 :: 0 :: 0 :: z) F S [] P) ctx)
      (cfg (some (phaseLabel (.restoreScratch .successRight))) (reset regs)
        (data (1 :: 0 :: z) F (0 :: 1 :: S) [] P) ctx) := by
  refine LocalRun.cons ⟨True.intro, scanScratch_step_node caller .right (0 :: 0 :: z) (data [] F S [] P) regs ctx⟩ ?_
  refine LocalRun.cons ⟨True.intro, scanScratch_right_step_finish caller (0 :: z) (data [] F (1 :: S) [()] P)
      (reset regs) ctx rfl⟩ ?_
  exact .refl _

end MinimalSegments

theorem minimal_left_first_return (caller : ExampleCaller) (flag : Bool) :
    FirstRun caller (cleanEntry .left flag [1,0,1,0,0] []) 7
      (atResult .success flag (data [1,1,0,0,0] [] [] [] [])) :=
  firstRun_of_localRun caller (minimal_left_physical_segment caller (stale flag) ordinaryContext)
    (by simp [Owned, atResult, cfg, resultLabel])

theorem minimal_right_first_return (caller : ExampleCaller) (flag : Bool) :
    FirstRun caller (cleanEntry .right flag [1,1,0,0,0] []) 6
      (atResult .success flag (data [1,0,1,0,0] [] [] [] [])) :=
  firstRun_of_localRun caller (minimal_right_physical_segment caller (stale flag) ordinaryContext)
    (by simp [Owned, atResult, cfg, resultLabel])

def minimalLeftInTime (caller : ExampleCaller) (flag : Bool) :
    StateTransition.EvalsToInTime (step caller) (cleanEntry .left flag [1,0,1,0,0] [])
      (some (atResult .success flag (data [1,1,0,0,0] [] [] [] []))) 7 :=
  localRunInTime caller (minimal_left_physical_segment caller (stale flag) ordinaryContext)

def minimalRightInTime (caller : ExampleCaller) (flag : Bool) :
    StateTransition.EvalsToInTime (step caller) (cleanEntry .right flag [1,1,0,0,0] [])
      (some (atResult .success flag (data [1,0,1,0,0] [] [] [] []))) 6 :=
  localRunInTime caller (minimal_right_physical_segment caller (stale flag) ordinaryContext)

def sentinelHalt (flag : Bool) (D : LocalData) : ExampleCfg :=
  cfg none (clean flag) D (protectedWords [13,15,2,7,10,3] [(),()])

def sentinelSuccessCallerInTime (flag : Bool) :
    StateTransition.EvalsToInTime (step (sentinelCaller 13))
      (atResult .success flag (data [1,1,0,0,0] [] [] [] []))
      (some (sentinelHalt flag (data [1,1,0,0,0] [] [] [] []))) 1 :=
  oneActualStepTime (sentinelCaller 13) _ _
    (sentinel_push_step 13 .success (clean flag) (data [1,1,0,0,0] [] [] [] [])
      [15,2,7,10,3] [(),()])

def sentinelSuccessInTime (flag : Bool) :
    StateTransition.EvalsToInTime (step (sentinelCaller 13))
      (cleanEntry .left flag [1,0,1,0,0] [])
      (some (sentinelHalt flag (data [1,1,0,0,0] [] [] [] []))) 8 :=
  appendTimed (sentinelCaller 13) _ _ _ 7 1
    (minimalLeftInTime (sentinelCaller 13) flag) (sentinelSuccessCallerInTime flag)

def sentinelSuccessOuterNoneInTime (flag : Bool) :
    StateTransition.EvalsToInTime (step (sentinelCaller 13))
      (cleanEntry .left flag [1,0,1,0,0] []) none 9 :=
  appendTimed (sentinelCaller 13) _ _ _ 8 1 (sentinelSuccessInTime flag)
    (oneActualStepTime (sentinelCaller 13) _ none rfl)

theorem sentinel_success_three_stages (flag : Bool) :
    (next (sentinelCaller 13))^[7] (some (cleanEntry .left flag [1,0,1,0,0] [])) =
        some (atResult .success flag (data [1,1,0,0,0] [] [] [] [])) ∧
      (next (sentinelCaller 13))^[8] (some (cleanEntry .left flag [1,0,1,0,0] [])) =
        some (sentinelHalt flag (data [1,1,0,0,0] [] [] [] [])) ∧
      (next (sentinelCaller 13))^[9] (some (cleanEntry .left flag [1,0,1,0,0] [])) = none ∧
      (minimalLeftInTime (sentinelCaller 13) flag).steps = 7 ∧
      (sentinelSuccessCallerInTime flag).steps = 1 ∧
      (sentinelSuccessInTime flag).steps = 8 ∧
      (sentinelSuccessOuterNoneInTime flag).steps = 9 := by
  have returned := (minimal_left_first_return (sentinelCaller 13) flag).1
  have halted := append_actual_step (sentinelCaller 13) 7 _ _ _ returned
    (sentinel_push_step 13 .success (clean flag) (data [1,1,0,0,0] [] [] [] [])
      [15,2,7,10,3] [(),()])
  have absent := append_actual_step (sentinelCaller 13) 8 _ _ none halted rfl
  exact ⟨returned, halted, absent, rfl, rfl, rfl, rfl⟩

def missingNilInTime (caller : ExampleCaller) (flag : Bool) :
    StateTransition.EvalsToInTime (step caller)
      (cleanEntry .left flag [0] [.left,.right,.left])
      (some (atResult .failure flag (data [0] [] [] [] [.right,.left]))) 3 :=
  localRunInTime caller
    (missing_nil_physical_segment caller (stale flag) ordinaryContext .left .left [.right,.left])

def sentinelMissingInTime (flag : Bool) :
    StateTransition.EvalsToInTime (step (sentinelCaller 13))
      (cleanEntry .left flag [0] [.left,.right,.left])
      (some (sentinelHalt flag (data [0] [] [] [] [.right,.left]))) 4 :=
  appendTimed (sentinelCaller 13) _ _ _ 3 1 (missingNilInTime (sentinelCaller 13) flag)
    (oneActualStepTime (sentinelCaller 13) _ _
      (sentinel_push_step 13 .failure (clean flag) (data [0] [] [] [] [.right,.left])
        [15,2,7,10,3] [(),()]))

def sentinelMissingOuterNoneInTime (flag : Bool) :
    StateTransition.EvalsToInTime (step (sentinelCaller 13))
      (cleanEntry .left flag [0] [.left,.right,.left]) none 5 :=
  appendTimed (sentinelCaller 13) _ _ _ 4 1 (sentinelMissingInTime flag)
    (oneActualStepTime (sentinelCaller 13) _ none rfl)

theorem sentinel_failure_retains_the_unvisited_path (flag : Bool) :
    (next (sentinelCaller 13))^[3]
        (some (cleanEntry .left flag [0] [.left,.right,.left])) =
        some (atResult .failure flag (data [0] [] [] [] [.right,.left])) ∧
      (next (sentinelCaller 13))^[4]
        (some (cleanEntry .left flag [0] [.left,.right,.left])) =
        some (sentinelHalt flag (data [0] [] [] [] [.right,.left])) ∧
      (next (sentinelCaller 13))^[5]
        (some (cleanEntry .left flag [0] [.left,.right,.left])) = none ∧
      (missingNilInTime (sentinelCaller 13) flag).steps = 3 ∧
      (sentinelMissingInTime flag).steps = 4 ∧
      (sentinelMissingOuterNoneInTime flag).steps = 5 := by
  have returned := LocalRun.iterate (sentinelCaller 13)
    (missing_nil_physical_segment (sentinelCaller 13) (stale flag) ordinaryContext
      .left .left [.right,.left])
  have halted := append_actual_step (sentinelCaller 13) 3 _ _ _ returned
    (sentinel_push_step 13 .failure (clean flag) (data [0] [] [] [] [.right,.left])
      [15,2,7,10,3] [(),()])
  have absent := append_actual_step (sentinelCaller 13) 4 _ _ none halted rfl
  exact ⟨returned, halted, absent, rfl, rfl, rfl⟩

theorem allocating_caller_retains_two_actual_allocations (flag : Bool) :
    (next allocatingCaller)^[4] (some (cleanEntry .left flag [] [])) =
        some (atResult .failure flag (data [] [] [] [] [])) ∧
      (next allocatingCaller)^[5] (some (cleanEntry .left flag [] [])) =
        some (cfg (some (resultLabel .failure)) (clean flag) (data [] [] [] [] [])
          (protectedWords [15,2,7,10,3] [(),(),()])) ∧
      (next allocatingCaller)^[6] (some (cleanEntry .left flag [] [])) =
        some (cfg (some (resultLabel .failure)) (clean flag) (data [] [] [] [] [])
          (protectedWords [15,2,7,10,3] [(),(),(),()])) := by
  have returned := LocalRun.iterate allocatingCaller
    (empty_root_physical_segment allocatingCaller (stale flag) ordinaryContext .left)
  have once := append_actual_step allocatingCaller 4 _ _ _ returned
    (allocation_is_an_actual_protected_unit_push .failure (clean flag) (data [] [] [] [] [])
      [15,2,7,10,3] [(),()])
  have twice := append_actual_step allocatingCaller 5 _ _ _ once
    (allocation_is_an_actual_protected_unit_push .failure (clean flag) (data [] [] [] [] [])
      [15,2,7,10,3] [(),(),()])
  exact ⟨returned, once, twice⟩

theorem an_eventual_failure_can_follow_the_first_success (flag : Bool) :
    FirstRun misleadingCaller (cleanEntry .left flag [1,0,1,0,0] []) 7
        (atResult .success flag (data [1,1,0,0,0] [] [] [] [])) ∧
      (next misleadingCaller)^[8] (some (cleanEntry .left flag [1,0,1,0,0] [])) =
        some (atResult .failure flag (data [1,1,0,0,0] [] [] [] [])) ∧
      ¬ FirstRun misleadingCaller (cleanEntry .left flag [1,0,1,0,0] []) 8
        (atResult .failure flag (data [1,1,0,0,0] [] [] [] [])) := by
  have first := minimal_left_first_return misleadingCaller flag
  refine ⟨first, ?_, ?_⟩
  · exact append_actual_step misleadingCaller 7 _ _ _ first.1
      (a_caller_can_forge_the_opposite_result (clean flag)
        (data [1,1,0,0,0] [] [] [] []) ordinaryContext).1
  · intro later
    have impossible := (firstRun_unique misleadingCaller first later).1
    omega

theorem an_eventual_success_can_follow_the_first_failure (flag : Bool) :
    FirstRun misleadingCaller (cleanEntry .left flag [] []) 4
        (atResult .failure flag (data [] [] [] [] [])) ∧
      (next misleadingCaller)^[5] (some (cleanEntry .left flag [] [])) =
        some (atResult .success flag (data [] [] [] [] [])) ∧
      ¬ FirstRun misleadingCaller (cleanEntry .left flag [] []) 5
        (atResult .success flag (data [] [] [] [] [])) := by
  have first : FirstRun misleadingCaller (cleanEntry .left flag [] []) 4
      (atResult .failure flag (data [] [] [] [] [])) :=
    firstRun_of_localRun misleadingCaller
      (empty_root_physical_segment misleadingCaller (stale flag) ordinaryContext .left)
      (by simp [Owned, atResult, cfg, resultLabel])
  refine ⟨first, ?_, ?_⟩
  · exact append_actual_step misleadingCaller 4 _ _ _ first.1
      (a_caller_can_forge_the_opposite_result (clean flag) (data [] [] [] [] []) ordinaryContext).2
  · intro later
    have impossible := (firstRun_unique misleadingCaller first later).1
    omega

theorem external_label_has_its_own_transition_and_halt (flag : Bool) :
    (next externalCaller)^[4] (some (cleanEntry .left flag [] [])) =
        some (atResult .failure flag (data [] [] [] [] [])) ∧
      (next externalCaller)^[5] (some (cleanEntry .left flag [] [])) =
        some (cfg (some (callerLabel ())) (clean flag) (data [] [] [] [] []) ordinaryContext) ∧
      (next externalCaller)^[6] (some (cleanEntry .left flag [] [])) =
        some (sentinelHalt flag (data [] [] [] [] [])) ∧
      (next externalCaller)^[7] (some (cleanEntry .left flag [] [])) = none := by
  have returned := LocalRun.iterate externalCaller
    (empty_root_physical_segment externalCaller (stale flag) ordinaryContext .left)
  have external := append_actual_step externalCaller 4 _ _ _ returned
    (separate_external_label_is_reached_first .failure (clean flag)
      (data [] [] [] [] []) ordinaryContext)
  have halted := append_actual_step externalCaller 5 _ _ _ external
    (external_label_executes_its_own_push_and_halt (clean flag)
      (data [] [] [] [] []) [15,2,7,10,3] [(),()])
  have absent := append_actual_step externalCaller 6 _ _ none halted rfl
  exact ⟨returned, external, halted, absent⟩

section ScannerContracts

variable {K Λ R : Type} {Γ : K → Type} [DecidableEq K]
variable (caller : External Λ → Statement Γ Λ R)
variable (regs : Registers R) (ctx : ∀ k, List (Γ k))

/-- The source is a represented prefix; old accumulators and the external suffix stay literal. -/
theorem represented_subtree_scans_into_saved (d : RotationDirection) (t : BinaryTree Unit)
    (F S z : Word) (outer : List Unit) (P : List Branch) :
    (next caller)^[(treeCode t).length]
        (some (cfg (some (phaseLabel (.scanPrefix d))) regs
          (data (treeCode t ++ z) F S (() :: outer) P) ctx)) =
      some (cfg (some (phaseLabel (if outer = [] then .seek d else .scanPrefix d)))
        (reset regs) (data z ((treeCode t).reverse ++ F) S outer P) ctx) :=
  LocalRun.iterate caller
    (scanPrefix_treeCode_localRun caller d t z outer (data [] F S [] P) regs ctx)

theorem represented_left_subtree_scans_into_scratch (t : BinaryTree Unit)
    (F S z : Word) (P : List Branch) :
    (next caller)^[(treeCode t).length]
        (some (cfg (some (phaseLabel (.scanScratch .left))) regs
          (data (treeCode t ++ z) F S [()] P) ctx)) =
      some (cfg (some (phaseLabel .checkRight)) (reset regs)
        (data z F ((treeCode t).reverse ++ S) [] P) ctx) :=
  LocalRun.iterate caller
    (scanScratch_treeCode_localRun caller .left t z [] (data [] F S [] P) regs ctx)

theorem represented_right_subtree_scans_and_inserts_its_node (t : BinaryTree Unit)
    (F S z : Word) (P : List Branch) :
    (next caller)^[(treeCode t).length]
        (some (cfg (some (phaseLabel (.scanScratch .right))) regs
          (data (treeCode t ++ z) F S [()] P) ctx)) =
      some (cfg (some (phaseLabel (.restoreScratch .successRight))) (reset regs)
        (data (1 :: z) F ((treeCode t).reverse ++ S) [] P) ctx) :=
  LocalRun.iterate caller
    (scanScratch_treeCode_localRun caller .right t z [] (data [] F S [] P) regs ctx)

theorem represented_scratch_scan_keeps_an_outer_pending_slot (d : RotationDirection)
    (t : BinaryTree Unit) (F S z : Word) (outer : List Unit) (P : List Branch) :
    (next caller)^[(treeCode t).length]
        (some (cfg (some (phaseLabel (.scanScratch d))) regs
          (data (treeCode t ++ z) F S (() :: () :: outer) P) ctx)) =
      some (cfg (some (phaseLabel (.scanScratch d))) (reset regs)
        (data z F ((treeCode t).reverse ++ S) (() :: outer) P) ctx) := by
  simpa only [scratchScanEnd, scratchScanSource, List.cons_ne_nil, ite_false, data] using
    LocalRun.iterate caller
      (scanScratch_treeCode_localRun caller d t z (() :: outer) (data [] F S [] P) regs ctx)

/-- Continued scanning has no hidden initial-one-slot assumption. -/
theorem continued_prefix_has_its_actual_saved_segment {w : Word} {h k : Nat}
    (continued : Continues w h k) (d : RotationDirection) (F S z : Word) (P : List Branch) :
    (next caller)^[w.length]
        (some (cfg (some (phaseLabel (.scanPrefix d))) regs
          (data (w ++ z) F S (List.replicate h ()) P) ctx)) =
      some (cfg (some (phaseLabel (.scanPrefix d)))
        (if w = [] then regs else reset regs)
        (data z (w.reverse ++ F) S (List.replicate k ()) P) ctx) :=
  LocalRun.iterate caller
    (scanPrefix_continues_localRun caller continued d z (data [] F S [] P) regs ctx)

theorem continued_prefix_has_its_actual_scratch_segment {w : Word} {h k : Nat}
    (continued : Continues w h k) (d : RotationDirection) (F S z : Word) (P : List Branch) :
    (next caller)^[w.length]
        (some (cfg (some (phaseLabel (.scanScratch d))) regs
          (data (w ++ z) F S (List.replicate h ()) P) ctx)) =
      some (cfg (some (phaseLabel (.scanScratch d)))
        (if w = [] then regs else reset regs)
        (data z F (w.reverse ++ S) (List.replicate k ()) P) ctx) :=
  LocalRun.iterate caller
    (scanScratch_continues_localRun caller continued d z (data [] F S [] P) regs ctx)

end ScannerContracts

theorem nonpalindromic_right_scratch_boundary (caller : ExampleCaller) (flag : Bool) :
    (next caller)^[5]
        (some (atPhase (.scanScratch .right) flag
          (data [1,0,1,0,0,15,2] [12,3] [8,5] [()] [.right,.left]))) =
      some (cfg (some (phaseLabel (.restoreScratch .successRight))) (clean flag)
        (data [1,15,2] [12,3] [0,0,1,0,1,8,5] [] [.right,.left]) ordinaryContext) :=
  represented_right_subtree_scans_and_inserts_its_node caller (stale flag) ordinaryContext
    rightTwo [12,3] [8,5] [15,2] [.right,.left]

section TotalDirtyExecution

variable {K Λ R : Type} {Γ : K → Type} [DecidableEq K]
variable (caller : External Λ → Statement Γ Λ R)

/-- Totality is about every actual dirty phase, with no source representation premise. -/
theorem every_dirty_phase_has_an_exact_first_live_result (q : Phase) (D : LocalData)
    (regs : Registers R) (ctx : ∀ k, List (Γ k)) :
    0 < phaseSteps q D ∧ phaseSteps q D ≤ countdown (.inl q) D ∧
      FirstRun caller (cfg (some (phaseLabel q)) regs D ctx) (phaseSteps q D)
        (phaseResult q regs D ctx) ∧
      (∃ r, (phaseResult (Λ := Λ) q regs D ctx).l = some (resultLabel r)) ∧
      (phaseResult (Λ := Λ) q regs D ctx).var = reset regs ∧
      ∀ k, (phaseResult (Λ := Λ) q regs D ctx).stk (.inr k) = ctx k := by
  refine ⟨phaseSteps_pos q D, phaseSteps_le_countdown q D, ?_, ?_, rfl, fun _ => rfl⟩
  · exact firstRun_of_localRun caller (phase_localRun caller q D regs ctx)
      (by simp [phaseResult, cfg, resultLabel, Owned])
  · exact ⟨(evaluate (.inl q) D).result, rfl⟩

def arbitraryDirtyPhaseInTime (q : Phase) (D : LocalData)
    (regs : Registers R) (ctx : ∀ k, List (Γ k)) :
    StateTransition.EvalsToInTime (step caller) (cfg (some (phaseLabel q)) regs D ctx)
      (some (phaseResult q regs D ctx)) (phaseSteps q D) :=
  localRunInTime caller (phase_localRun caller q D regs ctx)

theorem arbitrary_dirty_timed_data_has_the_exact_steps (q : Phase) (D : LocalData)
    (regs : Registers R) (ctx : ∀ k, List (Γ k)) :
    (arbitraryDirtyPhaseInTime caller q D regs ctx).steps = phaseSteps q D := rfl

/-- Ownedness is required before asserting that rank zero will be a live local result. -/
theorem every_owned_configuration_returns_live (start : Cfg Γ Λ R) (owned : Owned start.l) :
    ∃ finish r, FirstRun caller start (remainingSteps start) finish ∧
      finish.l = some (resultLabel r) ∧ finish.var = reset start.var ∧
      ∀ k, finish.stk (.inr k) = start.stk (.inr k) := by
  obtain ⟨q, regs, D, ctx, rfl⟩ := owned_cases start owned
  obtain ⟨_, _, first, ⟨r, label⟩, registers, frame⟩ :=
    every_dirty_phase_has_an_exact_first_live_result caller q D regs ctx
  exact ⟨phaseResult q regs D ctx, r, first, label, registers, frame⟩

theorem nonowned_prefix_is_only_identity (start : Cfg Γ Λ R)
    (outside : ¬ Owned start.l) :
    remainingSteps start = 0 ∧
      (next caller)^[remainingSteps start] (some start) = some start := by
  have zero : remainingSteps start = 0 := by
    have noPositive : ¬ 0 < remainingSteps start :=
      fun positive => outside ((remainingSteps_pos_iff start).mp positive)
    omega
  exact ⟨zero, by rw [zero]; rfl⟩

omit [DecidableEq K] in
theorem rank_zero_includes_both_live_results_external_and_halt
    (regs : Registers R) (D : LocalData) (ctx : ∀ k, List (Γ k)) (label : Λ) :
    remainingSteps (cfg (some (resultLabel (Λ := Λ) .success)) regs D ctx) = 0 ∧
      remainingSteps (cfg (some (resultLabel (Λ := Λ) .failure)) regs D ctx) = 0 ∧
      remainingSteps (cfg (some (callerLabel label)) regs D ctx) = 0 ∧
      remainingSteps (cfg (Λ := Λ) none regs D ctx) = 0 := ⟨rfl, rfl, rfl, rfl⟩

theorem positive_rank_is_actual_resetting_progress (start : Cfg Γ Λ R)
    (owned : Owned start.l) :
    0 < remainingSteps start ∧ ∃ reached,
      step caller start = some reached ∧ remainingSteps start = remainingSteps reached + 1 ∧
      reached.var = reset start.var ∧
      ∀ k, reached.stk (.inr k) = start.stk (.inr k) := by
  have positive := (remainingSteps_pos_iff start).mpr owned
  obtain ⟨reached, executed, rank⟩ := local_progress caller start positive
  have effects := local_step_data caller ⟨owned, executed⟩
  exact ⟨positive, reached, executed, rank, effects.2.1, effects.2.2⟩

theorem raw_time_bounds_are_upper_bounds_for_the_exact_clock
    (d : RotationDirection) (w : Word) (p : List Branch) :
    0 < runSteps d w p ∧ runSteps d w p ≤ 3 * w.length + p.length + 5 ∧
      runSteps d w p ≤ 4 * w.length + p.length + 12 :=
  ⟨runSteps_pos d w p, runSteps_le d w p, runSteps_le_conservative d w p⟩

end TotalDirtyExecution

theorem all_sixteen_phases_accept_both_fixed_dirty_profiles
    (caller : ExampleCaller) (flag : Bool) (q : Phase) :
    FirstRun caller (atPhase q flag dirtyPhaseA) (phaseSteps q dirtyPhaseA)
        (phaseResult q (stale flag) dirtyPhaseA ordinaryContext) ∧
      FirstRun caller (atPhase q flag dirtyPhaseB) (phaseSteps q dirtyPhaseB)
        (phaseResult q (stale flag) dirtyPhaseB ordinaryContext) :=
  ⟨(every_dirty_phase_has_an_exact_first_live_result caller q dirtyPhaseA
      (stale flag) ordinaryContext).2.2.1,
    (every_dirty_phase_has_an_exact_first_live_result caller q dirtyPhaseB
      (stale flag) ordinaryContext).2.2.1⟩

/-- A literal evaluator equality is useful only through the producer's actual owned run. -/
theorem fixture_localRun_of_evaluation (caller : ExampleCaller) (flag : Bool)
    (c : RunFixture)
    (checked : evaluate (.inl c.phase) c.before = ⟨c.result, c.after, c.ticks⟩) :
    LocalRun caller c.ticks (atPhase c.phase flag c.before) (atResult c.result flag c.after) := by
  simpa only [phaseSteps, phaseResult, checked, atPhase, atResult, reset, stale, clean] using
    phase_localRun caller c.phase c.before (stale flag) ordinaryContext

theorem fixture_expected_of_evaluation (caller : ExampleCaller) (flag : Bool)
    (c : RunFixture)
    (checked : evaluate (.inl c.phase) c.before = ⟨c.result, c.after, c.ticks⟩) :
    c.Expected caller flag :=
  firstRun_of_localRun caller (fixture_localRun_of_evaluation caller flag c checked)
    (by simp [atResult, cfg, resultLabel, Owned])

def fixtureInTime (caller : ExampleCaller) (flag : Bool) (c : RunFixture)
    (checked : evaluate (.inl c.phase) c.before = ⟨c.result, c.after, c.ticks⟩) :
    StateTransition.EvalsToInTime (step caller) (atPhase c.phase flag c.before)
      (some (atResult c.result flag c.after)) c.ticks :=
  localRunInTime caller (fixture_localRun_of_evaluation caller flag c checked)

theorem every_dirty_transfer_fixture_is_an_actual_first_return
    (caller : ExampleCaller) (flag : Bool) (c : RunFixture) (member : c ∈ transferFixtures) :
    c.Expected caller flag := by
  simp only [transferFixtures, List.mem_cons, List.mem_nil_iff, or_false] at member
  rcases member with rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact firstRun_of_localRun caller
      (restoreScratch_localRun caller .successLeft dirtyData (stale flag) ordinaryContext)
      (by simp [Owned, atResult, cfg, resultLabel])
  · exact firstRun_of_localRun caller
      (restoreScratch_localRun caller .successRight dirtyData (stale flag) ordinaryContext)
      (by simp [Owned, atResult, cfg, resultLabel])
  · exact firstRun_of_localRun caller
      (restoreScratch_localRun caller .failureLeft dirtyData (stale flag) ordinaryContext)
      (by simp [Owned, atResult, cfg, resultLabel])
  · exact firstRun_of_localRun caller
      (restoreScratch_localRun caller .failureRight dirtyData (stale flag) ordinaryContext)
      (by simp [Owned, atResult, cfg, resultLabel])
  · exact firstRun_of_localRun caller
      (dropPending_localRun caller dirtyData (stale flag) ordinaryContext)
      (by simp [Owned, atResult, cfg, resultLabel])
  · exact firstRun_of_localRun caller
      (restorePrefix_localRun caller .success dirtyData (stale flag) ordinaryContext)
      (by simp [Owned, atResult, cfg, resultLabel])
  · exact firstRun_of_localRun caller
      (restorePrefix_localRun caller .failure dirtyData (stale flag) ordinaryContext)
      (by simp [Owned, atResult, cfg, resultLabel])

def dirtyTransferInTime (caller : ExampleCaller) (flag : Bool)
    (c : RunFixture) (member : c ∈ transferFixtures) :
    StateTransition.EvalsToInTime (step caller) (atPhase c.phase flag c.before)
      (some (atResult c.result flag c.after)) c.ticks where
  steps := c.ticks
  evals_in_steps := (every_dirty_transfer_fixture_is_an_actual_first_return caller flag c member).1
  steps_le_m := Nat.le_refl _

theorem raw_fixture_evaluations (c : RunFixture) (member : c ∈ rawFixtures) :
    evaluate (.inl c.phase) c.before = ⟨c.result, c.after, c.ticks⟩ := by
  simp only [rawFixtures, List.mem_cons, List.mem_nil_iff, or_false] at member
  rcases member with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;>
    simp [evaluate_phase, evaluate_result, advance, scratchFailure, markerWord, modeResult,
      nodeTag, emptyTag, data]

theorem every_raw_fixture_is_an_actual_first_return
    (caller : ExampleCaller) (flag : Bool) (c : RunFixture) (member : c ∈ rawFixtures) :
    c.Expected caller flag :=
  fixture_expected_of_evaluation caller flag c (raw_fixture_evaluations c member)

def rawFixtureInTime (caller : ExampleCaller) (flag : Bool)
    (c : RunFixture) (member : c ∈ rawFixtures) :
    StateTransition.EvalsToInTime (step caller) (atPhase c.phase flag c.before)
      (some (atResult c.result flag c.after)) c.ticks :=
  fixtureInTime caller flag c (raw_fixture_evaluations c member)

theorem fixed_fixture_timed_data_keeps_exact_steps (caller : ExampleCaller) (flag : Bool)
    (transfer raw : RunFixture) (isTransfer : transfer ∈ transferFixtures)
    (isRaw : raw ∈ rawFixtures) :
    (dirtyTransferInTime caller flag transfer isTransfer).steps = transfer.ticks ∧
      (rawFixtureInTime caller flag raw isRaw).steps = raw.ticks := ⟨rfl, rfl⟩

section DirtyTransferContracts

variable {K Λ R : Type} {Γ : K → Type} [DecidableEq K]
variable (caller : External Λ → Statement Γ Λ R)
variable (regs : Registers R) (ctx : ∀ k, List (Γ k))

theorem arbitrary_scratch_split_retains_the_empty_probe (mode : RestoreMode)
    (X F A B : Word) (H : List Unit) (P : List Branch) :
    (next caller)^[A.length]
        (some (cfg (some (phaseLabel (.restoreScratch mode))) regs (data X F (A ++ B) H P) ctx)) =
      some (cfg (some (phaseLabel (.restoreScratch mode)))
        (if A = [] then regs else reset regs) (data (A.reverse ++ X) F B H P) ctx) :=
  restoreScratch_prefix caller mode A B (data X F [] H P) regs ctx

theorem arbitrary_saved_split_retains_the_empty_probe (r : Result)
    (X A B S : Word) (H : List Unit) (P : List Branch) :
    (next caller)^[A.length]
        (some (cfg (some (phaseLabel (.restorePrefix r))) regs (data X (A ++ B) S H P) ctx)) =
      some (cfg (some (phaseLabel (.restorePrefix r)))
        (if A = [] then regs else reset regs) (data (A.reverse ++ X) B S H P) ctx) :=
  restorePrefix_prefix caller r A B (data X [] S H P) regs ctx

theorem arbitrary_pending_split_retains_the_empty_probe
    (X F S : Word) (A B : List Unit) (P : List Branch) :
    (next caller)^[A.length]
        (some (cfg (some (phaseLabel .dropPending)) regs (data X F S (A ++ B) P) ctx)) =
      some (cfg (some (phaseLabel .dropPending))
        (if A = [] then regs else reset regs) (data X F S B P) ctx) :=
  dropPending_prefix caller A B (data X F S [] P) regs ctx

/-- All four modes retain arbitrary source, saved, scratch, pending, and path data. -/
theorem four_complete_scratch_transfers_have_the_fixed_dirty_endpoints
    (X F S : Word) (H : List Unit) (P : List Branch) :
    FirstRun caller
        (cfg (some (phaseLabel (.restoreScratch .successLeft))) regs (data X F S H P) ctx)
        (S.length + F.length + 2)
        (cfg (some (resultLabel .success)) (reset regs)
          (data (F.reverse ++ [1,1] ++ S.reverse ++ X) [] [] H P) ctx) ∧
      FirstRun caller
        (cfg (some (phaseLabel (.restoreScratch .successRight))) regs (data X F S H P) ctx)
        (S.length + F.length + 2)
        (cfg (some (resultLabel .success)) (reset regs)
          (data (F.reverse ++ [1] ++ S.reverse ++ X) [] [] H P) ctx) ∧
      FirstRun caller
        (cfg (some (phaseLabel (.restoreScratch .failureLeft))) regs (data X F S H P) ctx)
        (S.length + H.length + F.length + 3)
        (cfg (some (resultLabel .failure)) (reset regs)
          (data (F.reverse ++ [1] ++ S.reverse ++ X) [] [] [] P) ctx) ∧
      FirstRun caller
        (cfg (some (phaseLabel (.restoreScratch .failureRight))) regs (data X F S H P) ctx)
        (S.length + H.length + F.length + 3)
        (cfg (some (resultLabel .failure)) (reset regs)
          (data (F.reverse ++ [1,1] ++ S.reverse ++ X) [] [] [] P) ctx) :=
  ⟨firstRun_of_localRun caller
      (restoreScratch_localRun caller .successLeft (data X F S H P) regs ctx)
      (by simp [Owned, cfg, resultLabel]),
    firstRun_of_localRun caller
      (restoreScratch_localRun caller .successRight (data X F S H P) regs ctx)
      (by simp [Owned, cfg, resultLabel]),
    firstRun_of_localRun caller
      (restoreScratch_localRun caller .failureLeft (data X F S H P) regs ctx)
      (by simp [Owned, cfg, resultLabel]),
    firstRun_of_localRun caller
      (restoreScratch_localRun caller .failureRight (data X F S H P) regs ctx)
      (by simp [Owned, cfg, resultLabel])⟩

theorem dropping_pending_preserves_dirty_scratch (X F S : Word)
    (H : List Unit) (P : List Branch) :
    FirstRun caller (cfg (some (phaseLabel .dropPending)) regs (data X F S H P) ctx)
      (H.length + F.length + 2)
      (cfg (some (resultLabel .failure)) (reset regs) (data (F.reverse ++ X) [] S [] P) ctx) :=
  firstRun_of_localRun caller (dropPending_localRun caller (data X F S H P) regs ctx)
    (by simp [Owned, cfg, resultLabel])

theorem restoring_saved_preserves_dirty_scratch_and_pending (r : Result)
    (X F S : Word) (H : List Unit) (P : List Branch) :
    FirstRun caller (cfg (some (phaseLabel (.restorePrefix r))) regs (data X F S H P) ctx)
      (F.length + 1)
      (cfg (some (resultLabel r)) (reset regs) (data (F.reverse ++ X) [] S H P) ctx) :=
  firstRun_of_localRun caller (restorePrefix_localRun caller r (data X F S H P) regs ctx)
    (by simp [Owned, cfg, resultLabel])

end DirtyTransferContracts

theorem all_partial_dirty_transfer_expectations (caller : ExampleCaller) (flag : Bool)
    (mode : RestoreMode) (r : Result) (X F S A B : Word)
    (H HA HB : List Unit) (P : List Branch) :
    ScratchSplitExpected caller flag mode X F A B H P ∧
      SavedSplitExpected caller flag r X A B S H P ∧
      PendingSplitExpected caller flag X F S HA HB P :=
  ⟨arbitrary_scratch_split_retains_the_empty_probe caller (stale flag) ordinaryContext
      mode X F A B H P,
    arbitrary_saved_split_retains_the_empty_probe caller (stale flag) ordinaryContext
      r X A B S H P,
    arbitrary_pending_split_retains_the_empty_probe caller (stale flag) ordinaryContext
      X F S HA HB P⟩

section PrefixAndTimingContracts

variable {K Λ R : Type} {Γ : K → Type} [DecidableEq K]
variable (caller : External Λ → Statement Γ Λ R)

/-- All facts refer to one actual reached configuration, including the zero-step state. -/
theorem inclusive_prefix_has_one_rank_reset_and_frame_witness
    (start : Cfg Γ Λ R) (n : Nat) (bound : n ≤ remainingSteps start) :
    ∃ reached, (next caller)^[n] (some start) = some reached ∧
      remainingSteps reached = remainingSteps start - n ∧
      Relation.ReflTransGen (LocalStep caller) start reached ∧
      (n < remainingSteps start ↔ Owned reached.l) ∧
      (n = 0 → reached = start) ∧
      reached.var = (if n = 0 then start.var else reset start.var) ∧
      ∀ k, reached.stk (.inr k) = start.stk (.inr k) :=
  owned_prefix_frame caller start n bound

theorem arbitrary_callers_agree_through_the_inclusive_first_handoff
    (other : External Λ → Statement Γ Λ R) (start : Cfg Γ Λ R)
    (n : Nat) (bound : n ≤ remainingSteps start) :
    (next caller)^[n] (some start) = (next other)^[n] (some start) :=
  prefix_caller_independent caller other start n bound

theorem installed_owned_blocks_give_the_same_actual_prefix
    (ambient : Label Λ → Statement Γ Λ R)
    (agrees : ∀ q, ambient (phaseLabel q) = block q)
    (start : Cfg Γ Λ R) (n : Nat) (bound : n ≤ remainingSteps start) :
    (next caller)^[n] (some start) =
      (fun c : Option (Cfg Γ Λ R) => c.bind (Turing.TM2.step ambient))^[n] (some start) :=
  ambient_prefix_eq caller ambient agrees start n bound

theorem every_first_dirty_exit_has_the_evaluator_clock_and_complete_endpoint
    (q : Phase) (D : LocalData) (regs : Registers R) (ctx : ∀ k, List (Γ k))
    (n : Nat) (reached : Cfg Γ Λ R)
    (first : FirstRun caller (cfg (some (phaseLabel q)) regs D ctx) n reached) :
    n = phaseSteps q D ∧ reached = phaseResult q regs D ctx :=
  first_return_unique caller q D regs ctx n reached first.1 first.2.1 first.2.2

def allRawInExactTime (d : RotationDirection) (raw : Word) (path : List Branch)
    (regs : Registers R) (ctx : ∀ k, List (Γ k)) :
    StateTransition.EvalsToInTime (step caller) (entry d regs raw path ctx)
      (some (phaseResult (.seek d) regs { source := raw, path := path } ctx))
      (runSteps d raw path) := runInTimeExact caller d raw path regs ctx

def allRawInLinearTime (d : RotationDirection) (raw : Word) (path : List Branch)
    (regs : Registers R) (ctx : ∀ k, List (Γ k)) :
    StateTransition.EvalsToInTime (step caller) (entry d regs raw path ctx)
      (some (phaseResult (.seek d) regs { source := raw, path := path } ctx))
      (3 * raw.length + path.length + 5) := runInLinearTime caller d raw path regs ctx

def allRawInConservativeTime (d : RotationDirection) (raw : Word) (path : List Branch)
    (regs : Registers R) (ctx : ∀ k, List (Γ k)) :
    StateTransition.EvalsToInTime (step caller) (entry d regs raw path ctx)
      (some (phaseResult (.seek d) regs { source := raw, path := path } ctx))
      (4 * raw.length + path.length + 12) := runInConservativeTime caller d raw path regs ctx

theorem bounded_timing_keeps_the_actual_exact_steps (d : RotationDirection)
    (raw : Word) (path : List Branch) (regs : Registers R) (ctx : ∀ k, List (Γ k)) :
    (allRawInExactTime caller d raw path regs ctx).steps = runSteps d raw path ∧
      (allRawInLinearTime caller d raw path regs ctx).steps = runSteps d raw path ∧
      (allRawInConservativeTime caller d raw path regs ctx).steps = runSteps d raw path ∧
      (phaseInTime caller (.seek d) { source := raw, path := path } regs ctx).steps =
        runSteps d raw path := ⟨rfl, rfl, rfl, rfl⟩

end PrefixAndTimingContracts

theorem callers_agree_through_return_and_differ_on_the_next_activation (flag : Bool) :
    (∀ n, n ≤ 7 →
      (next (sentinelCaller 13))^[n] (some (cleanEntry .left flag [1,0,1,0,0] [])) =
        (next (sentinelCaller 14))^[n] (some (cleanEntry .left flag [1,0,1,0,0] []))) ∧
      (next (sentinelCaller 13))^[8] (some (cleanEntry .left flag [1,0,1,0,0] [])) ≠
        (next (sentinelCaller 14))^[8] (some (cleanEntry .left flag [1,0,1,0,0] [])) := by
  have rank : remainingSteps (cleanEntry .left flag [1,0,1,0,0] []) = 7 := by
    have exactRank := LocalRun.remaining (sentinelCaller 13)
      (minimal_left_physical_segment (sentinelCaller 13) (stale flag) ordinaryContext)
    simpa only [cleanEntry, atPhase, remainingSteps, cfg, resultLabel, Nat.add_zero] using exactRank
  refine ⟨?_, ?_⟩
  · intro n bound
    apply prefix_caller_independent (sentinelCaller 13) (sentinelCaller 14)
    rwa [rank]
  · have first13 := (sentinel_success_three_stages flag).2.1
    have returned14 := (minimal_left_first_return (sentinelCaller 14) flag).1
    have first14 := append_actual_step (sentinelCaller 14) 7 _ _ _ returned14
      (sentinel_push_step 14 .success (clean flag) (data [1,1,0,0,0] [] [] [] [])
        [15,2,7,10,3] [(),()])
    rw [first13, first14]
    intro same
    have heads := congrArg (fun c : ExampleCfg => (c.stk (.inr (0 : Fin 2))).head?)
      (Option.some.inj same)
    have impossible : (13 : Tag) = 14 := Option.some.inj heads
    exact (by decide : (13 : Tag) ≠ 14) impossible

theorem emptyContext_eq : emptyContext = (fun _ => []) := by
  funext k
  fin_cases k <;> rfl

theorem the_actual_package_has_seven_nineteen_two_hundred_four
    (d : RotationDirection) (caller : ExampleCaller) (initial : Bool) :
    @Fintype.card (concreteMachine d caller initial).K (concreteMachine d caller initial).kFin = 7 ∧
      @Fintype.card (concreteMachine d caller initial).Λ (concreteMachine d caller initial).ΛFin = 19 ∧
      @Fintype.card (concreteMachine d caller initial).σ (concreteMachine d caller initial).σFin = 204 := by
  change Fintype.card (StackId (Fin 2)) = 7 ∧ Fintype.card (Label Unit) = 19 ∧
    Fintype.card (Registers Bool) = 204
  exact actual_finite_carrier_counts.2.2.2.2

@[instance_reducible]
def everyPackagedAlphabetIsFinite (d : RotationDirection) (caller : ExampleCaller)
    (initial : Bool) (k : (concreteMachine d caller initial).K) :
    Fintype ((concreteMachine d caller initial).Γ k) := machineAlphabetFintype caller d initial k

theorem real_package_source_input_output_and_main
    (d : RotationDirection) (caller : ExampleCaller) (initial : Bool) :
    (concreteMachine d caller initial).k₀ = .inl .source ∧
      (concreteMachine d caller initial).k₁ = .inl .source ∧
      (concreteMachine d caller initial).main = phaseLabel (.seek d) ∧
      (concreteMachine d caller initial).initialState = clean initial := ⟨rfl, rfl, rfl, rfl⟩

/-- Genuine one-input initialization fills source only, including when source is malformed. -/
theorem genuine_initializer_has_no_path_or_protected_cells
    (d : RotationDirection) (caller : ExampleCaller) (initial : Bool) (raw : Word) :
    Turing.initList (concreteMachine d caller initial) raw =
      cfg (some (phaseLabel (.seek d))) (clean initial) (data raw [] [] [] []) emptyContext := by
  rw [emptyContext_eq]
  exact initList_eq caller d initial raw

theorem actual_package_step_is_the_component_step
    (d : RotationDirection) (caller : ExampleCaller) (initial : Bool) (c : ExampleCfg) :
    (concreteMachine d caller initial).step c = step caller c := machine_step_eq caller d initial c

theorem the_package_executes_the_actually_installed_path
    (d : RotationDirection) (caller : ExampleCaller) (initial : Bool)
    (raw : Word) (path : List Branch) (regs : Registers Bool)
    (ctx : ∀ k, List (ProtectedAlphabet k)) :
    (fun c => c.bind (concreteMachine d caller initial).step)^[runSteps d raw path]
        (some (cfg (some (phaseLabel (.seek d))) regs (data raw [] [] [] path) ctx)) =
      some (phaseResult (.seek d) regs (data raw [] [] [] path) ctx) :=
  machine_cfg_run caller d initial raw path regs ctx

def allGenuineInputsInTime (d : RotationDirection) (caller : ExampleCaller)
    (initial : Bool) (raw : Word) :
    StateTransition.EvalsToInTime (concreteMachine d caller initial).step
      (Turing.initList (concreteMachine d caller initial) raw)
      (some (phaseResult (.seek d) (clean initial) (data raw [] [] [] []) (fun _ => [])))
      (runSteps d raw []) := machineInitInTime caller d initial raw

def installedConfigurationInTime (d : RotationDirection) (caller : ExampleCaller)
    (initial : Bool) (raw : Word) (path : List Branch) (regs : Registers Bool)
    (ctx : ∀ k, List (ProtectedAlphabet k)) :
    StateTransition.EvalsToInTime (concreteMachine d caller initial).step
      (cfg (some (phaseLabel (.seek d))) regs (data raw [] [] [] path) ctx)
      (some (phaseResult (.seek d) regs (data raw [] [] [] path) ctx))
      (runSteps d raw path) := machineCfgInTime caller d initial raw path regs ctx

theorem initializer_and_installed_path_are_distinct (caller : ExampleCaller)
    (initial : Bool) :
    Turing.initList (concreteMachine .left caller initial) ([1,1,0,1,0,0,0] : Word) ≠
      cfg (some (phaseLabel (.seek .left))) (clean initial)
        (data [1,1,0,1,0,0,0] [] [] [] [.left]) emptyContext := by
  rw [genuine_initializer_has_no_path_or_protected_cells]
  intro same
  have paths := congrArg (fun c : ExampleCfg => c.stk (.inl .path)) same
  cases paths

theorem genuine_root_fixture_evaluation :
    evaluate (.inl (.seek .left)) (data [1,1,0,1,0,0,0] [] [] [] []) =
      ⟨.failure, data [1,1,0,1,0,0,0] [] [] [] [], 16⟩ := by
  simp [evaluate_phase, evaluate_result, advance, markerWord, modeResult,
    nodeTag, emptyTag, data]

theorem installed_left_path_fixture_evaluation :
    evaluate (.inl (.seek .left)) (data [1,1,0,1,0,0,0] [] [] [] [.left]) =
      ⟨.success, data [1,1,1,0,0,0,0] [] [] [] [], 9⟩ := by
  simp [evaluate_phase, evaluate_result, advance, markerWord, modeResult,
    nodeTag, emptyTag, data]

theorem genuine_root_failure_and_installed_path_success_use_the_same_package
    (caller : ExampleCaller) (initial : Bool) :
    (fun c => c.bind (concreteMachine .left caller initial).step)^[16]
        (some (Turing.initList (concreteMachine .left caller initial) ([1,1,0,1,0,0,0] : Word))) =
        some (cfg (some (resultLabel .failure)) (clean initial)
          (data [1,1,0,1,0,0,0] [] [] [] []) emptyContext) ∧
      (fun c => c.bind (concreteMachine .left caller initial).step)^[9]
        (some (cfg (some (phaseLabel (.seek .left))) (clean initial)
          (data [1,1,0,1,0,0,0] [] [] [] [.left]) emptyContext)) =
        some (cfg (some (resultLabel .success)) (clean initial)
          (data [1,1,1,0,0,0,0] [] [] [] []) emptyContext) := by
  constructor
  · change (fun c : Option ExampleCfg =>
        c.bind (concreteMachine .left caller initial).step)^[16]
        (some (Turing.initList (concreteMachine .left caller initial)
          ([1,1,0,1,0,0,0] : Word))) = _
    have actual := machine_init_run caller .left initial [1,1,0,1,0,0,0]
    simpa only [concreteMachine, runSteps, phaseSteps, phaseResult,
      show ({ source := [1,1,0,1,0,0,0] } : LocalData) = data [1,1,0,1,0,0,0] [] [] [] [] from rfl,
      show ({ source := [1,1,0,1,0,0,0], path := [] } : LocalData) =
        data [1,1,0,1,0,0,0] [] [] [] [] from rfl,
      genuine_root_fixture_evaluation, emptyContext_eq, initialRegisters, clean, reset]
      using actual
  · have actual := machine_cfg_run caller .left initial [1,1,0,1,0,0,0] [.left]
      (clean initial) emptyContext
    simpa only [concreteMachine, runSteps, phaseSteps, phaseResult, entry,
      show ({ source := [1,1,0,1,0,0,0], path := [.left] } : LocalData) =
        data [1,1,0,1,0,0,0] [] [] [] [.left] from rfl,
      installed_left_path_fixture_evaluation, reset, clean]
      using actual

def genuineRootFixtureInTime (caller : ExampleCaller) (initial : Bool) :
    StateTransition.EvalsToInTime (concreteMachine .left caller initial).step
      (Turing.initList (concreteMachine .left caller initial) ([1,1,0,1,0,0,0] : Word))
      (some (cfg (some (resultLabel .failure)) (clean initial)
        (data [1,1,0,1,0,0,0] [] [] [] []) emptyContext)) 16 where
  steps := 16
  evals_in_steps :=
    (genuine_root_failure_and_installed_path_success_use_the_same_package caller initial).1
  steps_le_m := Nat.le_refl _

def installedPathFixtureInTime (caller : ExampleCaller) (initial : Bool) :
    StateTransition.EvalsToInTime (concreteMachine .left caller initial).step
      (cfg (some (phaseLabel (.seek .left))) (clean initial)
        (data [1,1,0,1,0,0,0] [] [] [] [.left]) emptyContext)
      (some (cfg (some (resultLabel .success)) (clean initial)
        (data [1,1,1,0,0,0,0] [] [] [] []) emptyContext)) 9 where
  steps := 9
  evals_in_steps :=
    (genuine_root_failure_and_installed_path_success_use_the_same_package caller initial).2
  steps_le_m := Nat.le_refl _

section BlockedScans

variable {K Λ R : Type} {Γ : K → Type} [DecidableEq K]
variable (caller : External Λ → Statement Γ Λ R)
variable (regs : Registers R) (ctx : ∀ k, List (Γ k))

/-- The continued-prefix premise is retained, and dirty scratch survives prefix cleanup. -/
theorem blocked_saved_scan_has_its_exact_dirty_first_return
    {w z : Word} {h k : Nat} (continued : Continues w h k)
    (blocked : TreeParserMachine.Blocked z) (d : RotationDirection)
    (F S : Word) (P : List Branch) :
    FirstRun caller
      (cfg (some (phaseLabel (.scanPrefix d))) regs
        (data (w ++ z) F S (List.replicate h ()) P) ctx)
      (2 * w.length + k + F.length + 3)
      (cfg (some (resultLabel .failure)) (reset regs)
        (data (F.reverse ++ w ++ z) [] S [] P) ctx) :=
  firstRun_of_localRun caller
    (scanPrefix_blocked_localRun caller continued blocked d (data [] F S [] P) regs ctx)
    (by simp [Owned, cfg, resultLabel])

theorem blocked_scratch_scan_restores_both_accumulators_and_direction_markers
    {w z : Word} {h k : Nat} (continued : Continues w h k)
    (blocked : TreeParserMachine.Blocked z) (d : RotationDirection)
    (F S : Word) (P : List Branch) :
    FirstRun caller
      (cfg (some (phaseLabel (.scanScratch d))) regs
        (data (w ++ z) F S (List.replicate h ()) P) ctx)
      (2 * w.length + k + S.length + F.length + 4)
      (cfg (some (resultLabel .failure)) (reset regs)
        (data (F.reverse ++ markerWord (scratchFailure d) ++ S.reverse ++ w ++ z) [] [] [] P) ctx) :=
  firstRun_of_localRun caller
    (scanScratch_blocked_localRun caller continued blocked d (data [] F S [] P) regs ctx)
    (by simp [Owned, cfg, resultLabel])

theorem both_raw_root_patterns_preserve_arbitrary_saved_words_and_suffixes
    (A : BinaryTree Unit) (F z : Word) :
    FirstRun caller
      (cfg (some (phaseLabel (.seek .left))) regs
        (data ([1] ++ treeCode A ++ [1] ++ z) F [] [] []) ctx)
      (2 * (treeCode A).length + 5 + F.length)
      (cfg (some (resultLabel .success)) (reset regs)
        (data (F.reverse ++ [1,1] ++ treeCode A ++ z) [] [] [] []) ctx) ∧
      FirstRun caller
        (cfg (some (phaseLabel (.seek .right))) regs
          (data ([1,1] ++ treeCode A ++ z) F [] [] []) ctx)
        (2 * (treeCode A).length + 4 + F.length)
        (cfg (some (resultLabel .success)) (reset regs)
          (data (F.reverse ++ [1] ++ treeCode A ++ [1] ++ z) [] [] [] []) ctx) := by
  constructor
  · simpa only [List.singleton_append, List.cons_append, List.nil_append, List.append_assoc, data, nodeTag] using
      firstRun_of_localRun caller (root_left_pattern_localRun caller A z F regs ctx)
        (by simp [Owned, cfg, resultLabel])
  · simpa only [List.singleton_append, List.cons_append, List.nil_append, List.append_assoc, data, nodeTag] using
      firstRun_of_localRun caller (root_right_pattern_localRun caller A z F regs ctx)
        (by simp [Owned, cfg, resultLabel])

end BlockedScans

theorem left_raw_root_pattern_has_the_fixed_clock_and_complete_output
    (caller : ExampleCaller) (flag : Bool) (A : BinaryTree Unit) (z : Word) :
    LeftRootPatternExpected caller flag A z := by
  have segment := root_left_pattern_localRun caller A z [] (stale flag) ordinaryContext
  have rank := LocalRun.remaining caller segment
  refine ⟨?_, ?_⟩
  · simpa only [remainingSteps, cfg, phaseLabel, resultLabel, dataOfCfg,
      List.length_nil, Nat.add_zero, List.singleton_append, List.cons_append,
      List.nil_append, List.append_assoc, runSteps, nodeTag] using rank
  · simpa only [List.singleton_append, List.cons_append, List.nil_append,
      List.length_nil, Nat.add_zero, List.reverse_nil, List.append_assoc,
      cleanEntry, atPhase, atResult, data, nodeTag, reset, stale, clean] using
      firstRun_of_localRun caller segment (by simp [Owned, cfg, resultLabel])

theorem right_raw_root_pattern_has_the_fixed_clock_and_complete_output
    (caller : ExampleCaller) (flag : Bool) (A : BinaryTree Unit) (z : Word) :
    RightRootPatternExpected caller flag A z := by
  have segment := root_right_pattern_localRun caller A z [] (stale flag) ordinaryContext
  have rank := LocalRun.remaining caller segment
  refine ⟨?_, ?_⟩
  · simpa only [remainingSteps, cfg, phaseLabel, resultLabel, dataOfCfg,
      List.length_nil, Nat.add_zero, List.singleton_append, List.cons_append,
      List.nil_append, List.append_assoc, runSteps, nodeTag] using rank
  · simpa only [List.singleton_append, List.cons_append, List.nil_append,
      List.length_nil, Nat.add_zero, List.reverse_nil, List.append_assoc,
      cleanEntry, atPhase, atResult, data, nodeTag, reset, stale, clean] using
      firstRun_of_localRun caller segment (by simp [Owned, cfg, resultLabel])

theorem protected_words_have_the_actual_two_stack_cell_sum (tags : Word) (units : List Unit) :
    contextCells (protectedWords tags units) = tags.length + units.length := by
  rw [contextCells, show (Finset.univ : Finset (Fin 2)) = {0, 1} from by decide]
  simp [protectedWords]
  rfl

theorem ordinary_context_has_seven_actual_cells : contextCells ordinaryContext = 7 :=
  protected_words_have_the_actual_two_stack_cell_sum _ _

theorem all_fixed_carrier_expectations : CarrierExpected := by
  obtain ⟨localsCount, phases, results, temporaries, stackCount, labels, registers⟩ :=
    actual_finite_carrier_counts
  exact ⟨localsCount, phases, results, temporaries, stackCount, labels, registers,
    owned_labels_stay_finite_with_nat_callers.1,
    owned_labels_stay_finite_with_nat_callers.2, ordinary_context_has_seven_actual_cells⟩

section PhysicalPrefixes

variable {K Λ R : Type} {Γ : K → Type} [DecidableEq K] [Fintype K]
variable (caller : External Λ → Statement Γ Λ R)

/-- Rank, reset, frame, conserved Tags and the cell bound share one actual prefix. -/
theorem every_inclusive_prefix_satisfies_the_complete_fixed_contract
    (start : Cfg Γ Λ R) (n : Nat) : PrefixExpected caller start n := by
  intro bound
  obtain ⟨reached, executed, rank, path, ownership, zero, registers, frame⟩ :=
    owned_prefix_frame caller start n bound
  have bounded := local_reaches_potential_le caller path
  exact ⟨reached, executed, rank, path, ownership, zero, registers, frame,
    local_reaches_tag_debt caller path, bounded,
    (stackCells_le_potential reached).trans bounded⟩

theorem every_clean_raw_prefix_has_the_physical_dependent_sum_bound
    (d : RotationDirection) (raw : Word) (path : List Branch)
    (regs : Registers R) (ctx : ∀ k, List (Γ k)) (n : Nat)
    (bound : n ≤ runSteps d raw path) (reached : Cfg Γ Λ R)
    (executed : Runs caller (entry d regs raw path ctx) n reached) :
    (∑ k : StackId K, (reached.stk k).length) ≤
      2 * raw.length + path.length + contextCells ctx :=
  prefix_stackCells_le caller d raw path regs ctx n bound reached executed

omit [Fintype K] in
theorem inclusive_prefix_rank_of_actual_run (start reached : Cfg Γ Λ R)
    (total n : Nat) (rank : remainingSteps start = total) (bound : n ≤ total)
    (executed : Runs caller start n reached) : remainingSteps reached = total - n := by
  obtain ⟨actual, actualRun, actualRank, _, _⟩ :=
    owned_prefix caller start n (by simpa only [rank] using bound)
  have same := Option.some.inj (actualRun.symm.trans executed)
  subst actual
  simpa only [rank] using actualRank

end PhysicalPrefixes

def boundaryReached (flag : Bool) (b : Boundary) : ExampleCfg :=
  cfg (some (controlLabel b.2.1)) (if b.1 = 0 then stale flag else clean flag)
    b.2.2.1 ordinaryContext

def Boundary.Expected (caller : ExampleCaller) (flag : Bool)
    (d : RotationDirection) (input : Word) (total : Nat) (b : Boundary) : Prop :=
  Runs caller (cleanEntry d flag input []) b.1 (boundaryReached flag b) ∧
    remainingSteps (boundaryReached flag b) = total - b.1 ∧
    ownedCells (boundaryReached flag b) = b.2.2.2 ∧
    stackCells (boundaryReached flag b) = b.2.2.2 + 7 ∧
    tagCells (boundaryReached flag b) + debt (boundaryReached flag b).l = 5

theorem every_left_literal_boundary_is_an_actual_prefix
    (caller : ExampleCaller) (flag : Bool) (b : Boundary) (member : b ∈ leftBoundaries) :
    Runs caller (cleanEntry .left flag [1,0,1,0,0] []) b.1 (boundaryReached flag b) := by
  simp only [leftBoundaries, List.mem_cons, List.mem_nil_iff, or_false] at member
  rcases member with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;>
    simp [Runs, cleanEntry, atPhase, boundaryReached, Function.iterate_succ_apply,
      next_some, advance_step, advance, controlLabel,
      nodeTag, emptyTag, data, reset, stale, clean, markerWord, modeResult]

theorem every_right_literal_boundary_is_an_actual_prefix
    (caller : ExampleCaller) (flag : Bool) (b : Boundary) (member : b ∈ rightBoundaries) :
    Runs caller (cleanEntry .right flag [1,1,0,0,0] []) b.1 (boundaryReached flag b) := by
  simp only [rightBoundaries, List.mem_cons, List.mem_nil_iff, or_false] at member
  rcases member with rfl | rfl | rfl | rfl | rfl | rfl | rfl <;>
    simp [Runs, cleanEntry, atPhase, boundaryReached, Function.iterate_succ_apply,
      next_some, advance_step, advance, controlLabel,
      nodeTag, emptyTag, data, reset, stale, clean, markerWord, modeResult]

theorem minimal_initial_ranks_are_seven_and_six (flag : Bool) :
    remainingSteps (cleanEntry .left flag [1,0,1,0,0] []) = 7 ∧
      remainingSteps (cleanEntry .right flag [1,1,0,0,0] []) = 6 := by
  constructor
  · simpa [remainingSteps, cleanEntry, atPhase, data, cfg, phaseLabel, resultLabel,
      dataOfCfg, treeCode, nodeTag, emptyTag] using
      LocalRun.remaining haltCaller
        (root_left_pattern_localRun haltCaller .nil [0,0] [] (stale flag) ordinaryContext)
  · simpa [remainingSteps, cleanEntry, atPhase, data, cfg, phaseLabel, resultLabel,
      dataOfCfg, treeCode, nodeTag, emptyTag] using
      LocalRun.remaining haltCaller
        (root_right_pattern_localRun haltCaller .nil [0,0] [] (stale flag) ordinaryContext)

theorem every_left_literal_boundary_has_its_rank_and_actual_cell_count
    (caller : ExampleCaller) (flag : Bool) (b : Boundary) (member : b ∈ leftBoundaries) :
    Boundary.Expected caller flag .left [1,0,1,0,0] 7 b := by
  have executed := every_left_literal_boundary_is_an_actual_prefix caller flag b member
  have bound : b.1 ≤ 7 := by
    simp only [leftBoundaries, List.mem_cons, List.mem_nil_iff, or_false] at member
    rcases member with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> decide
  refine ⟨executed, inclusive_prefix_rank_of_actual_run caller _ _ 7 b.1
    (minimal_initial_ranks_are_seven_and_six flag).1 bound executed, ?_⟩
  simp only [leftBoundaries, List.mem_cons, List.mem_nil_iff, or_false] at member
  rcases member with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;>
    simp only [boundaryReached, stackCells_cfg]
  all_goals
    simp [ownedCells, tagCells, dataOfCfg, cfg, localCells, localTagCells,
      ordinary_context_has_seven_actual_cells, debt, controlLabel, phaseLabel,
      resultLabel, phaseDebt, data]

theorem every_right_literal_boundary_has_its_rank_and_actual_cell_count
    (caller : ExampleCaller) (flag : Bool) (b : Boundary) (member : b ∈ rightBoundaries) :
    Boundary.Expected caller flag .right [1,1,0,0,0] 6 b := by
  have executed := every_right_literal_boundary_is_an_actual_prefix caller flag b member
  have bound : b.1 ≤ 6 := by
    simp only [rightBoundaries, List.mem_cons, List.mem_nil_iff, or_false] at member
    rcases member with rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> decide
  refine ⟨executed, inclusive_prefix_rank_of_actual_run caller _ _ 6 b.1
    (minimal_initial_ranks_are_seven_and_six flag).2 bound executed, ?_⟩
  simp only [rightBoundaries, List.mem_cons, List.mem_nil_iff, or_false] at member
  rcases member with rfl | rfl | rfl | rfl | rfl | rfl | rfl <;>
    simp only [boundaryReached, stackCells_cfg]
  all_goals
    simp [ownedCells, tagCells, dataOfCfg, cfg, localCells, localTagCells,
      ordinary_context_has_seven_actual_cells, debt, controlLabel, phaseLabel,
      resultLabel, phaseDebt, data]


theorem empty_success_restoration_reifies_two_owed_markers
    (caller : ExampleCaller) (flag : Bool) :
    step caller (atPhase (.restoreScratch .successLeft) flag (data [] [] [] [] [])) =
      some (cfg (some (phaseLabel (.restorePrefix .success))) (clean flag)
        (data [1,1] [] [] [] []) ordinaryContext) ∧
      ownedCells (atPhase (.restoreScratch .successLeft) flag (data [] [] [] [] [])) = 0 ∧
      ownedCells (cfg (some (phaseLabel (.restorePrefix .success))) (clean flag)
        (data [1,1] [] [] [] []) ordinaryContext : ExampleCfg) = 2 ∧
      debt (atPhase (.restoreScratch .successLeft) flag (data [] [] [] [] [])).l = 2 := by
  exact ⟨restoreScratch_step_nil caller .successLeft (data [] [] [] [] [])
    (stale flag) ordinaryContext, rfl, rfl, rfl⟩

theorem a_node_scan_needs_source_credit_for_its_pending_cell
    (caller : ExampleCaller) (flag : Bool) :
    step caller (atPhase (.scanPrefix .left) flag (data [1] [] [] [] [])) =
      some (cfg (some (phaseLabel (.scanPrefix .left))) (clean flag)
        (data [] [1] [] [()] []) ordinaryContext) ∧
      ownedCells (atPhase (.scanPrefix .left) flag (data [1] [] [] [] [])) = 1 ∧
      ownedCells (cfg (some (phaseLabel (.scanPrefix .left))) (clean flag)
        (data [] [1] [] [()] []) ordinaryContext : ExampleCfg) = 2 ∧
      credit (atPhase (.scanPrefix .left) flag (data [1] [] [] [] [])) = 1 := by
  exact ⟨scanPrefix_step_node caller .left [] (data [1] [] [] [] [])
    (stale flag) ordinaryContext, rfl, rfl, rfl⟩

theorem the_real_initializer_has_the_inclusive_twice_input_bound
    (caller : ExampleCaller) (d : RotationDirection) (initial : Bool) (raw : Word)
    (n : Nat) (bound : n ≤ runSteps d raw []) (reached : ExampleCfg)
    (executed : (fun c => c.bind (concreteMachine d caller initial).step)^[n]
      (some (Turing.initList (concreteMachine d caller initial) raw)) = some reached) :
    stackCells reached ≤ 2 * raw.length :=
  machine_prefix_stackCells_le caller d initial raw n bound reached executed

theorem the_real_installed_path_keeps_the_path_and_context_cell_terms
    (caller : ExampleCaller) (d : RotationDirection) (initial : Bool) (raw : Word)
    (path : List Branch) (flag : Bool) (n : Nat) (bound : n ≤ runSteps d raw path)
    (reached : ExampleCfg)
    (executed : (fun c => c.bind (concreteMachine d caller initial).step)^[n]
      (some (entry d (stale flag) raw path ordinaryContext)) = some reached) :
    stackCells reached ≤ 2 * raw.length + path.length + 7 := by
  simpa only [ordinary_context_has_seven_actual_cells] using
    machine_cfg_prefix_stackCells_le caller d initial raw path (stale flag)
      ordinaryContext n bound reached executed

section RepresentedExecution

variable {K Λ R : Type} {Γ : K → Type} [DecidableEq K]
variable (caller : External Λ → Statement Γ Λ R)
variable (regs : Registers R) (ctx : ∀ k, List (Γ k))

/-- The actual source operation determines the first live endpoint, with literal old data. -/
theorem represented_first_return_retains_every_saved_word_and_suffix
    (d : RotationDirection) (p : List Branch) (s : BinaryTree Unit) (F z : Word) :
    FirstRun caller
      (cfg (some (phaseLabel (.seek d))) regs (data (treeCode s ++ z) F [] [] p) ctx)
      (representedClock d p s + F.length)
      (cfg (some (resultLabel (if (applyMoveRun ⟨d,p⟩ s).1.isSome then .success else .failure)))
        (reset regs)
        (data (F.reverse ++ treeCode ((applyMoveRun ⟨d,p⟩ s).1.getD s) ++ z)
          [] [] [] (remainingPath p s)) ctx) := by
  exact firstRun_of_localRun caller (run_code_localRun caller d p s F z regs ctx)
    (by simp [Owned, cfg, resultLabel])

def representedWithSavedInTime (d : RotationDirection) (p : List Branch)
    (s : BinaryTree Unit) (F z : Word) :
    StateTransition.EvalsToInTime (step caller)
      (cfg (some (phaseLabel (.seek d))) regs (data (treeCode s ++ z) F [] [] p) ctx)
      (some (cfg
        (some (resultLabel (if (applyMoveRun ⟨d,p⟩ s).1.isSome then .success else .failure)))
        (reset regs)
        (data (F.reverse ++ treeCode ((applyMoveRun ⟨d,p⟩ s).1.getD s) ++ z)
          [] [] [] (remainingPath p s)) ctx))
      (representedClock d p s + F.length) :=
  localRunInTime caller (run_code_localRun caller d p s F z regs ctx)

theorem represented_timing_charges_old_saved_cells_exactly
    (d : RotationDirection) (p : List Branch) (s : BinaryTree Unit) (F z : Word) :
    (representedWithSavedInTime caller regs ctx d p s F z).steps =
      representedClock d p s + F.length := rfl

theorem represented_success_has_empty_physical_path
    (d : RotationDirection) (p : List Branch) (s t : BinaryTree Unit)
    (returned : (applyMoveRun ⟨d,p⟩ s).1 = some t) (F z : Word) :
    FirstRun caller
      (cfg (some (phaseLabel (.seek d))) regs (data (treeCode s ++ z) F [] [] p) ctx)
      (representedClock d p s + F.length)
      (cfg (some (resultLabel .success)) (reset regs)
        (data (F.reverse ++ treeCode t ++ z) [] [] [] []) ctx) := by
  have actual := represented_first_return_retains_every_saved_word_and_suffix
    caller regs ctx d p s F z
  simpa only [returned, Option.isSome_some, ite_true, Option.getD_some,
    remainingPath_nil_of_source_success d p s t returned] using actual

theorem represented_failure_restores_the_literal_code_and_keeps_the_actual_tail
    (d : RotationDirection) (p : List Branch) (s : BinaryTree Unit)
    (failed : (applyMoveRun ⟨d,p⟩ s).1 = none) (F z : Word) :
    FirstRun caller
      (cfg (some (phaseLabel (.seek d))) regs (data (treeCode s ++ z) F [] [] p) ctx)
      (representedClock d p s + F.length)
      (cfg (some (resultLabel .failure)) (reset regs)
        (data (F.reverse ++ treeCode s ++ z) [] [] [] (remainingPath p s)) ctx) := by
  simpa only [failed, Option.isSome_none, Bool.false_eq_true, ite_false, Option.getD_none] using
    represented_first_return_retains_every_saved_word_and_suffix caller regs ctx d p s F z

/-- Common-prefix cancellation and actual code-prefix injectivity identify the returned tree. -/
theorem represented_first_success_iff_the_actual_source_result
    (d : RotationDirection) (p : List Branch) (s t : BinaryTree Unit) (F z : Word) :
    (∃ n, FirstRun caller
      (cfg (some (phaseLabel (.seek d))) regs (data (treeCode s ++ z) F [] [] p) ctx) n
      (cfg (some (resultLabel .success)) (reset regs)
        (data (F.reverse ++ treeCode t ++ z) [] [] [] []) ctx)) ↔
      (applyMoveRun ⟨d,p⟩ s).1 = some t := by
  constructor
  · rintro ⟨n, first⟩
    have specified := represented_first_return_retains_every_saved_word_and_suffix
      caller regs ctx d p s F z
    have same := (firstRun_unique caller first specified).2
    have label := congrArg (fun c : Cfg Γ Λ R => c.l) same
    have source := congrArg (fun c : Cfg Γ Λ R => c.stk (.inl .source)) same
    cases actual : (applyMoveRun ⟨d,p⟩ s).1 with
    | none => simp [actual, cfg, resultLabel] at label
    | some u =>
        have codes : treeCode t ++ z = treeCode u ++ z :=
          List.append_cancel_left (as := F.reverse)
            (by simpa [actual, cfg, data, List.append_assoc] using source)
        have equal := (parseTreeRun_prefix_injective t u z z codes).1
        simp only [equal]
  · intro actual
    exact ⟨representedClock d p s + F.length,
      represented_success_has_empty_physical_path caller regs ctx d p s t actual F z⟩

end RepresentedExecution

theorem every_represented_fixture_is_an_actual_first_return
    (caller : ExampleCaller) (flag : Bool) (c : RepresentedFixture)
    (member : c ∈ representedFixtures) (F z : Word) : c.Expected caller flag F z := by
  have source := every_represented_fixture_has_its_source_result c member
  obtain ⟨clock, path⟩ := every_represented_fixture_has_its_fixed_clock_and_remaining_path c member
  refine ⟨source, clock, path, ?_⟩
  simpa only [atPhase, atResult, source, clock, path, reset, stale, clean] using
    represented_first_return_retains_every_saved_word_and_suffix caller (stale flag)
      ordinaryContext c.move.direction c.move.position c.tree F z

theorem all_represented_rows_keep_the_nonpalindromic_suffix
    (caller : ExampleCaller) (flag : Bool) (c : RepresentedFixture)
    (member : c ∈ representedFixtures) (F : Word) :
    c.Expected caller flag F [15,2,7] :=
  every_represented_fixture_is_an_actual_first_return caller flag c member F [15,2,7]

def representedFixtureInTime (caller : ExampleCaller) (flag : Bool)
    (c : RepresentedFixture) (member : c ∈ representedFixtures) (F z : Word) :
    StateTransition.EvalsToInTime (step caller)
      (atPhase (.seek c.move.direction) flag
        (data (treeCode c.tree ++ z) F [] [] c.move.position))
      (some (atResult (if c.value.isSome then .success else .failure) flag
        (data (F.reverse ++ treeCode (c.value.getD c.tree) ++ z) [] [] [] c.remaining)))
      (c.ticks + F.length) where
  steps := c.ticks + F.length
  evals_in_steps :=
    (every_represented_fixture_is_an_actual_first_return caller flag c member F z).2.2.2.1
  steps_le_m := Nat.le_refl _

theorem represented_fixture_time_uses_machine_ticks_and_saved_length
    (caller : ExampleCaller) (flag : Bool) (c : RepresentedFixture)
    (member : c ∈ representedFixtures) (F z : Word) :
    (representedFixtureInTime caller flag c member F z).steps = c.ticks + F.length := rfl

theorem the_context_prefix_is_the_actual_encoded_prefix
    (frames : List PositionFrame) (focus : BinaryTree Unit) :
    treeCode (plugFrames frames focus) =
      contextPrefix frames ++ treeCode focus ++ contextSuffix frames :=
  treeCode_plugFrames frames focus

theorem source_and_machine_clocks_have_separate_cursor_formulas
    (d : RotationDirection) (p : List Branch) (s : BinaryTree Unit) :
    (applyMoveRun ⟨d,p⟩ s).2 =
      (if (applyMoveRun ⟨d,p⟩ s).1.isSome then 3 * descentCount p s + 5
       else 2 * descentCount p s + if stoppedPath p s = [] then 3 else 2) ∧
      representedClock d p s = 2 * navigationLength p s +
        (if stoppedPath p s = [] then representedClock d [] (stoppedTree p s) else 3) ∧
      remainingPath p s =
        (if stoppedPath p s = [] then [] else (stoppedPath p s).tail) :=
  ⟨source_cost_eq_stopped d p s, representedClock_eq_stopped d p s,
    remainingPath_eq_stopped p s⟩

def inverseStart (flag : Bool) : ExampleCfg :=
  cleanEntry .left flag [1,1,0,1,0,0,0] [.left]

def inverseReturned (flag : Bool) : ExampleCfg :=
  atResult .success flag (data [1,1,1,0,0,0,0] [] [] [] [])

def inverseReentry (reinstall flag : Bool) : ExampleCfg :=
  cfg (some (phaseLabel (.seek .right))) (clean flag)
    (data [1,1,1,0,0,0,0] [] [] [] (if reinstall then [.left] else [])) ordinaryContext

def inverseFinished (reinstall flag : Bool) : ExampleCfg :=
  atResult .success flag
    (data (if reinstall then [1,1,0,1,0,0,0] else [1,1,0,0,1,0,0]) [] [] [] [])

theorem inverse_first_segment (reinstall flag : Bool) :
    LocalRun (inverseCaller reinstall) 9 (inverseStart flag) (inverseReturned flag) :=
  run_code_localRun (inverseCaller reinstall) .left [.left] leftContext [] []
    (stale flag) ordinaryContext

theorem inverse_paid_reentry (reinstall flag : Bool) :
    step (inverseCaller reinstall) (inverseReturned flag) = some (inverseReentry reinstall flag) := by
  cases reinstall with
  | false =>
      exact inverse_reentry_without_push (clean flag)
        (data [1,1,1,0,0,0,0] [] [] [] []) ordinaryContext
  | true =>
      exact inverse_reentry_with_physical_push (clean flag)
        (data [1,1,1,0,0,0,0] [] [] [] []) ordinaryContext

theorem inverse_second_segment (reinstall flag : Bool) :
    LocalRun (inverseCaller reinstall) (if reinstall then 8 else 10)
      (inverseReentry reinstall flag) (inverseFinished reinstall flag) := by
  cases reinstall with
  | false =>
      exact run_code_localRun (inverseCaller false) .right [] afterLeftContext [] []
        (clean flag) ordinaryContext
  | true =>
      exact run_code_localRun (inverseCaller true) .right [.left] afterLeftContext [] []
        (clean flag) ordinaryContext

def inverseFirstInTime (reinstall flag : Bool) :
    StateTransition.EvalsToInTime (step (inverseCaller reinstall))
      (inverseStart flag) (some (inverseReturned flag)) 9 :=
  localRunInTime (inverseCaller reinstall) (inverse_first_segment reinstall flag)

def inverseReentryInTime (reinstall flag : Bool) :
    StateTransition.EvalsToInTime (step (inverseCaller reinstall))
      (inverseReturned flag) (some (inverseReentry reinstall flag)) 1 :=
  oneActualStepTime (inverseCaller reinstall) _ _ (inverse_paid_reentry reinstall flag)

def inverseSecondInTime (reinstall flag : Bool) :
    StateTransition.EvalsToInTime (step (inverseCaller reinstall))
      (inverseReentry reinstall flag) (some (inverseFinished reinstall flag))
      (if reinstall then 8 else 10) :=
  localRunInTime (inverseCaller reinstall) (inverse_second_segment reinstall flag)

/-- Two genuine segments are joined by a paid caller activation on the same finite program. -/
def composedInverseInTime (reinstall flag : Bool) :
    StateTransition.EvalsToInTime (step (inverseCaller reinstall))
      (inverseStart flag) (some (inverseFinished reinstall flag))
      ((if reinstall then 8 else 10) + 1 + 9) :=
  appendTimed (inverseCaller reinstall) (inverseStart flag) (inverseReturned flag)
    (some (inverseFinished reinstall flag)) 9 ((if reinstall then 8 else 10) + 1)
    (inverseFirstInTime reinstall flag)
    (appendTimed (inverseCaller reinstall) (inverseReturned flag)
      (inverseReentry reinstall flag) (some (inverseFinished reinstall flag))
      1 (if reinstall then 8 else 10)
      (inverseReentryInTime reinstall flag) (inverseSecondInTime reinstall flag))

theorem inverse_composition_retains_every_exact_paid_step (flag : Bool) :
    (inverseFirstInTime false flag).steps = 9 ∧
      (inverseReentryInTime false flag).steps = 1 ∧
      (inverseSecondInTime false flag).steps = 10 ∧
      (composedInverseInTime false flag).steps = 20 ∧
      (inverseFirstInTime true flag).steps = 9 ∧
      (inverseReentryInTime true flag).steps = 1 ∧
      (inverseSecondInTime true flag).steps = 8 ∧
      (composedInverseInTime true flag).steps = 18 :=
  ⟨rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl⟩

theorem a_consumed_path_changes_the_actual_inverse_endpoint (flag : Bool) :
    FirstRun (inverseCaller false) (inverseStart flag) 9 (inverseReturned flag) ∧
      (next (inverseCaller false))^[20] (some (inverseStart flag)) =
        some (atResult .success flag (data [1,1,0,0,1,0,0] [] [] [] [])) ∧
      (next (inverseCaller true))^[18] (some (inverseStart flag)) =
        some (atResult .success flag (data [1,1,0,1,0,0,0] [] [] [] [])) ∧
      (inverseReturned flag).stk (.inl .path) = [] ∧
      (inverseReentry true flag).stk (.inl .path) = [.left] ∧
      (inverseFinished false flag).stk (.inl .source) ≠
        (inverseStart flag).stk (.inl .source) := by
  refine ⟨firstRun_of_localRun (inverseCaller false) (inverse_first_segment false flag)
    (by simp [inverseReturned, atResult, cfg, resultLabel, Owned]),
    (composedInverseInTime false flag).evals_in_steps,
    (composedInverseInTime true flag).evals_in_steps, rfl, rfl, ?_⟩
  change ([1,1,0,0,1,0,0] : Word) ≠ [1,1,0,1,0,0,0]
  decide

def allocationReturned (flag : Bool) : ExampleCfg :=
  atResult .failure flag (data [] [] [] [] [])

def allocationOnce (flag : Bool) : ExampleCfg :=
  cfg (some (resultLabel .failure)) (clean flag) (data [] [] [] [] [])
    (protectedWords [15,2,7,10,3] [(),(),()])

def allocationTwice (flag : Bool) : ExampleCfg :=
  cfg (some (resultLabel .failure)) (clean flag) (data [] [] [] [] [])
    (protectedWords [15,2,7,10,3] [(),(),(),()])

def allocationReturnInTime (flag : Bool) :
    StateTransition.EvalsToInTime (step allocatingCaller)
      (cleanEntry .left flag [] []) (some (allocationReturned flag)) 4 :=
  localRunInTime allocatingCaller
    (empty_root_physical_segment allocatingCaller (stale flag) ordinaryContext .left)

def allocationOnceInTime (flag : Bool) :
    StateTransition.EvalsToInTime (step allocatingCaller)
      (cleanEntry .left flag [] []) (some (allocationOnce flag)) 5 :=
  appendTimed allocatingCaller _ (allocationReturned flag) _ 4 1
    (allocationReturnInTime flag)
    (oneActualStepTime allocatingCaller _ _
      (allocation_is_an_actual_protected_unit_push .failure (clean flag)
        (data [] [] [] [] []) [15,2,7,10,3] [(),()]))

def allocationTwiceInTime (flag : Bool) :
    StateTransition.EvalsToInTime (step allocatingCaller)
      (cleanEntry .left flag [] []) (some (allocationTwice flag)) 6 :=
  appendTimed allocatingCaller _ (allocationOnce flag) _ 5 1
    (allocationOnceInTime flag)
    (oneActualStepTime allocatingCaller _ _
      (allocation_is_an_actual_protected_unit_push .failure (clean flag)
        (data [] [] [] [] []) [15,2,7,10,3] [(),(),()]))

theorem allocation_escapes_only_after_the_original_space_bound_ends (flag : Bool) :
    FirstRun allocatingCaller (cleanEntry .left flag [] []) 4 (allocationReturned flag) ∧
      stackCells (allocationReturned flag) = 7 ∧
      stackCells (allocationOnce flag) = 8 ∧
      stackCells (allocationTwice flag) = 9 ∧
      7 < stackCells (allocationOnce flag) ∧ 7 < stackCells (allocationTwice flag) ∧
      (allocationReturnInTime flag).steps = 4 ∧
      (allocationOnceInTime flag).steps = 5 ∧ (allocationTwiceInTime flag).steps = 6 := by
  have cells0 : stackCells (allocationReturned flag) = 7 := by
    simp [allocationReturned, atResult, stackCells_cfg, localCells, data,
      ordinaryContext, protected_words_have_the_actual_two_stack_cell_sum]
  have cells1 : stackCells (allocationOnce flag) = 8 := by
    simp [allocationOnce, stackCells_cfg, localCells, data,
      protected_words_have_the_actual_two_stack_cell_sum]
  have cells2 : stackCells (allocationTwice flag) = 9 := by
    simp [allocationTwice, stackCells_cfg, localCells, data,
      protected_words_have_the_actual_two_stack_cell_sum]
  exact ⟨firstRun_of_localRun allocatingCaller
      (empty_root_physical_segment allocatingCaller (stale flag) ordinaryContext .left)
      (by simp [allocationReturned, atResult, cfg, resultLabel, Owned]),
    cells0, cells1, cells2, by omega, by omega, rfl, rfl, rfl⟩

def misleadingLaterFailureInTime (flag : Bool) :
    StateTransition.EvalsToInTime (step misleadingCaller)
      (cleanEntry .left flag [1,0,1,0,0] [])
      (some (atResult .failure flag (data [1,1,0,0,0] [] [] [] []))) 8 :=
  appendTimed misleadingCaller _
    (atResult .success flag (data [1,1,0,0,0] [] [] [] [])) _ 7 1
    (minimalLeftInTime misleadingCaller flag)
    (oneActualStepTime misleadingCaller _ _
      (a_caller_can_forge_the_opposite_result (clean flag)
        (data [1,1,0,0,0] [] [] [] []) ordinaryContext).1)

def misleadingLaterSuccessInTime (flag : Bool) :
    StateTransition.EvalsToInTime (step misleadingCaller)
      (cleanEntry .left flag [] [])
      (some (atResult .success flag (data [] [] [] [] []))) 5 :=
  appendTimed misleadingCaller _ (atResult .failure flag (data [] [] [] [] [])) _ 4 1
    (localRunInTime misleadingCaller
      (empty_root_physical_segment misleadingCaller (stale flag) ordinaryContext .left))
    (oneActualStepTime misleadingCaller _ _
      (a_caller_can_forge_the_opposite_result (clean flag)
        (data [] [] [] [] []) ordinaryContext).2)

def externalLive (flag : Bool) : ExampleCfg :=
  cfg (some (callerLabel ())) (clean flag) (data [] [] [] [] []) ordinaryContext

def externalHalt (flag : Bool) : ExampleCfg :=
  cfg none (clean flag) (data [] [] [] [] [])
    (protectedWords [13,15,2,7,10,3] [(),()])

def externalGotoInTime (flag : Bool) :
    StateTransition.EvalsToInTime (step externalCaller)
      (cleanEntry .left flag [] []) (some (externalLive flag)) 5 :=
  appendTimed externalCaller _ (atResult .failure flag (data [] [] [] [] [])) _ 4 1
    (localRunInTime externalCaller
      (empty_root_physical_segment externalCaller (stale flag) ordinaryContext .left))
    (oneActualStepTime externalCaller _ _
      (separate_external_label_is_reached_first .failure (clean flag)
        (data [] [] [] [] []) ordinaryContext))

def externalHaltInTime (flag : Bool) :
    StateTransition.EvalsToInTime (step externalCaller)
      (cleanEntry .left flag [] []) (some (externalHalt flag)) 6 :=
  appendTimed externalCaller _ (externalLive flag) _ 5 1
    (externalGotoInTime flag)
    (oneActualStepTime externalCaller _ _
      (external_label_executes_its_own_push_and_halt (clean flag)
        (data [] [] [] [] []) [15,2,7,10,3] [(),()]))

def externalOuterNoneInTime (flag : Bool) :
    StateTransition.EvalsToInTime (step externalCaller)
      (cleanEntry .left flag [] []) none 7 :=
  appendTimed externalCaller _ (externalHalt flag) none 6 1
    (externalHaltInTime flag) (oneActualStepTime externalCaller _ none rfl)

theorem misleading_and_external_timing_retains_the_actual_activations (flag : Bool) :
    (misleadingLaterFailureInTime flag).steps = 8 ∧
      (misleadingLaterSuccessInTime flag).steps = 5 ∧
      (externalGotoInTime flag).steps = 5 ∧
      (externalHaltInTime flag).steps = 6 ∧
      (externalOuterNoneInTime flag).steps = 7 := ⟨rfl, rfl, rfl, rfl, rfl⟩

theorem firstSuccess_iff_the_canonical_live_label
    {K Λ R : Type} {Γ : K → Type} [DecidableEq K]
    (caller : External Λ → Statement Γ Λ R) (q : Phase)
    (regs : Registers R) (D : LocalData) (ctx : ∀ k, List (Γ k)) :
    FirstSuccess caller (cfg (some (phaseLabel q)) regs D ctx) ↔
      (phaseResult (Λ := Λ) q regs D ctx).l = some (resultLabel .success) := by
  constructor
  · rintro ⟨n, reached, first, label⟩
    have same := (firstRun_unique caller first (phase_first_return caller q D regs ctx)).2
    simpa only [same] using label
  · intro label
    exact ⟨phaseSteps q D, phaseResult q regs D ctx,
      phase_first_return caller q D regs ctx, label⟩

theorem arbitrary_raw_root_first_success_characterizations
    {K Λ R : Type} {Γ : K → Type} [DecidableEq K]
    (caller : External Λ → Statement Γ Λ R) (regs : Registers R)
    (ctx : ∀ k, List (Γ k)) (w F : Word) :
    (FirstSuccess caller
      (cfg (some (phaseLabel (.seek .left))) regs (data w F [] [] []) ctx) ↔
      ∃ A : BinaryTree Unit, ∃ z : Word, w = [1] ++ treeCode A ++ [1] ++ z) ∧
      (FirstSuccess caller
        (cfg (some (phaseLabel (.seek .right))) regs (data w F [] [] []) ctx) ↔
        ∃ A : BinaryTree Unit, ∃ z : Word, w = [1,1] ++ treeCode A ++ z) := by
  constructor
  · exact (firstSuccess_iff_the_canonical_live_label caller (.seek .left) regs
      (data w F [] [] []) ctx).trans (by
      simpa only [List.singleton_append, List.cons_append, List.nil_append,
        List.append_assoc, data, nodeTag] using root_left_phaseResult_success_iff caller w F regs ctx)
  · exact (firstSuccess_iff_the_canonical_live_label caller (.seek .right) regs
      (data w F [] [] []) ctx).trans (by
      simpa only [List.singleton_append, List.cons_append, List.nil_append,
        List.append_assoc, data, nodeTag] using root_right_phaseResult_success_iff caller w F regs ctx)

/-- The two root iff clauses concern the first actual handoff under arbitrary caller bodies. -/
theorem both_raw_root_success_characterizations (caller : ExampleCaller)
    (flag : Bool) (w : Word) : RootSuccessIffExpected caller flag w := by
  exact arbitrary_raw_root_first_success_characterizations caller (stale flag) ordinaryContext w []

theorem both_malformed_root_successes_are_actual_unrecognized_first_returns
    (caller : ExampleCaller) (flag : Bool) :
    FirstRun caller (cleanEntry .left flag [1,0,1,15] []) 7
      (atResult .success flag (data [1,1,0,15] [] [] [] [])) ∧
      FirstRun caller (cleanEntry .right flag [1,1,0,15] []) 6
        (atResult .success flag (data [1,0,1,15] [] [] [] [])) ∧
      (parseTreeRun [1,0,1,15]).1 = none ∧ (parseTreeRun [1,1,0,15]).1 = none := by
  exact ⟨firstRun_of_localRun caller
      (root_left_pattern_localRun caller nilTree [15] [] (stale flag) ordinaryContext)
      (by simp [atResult, cfg, resultLabel, Owned]),
    firstRun_of_localRun caller
      (root_right_pattern_localRun caller nilTree [15] [] (stale flag) ordinaryContext)
      (by simp [atResult, cfg, resultLabel, Owned]), rfl, rfl⟩

theorem old_pending_changes_the_valid_tree_operation (caller : ExampleCaller) (flag : Bool) :
    FirstRun caller (cleanEntry .left flag [1,0,1,0,0] []) 7
      (atResult .success flag (data [1,1,0,0,0] [] [] [] [])) ∧
      FirstRun caller (atPhase (.seek .left) flag (data [1,0,1,0,0] [] [] [()] [])) 14
        (atResult .failure flag (data [1,0,1,0,0] [] [] [] [])) := by
  refine ⟨minimal_left_first_return caller flag, ?_⟩
  exact every_raw_fixture_is_an_actual_first_return caller flag
    ⟨.seek .left, data [1,0,1,0,0] [] [] [()] [], .failure,
      data [1,0,1,0,0] [] [] [] [], 14⟩ (by simp [rawFixtures])

section SharpMalformedFamilies

variable {K Λ R : Type} {Γ : K → Type} [DecidableEq K] [Fintype K]
variable (caller : External Λ → Statement Γ Λ R)
variable (regs : Registers R) (ctx : ∀ k, List (Γ k))

/-- All n, including zero, reach the literal size-maximizing drop state before failure. -/
theorem left_all_nodes_have_the_sharp_actual_clock_and_space (n : Nat) :
    FirstRun caller
      (cfg (some (phaseLabel (.seek .left))) regs (data (List.replicate n 1) [] [] [] []) ctx)
      (3 * n + 4)
      (cfg (some (resultLabel .failure)) (reset regs) (data (List.replicate n 1) [] [] [] []) ctx) ∧
      Runs caller
        (cfg (some (phaseLabel (.seek .left))) regs (data (List.replicate n 1) [] [] [] []) ctx)
        (2 * n + 2)
        (cfg (some (phaseLabel .dropPending)) (reset regs)
          (data (List.replicate n 1) [] [] (List.replicate n ()) []) ctx) ∧
      remainingSteps (cfg (some (phaseLabel .dropPending)) (reset regs)
        (data (List.replicate n 1) [] [] (List.replicate n ()) []) ctx : Cfg Γ Λ R) = n + 2 ∧
      stackCells (cfg (some (phaseLabel .dropPending)) (reset regs)
        (data (List.replicate n 1) [] [] (List.replicate n ()) []) ctx : Cfg Γ Λ R) =
          2 * n + contextCells ctx :=
  ⟨firstRun_of_localRun caller (left_nodes_run caller n regs ctx)
      (by simp [cfg, resultLabel, Owned]),
    LocalRun.iterate caller (left_nodes_drop caller n regs ctx),
    left_nodes_drop_rank caller n (reset regs) ctx,
    left_nodes_drop_cells n (reset regs) ctx⟩

theorem right_all_nodes_keep_the_one_cell_gap (m : Nat) :
    FirstRun caller
      (cfg (some (phaseLabel (.seek .right))) regs
        (data (List.replicate (m + 2) 1) [] [] [] []) ctx)
      (3 * m + 7)
      (cfg (some (resultLabel .failure)) (reset regs)
        (data (List.replicate (m + 2) 1) [] [] [] []) ctx) ∧
      Runs caller
        (cfg (some (phaseLabel (.seek .right))) regs
          (data (List.replicate (m + 2) 1) [] [] [] []) ctx)
        (2 * m + 4)
        (cfg (some (phaseLabel .dropPending)) (reset regs)
          (data (List.replicate (m + 2) 1) [] [] (List.replicate (m + 1) ()) []) ctx) ∧
      remainingSteps (cfg (some (phaseLabel .dropPending)) (reset regs)
        (data (List.replicate (m + 2) 1) [] [] (List.replicate (m + 1) ()) []) ctx : Cfg Γ Λ R) =
          m + 3 ∧
      stackCells (cfg (some (phaseLabel .dropPending)) (reset regs)
        (data (List.replicate (m + 2) 1) [] [] (List.replicate (m + 1) ()) []) ctx : Cfg Γ Λ R) =
          2 * m + 3 + contextCells ctx :=
  ⟨firstRun_of_localRun caller (right_nodes_run caller m regs ctx)
      (by simp [cfg, resultLabel, Owned]),
    LocalRun.iterate caller (right_nodes_drop caller m regs ctx),
    right_nodes_drop_rank caller m (reset regs) ctx,
    right_nodes_drop_cells m (reset regs) ctx⟩

omit [Fintype K] in
theorem right_empty_and_singleton_are_the_separate_four_step_routes :
    FirstRun caller
      (cfg (some (phaseLabel (.seek .right))) regs (data [] [] [] [] []) ctx) 4
      (cfg (some (resultLabel .failure)) (reset regs) (data [] [] [] [] []) ctx) ∧
      FirstRun caller
        (cfg (some (phaseLabel (.seek .right))) regs (data [1] [] [] [] []) ctx) 4
        (cfg (some (resultLabel .failure)) (reset regs) (data [1] [] [] [] []) ctx) :=
  ⟨firstRun_of_localRun caller (root_nonnode_localRun caller .right [] [] True.intro regs ctx)
      (by simp [cfg, resultLabel, Owned]),
    firstRun_of_localRun caller (root_right_second_nonnode_localRun caller [] [] True.intro regs ctx)
      (by simp [cfg, resultLabel, Owned])⟩

omit [Fintype K] in
theorem an_overlong_position_consumes_only_its_first_failing_head
    (d : RotationDirection) (n k : Nat) (positive : 0 < k) :
    FirstRun caller
      (cfg (some (phaseLabel (.seek d))) regs
        (data (List.replicate n 1) [] [] [] (List.replicate (n + k) .left)) ctx)
      (2 * n + 3)
      (cfg (some (resultLabel .failure)) (reset regs)
        (data (List.replicate n 1) [] [] [] (List.replicate (k - 1) .left)) ctx) :=
  firstRun_of_localRun caller (left_path_overrun caller d n k positive regs ctx)
    (by simp [cfg, resultLabel, Owned])

omit [Fintype K] in
theorem exhausting_the_position_before_eof_takes_the_distinct_root_route
    (d : RotationDirection) (n : Nat) :
    FirstRun caller
      (cfg (some (phaseLabel (.seek d))) regs
        (data (List.replicate n 1) [] [] [] (List.replicate n .left)) ctx)
      (2 * n + 4)
      (cfg (some (resultLabel .failure)) (reset regs) (data (List.replicate n 1) [] [] [] []) ctx) :=
  firstRun_of_localRun caller (left_path_exhausted caller d n regs ctx)
    (by simp [cfg, resultLabel, Owned])

def leftAllNodesInTime (n : Nat) :
    StateTransition.EvalsToInTime (step caller)
      (cfg (some (phaseLabel (.seek .left))) regs (data (List.replicate n 1) [] [] [] []) ctx)
      (some (cfg (some (resultLabel .failure)) (reset regs)
        (data (List.replicate n 1) [] [] [] []) ctx)) (3 * n + 4) :=
  localRunInTime caller (left_nodes_run caller n regs ctx)

def rightAllNodesInTime (m : Nat) :
    StateTransition.EvalsToInTime (step caller)
      (cfg (some (phaseLabel (.seek .right))) regs (data (List.replicate (m + 2) 1) [] [] [] []) ctx)
      (some (cfg (some (resultLabel .failure)) (reset regs)
        (data (List.replicate (m + 2) 1) [] [] [] []) ctx)) (3 * m + 7) :=
  localRunInTime caller (right_nodes_run caller m regs ctx)

def overlongPathInTime (d : RotationDirection) (n k : Nat) (positive : 0 < k) :
    StateTransition.EvalsToInTime (step caller)
      (cfg (some (phaseLabel (.seek d))) regs
        (data (List.replicate n 1) [] [] [] (List.replicate (n + k) .left)) ctx)
      (some (cfg (some (resultLabel .failure)) (reset regs)
        (data (List.replicate n 1) [] [] [] (List.replicate (k - 1) .left)) ctx)) (2 * n + 3) :=
  localRunInTime caller (left_path_overrun caller d n k positive regs ctx)

def exhaustedPathInTime (d : RotationDirection) (n : Nat) :
    StateTransition.EvalsToInTime (step caller)
      (cfg (some (phaseLabel (.seek d))) regs
        (data (List.replicate n 1) [] [] [] (List.replicate n .left)) ctx)
      (some (cfg (some (resultLabel .failure)) (reset regs)
        (data (List.replicate n 1) [] [] [] []) ctx)) (2 * n + 4) :=
  localRunInTime caller (left_path_exhausted caller d n regs ctx)

omit [Fintype K] in
theorem sharp_family_timing_retains_the_exact_machine_counts
    (d : RotationDirection) (n m k : Nat) (positive : 0 < k) :
    (leftAllNodesInTime caller regs ctx n).steps = 3 * n + 4 ∧
      (rightAllNodesInTime caller regs ctx m).steps = 3 * m + 7 ∧
      (overlongPathInTime caller regs ctx d n k positive).steps = 2 * n + 3 ∧
      (exhaustedPathInTime caller regs ctx d n).steps = 2 * n + 4 := ⟨rfl, rfl, rfl, rfl⟩

end SharpMalformedFamilies

section AllRawContracts

variable {K Λ R : Type} {Γ : K → Type} [DecidableEq K]
variable (caller : External Λ → Statement Γ Λ R)
variable (regs : Registers R) (ctx : ∀ k, List (Γ k))

theorem every_raw_word_has_a_clean_first_endpoint_with_its_actual_path_suffix
    (d : RotationDirection) (raw : Word) (path : List Branch) :
    ∃ r output rest,
      FirstRun caller (entry d regs raw path ctx) (runSteps d raw path)
        (cfg (some (resultLabel r)) (reset regs) (data output [] [] [] rest) ctx) ∧
      output.length = raw.length ∧ (∃ consumed, path = consumed ++ rest) ∧
      (r = .failure → output = raw) ∧ (r = .success → rest = []) := by
  obtain ⟨r, output, rest, segment, length, suffix, failure, success⟩ :=
    run_raw caller d raw path regs ctx
  exact ⟨r, output, rest, firstRun_of_localRun caller segment
    (by simp [cfg, resultLabel, Owned]), length, suffix, failure, success⟩

/-- Failure restores the original literal input at the unique first handoff. -/
theorem any_raw_first_failure_restores_every_original_source_cell
    (d : RotationDirection) (raw : Word) (path : List Branch)
    (n : Nat) (finish : Cfg Γ Λ R)
    (first : FirstRun caller (entry d regs raw path ctx) n finish)
    (failed : finish.l = some (resultLabel .failure)) :
    n = runSteps d raw path ∧ finish.stk (.inl .source) = raw ∧
      finish.stk (.inl .saved) = [] ∧ finish.stk (.inl .scratch) = [] ∧
      finish.stk (.inl .pending) = [] ∧
      (∃ consumed, path = consumed ++ finish.stk (.inl .path)) ∧
      finish.var = reset regs ∧ ∀ k, finish.stk (.inr k) = ctx k := by
  obtain ⟨count, same⟩ := firstRun_unique caller first
    (phase_first_return caller (.seek d) { source := raw, path := path } regs ctx)
  subst finish
  obtain ⟨saved, scratch, pending⟩ := run_raw_clean caller d raw path regs ctx
  exact ⟨count, run_raw_failure caller d raw path regs ctx failed,
    saved, scratch, pending, run_raw_path_suffix caller d raw path regs ctx,
    rfl, fun _ => rfl⟩

theorem any_raw_first_success_preserves_length_and_consumes_the_position
    (d : RotationDirection) (raw : Word) (path : List Branch)
    (n : Nat) (finish : Cfg Γ Λ R)
    (first : FirstRun caller (entry d regs raw path ctx) n finish)
    (succeeded : finish.l = some (resultLabel .success)) :
    n = runSteps d raw path ∧ (finish.stk (.inl .source)).length = raw.length ∧
      finish.stk (.inl .saved) = [] ∧ finish.stk (.inl .scratch) = [] ∧
      finish.stk (.inl .pending) = [] ∧ finish.stk (.inl .path) = [] ∧
      finish.var = reset regs ∧ ∀ k, finish.stk (.inr k) = ctx k := by
  obtain ⟨count, same⟩ := firstRun_unique caller first
    (phase_first_return caller (.seek d) { source := raw, path := path } regs ctx)
  subst finish
  obtain ⟨saved, scratch, pending⟩ := run_raw_clean caller d raw path regs ctx
  exact ⟨count, run_raw_length caller d raw path regs ctx,
    saved, scratch, pending, run_raw_success caller d raw path regs ctx succeeded,
    rfl, fun _ => rfl⟩

theorem every_actual_dirty_successor_has_the_natural_countdown_drop
    (q : Phase) (D : LocalData) :
    step caller (cfg (some (phaseLabel q)) regs D ctx) =
      some (cfg (some (controlLabel (advance q D).1)) (reset regs) (advance q D).2 ctx) ∧
      countdown (advance q D).1 (advance q D).2 + 1 ≤ countdown (.inl q) D :=
  ⟨advance_step caller q D regs ctx, advance_countdown q D⟩

theorem the_natural_countdown_is_distinct_from_the_exact_remaining_rank :
    step caller (cfg (some (phaseLabel (.start .left))) regs (data [] [] [] [] []) ctx) =
      some (cfg (some (phaseLabel .dropPending)) (reset regs) (data [] [] [] [] []) ctx) ∧
      countdown (.inl (.start .left)) (data [] [] [] [] []) = 4 ∧
      countdown (.inl .dropPending) (data [] [] [] [] []) = 2 ∧
      remainingSteps (cfg (some (phaseLabel (.start .left))) regs
        (data [] [] [] [] []) ctx : Cfg Γ Λ R) = 3 := by
  refine ⟨start_left_step_nil caller (data [] [] [] [] []) regs ctx, rfl, rfl, ?_⟩
  have segment := LocalRun.trans caller
    (phase_step_localRun caller (start_left_step_nil caller (data [] [] [] [] []) regs ctx))
    (dropPending_localRun caller (data [] [] [] [] []) (reset regs) ctx)
  simpa only [remainingSteps, cfg, phaseLabel, resultLabel, dataOfCfg,
    data, List.length_nil, Nat.add_zero] using LocalRun.remaining caller segment

end AllRawContracts

def genericBoundaryCfg {K Λ R : Type} {Γ : K → Type}
    (regs : Registers R) (ctx : ∀ k, List (Γ k)) (b : Boundary) : Cfg Γ Λ R :=
  cfg (some (controlLabel b.2.1)) (if b.1 = 0 then regs else reset regs) b.2.2.1 ctx

section GenericBoundaryContracts

variable {K Λ R : Type} {Γ : K → Type} [DecidableEq K] [Fintype K]
variable (caller : External Λ → Statement Γ Λ R)
variable (regs : Registers R) (ctx : ∀ k, List (Γ k))

/-- Every literal left boundary also holds for arbitrary stale fields and protected words. -/
theorem left_literal_boundaries_keep_arbitrary_registers_and_protected_data
    (b : Boundary) (member : b ∈ leftBoundaries) :
    Runs caller
      (cfg (some (phaseLabel (.seek .left))) regs (data [1,0,1,0,0] [] [] [] []) ctx)
      b.1 (genericBoundaryCfg regs ctx b) ∧
      stackCells (genericBoundaryCfg regs ctx b : Cfg Γ Λ R) = b.2.2.2 + contextCells ctx ∧
      (genericBoundaryCfg regs ctx b : Cfg Γ Λ R).var =
        (if b.1 = 0 then regs else reset regs) := by
  simp only [leftBoundaries, List.mem_cons, List.mem_nil_iff, or_false] at member
  rcases member with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  all_goals
    refine ⟨?_, ?_, rfl⟩
    · simp [Runs, genericBoundaryCfg, Function.iterate_succ_apply, next_some,
        advance_step, advance, controlLabel, nodeTag, emptyTag, data, reset_reset,
        markerWord, modeResult]
    · simp only [genericBoundaryCfg, stackCells_cfg]
      simp [localCells, data]

theorem right_literal_boundaries_keep_arbitrary_registers_and_protected_data
    (b : Boundary) (member : b ∈ rightBoundaries) :
    Runs caller
      (cfg (some (phaseLabel (.seek .right))) regs (data [1,1,0,0,0] [] [] [] []) ctx)
      b.1 (genericBoundaryCfg regs ctx b) ∧
      stackCells (genericBoundaryCfg regs ctx b : Cfg Γ Λ R) = b.2.2.2 + contextCells ctx ∧
      (genericBoundaryCfg regs ctx b : Cfg Γ Λ R).var =
        (if b.1 = 0 then regs else reset regs) := by
  simp only [rightBoundaries, List.mem_cons, List.mem_nil_iff, or_false] at member
  rcases member with rfl | rfl | rfl | rfl | rfl | rfl | rfl
  all_goals
    refine ⟨?_, ?_, rfl⟩
    · simp [Runs, genericBoundaryCfg, Function.iterate_succ_apply, next_some,
        advance_step, advance, controlLabel, nodeTag, emptyTag, data, reset_reset,
        markerWord, modeResult]
    · simp only [genericBoundaryCfg, stackCells_cfg]
      simp [localCells, data]

end GenericBoundaryContracts

theorem actual_source_success_is_decided_at_the_stopped_cursor
    (d : RotationDirection) (p : List Branch) (s : BinaryTree Unit) :
    (applyMoveRun ⟨d,p⟩ s).1.isSome =
      (if stoppedPath p s = [] then (rotateRun d (stoppedTree p s)).1.isSome else false) := by
  induction p generalizing s with
  | nil => simp only [source_root, stoppedPath, stoppedTree, ite_true]
  | cons b p ih =>
      cases s with
      | nil => simp only [source_nil_cons, stoppedPath, List.cons_ne_nil, ite_false, Option.isSome_none]
      | node a l r =>
          cases a
          cases b with
          | left =>
              have child := ih l
              cases actual : (applyMoveRun ⟨d,p⟩ l).1 <;>
                by_cases ended : stoppedPath p l = [] <;>
                simpa [source_left, actual, stoppedPath, stoppedTree, ended] using child
          | right =>
              have child := ih r
              cases actual : (applyMoveRun ⟨d,p⟩ r).1 <;>
                by_cases ended : stoppedPath p r = [] <;>
                simpa [source_right, actual, stoppedPath, stoppedTree, ended] using child

theorem cursor_left_success_has_the_fixed_source_machine_pair
    (p : List Branch) (s A B C : BinaryTree Unit)
    (ended : stoppedPath p s = [])
    (focus : stoppedTree p s = .node () A (.node () B C)) :
    ((applyMoveRun ⟨.left,p⟩ s).2, representedClock .left p s) =
      (3 * descentCount p s + 5, 2 * navigationLength p s + 2 * (treeCode A).length + 5) := by
  rw [source_cost_eq_stopped, representedClock_eq_stopped]
  simp [actual_source_success_is_decided_at_the_stopped_cursor, ended, focus,
    representedClock, Nat.add_assoc]

theorem cursor_right_success_has_the_fixed_source_machine_pair
    (p : List Branch) (s A B C : BinaryTree Unit)
    (ended : stoppedPath p s = [])
    (focus : stoppedTree p s = .node () (.node () A B) C) :
    ((applyMoveRun ⟨.right,p⟩ s).2, representedClock .right p s) =
      (3 * descentCount p s + 5, 2 * navigationLength p s + 2 * (treeCode A).length + 4) := by
  rw [source_cost_eq_stopped, representedClock_eq_stopped]
  simp [actual_source_success_is_decided_at_the_stopped_cursor, ended, focus,
    representedClock, Nat.add_assoc]

theorem cursor_missing_nil_has_the_fixed_source_machine_pair
    (d : RotationDirection) (p : List Branch) (s : BinaryTree Unit)
    (missing : stoppedPath p s ≠ []) :
    ((applyMoveRun ⟨d,p⟩ s).2, representedClock d p s) =
      (2 * descentCount p s + 2, 2 * navigationLength p s + 3) := by
  rw [source_cost_eq_stopped, representedClock_eq_stopped]
  simp [actual_source_success_is_decided_at_the_stopped_cursor, missing]

theorem cursor_exhausted_nil_has_the_fixed_source_machine_pair
    (d : RotationDirection) (p : List Branch) (s : BinaryTree Unit)
    (ended : stoppedPath p s = []) (focus : stoppedTree p s = .nil) :
    ((applyMoveRun ⟨d,p⟩ s).2, representedClock d p s) =
      (2 * descentCount p s + 3, 2 * navigationLength p s + 4) := by
  rw [source_cost_eq_stopped, representedClock_eq_stopped]
  simp [actual_source_success_is_decided_at_the_stopped_cursor, ended, focus, representedClock]

theorem cursor_right_nil_child_has_the_fixed_source_machine_pair
    (p : List Branch) (s C : BinaryTree Unit)
    (ended : stoppedPath p s = []) (focus : stoppedTree p s = .node () .nil C) :
    ((applyMoveRun ⟨.right,p⟩ s).2, representedClock .right p s) =
      (2 * descentCount p s + 3, 2 * navigationLength p s + 4) := by
  rw [source_cost_eq_stopped, representedClock_eq_stopped]
  simp [actual_source_success_is_decided_at_the_stopped_cursor, ended, focus,
    representedClock, rotateRun]

theorem cursor_left_nil_child_has_the_fixed_source_machine_pair
    (p : List Branch) (s A : BinaryTree Unit)
    (ended : stoppedPath p s = []) (focus : stoppedTree p s = .node () A .nil) :
    ((applyMoveRun ⟨.left,p⟩ s).2, representedClock .left p s) =
      (2 * descentCount p s + 3, 2 * navigationLength p s + 2 * (treeCode A).length + 6) := by
  rw [source_cost_eq_stopped, representedClock_eq_stopped]
  simp [actual_source_success_is_decided_at_the_stopped_cursor, ended, focus,
    representedClock, rotateRun, Nat.add_assoc]

section ActualCursorPrefix

variable {K Λ R : Type} {Γ : K → Type} [DecidableEq K]
variable (caller : External Λ → Statement Γ Λ R)
variable (regs : Registers R) (ctx : ∀ k, List (Γ k))

theorem represented_cursor_is_reached_before_its_final_path_observation
    (d : RotationDirection) (p : List Branch) (s : BinaryTree Unit) (F z : Word) :
    Runs caller
      (cfg (some (phaseLabel (.seek d))) regs (data (treeCode s ++ z) F [] [] p) ctx)
      (navigationLength p s)
      (cfg (some (phaseLabel (.seek d)))
        (if navigationLength p s = 0 then regs else reset regs)
        (data (treeCode (stoppedTree p s) ++ contextSuffix (navigationFrames p s) ++ z)
          ((contextPrefix (navigationFrames p s)).reverse ++ F) [] [] (stoppedPath p s)) ctx) := by
  simpa only [Runs, data, afterScanRegisters, navigationLength_eq_prefix,
    List.length_eq_zero_iff] using
    seek_cursor_iterate caller d p s F z regs ctx

def representedCursorInTime (d : RotationDirection) (p : List Branch)
    (s : BinaryTree Unit) (F z : Word) :
    StateTransition.EvalsToInTime (step caller)
      (cfg (some (phaseLabel (.seek d))) regs (data (treeCode s ++ z) F [] [] p) ctx)
      (some (cfg (some (phaseLabel (.seek d)))
        (if navigationLength p s = 0 then regs else reset regs)
        (data (treeCode (stoppedTree p s) ++ contextSuffix (navigationFrames p s) ++ z)
          ((contextPrefix (navigationFrames p s)).reverse ++ F) [] [] (stoppedPath p s)) ctx))
      (navigationLength p s) where
  steps := navigationLength p s
  evals_in_steps := represented_cursor_is_reached_before_its_final_path_observation
    caller regs ctx d p s F z
  steps_le_m := Nat.le_refl _

end ActualCursorPrefix

end Examples.RotationCertificatePositionedRotationMachine
