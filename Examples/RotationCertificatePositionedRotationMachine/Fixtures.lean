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
    Nonempty (Fintype (Alphabet ProtectedAlphabet k)) := ⟨inferInstance⟩

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


end Examples.RotationCertificatePositionedRotationMachine
