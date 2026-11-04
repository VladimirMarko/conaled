import SquareKit.Internal.NestedSetting

/-! The frozen #319 client: a nonconstant internal presentation, then a second
presentation depending on the first generic summand. The values and failed
comparison below retain data; none is merely an inhabitation statement. -/
namespace Examples.NestedSetting
open SquareKit.Internal.FiniteSetting
open SquareKit.Internal.NestedSetting
open CategoryTheory Limits

/-- Internal parameter in Set/Nat, supplied to the finite geometric scheme. -/
def first : Presentation Nat := ⟨fun n => 0 < n⟩

/-- The second parameter reads the first generic model, not just its base. -/
def second : Presentation (Total first) := ⟨fun a => a.2.isLeft = true⟩

def firstChoice : Section first
  | 0 => .inr ()
  | n+1 => .inl ⟨Nat.zero_lt_succ n⟩

def secondChoice : Section (second.subst firstChoice.graph)
  | 0 => .inr ()
  | _+1 => .inl ⟨rfl⟩

def selected : Argument first second := ⟨firstChoice, secondChoice⟩

def tags (a : Nested first second) : Bool × Bool := (a.1.2.isLeft, a.2.isLeft)

/-- This fiber varies with the second selected generic value as well as n. -/
def payload (a : Nested first second) : Type :=
  Fin (if a.2.isLeft then a.1.1 + 2 else 1)

def payloadChoice (a : Nested first second) : payload a := by
  unfold payload
  split
  · exact ⟨a.1.1 + 1, Nat.lt_succ_self _⟩
  · exact ⟨0, Nat.zero_lt_succ 0⟩

def shift (n : Nat) := n + 1
def double (n : Nat) := 2 * n

/-- Base-zero forces right, while a successor admits the selected left. -/
theorem expected_zero : tags (classify selected 0) = (false,false) := rfl

theorem expected_successor (n : Nat) : tags (classify selected (n+1)) = (true,true) := rfl

/-- P is nonconstant: zero does not admit the first left alternative. -/
theorem no_first_left_zero (a : Fiber first 0) : a.isLeft = false := by
  cases a with
  | inl h => exact False.elim (Nat.not_lt_zero 0 h.down)
  | inr _ => rfl

/-- At the same positive base, the first choice changes the second parameter. -/
theorem second_really_depends :
    second.parameter ⟨1, .inl ⟨Nat.zero_lt_succ 0⟩⟩ ∧
      ¬ second.parameter ⟨1, .inr ()⟩ := by
  exact ⟨rfl, Bool.false_ne_true⟩

/-- The pair classifies two actual models of the existing geometric axioms. -/
example : Model first := selected.1.toModel
example : Model (second.subst selected.1.graph) := selected.2.toModel

example : (genericModel first).subst (fun n => (classify selected n).1) =
    selected.1.toModel := first_generic_recovery selected

example : (genericModel second).subst (classify selected) = selected.2.toModel :=
  second_generic_recovery selected

/-- A categorical setting really is constructed from each internal presentation. -/
example : Over (formedDisplay first) ≌ Setting first := settingEquivalence first
example : Over (formedDisplay second) ≌ Setting second :=
  secondSettingEquivalence first second

/-- The second classifier object has the same independently proved universal
coproduct property, now in the first generic context. -/
noncomputable example : formedDisplay second ≅
    parameterDisplay second ⨿ ⊤_ (Over (Total first)) := formedClassifierIso second

/-- Reuse the nested universal property, including uniqueness, at the client. -/
example : (argumentEquiv first second).symm
    ⟨classify selected, classify_base selected⟩ = selected := recover_classify selected

def substituted : Argument ((first.subst shift).subst double)
    (reindex (first.subst shift) (reindex first second shift) double) :=
  argumentSub (argumentSub selected shift) double

theorem selected_twice : substituted = argumentSub selected (shift ∘ double) :=
  argumentSub_comp selected shift double

/-- This checks the actual composite order: the original index is 2*n+1. -/
theorem original_index (n : Nat) :
    base first second (map first second (shift ∘ double) (classify substituted n)) =
      2*n+1 := rfl

/-- The public comparison reconstructs both selected summands. -/
theorem whole_selected (n : Nat) :
    comparison first second (shift ∘ double)
      ⟨n,classify selected (2*n+1),rfl⟩ = classify substituted n := by
  rw [selected_twice]
  exact selected_comparison selected (shift ∘ double) n

/-- The nested generic interpretation is universal after the same two
substitutions, not only before substitution. -/
example : (argumentOverEquiv first second (shift ∘ double)).symm
    ((argumentOverEquiv first second (shift ∘ double)) substituted) = substituted :=
  (argumentOverEquiv first second (shift ∘ double)).symm_apply_apply substituted

/-- This is a genuine pullback of nested settings' base displays. -/
example : IsPullback (↾(map first second (shift ∘ double)))
    (↾(base (first.subst (shift ∘ double)) (reindex first second (shift ∘ double))))
    (↾(base first second)) (↾(shift ∘ double)) :=
  SquareKit.Internal.NestedSetting.formed_isPullback first second (shift ∘ double)

/-- Arbitrary dependent type compatibility specializes to a nonconstant finite
payload fiber. -/
example (a : SquareKit.Internal.NestedSetting.Pullback first second shift) :
    typeSub payload shift (comparison first second shift a) = payload a.original :=
  type_comparison payload shift a

example (a : SquareKit.Internal.NestedSetting.Pullback first second shift) :
    cast (type_comparison payload shift a)
      (termSub payloadChoice shift (comparison first second shift a)) =
      payloadChoice a.original := term_comparison payloadChoice shift a

/-- Value 6 was fixed by the independent calculation: 2*2+1=5, then choose n+1.
The proof first uses the general dependent term substitution theorem. -/
theorem payload_after_two :
    (termSub (termSub payloadChoice shift) double (classify substituted 2)).val = 6 := by
  rw [termSub_comp]
  rfl

theorem order_detected :
    (termSub (termSub payloadChoice shift) double (classify substituted 0)).val = 2 ∧
      (termSub (termSub payloadChoice double) shift
        (classify (argumentSub (argumentSub selected double) shift) 0)).val = 3 := by
  rw [termSub_comp, termSub_comp]
  exact ⟨rfl,rfl⟩

def secondStagePoint : SquareKit.Internal.NestedSetting.Pullback
    (first.subst shift) (reindex first second shift) double :=
  ⟨2, classify (argumentSub selected shift) 4, rfl⟩

/-- Exercise the complete dependent comparison, including the selected payload,
through the public composition theorem rather than a separate arithmetic proof. -/
theorem payload_whole_twice :
    (⟨map first second (shift ∘ double)
      (comparison first second (shift ∘ double)
        (rebase first second shift double secondStagePoint)),
      termSub (termSub payloadChoice shift) double
        (comparison first second (shift ∘ double)
          (rebase first second shift double secondStagePoint))⟩ :
            (z : Nested first second) × payload z) =
      ⟨classify selected 5, (⟨6, Nat.lt_succ_self 6⟩ : Fin 7)⟩ := by
  rw [dependent_comparison_comp]
  rfl

/-- A second left branch cannot exist over a first right branch. -/
theorem no_second_left (n : Nat) (b : Fiber second ⟨n,.inr ()⟩) : b.isLeft = false := by
  cases b with
  | inl h => exact False.elim (Bool.false_ne_true h.down)
  | inr _ => rfl

/-- A deliberately lossy map is still a well-typed map over the base. -/
def erase (a : Nested first second) : Nested first second :=
  ⟨⟨a.1.1,.inr ()⟩,.inr ()⟩

theorem erase_over (a : Nested first second) :
    base first second (erase a) = base first second a := rfl

/-- It cannot fulfill the promised observation contract. -/
theorem erase_fails : tags (erase (classify selected 1)) ≠ tags (classify selected 1) := by
  decide

/-- No candidate retaining the erased first choice can retain second-left. -/
theorem cannot_repair_second (n : Nat) (b : Fiber second ⟨n,.inr ()⟩) :
    b.isLeft ≠ (classify selected 1).2.isLeft := by
  rw [no_second_left]
  exact Bool.false_ne_true

end Examples.NestedSetting
