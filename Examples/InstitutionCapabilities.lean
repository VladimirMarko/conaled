import SquareKit.Institutions.LinearCartesian
import SquareKit.Institutions.IndexedClients
import Examples.CompositionalSpecifications
import Examples.ExactParserRewrites

namespace Examples.InstitutionCapabilities
open SquareKit.Institutions
set_option backward.isDefEq.respectTransparency false

abbrev input : Linear.Formula Bool := .tensor (.atom false) (.atom true)
abbrev output : Linear.Formula Bool := .tensor (.atom true) (.atom false)

def swap : Linear.Proof (.tensor (.atom false) (.atom true)) (.tensor (.atom true) (.atom false)) := .swap

def tagged : Bool × Unit → Type := fun a => if a.1 then Fin 3 else Fin 2

def first : Compatible (linearConnection Bool) (linearProofs Bool) (cartesianProofs Bool)
    (linearProofs Bool).realization (cartesianProofs Bool).realization :=
  ⟨linearProofMap Bool, (linearProofMap Bool).realization⟩
def second : Compatible (renameConnection (fun b : Bool => (b, ())))
    (cartesianProofs Bool) (cartesianProofs (Bool × Unit))
    (cartesianProofs Bool).realization (cartesianProofs (Bool × Unit)).realization :=
  ⟨renameProofMap _, (renameProofMap _).realization⟩

theorem selected_swap :
    ((second.comp first).realization.map tagged (input,output) swap).denote tagged ((1 : Fin 2),(2 : Fin 3)) = ((2 : Fin 3),(1 : Fin 2)) := by
  have h := (second.comp first).realization.commutes tagged (input,output) swap
  exact congrFun h ((1 : Fin 2),(2 : Fin 3))

example : ((second.comp first).proof.map (input,input) (.comp .swap swap)).denote tagged ((1 : Fin 2),(2 : Fin 3)) = ((1 : Fin 2),(2 : Fin 3)) := by
  have h := (second.comp first).proof.commutes tagged (input,input) (.comp .swap swap)
  exact congrFun h ((1 : Fin 2),(2 : Fin 3))

/-- Cartesian contraction is admitted and evaluated independently. -/
def contraction : Cartesian.Proof (.atom () : Cartesian.Formula Unit) (.product (.atom ()) (.atom ())) :=
  .pair .id .id
example : contraction.denote (fun _ => Nat) (7 : Nat) = ((7 : Nat),(7 : Nat)) := rfl
example : ¬ Nonempty (Linear.Proof (.atom () : Linear.Formula Unit) (.tensor (.atom ()) (.atom ()))) :=
  Linear.no_contraction

/-- Two valid ordinary squares have different bottom arrows. The additional
compatibility required by ofSquares rejects the attempted combination. -/
def boolSetting : Setting.{0,0,0} := ⟨Unit, Unit, fun _ _ => Bool⟩
def boolRealization : Realization boolSetting := ⟨fun _ _ => Bool, fun _ _ => id⟩
def flipConnection : Connection boolSetting boolSetting := ⟨id,id,fun _ _ => Bool.not⟩
def identitySquare : Squares.Square ⟨Bool,Bool,id⟩ ⟨Bool,Bool,id⟩ := Squares.identity _
def flipSquare : Squares.Square ⟨Bool,Bool,id⟩ ⟨Bool,Bool,id⟩ := ⟨Bool.not,Bool.not,fun _ => rfl⟩
theorem incompatible_meanings : ¬ (∀ b, identitySquare.spec b = flipConnection.evidence () () b) := by
  intro h
  have bad := h false
  cases bad
example : ¬ Nonempty {c : RealizationMap flipConnection boolRealization boolRealization // c.map () () = id} := by
  rintro ⟨c,h⟩
  have bad := c.commutes () () false
  rw [h] at bad
  cases bad

/-- The proposition-only common specialization loses the selected bit even
though both evidence connections preserve satisfaction. -/
def identityConnection : Connection boolSetting boolSetting := Connection.identity _
example : identityConnection.satisfactionSquare () = flipConnection.satisfactionSquare () := rfl
example : identityConnection.evidence () () false ≠ flipConnection.evidence () () false := by intro h; cases h

/-- A genuinely many-valued relation: both endpoint values are admitted. -/
def enclosure : RelRealization boolSetting := ⟨fun _ _ => Unit, fun _ _ _ _ => True⟩
def flipEnclosure : RelRealizationMap flipConnection enclosure enclosure :=
  ⟨fun _ _ => id, fun _ _ _ _ _ => True.intro⟩
example : (flipEnclosure.comp flipEnclosure).map () () () = () := rfl

open LanguageWitnesses
open SquareKit.IndexedCompositional
open LanguageWitnesses.IndexedCompositional

def exchange {A : Type} : Iso (A ⊕ A) (A ⊕ A) where
  forward := Sum.swap
  backward := Sum.swap
  backward_forward x := by cases x <;> rfl
  forward_backward x := by cases x <;> rfl

abbrev ambiguous : LanguageWitnesses.Language Unit := fun w => epsilon w ⊕ epsilon w
def ambiguousParser : Parser ambiguous := .union .epsilon .epsilon

theorem selected_ambiguous :
    (Parser.transport (fun _ => exchange) (.transport (fun _ => exchange) ambiguousParser)).parse [] =
      .yes (.inl ⟨rfl⟩) := by
  rw [parser_pasting]
  rfl

theorem selected_refutation :
    (Parser.transport (fun _ => exchange) (.transport (fun _ => exchange) ambiguousParser)).parse [()] =
      (ambiguousParser.parse [()]).map (exchange.trans exchange) :=
  parser_pasting _ _ _ _

example : (Parser.transport (fun _ => exchange) (.transport (fun _ => exchange) ambiguousParser)).parse [()] =
    .no (fun x => by cases x with | inl p => cases p.proof | inr p => cases p.proof) := by
  rw [selected_refutation]
  rfl

def context : Term signature Source (ambiguous,1) :=
  .node (.union epsilon epsilon 1) (fun i => Fin.cases (.leaf .epsilon) (fun _ => .leaf .epsilon) i)

example : (Parser.transport (fun _ => exchange) (.transport (fun _ => exchange)
    (Term.fold sourceAlgebra (fun _ p => p) context))).parse [] =
    ((Term.fold targetAlgebra unfold context).lookup [] (by decide)).map (exchange.trans exchange) :=
  parser_context _ _ context [] (by decide)

/-- The pre-existing general context fusion still includes star, concatenation
and depth restriction; wrapping it does not narrow the constructor language. -/
example : (Term.fold sourceAlgebra (fun _ p => p)
    (ExactParserRewrites.surrounding.bind TransportPair.expanded)).parse [()] =
    (Term.fold sourceAlgebra (fun _ p => p)
      (ExactParserRewrites.surrounding.bind TransportPair.fused)).parse [()] :=
  contextual_transport_trans _ _ (by decide)

namespace Dependent
open Examples.CompositionalSpecifications

def family : M.extend (M.extend Unit A) B → Type := fun p => Fin (p.1.2 + 1)
def s : ∀ x, family x := fun x => branch.down x

theorem capability_twice :
    ((reindexConnection (family ∘ selected.down) double.down).comp
      (reindexConnection family selected.down)).section s 3 = (⟨6, by omega⟩ : Fin 8) := by
  rw [section_reindex_twice]
  rfl

/-- The decoded transported derivation agrees with the capability's selected
section, using the original local-rule proof transport rather than assuming
that the requested section exists. -/
theorem decoded_capability :
    Option.map (fun t : M.Section Nat (M.subTy (M.subTy C (S.pack A B)) selected) =>
      (M.subTm t double).down 3)
      (SquareKit.Internal.DependentJudgments.Value.termAt Nat
        (M.subTy (M.subTy C (S.pack A B)) selected)
        (expression.eval staged.toAlgebra valuation)) =
    some (((reindexConnection (family ∘ selected.down) double.down).comp
      (reindexConnection family selected.down)).section s 3) := by
  rw [capability_twice]
  exact decoded_twice
end Dependent
end Examples.InstitutionCapabilities
