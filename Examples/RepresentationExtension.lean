import SquareKit.RepresentationExtension.Logic
import SquareKit.RepresentationExtension.Descent
import Examples.ExactParserRewrites

/-! Independent old, extended, and failure cases for the frozen #287 fixture. -/
namespace Examples.RepresentationExtension
open SquareKit.RepresentationExtension

/-- The frozen symmetry and empty-predicate control is an admitted old model. -/
def twoPoint (P : Bool → Prop := fun _ => False) : Model where
  A := Bool
  B := Unit
  inhabitedA := ⟨false⟩
  inhabitedB := ⟨()⟩
  relation := ⟨fun _ _ => True, ⟨fun _ => trivial, fun _ => trivial, fun _ _ => trivial⟩⟩
  predicate := P

def swap : Hom twoPoint twoPoint where
  onA := Bool.not
  onB := id
  relation _ := trivial
  predicate h := h

/-- The quotient action of an admitted symmetry forgets the representative. -/
theorem swap_quotient_identity (z : (expand twoPoint).quotient.Q) :
    (liftHom (expand twoPoint) (expand twoPoint) swap).quotient.toFun z = z := by
  induction z using Quotient.inductionOn with | _ a =>
    exact ((liftHom (expand twoPoint) (expand twoPoint) swap).quotient.q_comm a).trans
      (Quotient.sound trivial)

/-- No selector can commute with this one admitted automorphism. -/
theorem no_equivariant_selector :
    ¬ ∃ s : (expand twoPoint).quotient.Q → Bool,
      ∀ z, swap.onA (s z) =
        s ((liftHom (expand twoPoint) (expand twoPoint) swap).quotient.toFun z) := by
  rintro ⟨s,hs⟩
  have h := hs ((expand twoPoint).quotient.q false)
  rw [swap_quotient_identity] at h
  cases he : s ((expand twoPoint).quotient.q false) <;> simp [swap,he] at h

/-- A finite noncanonical section still exists. -/
theorem noncanonical_section :
    ∃ s : (expand twoPoint).quotient.Q → Bool,
      ∀ z, (expand twoPoint).quotient.q (s z) = z := by
  refine ⟨fun _ => false, ?_⟩
  intro z
  induction z using Quotient.inductionOn with | _ a => exact Quotient.sound trivial

structure BadExtension (M : Model) where
  c : M.A
  selected : M.predicate c

theorem empty_predicate_no_expansion : ¬ Nonempty (BadExtension twoPoint) := by
  rintro ⟨N⟩
  exact N.selected

def selected_success : BadExtension (twoPoint (fun a => a = false)) := ⟨false,rfl⟩

/-- A forward homomorphism may destroy an old negated observation. -/
def predicateEnlargement : Hom twoPoint (twoPoint (fun _ => True)) :=
  ⟨id,id,fun _ => trivial,fun h => h.elim⟩

open FirstOrder.Language

def pAt : Logic.language.Formula Unit := .rel Logic.Relation.predicate (fun _ => .var (.inl ()))

theorem forward_not_preserved :
    Logic.Realize twoPoint pAt.not (fun _ => .inl false) ∧
    ¬ Logic.Realize (twoPoint (fun _ => True)) pAt.not
      (fun _ => .inl (predicateEnlargement.onA false)) := by
  exact ⟨fun h => h, fun h => h trivial⟩

def existsP : Logic.language.Sentence :=
  (BoundedFormula.rel Logic.Relation.predicate (fun _ => .var (.inr 0))).ex

theorem bad_implies_existsP {M : Model} (N : BadExtension M) :
    Logic.Realize M existsP (fun e => nomatch e) := by
  change FirstOrder.Language.Formula.Realize existsP _
  rw [FirstOrder.Language.Formula.Realize, existsP, BoundedFormula.realize_ex]
  exact ⟨.inl N.c, N.selected⟩

theorem existsP_not_old_consequence : ¬ Logic.Consequence.{0} (∅ : Set Logic.language.Sentence) existsP := by
  intro h
  have he := h twoPoint (fun e => nomatch e) (fun _ h => h.elim)
  change FirstOrder.Language.Formula.Realize existsP _ at he
  rw [FirstOrder.Language.Formula.Realize, existsP, FirstOrder.Language.BoundedFormula.realize_ex] at he
  obtain ⟨a,ha⟩ := he
  cases a <;> exact ha

theorem existsP_not_extended_consequence :
    ¬ Logic.ExtendedConsequence.{0} (∅ : Set Logic.language.Sentence) existsP :=
  fun h => existsP_not_old_consequence ((Logic.consequence_iff _ _).mp h)

/-- Both quantifier adapters are exercised in a sentence with nested old sorts. -/
def bothSorts : Logic.language.Sentence := Logic.allA (Logic.allB
  (.equal (.var (.inr 0)) (.var (.inr 0))))

theorem bothSorts_valid (M : Model) : Logic.Realize M bothSorts (fun e => nomatch e) := by
  change (Logic.allA _).Realize _ _
  apply (Logic.realize_allA M _ _ _).mpr
  intro a
  apply (Logic.realize_allB M _ _ _).mpr
  intro b
  rfl

example (M : Model) : Logic.ExtendedRealize (expand M) bothSorts (fun e => nomatch e) :=
  (Logic.realize_expand M _ _).mpr (bothSorts_valid M)

/-- A noncanonical presentation exercises comparison beyond the canonical pair. -/
def alternate : ExtendedModel where
  reduct :=
    { reduct := twoPoint
      product :=
        { C := Unit × Bool
          fst := Prod.snd
          snd := Prod.fst
          pair_unique a b := ⟨(b,a), ⟨rfl,rfl⟩,
            fun _ h => Prod.ext h.2 h.1⟩ } }
  quotient :=
    { Q := Unit
      q := fun _ => ()
      kernel _ _ := ⟨fun _ => trivial, fun _ => rfl⟩
      surjective := fun _ => ⟨false, Subsingleton.elim _ _⟩ }

theorem alternate_product : (comparison alternate).product.toFun ((),true) = (true,()) :=
  ProductSort.comparison_natural (Hom.id _) _ _ (comparison alternate).product ((),true)

theorem alternate_quotient : (comparison alternate).quotient.toFun () =
    (expand twoPoint).quotient.q true :=
  (comparison alternate).quotient.q_comm true

example : (comparisonInverse alternate).comp (comparison alternate) = ExtendedHom.id alternate :=
  comparison_inverse_left alternate

/-- Infinite carriers are admitted; the composite adds one and then doubles. -/
abbrev naturals : Model where
  A := Nat
  B := Nat
  inhabitedA := ⟨0⟩
  inhabitedB := ⟨0⟩
  relation := ⟨Eq, ⟨Eq.refl,Eq.symm,Eq.trans⟩⟩
  predicate := fun _ => True

def increment : Hom naturals naturals :=
  ⟨fun n => n+1, id, fun h => congrArg (fun n => n+1) h, fun _ => trivial⟩
def double : Hom naturals naturals :=
  ⟨fun n => n*2, fun n => n+1, fun h => congrArg (fun n => n*2) h, fun _ => trivial⟩

theorem composite_quotient :
    ((liftHom (expand naturals) (expand naturals) double).comp
      (liftHom (expand naturals) (expand naturals) increment)).quotient.toFun
        ((expand naturals).quotient.q (3 : Nat)) = (expand naturals).quotient.q (8 : Nat) := by
  exact ((liftHom (expand naturals) (expand naturals) double).comp
    (liftHom (expand naturals) (expand naturals) increment)).quotient.q_comm (3 : Nat)

theorem composite_product :
    ((liftHom (expand naturals) (expand naturals) double).comp
      (liftHom (expand naturals) (expand naturals) increment)).product.toFun (3,5) = (8,6) := by
  exact ProductSort.comparison_natural (double.comp increment) _ _
    ((liftHom (expand naturals) (expand naturals) double).comp
      (liftHom (expand naturals) (expand naturals) increment)).product (3,5)

namespace Dependent
/-- Class {0,1} has two witness indices; class {2} has only index 0. -/
def relation : Setoid (Fin 3) where
  r a b := (a.val = 2 ↔ b.val = 2)
  iseqv := ⟨fun _ => Iff.rfl, Iff.symm, Iff.trans⟩

def Fiber (a : Fin 3) := {i : Fin 2 // a.val = 2 → i.val = 0}

def data : DescentData relation Fiber where
  transport h :=
    { toFun := fun e => ⟨e.val,fun hb => e.property (h.mpr hb)⟩
      invFun := fun e => ⟨e.val,fun ha => e.property (h.mp ha)⟩
      left_inv := fun _ => rfl
      right_inv := fun _ => rfl }
  identity _ _ := rfl
  composition _ _ _ := rfl

def zeroSection (a : Fin 3) : Fiber a := ⟨0,fun _ => rfl⟩

theorem zero_equivariant : data.Equivariant zeroSection := fun _ => rfl

theorem zero_recovered (a : Fin 3) :
    ((data.fiberEquiv a).symm (data.descend zeroSection zero_equivariant
      (Quotient.mk relation a))).val = 0 := by
  rw [data.recover]
  rfl

/-- The two-element fiber is inhabited by genuinely distinct retained values. -/
theorem two_values : (⟨0,by decide⟩ : Fiber 0) ≠ ⟨1,by decide⟩ := by
  intro h
  have := congrArg (fun x : Fiber 0 => x.val.val) h
  contradiction

/-- The singleton fiber forbids index 1, so this is not a constant family. -/
theorem singleton_fiber (e : Fiber 2) : e = zeroSection 2 := by
  apply Subtype.ext
  apply Fin.ext
  exact e.property rfl

def constantData : DescentData twoPoint.relation (fun _ => Bool) where
  transport _ := Equiv.refl _
  identity _ _ := rfl
  composition _ _ _ := rfl

theorem representative_sensitive_fails : ¬ constantData.Equivariant (fun a => a) := by
  intro h
  have bad := h (a := false) (b := true) trivial
  cases bad

theorem no_selected_descent :
    ¬ ∃ s : ∀ z, constantData.Fiber z, ∀ a,
      (s (Quotient.mk twoPoint.relation a)).val =
        (constantData.fiberEquiv a a).val :=
  fun h => representative_sensitive_fails ((constantData.section_descends_iff _).mp h)
end Dependent

namespace Parsing
open LanguageWitnesses
open Examples.ObservationExtension.Parsing

/-- The native exact decision family, with its word and depth unchanged. -/
def exact (n : Nat) : Setoid (Parser P) :=
  SquareKit.ObservationExtension.agreement
    (fun w (p : Parser P) => p.parse w) {w | w.length ≤ n}

def model (n : Nat) : Model where
  A := Parser P
  B := PUnit
  inhabitedA := ⟨left⟩
  inhabitedB := ⟨⟨⟩⟩
  relation := exact n
  predicate := fun _ => True

/-- This also works for a noncanonical quotient presentation satisfying the axioms. -/
noncomputable def parse (n : Nat) (S : QuotientSort (model n))
    (w : List Char) (hw : w.length ≤ n) : S.Q → Decision (P w) :=
  S.observe (fun p => p.parse w) (fun {_ _} h => h w hw)

theorem recovered (n : Nat) (S : QuotientSort (model n)) (p : Parser P)
    (w : List Char) (hw : w.length ≤ n) : parse n S w hw (S.q p) = p.parse w :=
  S.observe_q _ _ p

/-- The existing independently specified trie lookup agrees with quotient recovery. -/
theorem recovered_trie (n : Nat) (p : Parser P) (w : List Char) (hw : w.length ≤ n) :
    parse n (expand (model n)).quotient w hw ((expand (model n)).quotient.q p) =
      (WitnessTrie.unfold p n).lookup w hw := by
  exact (recovered n _ p w hw).trans (WitnessTrie.lookup_unfold p n w hw).symm

/-- Direct parameterized quotient elimination and the certificate agree exactly. -/
theorem direct_agrees (n : Nat) (w : List Char) (hw : w.length ≤ n)
    (z : Quotient (exact n)) :
    SquareKit.ObservationExtension.descend (exact n) (fun p => p.parse w)
      (fun {_ _} h => h w hw) z = parse n (expand (model n)).quotient w hw z := by
  induction z using Quotient.inductionOn with | _ p =>
    exact (recovered n _ p w hw).symm

theorem selected_left : parse 0 (expand (model 0)).quotient [] (by decide)
    ((expand (model 0)).quotient.q left) = .yes (.inl ⟨rfl⟩) :=
  recovered 0 _ left [] (by decide)

theorem selected_right : parse 0 (expand (model 0)).quotient [] (by decide)
    ((expand (model 0)).quotient.q right) = .yes (.inr ⟨rfl⟩) :=
  recovered 0 _ right [] (by decide)

theorem exact_distinguishes : (expand (model 0)).quotient.q left ≠
    (expand (model 0)).quotient.q right := by
  intro h
  have hr := ((expand (model 0)).quotient.kernel left right).mp h
  exact selected_different (hr [] (by decide))

/-- Coarser recognition still cannot retain this same selected decision. -/
example : ¬ ∃ f : Quotient recognition → Decision (P []),
    ∀ p, f (Quotient.mk recognition p) = selected p := selected_no_factor
end Parsing
end Examples.RepresentationExtension
