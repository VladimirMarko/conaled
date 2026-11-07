import SquareKit.SemanticBoundary
import Applications.Languages.Witnesses

/-! The specification retains each selected parse in `P w`. The extra Boolean
in the redundant representation is deliberately absent from that meaning. -/
namespace SemanticClientBoundary
open Squares Squares.SemanticBoundary

universe u

abbrev direct (W : Type u) : Rep.{u} := ⟨W, W, id⟩
abbrev redundant (W : Type u) : Rep.{u} := ⟨W × Bool, W, Prod.fst⟩

def encode (W : Type u) : Square (direct W) (redundant W) where
  impl x := (x, false)
  spec := id
  commutes _ := rfl

def decode (W : Type u) : Square (redundant W) (direct W) where
  impl := Prod.fst
  spec := id
  commutes _ := rfl

def redundantMap {W V : Type u} (f : W → V) : Square (redundant W) (redundant V) where
  impl x := (f x.1, !x.2)
  spec := f
  commutes _ := rfl

def directMap {W V : Type u} (f : W → V) : Square (direct W) (direct V) where
  impl := f
  spec := f
  commutes _ := rfl

/-- A compiler may change the flag; no semantic handle can reveal it. -/
theorem flags_unobservable {W : Type u} {T : Sort v}
    (client : Handle (redundant W) → T) (w : W) :
    client (pack (w, false)) = client (pack (w, true)) :=
  client_invariant client rfl

theorem no_flag_observer {W : Type u} (w : W) :
    ¬ ∃ client : Handle (redundant W) → Bool,
      ∀ x : W × Bool, client (pack x) = x.2 := by
  rintro ⟨client, agrees⟩
  have h := flags_unobservable client w
  rw [agrees, agrees] at h
  cases h

/-- Repacking changes raw flags but is the identity at the semantic boundary. -/
theorem repack {W : Type u} (x : Handle (redundant W)) :
    lift (encode W) (lift (decode W) x) = x := by
  induction x using Quotient.inductionOn with
  | h x => exact Quotient.sound rfl

/-- The same two-step client can run through either implementation. -/
theorem replacement {W V U : Type u} (f : W → V) (g : V → U)
    (x : Handle (direct W)) :
    lift (decode U) (lift (redundantMap g)
      (lift (redundantMap f) (lift (encode W) x))) =
      lift (directMap g) (lift (directMap f) x) := by
  induction x using Quotient.inductionOn with
  | h x => rfl

/-- Indexing by a word retains the entire selected witness type. -/
def parseHandle {α : Type u} (P : LanguageWitnesses.Language α) (w : List α) :=
  Handle (redundant (P w))

theorem selected_parse {α : Type u} (P : LanguageWitnesses.Language α)
    (w : List α) (p : P w) (flag : Bool) :
    meaning (pack (A := redundant (P w)) (p, flag)) = p := rfl

/-- Reindex a family of selected handles by precomposition. -/
def reindex {I J : Type u} {P : I → Type u} (f : J → I)
    (selected : ∀ i, Handle (redundant (P i))) :
    ∀ j, Handle (redundant (P (f j))) := fun j => selected (f j)

theorem reindex_compose {I J K : Type u} {P : I → Type u}
    (f : J → I) (g : K → J) (selected : ∀ i, Handle (redundant (P i))) :
    reindex g (reindex f selected) = reindex (fun k => f (g k)) selected := rfl

theorem reindex_meaning {I J : Type u} {P : I → Type u} (f : J → I)
    (selected : ∀ i, Handle (redundant (P i))) (j : J) :
    meaning (reindex f selected j) = meaning (selected (f j)) := rfl

def selectedIndex (n : Nat) : Handle (redundant (Fin (n + 1))) :=
  pack (⟨n, Nat.lt_succ_self n⟩, false)

/-- Reindexing a nonconstant family keeps the selected index, not merely inhabitation. -/
theorem selected_reindexed :
    (meaning (reindex (fun n : Nat => n * 2)
      (reindex (fun n : Nat => n + 1) selectedIndex) 3)).val = 7 := by
  rw [reindex_meaning, reindex_meaning]
  rfl

-- An ambiguous language has two specified parses at every word.
def ambiguous : LanguageWitnesses.Language Bool := fun _ => Bool

theorem alternatives_distinct (w : List Bool) :
    pack (A := redundant (ambiguous w)) (false, false) ≠ pack (true, false) := by
  intro h
  have bad := congrArg meaning h
  cases bad

/-- Two concrete witness transformations retain the exact selected alternative. -/
theorem selected_client :
    meaning (lift (compose (redundantMap Bool.not) (redundantMap Bool.not))
      (pack (A := redundant (ambiguous [])) (true, false))) = true := by
  exact (lift_meaning _ _).trans rfl

/-- Composition order is observable in the selected result. -/
theorem ordered_client :
    meaning (lift (compose (redundantMap (fun n : Nat => n * 2))
      (redundantMap (fun n : Nat => n + 1)))
      (pack (A := redundant Nat) (3, true))) = 8 := by
  exact (lift_meaning _ _).trans rfl

end SemanticClientBoundary
