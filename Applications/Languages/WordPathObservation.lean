import Applications.Languages.IndexedCompositional
import SquareKit.FiniteObservation

/-! Word observations through generic typed paths. The endpoint is packaged
with its exact selected-decision decoder, avoiding an exposed index cast. -/
namespace LanguageWitnesses.IndexedCompositional
open SquareKit.IndexedCompositional
universe u v w
variable {α : Type u}

abbrev WordObservation (P : Language α) (n : Nat) (word : List α) :=
  behavior.Observation (P,n) (Decision (P word))

def wordPath : {P : Language α} → {n : Nat} → (word : List α) →
    word.length ≤ n → WordObservation P n word
  | P, n, [], _ => ⟨(P,n), .stop, id⟩
  | _, 0, _::_, h => False.elim (Nat.not_succ_le_zero _ h)
  | P, n+1, a::word, h =>
    let tail := wordPath (P := derivative P a) (n := n) word (Nat.le_of_succ_le_succ h)
    ⟨tail.endpoint, .step a tail.path, tail.decode⟩

theorem observe_wordPath {X : Index α → Type v} (c : behavior.Coalgebra X)
    {P : Language α} {n : Nat} (x : X (P,n)) (word : List α) (bound : word.length ≤ n) :
    (wordPath word bound).decode (behavior.observe c (wordPath word bound).path x) =
      read c x word bound := by
  induction word generalizing P n with
  | nil => cases n <;> rfl
  | cons a word ih =>
    cases n with
    | zero => exact False.elim (Nat.not_succ_le_zero _ bound)
    | succ n => exact ih _ _

/-- The native word-facing statement follows from generic path preservation. -/
theorem read_morphism_via_path {X : Index α → Type v} {Y : Index α → Type w}
    (c : behavior.Coalgebra X) (d : behavior.Coalgebra Y)
    (f : ∀ j, X j → Y j) (h : behavior.Morphism c d f)
    {P : Language α} {n} (x : X (P,n)) (word : List α) (bound : word.length ≤ n) :
    read d (f _ x) word bound = read c x word bound := by
  rw [← observe_wordPath d, ← observe_wordPath c]
  exact (wordPath word bound).read_morphism c d f h x

/-- Existing parser and trie APIs retain their selected decision exactly. -/
theorem unfold_lookup_via_path [DecidableEq α] {P : Language α} {n}
    (p : Parser P) (word : List α) (bound : word.length ≤ n) :
    (unfold (P,n) p).lookup word bound = p.parse word := by
  rw [← read_target, ← read_source (n := n)]
  exact read_morphism_via_path source target unfold unfold_morphism p word bound

end LanguageWitnesses.IndexedCompositional
