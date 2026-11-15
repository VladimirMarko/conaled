import Applications.Search.Counting
import Applications.Checking.SearchCount

/-!
# Word generation and graph path occurrences

The word client decodes a word to its length. Its abstract successor list has
two identical states, so count transport must retain multiplicity even through
a noninjective decoder. The graph client has duplicate edges and dead ends;
its expected two-step endpoints are `[3, 3]`, not the singleton set `{3}`.
-/

set_option autoImplicit false
set_option warningAsError true

namespace Examples.SearchCounting

open FiniteSearch
universe u
variable {State : Type u}

def binaryNext (word : List Bool) : List (List Bool) :=
  [word ++ [false], word ++ [true]]

def lengthNext (length : Nat) : List Nat := [length + 1, length + 1]

theorem binary_length (word : List Bool) :
    (binaryNext word).map List.length = lengthNext word.length := by
  simp [binaryNext, lengthNext]

def wordsByLength : Squares.Rep := ⟨List Bool, Nat, List.length⟩

def wordCounter (depth : Nat) : Squares.Square wordsByLength (Squares.exact Nat) :=
  _root_.SearchCounting.countSquare wordsByLength binaryNext lengthNext binary_length depth

theorem length_count (depth length : Nat) : count lengthNext depth length = 2 ^ depth := by
  induction depth generalizing length with
  | zero => rfl
  | succ depth ih =>
      simp only [count, lengthNext, List.map_cons, List.map_nil, List.sum_cons,
        List.sum_nil, ih, Nat.add_zero, Nat.pow_succ]
      omega

/-- The general representation theorem supplies the concrete word count. -/
theorem binary_count (depth : Nat) (word : List Bool) :
    count binaryNext depth word = 2 ^ depth := by
  rw [count_map binaryNext lengthNext List.length binary_length]
  exact length_count depth word.length

/-- Eight occurrences, with the decoder accounting for all eight equal lengths. -/
theorem binary_three : (wordCounter 3).impl ([] : List Bool) = (8 : Nat) :=
  (wordCounter 3).commutes ([] : List Bool)

theorem binary_order : enumerate binaryNext 2 [] =
    [[false, false], [false, true], [true, false], [true, true]] := rfl

theorem decoded_binary_order :
    (enumerate binaryNext 2 []).map List.length = [2, 2, 2, 2] := by
  rw [enumerate_map binaryNext lengthNext List.length binary_length]
  rfl

/-- Ordinary shared square composition attaches a count consumer. -/
def hasWordSquare (depth : Nat) : Squares.Square wordsByLength (Squares.exact Bool) :=
  Squares.compose (Squares.exactSquare (fun count : Nat => decide (0 < count))) (wordCounter depth)

theorem has_word (depth : Nat) (word : List Bool) :
    (hasWordSquare depth).impl word = true := by
  change decide (0 < count binaryNext depth word) = true
  rw [binary_count]
  exact decide_eq_true (Nat.pow_pos (by decide))

/-- Composition states its semantic observation in terms of enumerated endpoints. -/
theorem has_word_spec (depth : Nat) (word : List Bool) :
    (hasWordSquare depth).impl word =
      decide (0 < (enumerate lengthNext depth word.length).length) :=
  (hasWordSquare depth).commutes word

def graphNext : Nat → List Nat
  | 0 => [1, 1, 2]
  | 1 => [3]
  | _ => []

theorem graph_endpoints : enumerate graphNext 2 0 = [3, 3] := rfl

theorem graph_count : count graphNext 2 0 = 2 := by
  rw [count_eq_length, graph_endpoints]
  rfl

theorem graph_partition : count graphNext (1 + 1) 0 = ([1, 1, 0] : List Nat).sum := by
  rw [count_partition]
  rfl

theorem graph_exhausted : count graphNext 3 0 = 0 := by
  rw [count_eq_length]
  rfl

theorem dead_end_zero_depth : count graphNext 0 3 = 1 := by
  rw [count_eq_length]
  rfl

theorem dead_end_positive_depth : count graphNext 1 3 = 0 := by
  rw [count_eq_length]
  rfl

/-- A small proved backend handles one remaining step and declines other depths. -/
def oneStepTail (next : State → List State) : Tail State :=
  fun depth state => if depth = 1 then some (next state).length else none

theorem oneStepTail_exact (next : State → List State) : Exact next (oneStepTail next) := by
  intro depth state value selected
  unfold oneStepTail at selected
  split at selected
  · rename_i depth_one
    cases depth_one
    have value_eq : (next state).length = value := Option.some.inj selected
    rw [← value_eq, count_eq_length]
    simp [enumerate]
  · cases selected

def graphCounter : Squares.Square (Squares.exact Nat) (Squares.exact Nat) :=
  _root_.SearchCounting.countWithSquare (Squares.exact Nat) graphNext graphNext
    (fun state => List.map_id (graphNext state))
    (oneStepTail graphNext) (oneStepTail_exact graphNext) 2

theorem graph_backend_count : graphCounter.impl (0 : Nat) = (2 : Nat) :=
  graphCounter.commutes (0 : Nat)

def graphCertificate : SearchCount.Certificate := ⟨1, [1, 1, 0]⟩

theorem graph_certificate_accepts : SearchCount.verify graphNext 2 0 graphCertificate = true := by
  change SearchCount.verify graphNext 2 0 (SearchCount.certificate graphNext 2 1 0) = true
  exact SearchCount.verify_certificate _ _ _ _ (by decide)

/-- The checked result theorem, rather than an assumed numerical claim, is used. -/
theorem graph_certificate_count : (enumerate graphNext 2 0).length = 2 :=
  SearchCount.verify_sound graphNext 2 0 graphCertificate graph_certificate_accepts

theorem graph_release : SearchCount.release graphNext 2 0 graphCertificate = some 2 := by
  apply (SearchCount.release_eq_some_iff _ _ _ _ _).mpr
  exact ⟨(SearchCount.verify_iff _ _ _ _).mp graph_certificate_accepts, rfl⟩

theorem released_graph_count : (enumerate graphNext 2 0).length = 2 :=
  SearchCount.release_sound graphNext 2 0 graphCertificate 2 graph_release

theorem wrong_count_rejected :
    SearchCount.release graphNext 2 0 ⟨1, [1, 2, 0]⟩ = none := rfl

/-- Equal proposed total does not make a missing frontier occurrence valid. -/
theorem missing_occurrence_rejected :
    SearchCount.release graphNext 2 0 ⟨1, [1, 1]⟩ = none := rfl

theorem reordered_counts_rejected :
    SearchCount.release graphNext 2 0 ⟨1, [0, 1, 1]⟩ = none := rfl

theorem too_deep_rejected :
    SearchCount.release graphNext 2 0 ⟨3, []⟩ = none := rfl

theorem unchecked_claim_rejected : SearchCount.checkCount graphNext 2 0 1 = false := rfl

/-- A producer of unchecked constant proposals still gives an exact checked backend. -/
theorem rejected_backend_falls_back :
    countWith graphNext (SearchCount.checkedTail graphNext (fun _ _ => ⟨0, [99]⟩)) 2 0 = 2 := by
  rw [countWith_eq_count _ _ (SearchCount.checkedTail_exact _ _)]
  exact graph_count

end Examples.SearchCounting
