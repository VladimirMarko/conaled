import Applications.Paragraphs.Greedy

/-! Exact source helper refinement and its justified partial-call domains. -/
set_option autoImplicit false
set_option warningAsError true
namespace Paragraphs
open OrderedPartitions

def help (maximum : Nat) (line : Line) : Text → Para
  | [] => [line]
  | w :: ws =>
    if fits maximum (line ++ [w]) then help maximum (line ++ [w]) ws
    else line :: help maximum [w] ws

/-- The source has only the nonempty clause; [] is a total extension. -/
def greedy2 (maximum : Nat) : Text → Para
  | [] => []
  | w :: ws => help maximum [w] ws

/-- Arbitrary accumulator identity, separate from initialized paragraph validity. -/
theorem help_foldl (maximum : Nat) (p : Para) (line : Line) (ws : Text)
    (hw : AllWordsFit maximum ws) :
    p ++ help maximum line ws = ws.foldl (add maximum) (p ++ [line]) := by
  induction ws generalizing p line with
  | nil => rfl
  | cons w ws ih =>
    have hwt : AllWordsFit maximum ws := fun v hv => hw v (by simp [hv])
    simp only [help, List.foldl_cons]
    rw [add_append_last maximum p line w (hw w (by simp))]
    cases hg : fits maximum (line ++ [w]) with
    | true => exact ih p (line ++ [w]) hwt
    | false =>
      change p ++ line :: help maximum [w] ws = (ws.foldl (add maximum) (p ++ [line, [w]]))
      simpa only [List.append_assoc, List.singleton_append] using ih (p ++ [line]) [w] hwt

theorem greedy2_eq_greedy (maximum : Nat) (ws : Text) (hw : AllWordsFit maximum ws) :
    greedy2 maximum ws = greedy maximum ws := by
  cases ws with
  | nil => rfl
  | cons w ws =>
    have hwt : AllWordsFit maximum ws := fun v hv => hw v (by simp [hv])
    simpa only [greedy2, greedy, List.foldl_cons, add_nil, List.nil_append] using
      help_foldl maximum [] [w] ws hwt

/-- Every reached helper line is nonempty and fitting; every tested extension is nonempty. -/
def HelpDomain (maximum : Nat) : Line → Text → Prop
  | line, [] => line ≠ [] ∧ FitsLine maximum line
  | line, w :: ws => line ≠ [] ∧ FitsLine maximum line ∧ line ++ [w] ≠ [] ∧
      if fits maximum (line ++ [w]) then HelpDomain maximum (line ++ [w]) ws
      else HelpDomain maximum [w] ws

def Greedy2Domain (maximum : Nat) (ws : Text) : Prop :=
  ∃ w rest, ws = w :: rest ∧ HelpDomain maximum [w] rest

theorem helpDomain_of_fit (maximum : Nat) (line : Line) (ws : Text)
    (hl : line ≠ []) (hf : FitsLine maximum line) (hw : AllWordsFit maximum ws) :
    HelpDomain maximum line ws := by
  induction ws generalizing line with
  | nil => exact ⟨hl, hf⟩
  | cons w ws ih =>
    have hwt : AllWordsFit maximum ws := fun v hv => hw v (by simp [hv])
    refine ⟨hl, hf, by simp, ?_⟩
    cases hg : fits maximum (line ++ [w]) with
    | true => exact ih (line ++ [w]) (by simp) ((fits_iff maximum _).mp hg) hwt
    | false =>
      exact ih [w] (by simp) ((fits_iff maximum [w]).mp (by simp [hw w (by simp)])) hwt

theorem greedy2_source_domain (maximum : Nat) (ws : Text) (h : SourceInput maximum ws) :
    Greedy2Domain maximum ws := by
  obtain ⟨w, rest, rfl⟩ := List.exists_cons_of_ne_nil h.1
  refine ⟨w, rest, rfl, helpDomain_of_fit maximum [w] rest (by simp) ?_ ?_⟩
  · exact (fits_iff maximum [w]).mp (by simp [h.2.2 w (by simp)])
  · exact fun v hv => h.2.2 v (by simp [hv])

/-- The initialized helper has an independent partition contract in addition to its fold identity. -/
theorem help_fitPartition (maximum : Nat) (line : Line) (ws : Text)
    (hl : line ≠ []) (hf : FitsLine maximum line) (hw : AllWordsFit maximum ws) :
    FitPartition maximum (line ++ ws) (help maximum line ws) := by
  induction ws generalizing line with
  | nil =>
    refine ⟨⟨by simp [help], ?_⟩, ?_⟩
    · simpa [help, NonemptyBlocks] using hl
    · simpa [help] using hf
  | cons w ws ih =>
    have hwt : AllWordsFit maximum ws := fun v hv => hw v (by simp [hv])
    rw [help]
    cases hg : fits maximum (line ++ [w]) with
    | true =>
      change FitPartition maximum (line ++ w :: ws) (help maximum (line ++ [w]) ws)
      have hs := ih (line ++ [w]) (by simp) ((fits_iff maximum _).mp hg) hwt
      simpa only [List.append_assoc, List.singleton_append] using hs
    | false =>
      change FitPartition maximum (line ++ w :: ws) (line :: help maximum [w] ws)
      have hs := ih [w] (by simp)
        ((fits_iff maximum [w]).mp (by simp [hw w (by simp)])) hwt
      refine ⟨⟨?_, (nonemptyBlocks_cons _ _).mpr ⟨hl, hs.1.2⟩⟩, ?_⟩
      · simp only [List.flatten_cons, hs.1.1, List.singleton_append]
      · intro block hb
        exact (List.mem_cons.mp hb).elim (fun he => he ▸ hf) (hs.2 block)

theorem greedy2_fitPartition (maximum : Nat) (ws : Text) (hw : AllWordsFit maximum ws) :
    FitPartition maximum ws (greedy2 maximum ws) := by
  rw [greedy2_eq_greedy maximum ws hw]
  exact greedy_fitPartition maximum ws hw

theorem greedy2_minimumLex (maximum : Nat) (ws : Text) (hw : AllWordsFit maximum ws) :
    MinimumLex maximum ws (greedy2 maximum ws) := by
  rw [greedy2_eq_greedy maximum ws hw]
  exact greedy_minimumLex maximum ws hw

theorem greedy2_minimumLines (maximum : Nat) (ws : Text) (hw : AllWordsFit maximum ws) :
    MinimumLines maximum ws (greedy2 maximum ws) := by
  rw [greedy2_eq_greedy maximum ws hw]
  exact greedy_minimumLines maximum ws hw

theorem greedy2_minimumLastWidth (maximum : Nat) (ws : Text) (hw : AllWordsFit maximum ws)
    (q : Para) (hq : FitPartition maximum ws q)
    (hc : cost1 (greedy2 maximum ws) = cost1 q) :
    lastWidth (greedy2 maximum ws) ≤ lastWidth q := by
  rw [greedy2_eq_greedy maximum ws hw] at hc ⊢
  exact greedy_minimumLastWidth maximum ws hw q hq hc

theorem greedy_sourceInput_output (maximum : Nat) (ws : Text) (h : SourceInput maximum ws) :
    FitPartition maximum ws (greedy maximum ws) ∧ FoldDomain maximum [] ws ∧
      greedy maximum ws ≠ [] ∧
      ∀ line ∈ greedy maximum ws, ∀ w ∈ line, SourceWord w := by
  have hp := greedy_fitPartition maximum ws h.2.2
  refine ⟨hp, greedy_source_domain maximum ws h.2.2, ?_, ?_⟩
  · intro he
    have hf := hp.1.1
    rw [he, List.flatten_nil] at hf
    exact h.1 hf.symm
  · intro line hl w hw
    apply h.2.1 w
    rw [← hp.1.1]
    exact List.mem_flatten.mpr ⟨line, hl, hw⟩


end Paragraphs
