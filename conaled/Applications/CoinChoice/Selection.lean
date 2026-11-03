import Applications.CoinChoice.Presentation
import Applications.Optimization.SelectionTies

/-! Two objectives over one feasible candidate semantics, with exact minimum ties. -/
set_option autoImplicit false
set_option warningAsError true

namespace Applications.CoinChoice
open Optimization Optimization.Thinning

/-- The common candidate domain is independent of enumeration and selection. -/
def feasible (ds : List Nat) (n : Nat) : Set (List Nat) := {cs | Represents ds cs n}

theorem minCoins_iff_minimizer (ds cs : List Nat) (n : Nat) :
    MinCoins ds n cs ↔ cs ∈ minimizers (feasible ds n) count := Iff.rfl

theorem lexical_iff_minimizer (ds cs : List Nat) (n : Nat) :
    LexMaximumTuple ds n cs ↔
      cs ∈ minimizers (feasible ds n) (fun xs => OrderDual.toDual xs) := Iff.rfl

/-- Enumeration completeness supplies the coverage obligation of shared optimizer transport. -/
theorem enumeration_minimizer {K : Type*} [Preorder K] (cost : List Nat → K)
    {ds : List Nat} (hds : Currency ds) (n : Nat) {cs : List Nat}
    (h : cs ∈ minimizers {xs | xs ∈ mktuples ds n} cost) :
    cs ∈ minimizers (feasible ds n) cost := by
  apply minimizer_transport (A := {xs | xs ∈ mktuples ds n}) (B := feasible ds n)
    (c := cost) (J := cost) (id : List Nat → List Nat) (id : K → K)
    monotone_id ?_ (fun _ _ => rfl) ?_ h
  · intro xs hx
    exact (mem_mktuples_iff hds n xs).mp hx
  · intro xs hx
    exact ⟨xs, (mem_mktuples_iff hds n xs).mpr hx, le_rfl⟩

/-- First minimum coin count in ascending source traversal. -/
def mkchange (ds : List Nat) (n : Nat) : Option (List Nat) := argmin count (mktuples ds n)

/-- Last ties reuse the shared selector's reversed traversal. -/
def mkchangeStrict (ds : List Nat) (n : Nat) : Option (List Nat) :=
  argminLast count (mktuples ds n)

/-- A second consumer maximizes lexical order using the ordinary order dual. -/
def lexicalChoice (ds : List Nat) (n : Nat) : Option (List Nat) :=
  argmin (fun xs => OrderDual.toDual xs) (mktuples ds n)

theorem mkchange_spec {ds : List Nat} (hds : Currency ds) (n : Nat) (cs : List Nat)
    (he : mkchange ds n = some cs) : MinCoins ds n cs :=
  (minCoins_iff_minimizer ds cs n).mpr
    (enumeration_minimizer count hds n (argmin_correct count _ cs he))

theorem mkchange_firstMinimum (ds : List Nat) (n : Nat) (cs : List Nat) :
    mkchange ds n = some cs ↔ FirstMinimum count (mktuples ds n) cs :=
  argmin_eq_some_iff_firstMinimum _ _ _

theorem mkchangeStrict_spec {ds : List Nat} (hds : Currency ds) (n : Nat) (cs : List Nat)
    (he : mkchangeStrict ds n = some cs) : MinCoins ds n cs :=
  (minCoins_iff_minimizer ds cs n).mpr
    (enumeration_minimizer count hds n (argminLast_correct count _ cs he))

theorem mkchangeStrict_lastMinimum (ds : List Nat) (n : Nat) (cs : List Nat) :
    mkchangeStrict ds n = some cs ↔ LastMinimum count (mktuples ds n) cs :=
  argminLast_eq_some_iff _ _ _

theorem mkchange_exists {ds : List Nat} (hds : Currency ds) (n : Nat) :
    ∃ cs, mkchange ds n = some cs ∧ MinCoins ds n cs := by
  cases he : mkchange ds n with
  | none => exact False.elim (mktuples_nonempty hds n ((argmin_eq_none_iff _ _).mp he))
  | some cs => exact ⟨cs, rfl, mkchange_spec hds n cs he⟩

theorem mkchangeStrict_exists {ds : List Nat} (hds : Currency ds) (n : Nat) :
    ∃ cs, mkchangeStrict ds n = some cs ∧ MinCoins ds n cs := by
  cases he : mkchangeStrict ds n with
  | none =>
    have hn := (argmin_eq_none_iff count (mktuples ds n).reverse).mp he
    exact False.elim (mktuples_nonempty hds n (by simpa using hn))
  | some cs => exact ⟨cs, rfl, mkchangeStrict_spec hds n cs he⟩

theorem lexicalChoice_spec {ds : List Nat} (hds : Currency ds) (n : Nat) (cs : List Nat)
    (he : lexicalChoice ds n = some cs) : LexMaximumTuple ds n cs :=
  (lexical_iff_minimizer ds cs n).mpr
    (enumeration_minimizer _ hds n (argmin_correct _ _ cs he))

theorem lexicalChoice_eq_greedy {ds : List Nat} (hds : Currency ds) (n : Nat) :
    lexicalChoice ds n = some (mkchange3 ds n) := by
  cases he : lexicalChoice ds n with
  | none => exact False.elim (mktuples_nonempty hds n ((argmin_eq_none_iff _ _).mp he))
  | some cs => exact congrArg some (eq_mkchange3_of_lexMaximum hds (lexicalChoice_spec hds n cs he))

/-- Coin-count optima have equal scores; their tuples and tie positions can differ. -/
theorem minCoins_count_unique {ds cs xs : List Nat} {n : Nat}
    (hc : MinCoins ds n cs) (hx : MinCoins ds n xs) : count cs = count xs :=
  Nat.le_antisymm (hc.2 xs hx.1) (hx.2 cs hc.1)

theorem mkchange_variant_count_eq {ds : List Nat} (hds : Currency ds)
    (n : Nat) (cs xs : List Nat) (hc : mkchange ds n = some cs)
    (hx : mkchangeStrict ds n = some xs) : count cs = count xs :=
  minCoins_count_unique (mkchange_spec hds n cs hc) (mkchangeStrict_spec hds n xs hx)

end Applications.CoinChoice
