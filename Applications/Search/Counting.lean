import SquareKit.FiniteSearch
import SquareKit.Combinators

/-!
# Representation transport for finite-search counts

The only representation law required is exact preservation of the ordered
successor list. The semantic observation is the length of the independently
enumerated result; the realization counts directly, optionally using a proved
residual backend. Ordinary functions remain available through `FiniteSearch`.
-/

set_option autoImplicit false
set_option warningAsError true

namespace SearchCounting

open FiniteSearch

/-- The state representation may be redundant; successor multiplicity is retained. -/
def countSquare (states : Squares.Rep)
    (next : states.R → List states.R) (semantic : states.S → List states.S)
    (law : ∀ state, (next state).map states.decode = semantic (states.decode state))
    (depth : Nat) : Squares.Square states (Squares.exact Nat) where
  impl := count next depth
  spec state := (enumerate semantic depth state).length
  commutes state :=
    (count_map next semantic states.decode law depth state).trans
      (count_eq_length semantic depth (states.decode state))

/-- Replacing residual subproblems composes with state representation transport. -/
def countWithSquare (states : Squares.Rep)
    (next : states.R → List states.R) (semantic : states.S → List states.S)
    (law : ∀ state, (next state).map states.decode = semantic (states.decode state))
    (tail : Tail states.R) (exactTail : Exact next tail) (depth : Nat) :
    Squares.Square states (Squares.exact Nat) where
  impl := countWith next tail depth
  spec := (countSquare states next semantic law depth).spec
  commutes state := (countWith_eq_count next tail exactTail depth state).trans
    ((countSquare states next semantic law depth).commutes state)

end SearchCounting
