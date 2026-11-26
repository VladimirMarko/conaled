import Examples.CubicalFiniteStateIdentity
import Mathlib.Algebra.BigOperators.Group.List.Basic

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option warningAsError true
namespace JournalTrial
open CategoryTheory SquareKit.Cubical SquareKit.Cubical.Presheaf
open Examples.CubicalStateTransport Examples.CubicalStatePackageFamily
open Examples.CubicalStatePackageUa Examples.CubicalStructuredState
open Examples.CubicalUnivalenceTransport Examples.CubicalGlue

abbrev Journals := List Nat × List Nat

def reverseJournals : Journals ≃ Journals where
  toFun s := (s.1.reverse, s.2.reverse)
  invFun s := (s.1.reverse, s.2.reverse)
  left_inv s := by cases s; simp
  right_inv s := by cases s; simp

def sourceLength : StatePackage Journals where
  initial := ([], [])
  step s := (s.1 ++ [1], s.2 ++ [1])
  Invariant s := s.1.length = s.2.length
  initial_valid := rfl
  preserves s h := by simpa using h

def targetLength : StatePackage Journals where
  initial := ([], [])
  step s := (1 :: s.1, 1 :: s.2)
  Invariant s := s.1.length = s.2.length
  initial_valid := rfl
  preserves s h := by simpa using h

/-- Changed dependent field: equal totals permits journals of different lengths. -/
def sourceSum : StatePackage Journals where
  initial := ([], [])
  step s := (s.1 ++ [1], s.2 ++ [1])
  Invariant s := s.1.sum = s.2.sum
  initial_valid := rfl
  preserves s h := by simpa using h

def targetSum : StatePackage Journals where
  initial := ([], [])
  step s := (1 :: s.1, 1 :: s.2)
  Invariant s := s.1.sum = s.2.sum
  initial_valid := rfl
  preserves s h := by simpa using h

/-- Same initial point and transition; the invariant was incorrectly discarded. -/
def badTarget : StatePackage Journals where
  initial := ([], [])
  step s := (1 :: s.1, 1 :: s.2)
  Invariant _ := True
  initial_valid := trivial
  preserves _ _ := trivial

noncomputable def nativeMap := (codeIso reverseJournals).hom

/-- The original supplied contraction is a parameter, never reconstructed. -/
noncomputable abbrev NativePath (E : HomotopyEquivalence nativeMap)
    (p q : StatePackage Journals) :=
  StructuredPath (admittedLine (S := Journals) (T := Journals) nativeMap E) (admittedPresentation (S := Journals) (T := Journals) nativeMap E)
    (admittedCarrier (S := Journals) (T := Journals) nativeMap E) p q

end JournalTrial
