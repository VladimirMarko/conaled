import Applications.Sequences.RunCompression

/-! Adjacent-input certificates exercise the public implementation equivalences. -/
set_option autoImplicit false
set_option warningAsError true

namespace Examples.RunCompression

open Applications.Sequences.RunCompression

/-- The empty certificate reaches both realizations through their equivalences. -/
theorem empty : build ([] : List Nat) = [] ∧ compress ([] : List Nat) = [] :=
  ⟨(build_equality_iff _ _).mpr .nil, (compress_iff _ _).mpr .nil⟩

theorem repeated : build ([4, 4, 4] : List Nat) = [4] :=
  (build_equality_iff _ _).mpr (.repeated (.repeated (.single 4)))

/-- The second occurrence of 1 has its own run after the intervening 2. -/
theorem separated_spec : Spec ([1, 1, 2, 1, 1] : List Nat) [1, 2, 1] :=
  .repeated (.boundary (by decide) (.boundary (by decide) (.repeated (.single 1))))

theorem separated_build : build ([1, 1, 2, 1, 1] : List Nat) = [1, 2, 1] :=
  (build_equality_iff _ _).mpr separated_spec

theorem separated_compress : compress ([1, 1, 2, 1, 1] : List Nat) = [1, 2, 1] :=
  compress_unique separated_spec

inductive Symbol
  | red | blue
  deriving DecidableEq, BEq, ReflBEq, LawfulBEq

open Symbol

def signals : List Symbol := [red, red, blue, red]

theorem signals_spec : Spec signals [red, blue, red] :=
  .repeated (.boundary (by decide) (.boundary (by decide) (.single red)))

theorem signals_build : build signals = [red, blue, red] :=
  (build_equality_iff _ _).mpr signals_spec

/-- Two injective label changes compose without changing run boundaries. -/
def label : Symbol → Option (Sum Symbol Unit) := Option.some ∘ Sum.inl

theorem label_injective : Function.Injective label := by
  intro x y h
  exact Sum.inl.inj (Option.some.inj h)

theorem relabeled_build : build (signals.map label) = [label red, label blue, label red] := by
  exact (build_equality_iff _ _).mpr (signals_spec.map label_injective)

theorem relabeled_compress :
    compress (signals.map label) = [label red, label blue, label red] := by
  rw [compress_map label label_injective, compress_unique signals_spec]
  rfl

/-- A constant relabeling destroys the red/blue boundary. -/
theorem noninjective_merges :
    compress (signals.map (fun _ => ())) = [()] ∧
      (compress signals).map (fun _ => ()) = [(), (), ()] := by
  constructor
  · apply (compress_iff _ _).mpr
    exact .repeated (.repeated (.repeated (.single ())))
  · rw [compress_unique signals_spec]
    rfl

/-- Membership and unequal neighbors omit the multiplicity of separated runs. -/
theorem membership_and_chain_insufficient :
    (∀ x : Nat, x ∈ [1, 2] ↔ x ∈ [1, 2, 1]) ∧
      ([1, 2] : List Nat).IsChain (· ≠ ·) ∧
      ¬ Spec ([1, 2, 1] : List Nat) [1, 2] := by
  refine ⟨?_, by decide, ?_⟩
  · intro x
    simp only [List.mem_cons, List.not_mem_nil, or_false]
    tauto
  · intro h
    have expected : Spec ([1, 2, 1] : List Nat) [1, 2, 1] :=
      .boundary (by decide) (.boundary (by decide) (.single 1))
    have wrong := expected.unique h
    contradiction

theorem signals_boundary : (build signals).IsChain (· ≠ ·) :=
  build_equality_noAdjacent signals

theorem signals_membership (s : Symbol) : s ∈ build signals ↔ s ∈ signals :=
  build_equality_membership signals s

theorem repeated_prefix (k : Nat) :
    compress (List.replicate (k + 1) red ++ [blue, red]) = [red, blue, red] := by
  rw [compress_replicate_prefix]
  exact compress_unique (.boundary (by decide) (.boundary (by decide) (.single red)))

end Examples.RunCompression
