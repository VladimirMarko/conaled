import Applications.OpenSystems.Wiring

/-! Checked report fixture and native comparator for issue #376. -/
noncomputable section
open scoped ContDiff
namespace Examples.OpenSystemWiring
open Applications.OpenSystems

abbrev One := Fin 1
abbrev Two := Fin 2

def A : System ℝ Two One := ⟨fun x i => -x + i 0 + i 1, fun x _ => x⟩
def B : System ℝ One One := ⟨fun y i => -2*y + i 0, fun y _ => y⟩
def C : System ℝ One Two := ⟨fun z i => -3*z + i 0, fun z _ => z⟩

/-- A.a supplies B.a; the two external inputs supply A.u and A.v. -/
def ab : Wiring (Two ⊕ One) (One ⊕ One) Two One where
  input := Sum.elim Sum.inr (fun _ => .inl (.inl 0))
  output _ := .inr 0
  admissible := by
    unfold Routing.Admissible Function.Bijective Function.Injective Function.Surjective
    decide

/-- B.b supplies C.b; both C outputs remain exposed. -/
def bc : Wiring (One ⊕ One) (One ⊕ Two) One Two where
  input := Sum.elim (fun _ => .inr 0) (fun _ => .inl (.inl 0))
  output j := .inr j
  admissible := by
    unfold Routing.Admissible Function.Bijective Function.Injective Function.Surjective
    decide

/-- The four outer connections for (AB,C) and (A,BC). -/
def close : Wiring (Two ⊕ One) (One ⊕ Two) One One where
  input := Sum.elim (fun i => if i = 0 then .inr 0 else .inl (.inr 0))
    (fun _ => .inl (.inl 0))
  output _ := .inr 1
  admissible := by
    unfold Routing.Admissible Function.Bijective Function.Injective Function.Surjective
    decide

def AB := (A.parallel B).wire ab.toRouting
def BC := (B.parallel C).wire bc.toRouting
def left := (AB.parallel C).wire close.toRouting
def right := (A.parallel BC).wire close.toRouting

/-- Native product functions fixed independently in the report. -/
def nativeField (s : ℝ × ℝ × ℝ) (u : ℝ) : ℝ × ℝ × ℝ :=
  (-s.1 + u + s.2.2, -2*s.2.1 + s.1, -3*s.2.2 + s.2.1)
def nativeReadout (s : ℝ × ℝ × ℝ) : ℝ := s.2.2

def coordinates : ((ℝ × ℝ) × ℝ) ≃ₗᵢ[ℝ] ℝ × ℝ × ℝ :=
  LinearIsometryEquiv.prodAssoc ℝ ℝ ℝ ℝ

theorem left_field (s : (ℝ × ℝ) × ℝ) (u : One → ℝ) :
    left.field s u = ((-s.1.1 + u 0 + s.2, -2*s.1.2 + s.1.1), -3*s.2 + s.1.2) := by
  rw [left, System.wire_field]
  rfl

theorem right_native (s : ℝ × ℝ × ℝ) (u : One → ℝ) :
    right.field s u = nativeField s (u 0) ∧ right.readout s 0 = nativeReadout s := by
  constructor
  · rw [right, System.wire_field]; rfl
  · rw [right, System.wire_readout]; rfl

/-- Both the tangent velocity and readout agree under the coordinate isomorphism. -/
theorem hierarchy (s : (ℝ × ℝ) × ℝ) (u : One → ℝ) :
    coordinates (left.field s u) = right.field (coordinates s) u ∧
    left.readout s = right.readout (coordinates s) := by
  constructor
  · rw [left_field, (right_native (coordinates s) u).1]
    rfl
  · rw [left, right, System.wire_readout, System.wire_readout]
    rfl

theorem coordinate_derivative (s : (ℝ × ℝ) × ℝ) :
    HasFDerivAt coordinates coordinates.toContinuousLinearEquiv.toContinuousLinearMap s :=
  coordinates.toContinuousLinearEquiv.toContinuousLinearMap.hasFDerivAt

theorem dynamics_conjugacy (s : (ℝ × ℝ) × ℝ) (u : One → ℝ) :
    (fderiv ℝ coordinates s) (left.field s u) = right.field (coordinates s) u := by
  rw [(coordinate_derivative s).fderiv]
  exact (hierarchy s u).1

/-- Coordinate comparison is reversible and retains the whole readout. -/
theorem hierarchy_reverse (s : ℝ × ℝ × ℝ) (u : One → ℝ) :
    coordinates.symm (right.field s u) = left.field (coordinates.symm s) u ∧
    right.readout s = left.readout (coordinates.symm s) := by
  obtain ⟨hf, hr⟩ := hierarchy (coordinates.symm s) u
  simp only [LinearIsometryEquiv.apply_symm_apply] at hf hr
  constructor
  · rw [← hf, LinearIsometryEquiv.symm_apply_apply]
  · exact hr.symm

theorem left_native (s : (ℝ × ℝ) × ℝ) (u : One → ℝ) :
    coordinates (left.field s u) = nativeField (coordinates s) (u 0) ∧
    left.readout s 0 = nativeReadout (coordinates s) := by
  obtain ⟨hf, hr⟩ := hierarchy s u
  obtain ⟨hn, ho⟩ := right_native (coordinates s) u
  exact ⟨hf.trans hn, congrFun hr 0 |>.trans ho⟩

theorem initial_coordinates : coordinates ((0,0),0) = (0,(0,0)) := rfl

/-- Smoothness of the native full field and readout uses Mathlib calculus. -/
theorem native_smooth :
    ContDiff ℝ ∞ (fun p : (ℝ × ℝ × ℝ) × ℝ => nativeField p.1 p.2) ∧
    ContDiff ℝ ∞ nativeReadout := by
  constructor
  · unfold nativeField; fun_prop
  · change ContDiff ℝ ∞ (fun s : ℝ × ℝ × ℝ => s.2.2)
    fun_prop

theorem components_smooth : A.Smooth ∧ B.Smooth ∧ C.Smooth := by
  simp only [System.Smooth, A, B, C]
  repeat' apply And.intro
  all_goals fun_prop

theorem hierarchies_smooth : left.Smooth ∧ right.Smooth := by
  obtain ⟨ha, hb, hc⟩ := components_smooth
  exact ⟨((ha.parallel hb).wire ab.toRouting |>.parallel hc).wire close.toRouting,
    (ha.parallel ((hb.parallel hc).wire bc.toRouting)).wire close.toRouting⟩

/-- Swap A's two exposed inputs: a real second boundary-port permutation. -/
def swapPorts : Wiring Two One Two One where
  input i := .inr (1 - i)
  output := id
  admissible := by
    unfold Routing.Admissible Function.Bijective Function.Injective Function.Surjective
    decide

def abSwap := (ab.comp swapPorts).toRouting

theorem abSwap_admissible : abSwap.Admissible := (ab.comp swapPorts).admissible

/-- Rewiring composition is obtained from the local substitution theorem. -/
theorem swapped_composition :
    AB.wire swapPorts.toRouting = (A.parallel B).wire abSwap :=
  System.wire_comp (A.parallel B) ab.toRouting swapPorts.toRouting

theorem swapped_field (s : ℝ × ℝ) (u : Two → ℝ) :
    (AB.wire swapPorts.toRouting).field s u = (-s.1 + u 1 + u 0, -2*s.2 + s.1) := by
  rw [swapped_composition]
  rfl

/-- A second closing connects feedback to the first swapped boundary port. -/
def closeSwap : Wiring (Two ⊕ One) (One ⊕ Two) One One where
  input := Sum.elim (fun i => if i = 0 then .inl (.inr 0) else .inr 0)
    (fun _ => .inl (.inl 0))
  output _ := .inr 1
  admissible := by
    unfold Routing.Admissible Function.Bijective Function.Injective Function.Surjective
    decide

def second := ((AB.wire swapPorts.toRouting).parallel C).wire closeSwap.toRouting

theorem second_hierarchy (s : (ℝ × ℝ) × ℝ) (u : One → ℝ) :
    second.field s u = left.field s u ∧ second.readout s = left.readout s := by
  constructor <;> rfl

theorem identity_case : left.wire Routing.identity = left := System.wire_identity left

/-- All five report connections in one certified flat diagram. -/
def flat : Wiring ((Two ⊕ One) ⊕ One) ((One ⊕ One) ⊕ Two) One One where
  input := Sum.elim
    (Sum.elim (fun i => if i = 0 then .inr 0 else .inl (.inr 0))
      (fun _ => .inl (.inl (.inl 0))))
    (fun _ => .inl (.inl (.inr 0)))
  output _ := .inr 1
  admissible := by
    unfold Routing.Admissible Function.Bijective Function.Injective Function.Surjective
    decide

theorem flatten_left : ((A.parallel B).parallel C).wire flat.toRouting = left := rfl

/-- A supplier reused for internal feedback and an outer output violates injectivity. -/
def fanout : Routing One One (Fin 0) One := ⟨fun _ => .inl 0, fun _ => 0⟩
theorem fanout_rejected : ¬ fanout.Admissible := by
  intro h
  have bad := h.1 (show fanout.wires (.inl 0) = fanout.wires (.inr 0) from rfl)
  exact Sum.inl_ne_inr bad

/-- A feedthrough q=i+1 cannot be represented by a state-only readout. -/
theorem feedthrough_not_state_only : ¬ ∃ r : Unit → ℝ, ∀ s i, r s = i + 1 := by
  rintro ⟨r, h⟩
  have h0 := h () 0
  have h1 := h () 1
  linarith

theorem feedthrough_feedback_unsolvable : ¬ ∃ i : ℝ, i = i + 1 := by
  rintro ⟨i, h⟩; linarith

/-- An output-only observation misses a change in velocity. -/
theorem readout_is_insufficient :
    nativeReadout (0,0,1) = 1 ∧ nativeField (0,0,1) 0 ≠ (-1,0,-3) := by
  norm_num [nativeReadout, nativeField]
end Examples.OpenSystemWiring
