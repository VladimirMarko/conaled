import Examples.OpenSystemWiring
import Applications.OpenSystems.CubicCoordinate
import SquareKit.DiscreteApproximation

/-! Experimental discrete approximate transport through the actual #376 feedback
wiring. All arithmetic is real; there is no continuous-flow or floating-point claim. -/
noncomputable section
namespace Examples.WiringApproximation
open Applications.OpenSystems Examples.OpenSystemWiring
open SquareKit.DiscreteApproximation

/-- Same readout, with simultaneous next-state update in place of velocity. -/
def euler {S I O : Type} [Add S] [SMul ℝ S] (h : ℝ) (f : System S I O) : System S I O where
  field s i := s + h • f.field s i
  readout := f.readout

theorem euler_wire {S I O J P : Type} [Add S] [SMul ℝ S]
    (h : ℝ) (f : System S I O) (w : Routing I O J P) :
    euler h (f.wire w) = (euler h f).wire w := rfl

theorem euler_parallel {S T I O J P : Type} [Add S] [SMul ℝ S] [Add T] [SMul ℝ T]
    (h : ℝ) (f : System S I O) (g : System T J P) :
    euler h (f.parallel g) = (euler h f).parallel (euler h g) := rfl

theorem euler_hierarchy (h : ℝ) (s : (ℝ × ℝ) × ℝ) (u : One → ℝ) :
    coordinates ((euler h left).field s u) =
      (euler h right).field (coordinates s) u ∧
    (euler h left).readout s = (euler h right).readout (coordinates s) := by
  obtain ⟨hf, hr⟩ := hierarchy s u
  exact ⟨by simpa [euler, map_add, map_smul] using congrArg (coordinates s + h • ·) hf, hr⟩

abbrev State := ℝ × ℝ × ℝ

def source (h : ℝ) (s : State) : State := (euler h right).field s (fun _ => 0)

theorem source_eq (h : ℝ) (s : State) : source h s =
    ((1-h)*s.1+h*s.2.2, (1-2*h)*s.2.1+h*s.1, (1-3*h)*s.2.2+h*s.2.1) := by
  simp only [source, euler, (right_native s (fun _ => 0)).1, nativeField]
  ext <;> simp <;> ring

def interpret (s : State) : State := (Cubic.encode s.1, s.2)
def decode (s : State) : State := (Cubic.decode s.1, s.2)

@[simp] theorem decode_interpret (s : State) : decode (interpret s) = s := by
  simp [decode, interpret]
@[simp] theorem interpret_decode (s : State) : interpret (decode s) = s := by
  simp [decode, interpret]

def transformedA : System ℝ Two One where
  field q i := (1+3*(Cubic.decode q)^2)*(-Cubic.decode q+i 0+i 1)
  readout q _ := Cubic.decode q

def transformed := (transformedA.parallel BC).wire close.toRouting

def target (h : ℝ) (s : State) : State := (euler h transformed).field s (fun _ => 0)

theorem transformed_field (s : State) (u : One → ℝ) : transformed.field s u =
    ((1+3*(Cubic.decode s.1)^2)*(-Cubic.decode s.1+u 0+s.2.2),
      -2*s.2.1+Cubic.decode s.1, -3*s.2.2+s.2.1) := rfl

theorem transformed_readout (s : State) : transformed.readout s 0 = s.2.2 := rfl

theorem target_eq (h : ℝ) (s : State) : target h s =
    (s.1+h*(1+3*(Cubic.decode s.1)^2)*(-Cubic.decode s.1+s.2.2),
      (1-2*h)*s.2.1+h*Cubic.decode s.1, (1-3*h)*s.2.2+h*s.2.1) := by
  simp only [target, euler, transformed_field]
  ext <;> simp <;> ring

/-- The transformed field is the derivative action on the full wired field. -/
theorem field_comparison (s : State) : transformed.field (interpret s) (fun _ => 0) =
    ((1+3*s.1^2)*(nativeField s 0).1, (nativeField s 0).2) := by
  simp [transformed_field, interpret, nativeField]

theorem transport_defect (h : ℝ) (s : State) :
    interpret (source h s) - target h (interpret s) =
      (3*s.1*h^2*(-s.1+s.2.2)^2+h^3*(-s.1+s.2.2)^3, 0, 0) := by
  rw [source_eq, target_eq]
  simp only [interpret, Cubic.decode_encode, Prod.mk_sub_mk]
  ext <;> simp [Cubic.encode] <;> ring

theorem defect_nonzero : interpret (source (1/4) (1,0,0)) -
    target (1/4) (interpret (1,0,0)) = ((11/64:ℝ),0,0) := by
  rw [transport_defect]; norm_num

def sourceBox (R : ℝ) : Set State := {s | |s.1| ≤ R ∧ |s.2.1| ≤ R ∧ |s.2.2| ≤ R}
def targetBox (R : ℝ) : Set State := {s | |s.1| ≤ Cubic.encode R ∧ |s.2.1| ≤ R ∧ |s.2.2| ≤ R}

theorem interpret_box {R : ℝ} {s : State} (hs : s ∈ sourceBox R) :
    interpret s ∈ targetBox R := ⟨Cubic.encode_box hs.1, hs.2⟩

/-- One component's two scalar sensitivities, before choosing any wires. -/
theorem scalar_gain (a b x y x' y' : ℝ) :
    |(a*x+b*y)-(a*x'+b*y')| ≤ |a| *|x-x'|+|b| *|y-y'| := by
  calc
    _ = |a*(x-x')+b*(y-y')| := by congr 1; ring
    _ ≤ _ := (abs_add_le _ _).trans (by rw [abs_mul, abs_mul])

theorem scalar_box {a b x y R : ℝ} (ha : 0 ≤ a) (hb : 0 ≤ b)
    (hab : a+b ≤ 1) (hR : 0 ≤ R) (hx : |x| ≤ R) (hy : |y| ≤ R) :
    |a*x+b*y| ≤ R := by
  calc
    _ ≤ |a*x|+|b*y| := abs_add_le _ _
    _ = a*|x|+b*|y| := by rw [abs_mul, abs_mul, abs_of_nonneg ha, abs_of_nonneg hb]
    _ ≤ a*R+b*R := add_le_add (mul_le_mul_of_nonneg_left hx ha) (mul_le_mul_of_nonneg_left hy hb)
    _ ≤ R := by nlinarith

theorem source_invariant {R h : ℝ} (hR : 0 ≤ R) (hh : 0 ≤ h) (hh' : h ≤ 1/3)
    {s : State} (hs : s ∈ sourceBox R) : source h s ∈ sourceBox R := by
  rw [source_eq]
  exact ⟨scalar_box (by linarith) hh (by linarith) hR hs.1 hs.2.2,
    scalar_box (by linarith) hh (by linarith) hR hs.2.1 hs.1,
    scalar_box (by linarith) hh (by linarith) hR hs.2.2 hs.2.1⟩

theorem target_invariant {R h : ℝ} (hR : 0 ≤ R) (hh : 0 ≤ h) (hh' : h ≤ 1/3)
    {s : State} (hs : s ∈ targetBox R) : target h s ∈ targetBox R := by
  have hx := Cubic.decode_box hs.1
  rw [target_eq]
  refine ⟨?_, scalar_box (by linarith) hh (by linarith) hR hs.2.1 hx,
    scalar_box (by linarith) hh (by linarith) hR hs.2.2 hs.2.1⟩
  simpa using Cubic.euler_box hR hx hs.2.2 hh hh'


/-- Errors are indexed by actual component states, in A/B/C order. -/
def component (s : State) : Fin 3 → ℝ := ![s.1,s.2.1,s.2.2]
def sourceGains (h : ℝ) : Matrix (Fin 3) (Fin 3) ℝ :=
  !![|1-h|, 0, |h|; |h|, |1-2*h|, 0; 0, |h|, |1-3*h|]
def targetFieldGains (R : ℝ) : Matrix (Fin 3) (Fin 3) ℝ :=
  !![1+15*R^2, 0, 1+3*R^2; 1, 2, 0; 0, 1, 3]

theorem source_gains_nonneg (h : ℝ) (i j : Fin 3) : 0 ≤ sourceGains h i j := by
  fin_cases i <;> fin_cases j <;> simp [sourceGains, abs_nonneg]

theorem target_gains_nonneg (R : ℝ) (i j : Fin 3) : 0 ≤ targetFieldGains R i j := by
  fin_cases i <;> fin_cases j <;> simp [targetFieldGains] <;> positivity

/-- Each matrix row follows from a component update and its actual suppliers. -/
theorem source_wired_gains (h : ℝ) (s t : State) (i : Fin 3) :
    |component (source h s) i-component (source h t) i| ≤
      ∑ j, sourceGains h i j * |component s j-component t j| := by
  fin_cases i <;> simp [source_eq, component, sourceGains, Fin.sum_univ_three]
  · exact scalar_gain _ _ _ _ _ _
  · simpa [add_comm] using scalar_gain (1-2*h) h s.2.1 s.1 t.2.1 t.1
  · simpa [add_comm] using scalar_gain (1-3*h) h s.2.2 s.2.1 t.2.2 t.2.1

theorem target_wired_gains {R : ℝ} (hR : 0 ≤ R) {s t : State}
    (hs : s ∈ targetBox R) (ht : t ∈ targetBox R) (i : Fin 3) :
    |component (transformed.field s (fun _ => 0)) i -
      component (transformed.field t (fun _ => 0)) i| ≤
      ∑ j, targetFieldGains R i j * |component s j-component t j| := by
  have hinv := Cubic.inverse_bound s.1 t.1
  fin_cases i <;> simp [transformed_field, component, targetFieldGains, Fin.sum_univ_three]
  · exact (Cubic.field_gain hR (Cubic.decode_box hs.1) (Cubic.decode_box ht.1) hs.2.2).trans
      (by gcongr)
  · have hh := scalar_gain (-2) 1 s.2.1 (Cubic.decode s.1) t.2.1 (Cubic.decode t.1)
    norm_num at hh
    linarith
  · have hh := scalar_gain (-3) 1 s.2.2 s.2.1 t.2.2 t.2.1
    norm_num at hh
    linarith

def fieldGain (R : ℝ) : ℝ := max 4 (2+18*R^2)
def stepGain (R h : ℝ) : ℝ := 1+h*fieldGain R
def defectBudget (R h : ℝ) : ℝ := 12*R^3*h^2+8*R^3*h^3

theorem component_le_norm (s : State) (i : Fin 3) : |component s i| ≤ ‖s‖ := by
  fin_cases i <;> simp [component, Prod.norm_def, Real.norm_eq_abs]

theorem norm_le_components {s : State} {b : ℝ} (h : ∀ i, |component s i| ≤ b) : ‖s‖ ≤ b := by
  exact (norm_prod_le_iff).mpr ⟨h 0, (norm_prod_le_iff).mpr ⟨h 1,h 2⟩⟩

theorem field_lipschitz {R : ℝ} (hR : 0 ≤ R) {s t : State}
    (hs : s ∈ targetBox R) (ht : t ∈ targetBox R) :
    ‖transformed.field s (fun _ => 0)-transformed.field t (fun _ => 0)‖ ≤
      fieldGain R * ‖s-t‖ := by
  apply norm_le_components
  intro i
  have hrow := target_wired_gains hR hs ht i
  have hj : ∀ j, |component s j-component t j| ≤ ‖s-t‖ := by
    intro j
    convert component_le_norm (s-t) j using 1
    fin_cases j <;> rfl
  have hsum : (∑ j, targetFieldGains R i j * |component s j-component t j|) ≤
      (∑ j, targetFieldGains R i j) * ‖s-t‖ := by
    rw [Finset.sum_mul]
    exact Finset.sum_le_sum (fun j _ => mul_le_mul_of_nonneg_left (hj j) (target_gains_nonneg R i j))
  have hweight : (∑ j, targetFieldGains R i j) ≤ fieldGain R := by
    fin_cases i <;> rw [Fin.sum_univ_three]
    · change 1+15*R^2+0+(1+3*R^2) ≤ fieldGain R
      unfold fieldGain
      nlinarith [le_max_right (4:ℝ) (2+18*R^2)]
    · change 1+2+0 ≤ fieldGain R
      exact le_trans (by norm_num : (1+2+0:ℝ) ≤ 4) (le_max_left _ _)
    · change 0+1+3 ≤ fieldGain R
      exact le_trans (by norm_num : (0+1+3:ℝ) ≤ 4) (le_max_left _ _)
  have he : component (transformed.field s (fun _ => 0)-transformed.field t (fun _ => 0)) i =
      component (transformed.field s (fun _ => 0)) i-component (transformed.field t (fun _ => 0)) i := by
    fin_cases i <;> rfl
  rw [he]
  exact hrow.trans (hsum.trans (mul_le_mul_of_nonneg_right hweight (norm_nonneg _)))

theorem target_lipschitz {R h : ℝ} (hR : 0 ≤ R) (hh : 0 ≤ h) {s t : State}
    (hs : s ∈ targetBox R) (ht : t ∈ targetBox R) :
    dist (target h s) (target h t) ≤ stepGain R h * dist s t := by
  rw [dist_eq_norm, dist_eq_norm]
  change ‖(s+h • transformed.field s (fun _ => 0))-(t+h • transformed.field t (fun _ => 0))‖ ≤ _
  rw [show (s+h • transformed.field s (fun _ => 0))-(t+h • transformed.field t (fun _ => 0)) =
    (s-t)+h • (transformed.field s (fun _ => 0)-transformed.field t (fun _ => 0)) by module]
  calc
    _ ≤ ‖s-t‖+‖h • (transformed.field s (fun _ => 0)-transformed.field t (fun _ => 0))‖ := norm_add_le _ _
    _ ≤ ‖s-t‖+h*(fieldGain R * ‖s-t‖) := by
      rw [norm_smul, Real.norm_eq_abs, abs_of_nonneg hh]
      gcongr
      exact field_lipschitz hR hs ht
    _ = _ := by unfold stepGain; ring

theorem local_defect_bound {R h : ℝ} (hR : 0 ≤ R) (hh : 0 ≤ h) {s : State}
    (hs : s ∈ sourceBox R) :
    dist (interpret (source h s)) (target h (interpret s)) ≤ defectBudget R h := by
  rw [dist_eq_norm, transport_defect]
  simp only [Prod.norm_def, Real.norm_eq_abs, abs_zero, max_self]
  rw [max_eq_left (abs_nonneg _)]
  have hv : |-s.1+s.2.2| ≤ 2*R := (abs_add_le _ _).trans (by rw [abs_neg]; linarith [hs.1, hs.2.2])
  simpa [Cubic.defect, defectBudget] using Cubic.defect_bound hR hs.1 hv hh


theorem stepGain_nonneg {R h : ℝ} (hh : 0 ≤ h) : 0 ≤ stepGain R h := by
  unfold stepGain fieldGain
  positivity

theorem source_orbit_box {R h : ℝ} (hR : 0 ≤ R) (hh : 0 ≤ h) (hh' : h ≤ 1/3)
    {s : State} (hs : s ∈ sourceBox R) (n : ℕ) : orbit (source h) s n ∈ sourceBox R :=
  orbit_mem (fun _ => source_invariant hR hh hh') hs n

theorem target_orbit_box {R h : ℝ} (hR : 0 ≤ R) (hh : 0 ≤ h) (hh' : h ≤ 1/3)
    {t : State} (ht : t ∈ targetBox R) (n : ℕ) : orbit (target h) t n ∈ targetBox R :=
  orbit_mem (fun _ => target_invariant hR hh hh') ht n

/-- Reusable route: each intermediate state and domain comes from the actual orbit. -/
theorem comparison {R h e : ℝ} (hR : 0 ≤ R) (hh : 0 ≤ h) (hh' : h ≤ 1/3)
    {s t : State} (hs : s ∈ sourceBox R) (ht : t ∈ targetBox R)
    (he : dist (interpret s) t ≤ e) (N : ℕ) :
    ∀ n ≤ N, dist (interpret (orbit (source h) s n)) (orbit (target h) t n) ≤
      budget (stepGain R h) (defectBudget R h) e n := by
  apply finite_bound (source h) (target h) interpret s t (stepGain_nonneg hh) he N
  · intro n _
    exact local_defect_bound hR hh (source_orbit_box hR hh hh' hs n)
  · intro n _
    exact target_lipschitz hR hh (interpret_box (source_orbit_box hR hh hh' hs n))
      (target_orbit_box hR hh hh' ht n)

/-- Native route: the same statement proved by direct orbit induction, without
using finite_bound or step_bound. It shares the component mathematics. -/
theorem comparison_native {R h e : ℝ} (hR : 0 ≤ R) (hh : 0 ≤ h) (hh' : h ≤ 1/3)
    {s t : State} (hs : s ∈ sourceBox R) (ht : t ∈ targetBox R)
    (he : dist (interpret s) t ≤ e) (N : ℕ) :
    ∀ n ≤ N, dist (interpret (orbit (source h) s n)) (orbit (target h) t n) ≤
      budget (stepGain R h) (defectBudget R h) e n := by
  intro n hn
  induction n with
  | zero => exact he
  | succ n ih =>
    have hd := local_defect_bound hR hh (source_orbit_box hR hh hh' hs n)
    have hg := target_lipschitz hR hh (interpret_box (source_orbit_box hR hh hh' hs n))
      (target_orbit_box hR hh hh' ht n)
    have hb := mul_le_mul_of_nonneg_left (ih (by omega)) (stepGain_nonneg (R := R) hh)
    have htri := dist_triangle (interpret (source h (orbit (source h) s n)))
      (target h (interpret (orbit (source h) s n))) (target h (orbit (target h) t n))
    change dist (interpret (source h (orbit (source h) s n)))
      (target h (orbit (target h) t n)) ≤ _
    rw [budget]
    linarith

theorem sampled_output {R h e : ℝ} (hR : 0 ≤ R) (hh : 0 ≤ h) (hh' : h ≤ 1/3)
    {s t : State} (hs : s ∈ sourceBox R) (ht : t ∈ targetBox R)
    (he : dist (interpret s) t ≤ e) (N n : ℕ) (hn : n ≤ N) :
    |right.readout (orbit (source h) s n) 0 - transformed.readout (orbit (target h) t n) 0| ≤
      (stepGain R h)^n*e + defectBudget R h * ∑ j ∈ Finset.range n, (stepGain R h)^j := by
  have hc := comparison hR hh hh' hs ht he N n hn
  rw [budget_sum, dist_eq_norm] at hc
  exact (component_le_norm (interpret (orbit (source h) s n)-orbit (target h) t n) 2).trans hc

/-- Restart uses the actual intermediate orbit pair and its accumulated budget. -/
theorem comparison_restart {R h e : ℝ} (hR : 0 ≤ R) (hh : 0 ≤ h) (hh' : h ≤ 1/3)
    {s t : State} (hs : s ∈ sourceBox R) (ht : t ∈ targetBox R)
    (he : dist (interpret s) t ≤ e) (n m : ℕ) :
    dist (interpret (orbit (source h) s (n+m))) (orbit (target h) t (n+m)) ≤
      budget (stepGain R h) (defectBudget R h)
        (budget (stepGain R h) (defectBudget R h) e n) m := by
  rw [orbit_add, orbit_add]
  exact comparison hR hh hh' (source_orbit_box hR hh hh' hs n)
    (target_orbit_box hR hh hh' ht n) (comparison hR hh hh' hs ht he n n le_rfl) m m le_rfl

/-- Nonzero admitted finite specialization; the same certificate covers every sample. -/
theorem fixture_comparison (n : ℕ) (hn : n ≤ 3) :
    dist (interpret (orbit (source (1/4)) (1,0,0) n))
      (orbit (target (1/4)) (2,0,0) n) ≤ budget 6 (7/8) 0 n := by
  have hh := comparison (R := 1) (h := 1/4) (e := 0) (by norm_num) (by norm_num) (by norm_num)
    (s := (1,0,0)) (t := (2,0,0))
    (by norm_num [sourceBox]) (by norm_num [targetBox, Cubic.encode])
    (by norm_num [interpret, Cubic.encode]) 3 n hn
  norm_num [stepGain, fieldGain, defectBudget] at hh
  exact hh

theorem fixture_domains (n : ℕ) : orbit (source (1/4)) (1,0,0) n ∈ sourceBox 1 ∧
    orbit (target (1/4)) (2,0,0) n ∈ targetBox 1 := by
  exact ⟨source_orbit_box (by norm_num) (by norm_num) (by norm_num) (by norm_num [sourceBox]) n,
    target_orbit_box (by norm_num) (by norm_num) (by norm_num)
      (by norm_num [targetBox, Cubic.encode]) n⟩

theorem false_exact_transport : ¬ ∀ h s, interpret (source h s) = target h (interpret s) := by
  intro h
  have hh := defect_nonzero
  rw [h, sub_self] at hh
  have := congrArg Prod.fst hh
  norm_num at this

/-- The discrepancy reaches the exposed output after three simultaneous steps. -/
theorem fixture_output_differs :
    (orbit (source (1/4)) (1,0,0) 3).2.2 ≠ (orbit (target (1/4)) (2,0,0) 3).2.2 := by
  have htwo : Cubic.decode 2 = 1 := by
    have hh := Cubic.decode_encode 1
    norm_num [Cubic.encode] at hh
    exact hh
  have hlt : Cubic.decode 1 < (3/4:ℝ) := by
    apply Cubic.strictMono.lt_iff_lt.mp
    rw [Cubic.encode_decode]
    norm_num [Cubic.encode]
  simp only [orbit, source_eq, target_eq]
  norm_num [htwo]
  linarith

end Examples.WiringApproximation
