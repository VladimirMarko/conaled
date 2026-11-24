import Applications.Rendering.Response
import Mathlib.Tactic

/-! A bounded Euclidean scene observed by positive-z orthographic point rays. -/
namespace Applications.Rendering.Orthographic

abbrev Point := Fin 3 → ℚ
abbrev RGB := Fin 3 → ℚ
abbrev Layer := Response ℚ RGB

/-- Only parallel rays in the positive z direction are supported. -/
structure Ray where
  origin : Point

def Ray.direction (_ : Ray) : Point := ![0, 0, 1]
def Ray.at (r : Ray) (t : ℚ) : Point := r.origin + t • r.direction

structure Rectangle where
  depth : ℚ
  xmin : ℚ
  xmax : ℚ
  ymin : ℚ
  ymax : ℚ
  response : Layer

/-- The unique plane-intersection parameter for a supported ray. -/
def distance (s : Rectangle) (r : Ray) : ℚ := s.depth - r.origin 2

/-- Closed edges and the forward half-ray, including its origin. -/
def Hits (s : Rectangle) (r : Ray) : Prop :=
  0 ≤ distance s r ∧ s.xmin ≤ r.origin 0 ∧ r.origin 0 ≤ s.xmax ∧
    s.ymin ≤ r.origin 1 ∧ r.origin 1 ≤ s.ymax
instance (s : Rectangle) (r : Ray) : Decidable (Hits s r) := inferInstanceAs (Decidable (_ ∧ _))

theorem hits_iff_intersection (s : Rectangle) (r : Ray) :
    Hits s r ↔ ∃ t : ℚ, 0 ≤ t ∧ (r.at t) 2 = s.depth ∧
      s.xmin ≤ (r.at t) 0 ∧ (r.at t) 0 ≤ s.xmax ∧
      s.ymin ≤ (r.at t) 1 ∧ (r.at t) 1 ≤ s.ymax := by
  change (0 ≤ s.depth - r.origin 2 ∧ s.xmin ≤ r.origin 0 ∧ r.origin 0 ≤ s.xmax ∧
    s.ymin ≤ r.origin 1 ∧ r.origin 1 ≤ s.ymax) ↔ _
  simp only [Ray.at, Ray.direction, Pi.add_apply, Pi.smul_apply, smul_eq_mul]
  change _ ↔ ∃ t : ℚ, 0 ≤ t ∧ r.origin 2 + t * 1 = s.depth ∧
    s.xmin ≤ r.origin 0 + t * 0 ∧ r.origin 0 + t * 0 ≤ s.xmax ∧
    s.ymin ≤ r.origin 1 + t * 0 ∧ r.origin 1 + t * 0 ≤ s.ymax
  simp only [mul_zero, mul_one, add_zero]
  constructor
  · rintro ⟨ht, hx, hx', hy, hy'⟩
    exact ⟨s.depth - r.origin 2, ht, by ring, hx, hx', hy, hy'⟩
  · rintro ⟨t, ht, hz, hx, hx', hy, hy'⟩
    exact ⟨by linarith, hx, hx', hy, hy'⟩

def near : Rectangle := ⟨1, -1/2, 1/2, -1, 1, ⟨![1/2, 0, 0], 1/2⟩⟩
def far : Rectangle := ⟨2, -1, 1, -1, 1, ⟨![0, 1/2, 0], 0⟩⟩

def cameraOffset (k : Fin 3) : ℚ := (k.val : ℚ) / 2 - 1/2
def u (i : Fin 32) : ℚ := (2 * (i.val : ℚ) + 1) / 16 - 2
def v (j : Fin 32) : ℚ := 2 - (2 * (j.val : ℚ) + 1) / 16

def query (k : Fin 3) (j i : Fin 32) : Ray := ⟨![cameraOffset k + u i, v j, 0]⟩

/-- Sorting is justified for this camera and these depths, independent of x and y. -/
theorem fixed_order (k : Fin 3) (j i : Fin 32) :
    0 ≤ distance near (query k j i) ∧
    distance near (query k j i) < distance far (query k j i) := by
  norm_num [distance, near, far, query]

theorem near_implies_far {r : Ray} (h : Hits near r) : Hits far r := by
  rcases h with ⟨hz, hx, hx', hy, hy'⟩
  dsimp [near, distance] at hz hx hx' hy hy'
  refine ⟨?_, ?_, ?_, hy, hy'⟩ <;> dsimp [far, distance] <;> linarith

/-- Misses are the response identity, so they cannot occlude deeper layers. -/
def layer (s : Rectangle) (r : Ray) : Layer := if Hits s r then s.response else 1

def scene (r : Ray) : Layer := ([layer near r, layer far r] : List Layer).prod

def renderRay (r : Ray) : RGB := (scene r).eval 0
def pixel (k : Fin 3) (j i : Fin 32) : RGB := renderRay (query k j i)

/-- Independent region/color specification, with no response operations. -/
def pixelSpec (k : Fin 3) (j i : Fin 32) : RGB :=
  let x := cameraOffset k + u i
  let y := v j
  if -1/2 ≤ x ∧ x ≤ 1/2 ∧ -1 ≤ y ∧ y ≤ 1 then ![1/2, 1/4, 0]
  else if -1 ≤ x ∧ x ≤ 1 ∧ -1 ≤ y ∧ y ≤ 1 then ![0, 1/2, 0]
  else 0

/-- All finite response composition in the renderer passes through the shared fold law. -/
theorem renderRay_eq (r : Ray) :
    renderRay r = if Hits near r then ![1/2, 1/4, 0]
      else if Hits far r then ![0, 1/2, 0] else 0 := by
  unfold renderRay scene
  rw [Response.eval_prod]
  simp only [List.foldr_cons, List.foldr_nil]
  by_cases hn : Hits near r
  · have hf := near_implies_far hn
    simp only [layer, ite_eq_left hn, ite_eq_left hf]
    ext c
    fin_cases c <;> norm_num [near, far, Response.eval]
  · by_cases hf : Hits far r
    · simp only [layer, ite_eq_right hn, ite_eq_left hf, Response.eval_one]
      simp [far, Response.eval]
    · simp [layer, hn, hf]

theorem pixel_eq_spec (k : Fin 3) (j i : Fin 32) : pixel k j i = pixelSpec k j i := by
  rw [pixel, renderRay_eq]
  simp [pixelSpec, Hits, distance, near, far, query]

/-- RGB emission is nonnegative; scalar transmission lies in [0,1]. -/
def Admissible (r : Layer) : Prop :=
  (∀ c, 0 ≤ r.emission c) ∧ 0 ≤ r.transmission ∧ r.transmission ≤ 1

theorem admissible_one : Admissible (1 : Layer) := by
  simp [Admissible]

theorem admissible_mul {a b : Layer} (ha : Admissible a) (hb : Admissible b) :
    Admissible (a * b) := by
  refine ⟨fun c => add_nonneg (ha.1 c) (mul_nonneg ha.2.1 (hb.1 c)),
    mul_nonneg ha.2.1 hb.2.1, ?_⟩
  exact (mul_le_mul_of_nonneg_left hb.2.2 ha.2.1).trans (by simpa using ha.2.2)

theorem scene_admissible (r : Ray) : Admissible (scene r) := by
  have hn : Admissible near.response := by
    refine ⟨?_, by norm_num [near], by norm_num [near]⟩
    intro c; fin_cases c <;> norm_num [near]
  have hf : Admissible far.response := by
    refine ⟨?_, by norm_num [far], by norm_num [far]⟩
    intro c; fin_cases c <;> norm_num [far]
  have lay (s : Rectangle) (h : Admissible s.response) : Admissible (layer s r) := by
    unfold layer
    split
    · exact h
    · exact admissible_one
  simpa [scene] using admissible_mul (lay near hn) (lay far hf)

theorem pixel_bounds (k : Fin 3) (j i : Fin 32) (c : Fin 3) :
    0 ≤ pixel k j i c ∧ pixel k j i c ≤ 1 := by
  rw [pixel_eq_spec]
  unfold pixelSpec
  split
  · fin_cases c <;> norm_num
  · split
    · fin_cases c <;> norm_num
    · simp

/-- Outer index is the top-to-bottom row, inner index the left-to-right column. -/
def frame (k : Fin 3) : Array (Array RGB) := Array.ofFn fun j => Array.ofFn fun i => pixel k j i

@[simp] theorem frame_size (k : Fin 3) : (frame k).size = 32 := by simp [frame]
@[simp] theorem frame_row_size (k : Fin 3) (j : Fin 32) :
    ((frame k)[j.val]'(by simp)).size = 32 := by simp [frame]

theorem frame_get (k : Fin 3) (j i : Fin 32) :
    (((frame k)[j.val]'(by simp))[i.val]'(by simp)) = pixelSpec k j i := by
  simp [frame, pixel_eq_spec]

end Applications.Rendering.Orthographic
