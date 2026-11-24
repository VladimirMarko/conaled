import Applications.Rendering.Orthographic
import Mathlib.Data.Rat.Floor

/-! Quantization and pure P3 presentation. Filesystem effects live in the driver. -/
namespace Applications.Rendering.PPM
open Orthographic

/-- Saturation precedes quantization; error is measured against this clamped value. -/
def clamp (x : ℚ) : ℚ := max 0 (min 1 x)
def encode (x : ℚ) : ℤ := ⌊255 * clamp x⌋
def decode (n : ℤ) : ℚ := (n : ℚ) / 255

theorem clamp_bounds (x : ℚ) : 0 ≤ clamp x ∧ clamp x ≤ 1 := by
  constructor
  · exact le_max_left _ _
  · exact max_le (by norm_num) (min_le_left _ _)

theorem clamp_of_nonpos {x : ℚ} (h : x ≤ 0) : clamp x = 0 := by
  exact max_eq_left ((min_le_right _ _).trans h)

theorem clamp_of_one_le {x : ℚ} (h : 1 ≤ x) : clamp x = 1 := by
  simp [clamp, min_eq_left h]

theorem clamp_of_unit {x : ℚ} (h : 0 ≤ x ∧ x ≤ 1) : clamp x = x := by
  simp [clamp, min_eq_right h.2, max_eq_right h.1]

theorem encode_bounds (x : ℚ) : 0 ≤ encode x ∧ encode x ≤ 255 := by
  have hc := clamp_bounds x
  constructor
  · exact Int.floor_nonneg.mpr (mul_nonneg (by norm_num) hc.1)
  · have h := Int.floor_le (255 * clamp x)
    have : (encode x : ℚ) ≤ 255 := by dsimp [encode]; linarith
    exact_mod_cast this

theorem encode_of_nonpos {x : ℚ} (h : x ≤ 0) : encode x = 0 := by
  simp [encode, clamp_of_nonpos h]

theorem encode_of_one_le {x : ℚ} (h : 1 ≤ x) : encode x = 255 := by
  norm_num [encode, clamp_of_one_le h]

/-- Floor rounds down, with an error strictly smaller than one output step. -/
theorem quantization_error (x : ℚ) :
    0 ≤ clamp x - decode (encode x) ∧ clamp x - decode (encode x) < 1/255 := by
  have hlo := Int.floor_le (255 * clamp x)
  have hhi := Int.lt_floor_add_one (255 * clamp x)
  dsimp [decode, encode]
  constructor <;> linarith

theorem quantization_abs_error (x : ℚ) :
    |decode (encode x) - clamp x| ≤ 1/255 := by
  have h := quantization_error x
  rw [abs_of_nonpos (by linarith : decode (encode x) - clamp x ≤ 0)]
  linarith

theorem scene_error (k : Fin 3) (j i : Fin 32) (c : Fin 3) :
    |decode (encode (pixel k j i c)) - pixel k j i c| ≤ 1/255 := by
  simpa [clamp_of_unit (pixel_bounds k j i c)] using quantization_abs_error (pixel k j i c)

abbrev EncodedRGB := Fin 3 → ℤ

def encodeRGB (p : RGB) : EncodedRGB := fun c => encode (p c)
def encodedFrame (k : Fin 3) : Array (Array EncodedRGB) :=
  (frame k).map (fun row => row.map encodeRGB)

@[simp] theorem encodedFrame_size (k : Fin 3) : (encodedFrame k).size = 32 := by
  simp [encodedFrame, frame]
@[simp] theorem encodedFrame_row_size (k : Fin 3) (j : Fin 32) :
    ((encodedFrame k)[j.val]'(by simp)).size = 32 := by
  simp [encodedFrame, frame]

theorem encodedFrame_get (k : Fin 3) (j i : Fin 32) (c : Fin 3) :
    (((encodedFrame k)[j.val]'(by simp))[i.val]'(by simp)) c =
      encode (pixelSpec k j i c) := by
  have h : (((encodedFrame k)[j.val]'(by simp))[i.val]'(by simp)) =
      encodeRGB (pixel k j i) := by simp [encodedFrame, frame]
  rw [h]
  simp [encodeRGB, pixel_eq_spec]


/-- One pixel per line, RGB order; whitespace still specifies ordinary P3 raster order. -/
def pixelText (p : EncodedRGB) : String := s!"{p 0} {p 1} {p 2}\n"
def rowText (row : Array EncodedRGB) : String :=
  String.join (row.toList.map pixelText)
def rasterText (rows : Array (Array EncodedRGB)) : String :=
  String.join (rows.toList.map rowText)
def frameText (k : Fin 3) : String :=
  "P3\n32 32\n255\n" ++ rasterText (encodedFrame k)


end Applications.Rendering.PPM
