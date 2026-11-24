import Applications.Rendering.PPM

/-! Worked point observations, geometric controls, and presentation fixtures. -/
namespace Examples.OrthographicRendering
open Applications.Rendering Applications.Rendering.Orthographic Applications.Rendering.PPM

theorem camera_sequence : (List.finRange 3).map cameraOffset = [-1/2, 0, 1/2] := by
  norm_num [List.finRange, cameraOffset]

theorem grid_corners :
    (query 1 0 0).origin = ![-31/16, 31/16, 0] ∧
    (query 1 31 31).origin = ![31/16, -31/16, 0] := by
  constructor <;> ext c <;> fin_cases c <;> norm_num [query, cameraOffset, u, v]

/-- Increasing row number moves down the image in world y. -/
theorem rows_descend {j j' : Fin 32} (h : j < j') : v j' < v j := by
  have hq : (j.val : ℚ) < j'.val := by exact_mod_cast h
  dsimp [v]
  linarith

theorem boundary_hits :
    Hits near ⟨![-1/2, -1, 0]⟩ ∧ Hits near ⟨![1/2, 1, 0]⟩ ∧
    Hits far ⟨![-1, -1, 0]⟩ ∧ Hits far ⟨![1, 1, 0]⟩ ∧
    Hits near ⟨![0, 0, 1]⟩ := by
  norm_num [Hits, distance, near, far]

theorem outside_misses :
    ¬ Hits near ⟨![9/16, 0, 0]⟩ ∧ ¬ Hits far ⟨![17/16, 0, 0]⟩ ∧
    ¬ Hits far ⟨![0, 17/16, 0]⟩ ∧ ¬ Hits near ⟨![0, 0, 3]⟩ := by
  norm_num [Hits, distance, near, far]

theorem no_near_only (r : Ray) : ¬ (Hits near r ∧ ¬ Hits far r) :=
  fun h => h.2 (near_implies_far h.1)

theorem overlap_premises : Hits near (query 1 16 16) ∧ Hits far (query 1 16 16) := by
  norm_num [Hits, distance, near, far, query, cameraOffset, u, v]

theorem far_only_premises : ¬ Hits near (query 1 16 8) ∧ Hits far (query 1 16 8) := by
  norm_num [Hits, distance, near, far, query, cameraOffset, u, v]

theorem black_premises : ¬ Hits near (query 1 0 0) ∧ ¬ Hits far (query 1 0 0) := by
  norm_num [Hits, distance, near, far, query, cameraOffset, u, v]

theorem overlap : pixel 1 16 16 = ![1/2, 1/4, 0] := by
  rw [pixel_eq_spec]
  norm_num [pixelSpec, cameraOffset, u, v]

theorem far_only : pixel 1 16 8 = ![0, 1/2, 0] := by
  rw [pixel_eq_spec]
  norm_num [pixelSpec, cameraOffset, u, v]

theorem black_background : pixel 1 0 0 = 0 := by
  rw [pixel_eq_spec]
  norm_num [pixelSpec, cameraOffset, u, v]

/-- The same pixel changes from background to the newly exposed far rectangle. -/
theorem camera_changes_pixel : pixel 0 16 8 = 0 ∧ pixel 1 16 8 = ![0, 1/2, 0] ∧
    pixel 0 16 8 ≠ pixel 1 16 8 := by
  have h0 : pixel 0 16 8 = 0 := by
    rw [pixel_eq_spec]
    norm_num [pixelSpec, cameraOffset, u, v]
  refine ⟨h0, far_only, ?_⟩
  rw [h0, far_only]
  intro h
  have := congrFun h 1
  norm_num at this

theorem overlap_encoded : encodeRGB (pixel 1 16 16) = ![127, 63, 0] := by
  rw [overlap]
  ext c
  fin_cases c <;> norm_num [encodeRGB, encode, clamp]

theorem saturation_controls : encode (-1) = 0 ∧ encode 2 = 255 ∧
    decode (encode (1/2)) = 127/255 := by norm_num [encode, decode, clamp]

/-- The bound cannot be extended to an unclamped out-of-range channel. -/
theorem unclamped_control : ¬ |decode (encode 2) - 2| ≤ 1/255 := by norm_num [encode, decode, clamp]

/-- Deliberately asymmetric fixture detects reversed rows, columns, and RGB channels. -/
def asymmetricRaster : Array (Array EncodedRGB) :=
  #[#[![255, 0, 0], ![0, 255, 0]], #[![0, 0, 255], ![1, 2, 3]]]

theorem asymmetric_serialization : rasterText asymmetricRaster =
    "255 0 0\n0 255 0\n0 0 255\n1 2 3\n" := by decide

theorem overlap_serialization : pixelText (encodeRGB (pixel 1 16 16)) = "127 63 0\n" := by
  rw [overlap_encoded]
  decide

end Examples.OrthographicRendering
