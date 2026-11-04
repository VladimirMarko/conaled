import Applications.Sequences.LCA.WordKey

/-! Bounded depth keys and their finite-word table interpretation. -/
namespace Sequences.LCA.WordKey

abbrev Cell (offset : Int) (heights stride : Nat) :=
  {k : Int ×ₗ Nat // 0 ≤ (ofLex k).1 + offset ∧
    (ofLex k).1 + offset < (heights : Int) ∧ (ofLex k).2 < stride}

def cellWord (k : Cell offset heights stride) : Fin (heights * stride) :=
  ⟨encode offset stride (ofLex k.val).1 (ofLex k.val).2,
    encode_lt_capacity k.property.2.2 (by have := k.property; omega)⟩

theorem cellWord_le_iff (a b : Cell offset heights stride) :
    cellWord a ≤ cellWord b ↔ a ≤ b := by
  exact encode_le_iff a.property.1 b.property.1 a.property.2.2 b.property.2.2

theorem cellWord_min (a b : Cell offset heights stride) :
    cellWord (min a b) = min (cellWord a) (cellWord b) := by
  by_cases h : a ≤ b
  · rw [min_eq_left h, min_eq_left ((cellWord_le_iff a b).2 h)]
  · have h' : b ≤ a := le_of_not_ge h
    rw [min_eq_right h', min_eq_right ((cellWord_le_iff b a).2 h')]

/-- Encoding preserves exact identity, including the leftmost tie index. -/
theorem cellWord_injective : Function.Injective (@cellWord offset heights stride) := by
  intro a b h
  apply le_antisymm
  · exact (cellWord_le_iff a b).1 (le_of_eq h)
  · exact (cellWord_le_iff b a).1 (le_of_eq h.symm)

def encodeStore (cells : Vector (Cell offset heights stride) n) :
    Vector (Fin (heights * stride)) n := cells.map cellWord

@[simp] theorem encodeStore_read (cells : Vector (Cell offset heights stride) n)
    (i : Fin n) : (encodeStore cells)[i.val] = cellWord cells[i.val] := by
  simp [encodeStore]

theorem encodeStore_write (cells : Vector (Cell offset heights stride) n)
    (i : Fin n) (value : Cell offset heights stride) :
    encodeStore (cells.set i.val value) = (encodeStore cells).set i.val (cellWord value) := by
  simp [encodeStore, Vector.map_set]

theorem encodeStore_read_min (cells : Vector (Cell offset heights stride) n)
    (i j : Fin n) :
    min (encodeStore cells)[i.val] (encodeStore cells)[j.val] =
      cellWord (min cells[i.val] cells[j.val]) := by
  rw [encodeStore_read, encodeStore_read, cellWord_min]

/-- Both arithmetic intermediates of packing fit whenever the resulting word
fits. This includes the multiplication before the final index addition. -/
theorem packing_intermediates (k : Cell offset heights stride)
    (hw : heights * stride ≤ 2^width) :
    ((ofLex k.val).1 + offset).toNat * stride < 2^width ∧
    (ofLex k.val).2 < 2^width ∧ (cellWord k).val < 2^width := by
  have h := (cellWord k).isLt.trans_le hw
  change encode offset stride (ofLex k.val).1 (ofLex k.val).2 < 2^width at h
  unfold encode pack at h
  change _ ∧ _ ∧ encode offset stride (ofLex k.val).1 (ofLex k.val).2 < _
  unfold encode pack
  omega

/-- Bare-key version for composing packed execution without changing the
semantic table's element type. Bounds concern both operands, including ties. -/
theorem encode_min {a b : Int ×ₗ Nat}
    (ha : 0 ≤ (ofLex a).1 + offset) (hb : 0 ≤ (ofLex b).1 + offset)
    (hi : (ofLex a).2 < stride) (hj : (ofLex b).2 < stride) :
    encode offset stride (ofLex (min a b)).1 (ofLex (min a b)).2 =
      min (encode offset stride (ofLex a).1 (ofLex a).2)
        (encode offset stride (ofLex b).1 (ofLex b).2) := by
  have horder : encode offset stride (ofLex a).1 (ofLex a).2 ≤
      encode offset stride (ofLex b).1 (ofLex b).2 ↔ a ≤ b :=
    encode_le_iff ha hb hi hj
  by_cases h : a ≤ b
  · rw [min_eq_left h, min_eq_left (horder.2 h)]
  · have h' : b ≤ a := le_of_not_ge h
    have hp : encode offset stride (ofLex b).1 (ofLex b).2 ≤
        encode offset stride (ofLex a).1 (ofLex a).2 := by
      have hr := encode_le_iff hb ha hj hi
      exact hr.2 h'
    rw [min_eq_right h', min_eq_right hp]

theorem encoded_min_index {a b : Int ×ₗ Nat}
    (ha : 0 ≤ (ofLex a).1 + offset) (hb : 0 ≤ (ofLex b).1 + offset)
    (hi : (ofLex a).2 < stride) (hj : (ofLex b).2 < stride) :
    min (encode offset stride (ofLex a).1 (ofLex a).2)
      (encode offset stride (ofLex b).1 (ofLex b).2) % stride =
      (ofLex (min a b)).2 := by
  rw [← encode_min ha hb hi hj]
  unfold encode
  apply pack_mod
  by_cases h : a ≤ b
  · simpa only [min_eq_left h] using hi
  · simpa only [min_eq_right (le_of_not_ge h)] using hj

example : min (encode 2 4 (-1) 3) (encode 2 4 (-1) 1) % 4 = 1 := by
  rw [encoded_min_index (offset := 2) (stride := 4) (a := toLex (-1,3)) (b := toLex (-1,1))
    (by decide) (by decide) (by decide) (by decide)]
  decide

private def early : Cell 2 4 4 := ⟨toLex (-1,1), by decide⟩
private def late : Cell 2 4 4 := ⟨toLex (-1,3), by decide⟩

/-- Equal depths select index 1, whose encoded word is 5. -/
example : cellWord (min late early) = ⟨5, by decide⟩ := by
  rw [cellWord_min]
  decide

/-- Overwriting a later tied key preserves the observed leftmost answer. -/
example :
    min (encodeStore ((#v[late,late]).set 0 early))[0]
      (encodeStore ((#v[late,late]).set 0 early))[1] = ⟨5, by decide⟩ := by
  rw [encodeStore_write _ ⟨0,by decide⟩ early]
  simp [encodeStore, cellWord, early, late, encode, pack]

example : ((ofLex early.val).1 + 2).toNat * 4 < 2^4 ∧
    (ofLex early.val).2 < 2^4 ∧ (cellWord early).val < 2^4 :=
  packing_intermediates early (by decide)

end Sequences.LCA.WordKey
