import Applications.Resources.Coloring.Coloring

/-!
# Bounds from the preserved states of Color

The graph invariant bounds every mentioned neighbor, including dangling keys.
Only normalization and bit bounds enter the resource argument. Symmetry and
looplessness belong to the separate semantic correctness theorem.
-/

set_option autoImplicit false
set_option warningAsError true

namespace Resources.Coloring

open Search.PositiveTrie Numerals.PositiveArithmetic Graphs.Coloring

theorem selectRun_work_le {bits : Nat} {g : Graph} (valid : GraphValid bits g)
    (positive : 1 ≤ bits) (bound : Nat) :
    work (selectRun unitPrices bound g).2 ≤
      23 * (SparseMap.cardinal g) ^ 2 * bits ^ 2 +
        4 * SparseMap.cardinal g * degreeMass g * bits + 5 := by
  induction g using (measure SparseMap.cardinal).wf.induction with
  | h g ih =>
      by_cases empty : SparseMap.cardinal g = 0
      · have same := valid.eq_nil_of_cardinal_zero empty
        subst g
        rw [selectRun_work_none unitPrices bound .nil rfl]
        change 5 ≤ 23 * 0 ^ 2 * bits ^ 2 + 4 * 0 * degreeMass .nil * bits + 5
        simp
      · have nonempty : 1 ≤ SparseMap.cardinal g := by omega
        have square : bits ≤ bits ^ 2 := by nlinarith
        have nb := Nat.mul_le_mul_left (SparseMap.cardinal g) square
        have oneSquare : 1 ≤ bits ^ 2 := by nlinarith
        have nSquare := Nat.mul_le_mul_left (SparseMap.cardinal g) oneSquare
        simp only [Nat.mul_one] at nSquare
        have scan := eligibleRun_work_le valid positive bound
        cases chosen : KeySet.choose (eligible bound g) with
        | none =>
            have choice := choose_work_of_none (eligible_valid valid bound) chosen
            rw [selectRun_work_none unitPrices bound g chosen, choice]
            have squareVertices : SparseMap.cardinal g ≤ (SparseMap.cardinal g) ^ 2 := by nlinarith
            have term := Nat.mul_le_mul_right (bits ^ 2) squareVertices
            have degrees := Nat.mul_le_mul_right (4 * degreeMass g * bits) nonempty
            nlinarith
        | some node =>
            have present := (chosen_facts bound g chosen).1
            have key := valid.mem_bits present
            have choice := choose_work_le_of_some (eligible_valid valid bound) chosen
            have removal := removeNodeRun_work_le valid node key
            rw [← cardinal_removeNode] at removal
            have cards := cardinal_removeNode_of_mem node g present
            have tail := ih (removeNode node g) (select_terminates bound g node chosen) (valid.remove node)
            have mass := degreeMass_remove_le node g
            have massTerm := Nat.mul_le_mul_right bits
              (Nat.mul_le_mul_left (4 * SparseMap.cardinal (removeNode node g)) mass)
            have stepBound : 2 + work (eligibleRun unitPrices bound g).2 + work (choose (eligible bound g)).2 +
                work (removeNodeRun node g).2 ≤
                23 * SparseMap.cardinal g * bits ^ 2 + 4 * degreeMass g * bits := by
              nlinarith
            rw [selectRun_work_some unitPrices bound g node chosen]
            calc
              _ ≤ 23 * SparseMap.cardinal g * bits ^ 2 + 4 * degreeMass g * bits +
                  (23 * (SparseMap.cardinal (removeNode node g)) ^ 2 * bits ^ 2 +
                    4 * SparseMap.cardinal (removeNode node g) * degreeMass g * bits + 5) := by
                nlinarith
              _ ≤ _ := by
                rw [← cards]
                nlinarith [Nat.zero_le (SparseMap.cardinal (removeNode node g) * bits ^ 2)]

theorem colorsStep_work_le {nodeBits colorBits : Nat} {palette vertices : NodeSet}
    (neighborValid : SetValid nodeBits vertices) (paletteValid : SetValid colorBits palette)
    (f : Assignment) (colors : PaletteValued palette f) (key : Node)
    (member : KeySet.mem key vertices = true) (used : NodeSet) :
    work (colorsStep f key used).2 ≤ nodeBits + 2 * colorBits := by
  have lookupBound := (lookup_work_le key f).trans (neighborValid.bounded key member)
  rw [colorsStep_work]
  cases found : SparseMap.find key f with
  | none =>
      change work (lookup key f).2 + 0 ≤ nodeBits + 2 * colorBits
      omega
  | some color =>
      have colorBound := paletteValid.bounded color (colors key color found)
      change work (lookup key f).2 + 2 * bitLength color ≤ nodeBits + 2 * colorBits
      omega

theorem colorsOfRun_work_le {nodeBits colorBits : Nat} {palette vertices : NodeSet}
    (neighborValid : SetValid nodeBits vertices) (paletteValid : SetValid colorBits palette)
    (f : Assignment) (colors : PaletteValued palette f) :
    work (colorsOfRun f vertices).2 ≤
      7 * KeySet.cardinal vertices * nodeBits + 2 * KeySet.cardinal vertices * colorBits + 2 := by
  have h := run_work_le_sum (colorsStep f) (fun key => KeySet.mem key vertices = true)
    (fun _ => True) (fun _ => nodeBits + 2 * colorBits) (fun _ _ _ _ => trivial)
    (fun key used member _ => colorsStep_work_le neighborValid paletteValid f colors key member used)
    (KeySet.elements vertices) (fun key member => (KeySet.mem_elements key vertices).mp member) .nil trivial
  simp only [List.map_const', List.sum_replicate_nat, KeySet.elements_length] at h
  have nodes := neighborValid.nodes_le
  have mass := KeySet.keyMass_le_cardinal_mul vertices nodeBits neighborValid.bounded
  rw [colorsOfRun_work]
  nlinarith

theorem availableColors_cardinal_le (palette : NodeSet) (g : Graph) (key : Node) (f : Assignment) :
    KeySet.cardinal (availableColors palette g key f) ≤ KeySet.cardinal palette := by
  rw [availableColors, ← KeySet.observe_card, KeySet.observe_diff, ← KeySet.observe_card palette]
  exact Finset.card_le_card (Finset.sdiff_subset)

theorem color1Run_work_le {nodeBits colorBits : Nat} {g : Graph} {palette : NodeSet}
    (graphValid : GraphValid nodeBits g) (paletteValid : SetValid colorBits palette)
    (key : Node) (keyBound : bitLength key ≤ nodeBits) (f : Assignment) (colors : PaletteValued palette f) :
    work (color1Run palette g key f).2 ≤
      3 * nodeBits + 7 * degree g key * nodeBits + 2 * degree g key * colorBits +
        7 * KeySet.cardinal palette * colorBits + 7 := by
  have adjacency := (adjRun_work_le g key).trans (Nat.add_le_add_right keyBound 1)
  have used := colorsOfRun_work_le (graphValid.adj key) paletteValid f colors
  have diff := difference_work_le paletteValid (colorsOf f (adj g key))
  have choice := choose_work_le (availableColors_valid paletteValid g key f)
  have card := availableColors_cardinal_le palette g key f
  have choiceCard := Nat.mul_le_mul_right colorBits (Nat.mul_le_mul_left 3 card)
  rw [color1Run_work, availableColorsRun_work]
  change _ ≤ 3 * nodeBits + 7 * KeySet.cardinal (adj g key) * nodeBits +
    2 * KeySet.cardinal (adj g key) * colorBits + 7 * KeySet.cardinal palette * colorBits + 7
  split_ifs <;> nlinarith

def colorStepBound (g : Graph) (nodeBits colorBits colors : Nat) (key : Node) : Nat :=
  3 * nodeBits + 7 * degree g key * nodeBits + 2 * degree g key * colorBits + 7 * colors * colorBits + 7

theorem sum_colorStepBound (g : Graph) (nodeBits colorBits colors : Nat) (vertices : List Node) :
    (vertices.map (colorStepBound g nodeBits colorBits colors)).sum =
      3 * vertices.length * nodeBits + 7 * (vertices.map (degree g)).sum * nodeBits +
        2 * (vertices.map (degree g)).sum * colorBits + 7 * vertices.length * colors * colorBits +
        7 * vertices.length := by
  induction vertices with
  | nil => simp
  | cons key rest ih =>
      simp only [List.map_cons, List.sum_cons, List.length_cons, colorStepBound] at ih ⊢
      rw [ih]
      ring

theorem colorListRun_work_le {nodeBits colorBits : Nat} {g : Graph} {palette : NodeSet}
    (graphValid : GraphValid nodeBits g) (paletteValid : SetValid colorBits palette)
    (vertices : List Node) (bounded : ∀ key ∈ vertices, bitLength key ≤ nodeBits) :
    work (colorListRun palette g vertices).2 ≤
      3 * vertices.length * nodeBits + 7 * (vertices.map (degree g)).sum * nodeBits +
        2 * (vertices.map (degree g)).sum * colorBits +
        7 * vertices.length * KeySet.cardinal palette * colorBits + 9 * vertices.length + 2 := by
  have h := listFold_work_le_sum (color1Run palette g) (fun key => bitLength key ≤ nodeBits)
    (PaletteValued palette) (colorStepBound g nodeBits colorBits (KeySet.cardinal palette))
    (fun key f _ colors => by rw [color1Run_value]; exact paletteValued_color1 colors)
    (fun key f bound colors => color1Run_work_le graphValid paletteValid key bound f colors)
    vertices bounded .nil (paletteValued_nil palette)
  rw [sum_colorStepBound] at h
  rw [colorListRun, enter_work]
  omega

def colorPolynomial (vertices degrees nodeBits colorBits colors : Nat) : Nat :=
  vertices ^ 2 * nodeBits ^ 2 + vertices * degrees * nodeBits +
    degrees * (nodeBits + colorBits) + (vertices + 1) * colors * colorBits + vertices + 1

/-- A fixed bound on the actual supplied-input program, separate from setup and exports. -/
theorem colorRun_work_le {nodeBits colorBits : Nat} {g : Graph} {palette : NodeSet}
    (graphValid : GraphValid nodeBits g) (paletteValid : SetValid colorBits palette)
    (positiveNodes : 1 ≤ nodeBits) (positiveColors : 1 ≤ colorBits) :
    work (colorRun unitPrices palette g).2 ≤
      64 * colorPolynomial (SparseMap.cardinal g) (degreeMass g) nodeBits colorBits
        (KeySet.cardinal palette) := by
  let n := SparseMap.cardinal g
  let d := degreeMass g
  let k := KeySet.cardinal palette
  let selected := select k g
  let r := selected.length
  let neighbors := (selected.map (degree g)).sum
  have selection : work (selectRun unitPrices k g).2 ≤ 23 * n ^ 2 * nodeBits ^ 2 +
      4 * n * d * nodeBits + 5 := selectRun_work_le graphValid positiveNodes k
  have painting : work (colorListRun palette g selected).2 ≤
      3 * r * nodeBits + 7 * neighbors * nodeBits + 2 * neighbors * colorBits +
        7 * r * k * colorBits + 9 * r + 2 :=
    colorListRun_work_le graphValid paletteValid selected
      (fun _ member => graphValid.mem_bits (mem_select k g member))
  have paletteWork : work (cardinality unitPrices palette).2 ≤ 4 * k * colorBits + 1 :=
    cardinality_unit_work_le paletteValid positiveColors
  have length : r ≤ n := select_length_le_cardinal k g
  have mass : neighbors ≤ d := selected_degrees_le k g
  have rb := Nat.mul_le_mul_right nodeBits length
  have rkc := Nat.mul_le_mul_right colorBits (Nat.mul_le_mul_right k length)
  have db := Nat.mul_le_mul_right nodeBits mass
  have dc := Nat.mul_le_mul_right colorBits mass
  have core : work (colorRun unitPrices palette g).2 ≤
      23 * n ^ 2 * nodeBits ^ 2 + 4 * n * d * nodeBits + 3 * n * nodeBits +
        7 * d * nodeBits + 2 * d * colorBits + 7 * n * k * colorBits +
        4 * k * colorBits + 9 * n + 9 := by
    rw [colorRun_work]
    change 1 + work (cardinality unitPrices palette).2 + work (selectRun unitPrices k g).2 +
      work (colorListRun palette g selected).2 ≤ _
    nlinarith
  have nb : n * nodeBits ≤ n ^ 2 * nodeBits ^ 2 := by
    calc
      _ ≤ (n * nodeBits) * (n * nodeBits) := Nat.le_mul_self _
      _ = _ := by ring
  change work (colorRun unitPrices palette g).2 ≤ 64 * colorPolynomial n d nodeBits colorBits k
  unfold colorPolynomial
  nlinarith [Nat.zero_le (n ^ 2 * nodeBits ^ 2), Nat.zero_le (n * d * nodeBits),
    Nat.zero_le (d * nodeBits), Nat.zero_le (d * colorBits), Nat.zero_le (n * k * colorBits),
    Nat.zero_le (k * colorBits)]

theorem colorRun_repriced_work_le {nodeBits colorBits : Nat} {g : Graph} {palette : NodeSet}
    (graphValid : GraphValid nodeBits g) (paletteValid : SetValid colorBits palette)
    (positiveNodes : 1 ≤ nodeBits) (positiveColors : 1 ≤ colorBits) (prices : Prices) :
    work (colorRun prices palette g).2 ≤
      64 * colorPolynomial (SparseMap.cardinal g) (degreeMass g) nodeBits colorBits
        (KeySet.cardinal palette) + arithmeticTariff prices palette g := by
  have base := colorRun_work_le graphValid paletteValid positiveNodes positiveColors
  have changePrice := colorRun_reprice prices unitPrices palette g
  omega

end Resources.Coloring
