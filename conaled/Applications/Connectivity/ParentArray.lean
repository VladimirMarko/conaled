import Std

set_option autoImplicit false
set_option warningAsError true

/-! Concrete ParentArray proofs adapted from adwh-checkpoint-233.
Source members and declaration dispositions: docs/research/adwh-connectivity-provenance.tsv.
Operations retain the source failure and representative-selection behavior. -/

namespace Connectivity.ParentArray

abbrev Vertex := Int
abbrev Name := Int
abbrev Size := Int

structure DSA where
  namesA : Array Vertex
  sizesA : Array Size
  deriving DecidableEq, Repr

def readCell (a : Array Int) (v : Int) : Option Int :=
  if 0 < v then a[v.toNat - 1]? else none

def writeCell (a : Array Int) (v : Int) (x : Int) : Option (Array Int) :=
  if 0 < v ∧ v.toNat ≤ a.size then
    some (a.setIfInBounds (v.toNat - 1) x)
  else none

def startDSA (n : Int) : DSA :=
  ⟨Array.ofFn (fun i : Fin n.toNat => (Int.ofNat (i.val + 1))),
   Array.replicate n.toNat 1⟩

def unionDSA (n1 n2 : Name) (ds : DSA) : Option DSA := do
  let s1 ← readCell ds.sizesA n1
  let s2 ← readCell ds.sizesA n2
  if s1 < s2 then
    let ns ← writeCell ds.namesA n1 n2
    let ss ← writeCell ds.sizesA n2 (s1 + s2)
    pure ⟨ns, ss⟩
  else
    let ns ← writeCell ds.namesA n2 n1
    let ss ← writeCell ds.sizesA n1 (s1 + s2)
    pure ⟨ns, ss⟩

def chase (ds : DSA) : Nat → Vertex → Option Name
  | 0, _ => none
  | fuel + 1, v =>
    match readCell ds.namesA v with
    | none => none
    | some p => if p = v then some v else chase ds fuel p

def findDSA (ds : DSA) (v : Vertex) : Option Name :=
  chase ds ds.namesA.size v

inductive RootSteps (ds : DSA) : Vertex → Name → Nat → Prop where
  | root {r : Name} (read : readCell ds.namesA r = some r) :
      RootSteps ds r r 0
  | step {v p r : Int} {k : Nat}
      (read : readCell ds.namesA v = some p) (nonself : p ≠ v)
      (tail : RootSteps ds p r k) : RootSteps ds v r (k + 1)

end Connectivity.ParentArray

namespace Connectivity.ParentArray

/-! One-based helper contracts. These apply to arbitrary finite arrays. -/

theorem readCell_nonpositive (a : Array Int) (v : Int) (hv : v ≤ 0) :
    readCell a v = none := by
  simp [readCell, show ¬ 0 < v by omega]

theorem readCell_positive (a : Array Int) (v : Int) (hv : 0 < v) :
    readCell a v = a[v.toNat - 1]? := by
  simp [readCell, hv]

theorem readCell_nat_succ (a : Array Int) (i : Nat) :
    readCell a (Int.ofNat (i + 1)) = a[i]? := by
  simp [readCell]

theorem readCell_none_iff (a : Array Int) (v : Int) :
    readCell a v = none ↔ v ≤ 0 ∨ a.size < v.toNat := by
  by_cases hv : 0 < v
  · rw [readCell_positive a v hv, Array.getElem?_eq_none_iff]
    omega
  · rw [readCell_nonpositive a v (by omega)]
    simp only [true_iff]
    exact Or.inl (by omega)

theorem readCell_some_iff (a : Array Int) (v x : Int) :
    readCell a v = some x ↔
      0 < v ∧ ∃ h : v.toNat - 1 < a.size, a[v.toNat - 1]'h = x := by
  by_cases hv : 0 < v
  · rw [readCell_positive a v hv, Array.getElem?_eq_some_iff]
    simp [hv]
  · simp [readCell, hv]

theorem writeCell_valid (a : Array Int) (v x : Int)
    (hv : 0 < v) (hb : v.toNat ≤ a.size) :
    writeCell a v x = some (a.setIfInBounds (v.toNat - 1) x) := by
  simp [writeCell, hv, hb]

theorem writeCell_none_iff (a : Array Int) (v x : Int) :
    writeCell a v x = none ↔ ¬ (0 < v ∧ v.toNat ≤ a.size) := by
  simp [writeCell]

theorem writeCell_some_iff (a out : Array Int) (v x : Int) :
    writeCell a v x = some out ↔
      0 < v ∧ v.toNat ≤ a.size ∧ out = a.setIfInBounds (v.toNat - 1) x := by
  constructor
  · intro h
    unfold writeCell at h
    split at h
    · rename_i hv
      exact ⟨hv.1, hv.2, (Option.some.inj h).symm⟩
    · cases h
  · rintro ⟨hv, hb, rfl⟩
    exact writeCell_valid a v x hv hb

theorem writeCell_size {a out : Array Int} {v x : Int}
    (h : writeCell a v x = some out) : out.size = a.size := by
  obtain ⟨_, _, rfl⟩ := (writeCell_some_iff a out v x).mp h
  simp

theorem writeCell_read_self {a out : Array Int} {v x : Int}
    (h : writeCell a v x = some out) : readCell out v = some x := by
  obtain ⟨hv, hb, rfl⟩ := (writeCell_some_iff a out v x).mp h
  have hi : v.toNat - 1 < a.size := by omega
  simp [readCell, hv, Array.getElem?_setIfInBounds_self_of_lt hi]

theorem writeCell_read_other {a out : Array Int} {v x w : Int}
    (h : writeCell a v x = some out) (hw : w ≠ v) :
    readCell out w = readCell a w := by
  obtain ⟨hv, _, rfl⟩ := (writeCell_some_iff a out v x).mp h
  by_cases hp : 0 < w
  · have hi : v.toNat - 1 ≠ w.toNat - 1 := by omega
    simp [readCell, hp, Array.getElem?_setIfInBounds_ne hi]
  · simp [readCell, hp]

/-! Initializer: identity parents and cached ones, with signed-bound extension. -/

theorem startDSA_sizes (n : Int) :
    (startDSA n).namesA.size = n.toNat ∧ (startDSA n).sizesA.size = n.toNat := by
  simp [startDSA]

theorem startDSA_parent (n v : Int) (hv : 0 < v) (hn : v ≤ n) :
    readCell (startDSA n).namesA v = some v := by
  have hb : v.toNat - 1 < n.toNat := by omega
  have he : Int.ofNat (v.toNat - 1 + 1) = v := by
    rw [Nat.sub_add_cancel (show 1 ≤ v.toNat by omega)]
    exact Int.toNat_of_nonneg (by omega)
  simpa [readCell, startDSA, hv, Array.getElem?_ofFn, hb] using congrArg some he

theorem startDSA_cache (n v : Int) (hv : 0 < v) (hn : v ≤ n) :
    readCell (startDSA n).sizesA v = some 1 := by
  have hb : v.toNat - 1 < n.toNat := by omega
  simp [readCell, startDSA, hv, hb]

theorem startDSA_nonpositive (n : Int) (hn : n ≤ 0) :
    startDSA n = ⟨#[], #[]⟩ := by
  simp [startDSA, Int.toNat_of_nonpos hn]

/-! Literal union branches retain both old-size reads and partial helper calls. -/

theorem unionDSA_of_lt (ds : DSA) (n1 n2 s1 s2 : Int)
    (h1 : readCell ds.sizesA n1 = some s1) (h2 : readCell ds.sizesA n2 = some s2)
    (hlt : s1 < s2) :
    unionDSA n1 n2 ds = (do
      let ns ← writeCell ds.namesA n1 n2
      let ss ← writeCell ds.sizesA n2 (s1 + s2)
      pure ⟨ns, ss⟩) := by
  simp [unionDSA, h1, h2, hlt]

theorem unionDSA_of_not_lt (ds : DSA) (n1 n2 s1 s2 : Int)
    (h1 : readCell ds.sizesA n1 = some s1) (h2 : readCell ds.sizesA n2 = some s2)
    (hlt : ¬ s1 < s2) :
    unionDSA n1 n2 ds = (do
      let ns ← writeCell ds.namesA n2 n1
      let ss ← writeCell ds.sizesA n1 (s1 + s2)
      pure ⟨ns, ss⟩) := by
  simp [unionDSA, h1, h2, hlt]

theorem unionDSA_first_read_failure (ds : DSA) (n1 n2 : Int)
    (h : readCell ds.sizesA n1 = none) : unionDSA n1 n2 ds = none := by
  simp [unionDSA, h]

theorem unionDSA_second_read_failure (ds : DSA) (n1 n2 : Int)
    (h : readCell ds.sizesA n2 = none) : unionDSA n1 n2 ds = none := by
  cases hr : readCell ds.sizesA n1 <;> simp [unionDSA, hr, h]

theorem unionDSA_sizes {ds out : DSA} {n1 n2 : Int}
    (hu : unionDSA n1 n2 ds = some out) :
    out.namesA.size = ds.namesA.size ∧ out.sizesA.size = ds.sizesA.size := by
  cases h1 : readCell ds.sizesA n1 with
  | none => simp [unionDSA, h1] at hu
  | some s1 =>
      cases h2 : readCell ds.sizesA n2 with
      | none => simp [unionDSA, h1, h2] at hu
      | some s2 =>
          by_cases hlt : s1 < s2
          · rw [unionDSA_of_lt ds n1 n2 s1 s2 h1 h2 hlt] at hu
            cases hn : writeCell ds.namesA n1 n2 with
            | none => simp [hn] at hu
            | some ns =>
                cases hs : writeCell ds.sizesA n2 (s1 + s2) with
                | none => simp [hn, hs] at hu
                | some ss =>
                    simp only [hn, hs, pure] at hu
                    cases hu
                    exact ⟨writeCell_size hn, writeCell_size hs⟩
          · rw [unionDSA_of_not_lt ds n1 n2 s1 s2 h1 h2 hlt] at hu
            cases hn : writeCell ds.namesA n2 n1 with
            | none => simp [hn] at hu
            | some ns =>
                cases hs : writeCell ds.sizesA n1 (s1 + s2) with
                | none => simp [hn, hs] at hu
                | some ss =>
                    simp only [hn, hs, pure] at hu
                    cases hu
                    exact ⟨writeCell_size hn, writeCell_size hs⟩

end Connectivity.ParentArray

namespace Connectivity.ParentArray

/-! Independent path and raw chase theory.
No forest invariant or complete valid-input execution is assumed implicitly.
-/

theorem chase_zero (ds : DSA) (v : Vertex) : chase ds 0 v = none := rfl

theorem chase_succ (ds : DSA) (fuel : Nat) (v : Vertex) :
    chase ds (fuel + 1) v =
      match readCell ds.namesA v with
      | none => none
      | some p => if p = v then some v else chase ds fuel p := rfl

theorem findDSA_eq_chase (ds : DSA) (v : Vertex) :
    findDSA ds v = chase ds ds.namesA.size v := rfl

theorem rootSteps_chase {ds : DSA} {v r : Int} {k fuel : Nat}
    (path : RootSteps ds v r k) (enough : k < fuel) :
    chase ds fuel v = some r := by
  induction path generalizing fuel with
  | root read =>
      cases fuel with
      | zero => omega
      | succ fuel => simp [chase, read]
  | step read nonself tail ih =>
      cases fuel with
      | zero => omega
      | succ fuel =>
          simp only [chase, read, nonself, ↓reduceIte]
          exact ih (by omega)

theorem chase_some_rootSteps {ds : DSA} {fuel : Nat} {v r : Int}
    (success : chase ds fuel v = some r) :
    ∃ k, RootSteps ds v r k ∧ k < fuel := by
  induction fuel generalizing v with
  | zero => simp [chase] at success
  | succ fuel ih =>
      cases read : readCell ds.namesA v with
      | none => simp [chase, read] at success
      | some p =>
          by_cases self : p = v
          · subst p
            have endpoint : v = r := by simpa [chase, read] using success
            subst r
            exact ⟨0, .root read, Nat.zero_lt_succ _⟩
          · have tailSuccess : chase ds fuel p = some r := by
              simpa [chase, read, self] using success
            obtain ⟨k, path, shorter⟩ := ih tailSuccess
            exact ⟨k + 1, .step read self path, by omega⟩

theorem chase_some_iff_rootSteps (ds : DSA) (fuel : Nat) (v r : Int) :
    chase ds fuel v = some r ↔ ∃ k, RootSteps ds v r k ∧ k < fuel := by
  constructor
  · exact chase_some_rootSteps
  · rintro ⟨k, path, enough⟩
    exact rootSteps_chase path enough

theorem RootSteps.unique {ds : DSA} {v r₁ r₂ : Int} {k₁ k₂ : Nat}
    (first : RootSteps ds v r₁ k₁) (second : RootSteps ds v r₂ k₂) :
    r₁ = r₂ ∧ k₁ = k₂ := by
  induction first generalizing r₂ k₂ with
  | root read =>
      cases second with
      | root _ => exact ⟨rfl, rfl⟩
      | step read₂ nonself₂ _ =>
          exact False.elim (nonself₂ (Option.some.inj (read₂.symm.trans read)))
  | step read nonself tail ih =>
      cases second with
      | root read₂ =>
          exact False.elim (nonself (Option.some.inj (read.symm.trans read₂)))
      | step read₂ _ tail₂ =>
          have parentEq := Option.some.inj (read.symm.trans read₂)
          subst_vars
          obtain ⟨endpoint, length⟩ := ih tail₂
          exact ⟨endpoint, congrArg Nat.succ length⟩

theorem rootSteps_fuel_insufficient {ds : DSA} {v r : Int} {k fuel : Nat}
    (path : RootSteps ds v r k) (short : fuel ≤ k) :
    chase ds fuel v = none := by
  cases result : chase ds fuel v with
  | none => rfl
  | some other =>
      obtain ⟨j, otherPath, enough⟩ := chase_some_rootSteps result
      have lengths := (path.unique otherPath).2
      omega

theorem rootSteps_exact_fuel_boundary {ds : DSA} {v r : Int} {k : Nat}
    (path : RootSteps ds v r k) :
    chase ds k v = none ∧ chase ds (k + 1) v = some r :=
  ⟨rootSteps_fuel_insufficient path (Nat.le_refl _),
   rootSteps_chase path (Nat.lt_succ_self _)⟩

theorem chase_success_mono {ds : DSA} {v r : Int} {fuel larger : Nat}
    (success : chase ds fuel v = some r) (increase : fuel ≤ larger) :
    chase ds larger v = some r := by
  obtain ⟨k, path, enough⟩ := chase_some_rootSteps success
  exact rootSteps_chase path (by omega)

theorem findDSA_some_iff_rootSteps (ds : DSA) (v r : Int) :
    findDSA ds v = some r ↔
      ∃ k, RootSteps ds v r k ∧ k < ds.namesA.size :=
  chase_some_iff_rootSteps ds ds.namesA.size v r

theorem findDSA_source_recurrence {ds : DSA} {v r : Int} {k : Nat}
    (path : RootSteps ds v r k) (withinCapacity : k < ds.namesA.size) :
    findDSA ds v =
      match readCell ds.namesA v with
      | none => none
      | some p => if p = v then some v else findDSA ds p := by
  have success : findDSA ds v = some r := rootSteps_chase path withinCapacity
  rw [success]
  cases path with
  | root read => simp [read]
  | step read nonself tail =>
      have tailSuccess : findDSA ds _ = some r := rootSteps_chase tail (by omega)
      simp [read, nonself, tailSuccess]

theorem chase_parent_arrays {ds₁ ds₂ : DSA} (same : ds₁.namesA = ds₂.namesA)
    (fuel : Nat) (v : Int) : chase ds₁ fuel v = chase ds₂ fuel v := by
  induction fuel generalizing v with
  | zero => rfl
  | succ fuel ih => simp [chase, same, ih]

theorem findDSA_parent_arrays {ds₁ ds₂ : DSA} (same : ds₁.namesA = ds₂.namesA)
    (v : Int) : findDSA ds₁ v = findDSA ds₂ v := by
  simpa only [findDSA, same] using chase_parent_arrays same ds₂.namesA.size v

end Connectivity.ParentArray
