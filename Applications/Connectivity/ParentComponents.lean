import Applications.Connectivity.ParentForest

set_option autoImplicit false
set_option warningAsError true

/-! Concrete ParentComponents proofs adapted from adwh-checkpoint-233.
Source members and declaration dispositions: docs/research/adwh-connectivity-provenance.tsv.
Operations retain the source failure and representative-selection behavior. -/

namespace Connectivity.ParentComponents

open ParentArray ParentForest

def vertexUniverse (ds : DSA) : List Int :=
  (List.range (capacity ds)).map (fun i => Int.ofNat (i + 1))

noncomputable def componentVertices (ds : DSA) (r : Int) : List Int := by
  classical
  exact (vertexUniverse ds).filter (fun v => decide (Root ds v r))

noncomputable def componentCard (ds : DSA) (r : Int) : Nat :=
  (componentVertices ds r).length

def RootSizesExact (ds : DSA) : Prop :=
  ∀ r, SelfRoot ds r → cache ds r = Int.ofNat (componentCard ds r)

def SameComponent (ds : DSA) (u v : Int) : Prop :=
  ∃ r, Root ds u r ∧ Root ds v r

theorem mem_vertexUniverse (ds : DSA) (v : Int) :
    v ∈ vertexUniverse ds ↔ Valid ds v := by
  constructor
  · intro hv
    obtain ⟨i, hi, rfl⟩ := List.mem_map.mp hv
    have hlt := List.mem_range.mp hi
    change (0 : Int) < (i : Int) + 1 ∧ i + 1 ≤ capacity ds
    omega
  · intro hv
    apply List.mem_map.mpr
    refine ⟨(v - 1).toNat, List.mem_range.mpr ?_, ?_⟩
    · unfold Valid at hv
      omega
    · change ((v - 1).toNat : Int) + 1 = v
      unfold Valid at hv
      omega

theorem vertexUniverse_length (ds : DSA) :
    (vertexUniverse ds).length = capacity ds := by
  simp [vertexUniverse]

theorem vertexUniverse_nodup (ds : DSA) : (vertexUniverse ds).Nodup := by
  apply List.Pairwise.map (fun i : Nat => Int.ofNat (i + 1)) ?_ List.nodup_range
  intro a b hab he
  exact hab (Nat.add_right_cancel (Int.ofNat.inj he))

theorem mem_componentVertices (ds : DSA) (v r : Int) :
    v ∈ componentVertices ds r ↔ Valid ds v ∧ Root ds v r := by
  classical
  simp [componentVertices, mem_vertexUniverse]

theorem componentVertices_nodup (ds : DSA) (r : Int) :
    (componentVertices ds r).Nodup := by
  classical
  exact List.Pairwise.filter _ (vertexUniverse_nodup ds)

theorem componentVertices_subset (ds : DSA) (r : Int) :
    componentVertices ds r ⊆ vertexUniverse ds := by
  intro v hv
  exact (mem_vertexUniverse ds v).mpr ((mem_componentVertices ds v r).mp hv).1

theorem componentVertices_disjoint (ds : DSA) (r s : Int) (hne : r ≠ s) :
    ∀ v, v ∈ componentVertices ds r → v ∉ componentVertices ds s := by
  intro v hr hs
  have hvr := ((mem_componentVertices ds v r).mp hr).2
  have hvs := ((mem_componentVertices ds v s).mp hs).2
  exact hne (hvr.unique hvs)

theorem componentVertices_append_nodup (ds : DSA) (r s : Int) (hne : r ≠ s) :
    (componentVertices ds r ++ componentVertices ds s).Nodup := by
  apply List.nodup_append.mpr
  refine ⟨componentVertices_nodup ds r, componentVertices_nodup ds s, ?_⟩
  intro v hv w hw he
  subst w
  exact componentVertices_disjoint ds r s hne v hv hw

theorem componentCard_le_capacity (ds : DSA) (r : Int) :
    componentCard ds r ≤ capacity ds := by
  have h := (componentVertices_nodup ds r).length_le_of_subset
    (componentVertices_subset ds r)
  simpa only [vertexUniverse_length, componentCard] using h

theorem componentCard_add_le_capacity (ds : DSA) (r s : Int) (hne : r ≠ s) :
    componentCard ds r + componentCard ds s ≤ capacity ds := by
  have hsub : componentVertices ds r ++ componentVertices ds s ⊆
      vertexUniverse ds := by
    intro v hv
    rcases List.mem_append.mp hv with hr | hs
    · exact componentVertices_subset ds r hr
    · exact componentVertices_subset ds s hs
  have h := (componentVertices_append_nodup ds r s hne).length_le_of_subset hsub
  simpa only [List.length_append, vertexUniverse_length, componentCard] using h

theorem root_cache_add_le_capacity {ds : DSA} (hexact : RootSizesExact ds)
    {r s : Int} (hr : SelfRoot ds r) (hs : SelfRoot ds s) (hne : r ≠ s) :
    cache ds r + cache ds s ≤ Int.ofNat (capacity ds) := by
  have hcard := componentCard_add_le_capacity ds r s hne
  have hrc := hexact r hr
  have hsc := hexact s hs
  change cache ds r = (componentCard ds r : Int) at hrc
  change cache ds s = (componentCard ds s : Int) at hsc
  change cache ds r + cache ds s ≤ (capacity ds : Int)
  omega

theorem componentVertices_eq_nil_of_not_selfRoot {ds : DSA} {r : Int}
    (h : ¬ SelfRoot ds r) : componentVertices ds r = [] := by
  apply List.eq_nil_iff_forall_not_mem.mpr
  intro v hv
  exact h (((mem_componentVertices ds v r).mp hv).2.selfRoot)

theorem componentCard_eq_zero_of_not_selfRoot {ds : DSA} {r : Int}
    (h : ¬ SelfRoot ds r) : componentCard ds r = 0 := by
  rw [componentCard, componentVertices_eq_nil_of_not_selfRoot h]
  rfl

theorem componentVertices_start (n r : Int) (hr : Valid (startDSA n) r) :
    componentVertices (startDSA n) r = [r] := by
  apply List.Perm.eq_singleton
  apply (List.perm_ext_iff_of_nodup (componentVertices_nodup _ _) (by simp)).mpr
  intro v
  rw [mem_componentVertices, root_start_iff]
  simp only [List.mem_singleton]
  constructor
  · rintro ⟨_, _, he⟩
    exact he.symm
  · intro he
    subst v
    exact ⟨hr, hr, rfl⟩

theorem componentCard_start (n r : Int) (hr : Valid (startDSA n) r) :
    componentCard (startDSA n) r = 1 := by
  rw [componentCard, componentVertices_start n r hr]
  rfl

theorem startDSA_rootSizesExact (n : Int) : RootSizesExact (startDSA n) := by
  intro r hr
  have hv := (root_self hr).valid_start
  rw [cache_startDSA hv, componentCard_start n r hv]
  rfl

theorem sameComponent_valid {ds : DSA} {u v : Int}
    (h : SameComponent ds u v) : Valid ds u ∧ Valid ds v := by
  obtain ⟨r, hu, hv⟩ := h
  exact ⟨hu.valid_start, hv.valid_start⟩

theorem sameComponent_refl {ds : DSA} (hF : Forest ds) {v : Int}
    (hv : Valid ds v) : SameComponent ds v v := by
  obtain ⟨r, hr⟩ := hF.valid_root_exists hv
  exact ⟨r, hr, hr⟩

theorem sameComponent_symm {ds : DSA} {u v : Int}
    (h : SameComponent ds u v) : SameComponent ds v u := by
  obtain ⟨r, hu, hv⟩ := h
  exact ⟨r, hv, hu⟩

theorem sameComponent_trans {ds : DSA} {u v w : Int}
    (huv : SameComponent ds u v) (hvw : SameComponent ds v w) :
    SameComponent ds u w := by
  obtain ⟨r, hu, hv⟩ := huv
  obtain ⟨s, hv', hw⟩ := hvw
  have he := hv.unique hv'
  subst s
  exact ⟨r, hu, hw⟩

theorem sameComponent_iff_common_find {ds : DSA} (hF : Forest ds) (u v : Int) :
    SameComponent ds u v ↔
      ∃ r, findDSA ds u = some r ∧ findDSA ds v = some r := by
  constructor
  · rintro ⟨r, hu, hv⟩
    exact ⟨r, (hF.findDSA_iff_Root u r).mpr hu, (hF.findDSA_iff_Root v r).mpr hv⟩
  · rintro ⟨r, hu, hv⟩
    exact ⟨r, (hF.findDSA_iff_Root u r).mp hu, (hF.findDSA_iff_Root v r).mp hv⟩

theorem sameComponent_iff_find_eq {ds : DSA} (hF : Forest ds) {u v : Int}
    (hu : Valid ds u) (hv : Valid ds v) :
    SameComponent ds u v ↔ findDSA ds u = findDSA ds v := by
  constructor
  · intro h
    obtain ⟨r, hru, hrv⟩ := (sameComponent_iff_common_find hF u v).mp h
    exact hru.trans hrv.symm
  · intro he
    obtain ⟨r, hr⟩ := hF.valid_root_exists hu
    obtain ⟨s, hs⟩ := hF.valid_root_exists hv
    have hru := (hF.findDSA_iff_Root u r).mpr hr
    have hsv := (hF.findDSA_iff_Root v s).mpr hs
    have hrs : r = s := Option.some.inj (hru.symm.trans (he.trans hsv))
    subst s
    exact ⟨r, hr, hs⟩

theorem sameComponent_start (n u v : Int) :
    SameComponent (startDSA n) u v ↔ Valid (startDSA n) u ∧ u = v := by
  constructor
  · rintro ⟨r, hu, hv⟩
    obtain ⟨huv, hru⟩ := (root_start_iff n u r).mp hu
    obtain ⟨_, hrv⟩ := (root_start_iff n v r).mp hv
    exact ⟨huv, hru.symm.trans hrv⟩
  · rintro ⟨hu, rfl⟩
    have hr := (root_start_iff n u u).mpr ⟨hu, rfl⟩
    exact ⟨u, hr, hr⟩

end Connectivity.ParentComponents
