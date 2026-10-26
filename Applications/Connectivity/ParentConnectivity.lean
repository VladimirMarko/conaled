import Applications.Connectivity.ParentHistory
import Applications.Connectivity.ListPartition

set_option autoImplicit false
set_option warningAsError true

/-! Concrete ParentConnectivity proofs adapted from adwh-checkpoint-233.
Source members and declaration dispositions: docs/research/adwh-connectivity-provenance.tsv.
Operations retain the source failure and representative-selection behavior. -/

namespace Connectivity.ParentConnectivity

open ParentArray ParentForest ParentComponents
open ParentUnion ParentHistory
open ListPartition (Connected vertices)

theorem vertexUniverse_eq_vertices_capacity (ds : DSA) :
    vertexUniverse ds = vertices (Int.ofNat (capacity ds)) := by
  simp [vertexUniverse, vertices]

theorem vertices_normalize_toNat (n : Int) :
    vertices (Int.ofNat n.toNat) = vertices n := by
  have hn : (max n 0).toNat = n.toNat := by omega
  simpa [vertices] using congrArg
    (fun k => (List.range k).map (fun (i : Nat) => (i : Int) + 1)) hn

theorem requestHistory_universe {n : Int} {requests : List (Int × Int)} {ds : DSA}
    (h : RequestHistory n requests ds) : vertexUniverse ds = vertices n := by
  have hs := (requestHistory_sizes h).1
  simp only [vertexUniverse, vertices, capacity, hs]

private theorem valid_iff_mem_vertices {n : Int} {requests : List (Int × Int)}
    {ds : DSA} (h : RequestHistory n requests ds) (v : Int) :
    Valid ds v ↔ v ∈ vertices n := by
  rw [← requestHistory_universe h, mem_vertexUniverse]

private theorem sameComponent_right_of_root {ds : DSA} {u r : Int}
    (hr : Root ds u r) (x : Int) :
    SameComponent ds x r ↔ SameComponent ds x u := by
  have hu : SameComponent ds u r := ⟨r, hr, root_self hr.selfRoot⟩
  exact ⟨fun h => sameComponent_trans h (sameComponent_symm hu),
    fun h => sameComponent_trans h hu⟩

private theorem sameComponent_left_of_root {ds : DSA} {u r : Int}
    (hr : Root ds u r) (x : Int) :
    SameComponent ds r x ↔ SameComponent ds u x := by
  constructor
  · intro h
    exact sameComponent_symm ((sameComponent_right_of_root hr x).mp
      (sameComponent_symm h))
  · intro h
    exact sameComponent_symm ((sameComponent_right_of_root hr x).mpr
      (sameComponent_symm h))

theorem requestStep_sameComponent_iff {ds out : DSA} {u v : Int}
    (hF : Forest ds) (h : RequestStep ds u v out) (x y : Int) :
    SameComponent out x y ↔ SameComponent ds x y ∨
      (SameComponent ds x u ∧ SameComponent ds v y) ∨
      (SameComponent ds x v ∧ SameComponent ds u y) := by
  obtain ⟨a, b, ha, hb, hne, hu⟩ := h
  have hru := (hF.findDSA_iff_Root u a).mp ha
  have hrv := (hF.findDSA_iff_Root v b).mp hb
  rw [union_sameComponent hF hru.selfRoot hrv.selfRoot hne hu,
    sameComponent_right_of_root hru x, sameComponent_left_of_root hrv y,
    sameComponent_right_of_root hrv x, sameComponent_left_of_root hru y]

private theorem connected_mono {vs : List Int} {old new : List (Int × Int)}
    (hsub : ∀ e ∈ old, e ∈ new) {u v : Int} (h : Connected vs old u v) :
    Connected vs new u v := by
  induction h with
  | refl hv => exact Connected.refl hv
  | edge hu hv he => exact Connected.edge hu hv (hsub _ he)
  | symm _ ih => exact Connected.symm ih
  | trans _ _ ih1 ih2 => exact Connected.trans ih1 ih2

private theorem connected_nil_iff (vs : List Int) (u v : Int) :
    Connected vs [] u v ↔ u = v ∧ u ∈ vs := by
  constructor
  · intro h
    induction h with
    | refl hv => exact ⟨rfl, hv⟩
    | edge _ _ he => simp at he
    | symm _ ih => exact ⟨ih.1.symm, by simpa [ih.1] using ih.2⟩
    | trans _ _ ih1 ih2 => exact ⟨ih1.1.trans ih2.1, ih1.2⟩
  · rintro ⟨rfl, hu⟩
    exact Connected.refl hu

private theorem connected_endpoints {vs : List Int} {links : List (Int × Int)}
    {u v : Int} (h : Connected vs links u v) : u ∈ vs ∧ v ∈ vs := by
  induction h with
  | refl hv => exact ⟨hv, hv⟩
  | edge hu hv _ => exact ⟨hu, hv⟩
  | symm _ ih => exact ⟨ih.2, ih.1⟩
  | trans _ _ ih1 ih2 => exact ⟨ih1.1, ih2.2⟩

theorem requestHistory_connected_iff {n : Int} {requests : List (Int × Int)}
    {ds : DSA} (h : RequestHistory n requests ds) :
    ∀ u v, SameComponent ds u v ↔ Connected (vertices n) requests u v := by
  induction h with
  | start =>
      intro u v
      rw [sameComponent_start, connected_nil_iff, ListPartition.mem_vertices_iff,
        valid_startDSA_iff]
      omega
  | @snoc requests ds out a b hh hstep ih =>
      have hF := requestHistory_forest hh
      have ho : RequestHistory n (requests ++ [(a, b)]) out := .snoc hh hstep
      have hFo := requestHistory_forest ho
      have hstepCopy := hstep
      obtain ⟨r, s, ha, hb, _, _⟩ := hstepCopy
      have hva := ((hF.findDSA_iff_Root a r).mp ha).valid_start
      have hvb := ((hF.findDSA_iff_Root b s).mp hb).valid_start
      have hlink : Connected (vertices n) (requests ++ [(a, b)]) a b :=
        .edge ((valid_iff_mem_vertices hh a).mp hva)
          ((valid_iff_mem_vertices hh b).mp hvb) (by simp)
      have hmono {u v : Int} (hc : Connected (vertices n) requests u v) :
          Connected (vertices n) (requests ++ [(a, b)]) u v :=
        connected_mono (fun _ he => List.mem_append_left _ he) hc
      intro u v
      constructor
      · intro hs
        rcases (requestStep_sameComponent_iff hF hstep u v).mp hs with
          hold | hcross | hcross
        · exact hmono ((ih u v).mp hold)
        · exact .trans (.trans (hmono ((ih u a).mp hcross.1)) hlink)
            (hmono ((ih b v).mp hcross.2))
        · exact .trans (.trans (hmono ((ih u b).mp hcross.1)) (.symm hlink))
            (hmono ((ih a v).mp hcross.2))
      · intro hs
        induction hs with
        | refl hv =>
            exact sameComponent_refl hFo ((valid_iff_mem_vertices ho _).mpr hv)
        | edge hv hw he =>
            apply (requestStep_sameComponent_iff hF hstep _ _).mpr
            rcases List.mem_append.mp he with he | he
            · exact Or.inl ((ih _ _).mpr (.edge hv hw he))
            · have he' := List.mem_singleton.mp he
              cases he'
              exact Or.inr (Or.inl ⟨sameComponent_refl hF hva,
                sameComponent_refl hF hvb⟩)
        | symm _ ihs => exact sameComponent_symm ihs
        | trans _ _ ih1 ih2 => exact sameComponent_trans ih1 ih2

theorem requestHistory_common_find_iff_connected {n : Int}
    {requests : List (Int × Int)} {ds : DSA} (h : RequestHistory n requests ds)
    (u v : Int) :
    (∃ r, findDSA ds u = some r ∧ findDSA ds v = some r) ↔
      Connected (vertices n) requests u v := by
  rw [← sameComponent_iff_common_find (requestHistory_forest h) u v,
    requestHistory_connected_iff h]

theorem requestHistory_find_equal_iff_connected {n : Int}
    {requests : List (Int × Int)} {ds : DSA} (h : RequestHistory n requests ds)
    {u v : Int} (hu : u ∈ vertices n) (hv : v ∈ vertices n) :
    findDSA ds u = findDSA ds v ↔ Connected (vertices n) requests u v := by
  rw [← sameComponent_iff_find_eq (requestHistory_forest h)
    ((valid_iff_mem_vertices h u).mpr hu) ((valid_iff_mem_vertices h v).mpr hv),
    requestHistory_connected_iff h]

theorem requestHistory_find_connected {n : Int} {requests : List (Int × Int)}
    {ds : DSA} (h : RequestHistory n requests ds) {v r : Int}
    (hf : findDSA ds v = some r) :
    r ∈ vertices n ∧ Connected (vertices n) requests v r := by
  have hr := ((requestHistory_forest h).findDSA_iff_Root v r).mp hf
  exact ⟨(valid_iff_mem_vertices h r).mp hr.valid_root,
    (requestHistory_connected_iff h v r).mp ⟨r, hr, root_self hr.selfRoot⟩⟩

theorem requestStep_exists_iff {n : Int} {requests : List (Int × Int)}
    {ds : DSA} (h : RequestHistory n requests ds) (u v : Int) :
    (∃ out, RequestStep ds u v out) ↔
      u ∈ vertices n ∧ v ∈ vertices n ∧ ¬ Connected (vertices n) requests u v := by
  have hF := requestHistory_forest h
  constructor
  · rintro ⟨out, a, b, ha, hb, hne, _⟩
    have hu := (valid_iff_mem_vertices h u).mp ((hF.findDSA_iff_Root u a).mp ha).valid_start
    have hv := (valid_iff_mem_vertices h v).mp ((hF.findDSA_iff_Root v b).mp hb).valid_start
    refine ⟨hu, hv, ?_⟩
    intro hc
    have he := (requestHistory_find_equal_iff_connected h hu hv).mpr hc
    rw [ha, hb] at he
    exact hne (Option.some.inj he)
  · rintro ⟨hu, hv, hnc⟩
    obtain ⟨a, ha⟩ := hF.find_complete ((valid_iff_mem_vertices h u).mpr hu)
    obtain ⟨b, hb⟩ := hF.find_complete ((valid_iff_mem_vertices h v).mpr hv)
    have hne : a ≠ b := by
      intro he
      apply hnc
      apply (requestHistory_find_equal_iff_connected h hu hv).mp
      rw [ha, hb, he]
    obtain ⟨out, hout⟩ := union_defined hF
      ((hF.findDSA_iff_Root u a).mp ha).selfRoot
      ((hF.findDSA_iff_Root v b).mp hb).selfRoot hne
    exact ⟨out, a, b, ha, hb, hne, hout⟩

theorem requestHistory_extension_iff {n : Int} {requests : List (Int × Int)}
    {ds : DSA} (h : RequestHistory n requests ds) (u v : Int) :
    (∃ out, RequestHistory n (requests ++ [(u, v)]) out) ↔
      u ∈ vertices n ∧ v ∈ vertices n ∧ ¬ Connected (vertices n) requests u v := by
  rw [← requestStep_exists_iff h u v]
  constructor
  · rintro ⟨out, hout⟩
    obtain ⟨before, hbefore, hstep⟩ := (requestHistory_snoc_iff n requests u v out).mp hout
    have he := requestHistory_deterministic hbefore h
    subst before
    exact ⟨out, hstep⟩
  · rintro ⟨out, hstep⟩
    exact ⟨out, RequestHistory.snoc h hstep⟩

private theorem two_request_history :
    RequestHistory 3 [(2, 3), (1, 2)] ⟨#[2, 2, 2], #[1, 3, 1]⟩ := by
  have h1 : RequestHistory 3 [(2, 3)] ⟨#[1, 2, 2], #[1, 2, 1]⟩ :=
    RequestHistory.snoc RequestHistory.start
      ⟨2, 3, by decide +kernel, by decide +kernel, by decide +kernel,
        by decide +kernel⟩
  exact RequestHistory.snoc h1
    ⟨1, 2, by decide +kernel, by decide +kernel, by decide +kernel,
      by decide +kernel⟩

end Connectivity.ParentConnectivity
