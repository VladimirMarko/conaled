import Applications.Connectivity.ParentComponents

set_option autoImplicit false
set_option warningAsError true

/-! Concrete ParentUnion proofs adapted from adwh-checkpoint-233.
Source members and declaration dispositions: docs/research/adwh-connectivity-provenance.tsv.
Operations retain the source failure and representative-selection behavior. -/

namespace Connectivity.ParentUnion

open ParentArray ParentForest ParentComponents

def loser (ds : DSA) (n1 n2 : Int) : Int :=
  if cache ds n1 < cache ds n2 then n1 else n2

def winner (ds : DSA) (n1 n2 : Int) : Int :=
  if cache ds n1 < cache ds n2 then n2 else n1

def renameRoot (losing surviving r : Int) : Int :=
  if r = losing then surviving else r

structure LinkEffect (ds out : DSA) (losing surviving : Int) : Prop where
  parent_size : out.namesA.size = ds.namesA.size
  cache_size : out.sizesA.size = ds.sizesA.size
  parent_reads : ∀ v, readCell out.namesA v =
    if v = losing then some surviving else readCell ds.namesA v
  cache_reads : ∀ v, readCell out.sizesA v =
    if v = surviving then some (cache ds losing + cache ds surviving)
    else readCell ds.sizesA v

theorem LinkEffect.valid_iff {ds out : DSA} {losing surviving : Int}
    (effect : LinkEffect ds out losing surviving) (v : Int) :
    Valid out v ↔ Valid ds v := by
  simp only [Valid, capacity, effect.parent_size]

theorem LinkEffect.cache_eq {ds out : DSA} {losing surviving : Int}
    (effect : LinkEffect ds out losing surviving) (v : Int) :
    cache out v = if v = surviving then cache ds losing + cache ds surviving
      else cache ds v := by
  by_cases hv : v = surviving
  · simp [cache, effect.cache_reads, hv]
  · simp [cache, effect.cache_reads, hv]

theorem LinkEffect.cache_mono {ds out : DSA} {losing surviving : Int}
    (effect : LinkEffect ds out losing surviving) (hpos : 0 ≤ cache ds losing)
    (v : Int) : cache ds v ≤ cache out v := by
  rw [effect.cache_eq]
  by_cases hv : v = surviving
  · subst v
    rw [ite_eq_left rfl]
    omega
  · rw [ite_eq_right hv]
    exact Int.le_refl _

private theorem linkEffect_of_writes {ds : DSA} {ns ss : Array Int}
    {losing surviving : Int}
    (hn : writeCell ds.namesA losing surviving = some ns)
    (hs : writeCell ds.sizesA surviving
      (cache ds losing + cache ds surviving) = some ss) :
    LinkEffect ds ⟨ns, ss⟩ losing surviving := by
  refine ⟨writeCell_size hn, writeCell_size hs, ?_, ?_⟩
  · intro v
    by_cases hv : v = losing
    · subst v
      simpa using writeCell_read_self hn
    · simpa only [ite_eq_right hv] using writeCell_read_other hn hv
  · intro v
    by_cases hv : v = surviving
    · subst v
      simpa using writeCell_read_self hs
    · simpa only [ite_eq_right hv] using writeCell_read_other hs hv

private theorem union_defined_effect {ds : DSA} {n1 n2 : Int}
    (hF : Forest ds) (h1 : SelfRoot ds n1) (h2 : SelfRoot ds n2) :
    ∃ out, unionDSA n1 n2 ds = some out ∧
      LinkEffect ds out (loser ds n1 n2) (winner ds n1 n2) := by
  have hv1 := valid_of_parent_read h1
  have hv2 := valid_of_parent_read h2
  have hc1 := hF.cache_read hv1
  have hc2 := hF.cache_read hv2
  have hb1 : n1.toNat ≤ ds.sizesA.size := by
    rw [hF.dimensions]
    exact hv1.2
  have hb2 : n2.toNat ≤ ds.sizesA.size := by
    rw [hF.dimensions]
    exact hv2.2
  by_cases hlt : cache ds n1 < cache ds n2
  · let ns := ds.namesA.setIfInBounds (n1.toNat - 1) n2
    let ss := ds.sizesA.setIfInBounds (n2.toNat - 1) (cache ds n1 + cache ds n2)
    have hn : writeCell ds.namesA n1 n2 = some ns :=
      writeCell_valid _ _ _ hv1.1 hv1.2
    have hs : writeCell ds.sizesA n2 (cache ds n1 + cache ds n2) = some ss :=
      writeCell_valid _ _ _ hv2.1 hb2
    refine ⟨⟨ns, ss⟩, ?_, ?_⟩
    · rw [unionDSA_of_lt ds n1 n2 _ _ hc1 hc2 hlt]
      simp [hn, hs]
    · simpa only [loser, winner, ite_eq_left hlt] using linkEffect_of_writes hn hs
  · let ns := ds.namesA.setIfInBounds (n2.toNat - 1) n1
    let ss := ds.sizesA.setIfInBounds (n1.toNat - 1) (cache ds n1 + cache ds n2)
    have hn : writeCell ds.namesA n2 n1 = some ns :=
      writeCell_valid _ _ _ hv2.1 hv2.2
    have hs : writeCell ds.sizesA n1 (cache ds n1 + cache ds n2) = some ss :=
      writeCell_valid _ _ _ hv1.1 hb1
    refine ⟨⟨ns, ss⟩, ?_, ?_⟩
    · rw [unionDSA_of_not_lt ds n1 n2 _ _ hc1 hc2 hlt]
      simp [hn, hs]
    · have hs' : writeCell ds.sizesA n1 (cache ds n2 + cache ds n1) = some ss := by
        simpa only [Int.add_comm] using hs
      simpa only [loser, winner, ite_eq_right hlt] using linkEffect_of_writes hn hs'

theorem union_defined {ds : DSA} {n1 n2 : Int}
    (hF : Forest ds) (h1 : SelfRoot ds n1) (h2 : SelfRoot ds n2) (_hne : n1 ≠ n2) :
    ∃ out, unionDSA n1 n2 ds = some out := by
  obtain ⟨out, hu, _⟩ := union_defined_effect hF h1 h2
  exact ⟨out, hu⟩

theorem union_linkEffect {ds out : DSA} {n1 n2 : Int}
    (hF : Forest ds) (h1 : SelfRoot ds n1) (h2 : SelfRoot ds n2) (_hne : n1 ≠ n2)
    (hu : unionDSA n1 n2 ds = some out) :
    LinkEffect ds out (loser ds n1 n2) (winner ds n1 n2) := by
  obtain ⟨other, ho, effect⟩ := union_defined_effect hF h1 h2
  have he : other = out := Option.some.inj (ho.symm.trans hu)
  subst other
  exact effect

theorem union_orientation {ds : DSA} {n1 n2 : Int}
    (h1 : SelfRoot ds n1) (h2 : SelfRoot ds n2) (hne : n1 ≠ n2) :
    SelfRoot ds (loser ds n1 n2) ∧ SelfRoot ds (winner ds n1 n2) ∧
      loser ds n1 n2 ≠ winner ds n1 n2 ∧
      cache ds (loser ds n1 n2) ≤ cache ds (winner ds n1 n2) := by
  by_cases hlt : cache ds n1 < cache ds n2
  · simp only [loser, winner, ite_eq_left hlt]
    exact ⟨h1, h2, hne, by omega⟩
  · simp only [loser, winner, ite_eq_right hlt]
    exact ⟨h2, h1, Ne.symm hne, by omega⟩

theorem union_capacity {ds out : DSA} {n1 n2 : Int}
    (hu : unionDSA n1 n2 ds = some out) : capacity out = capacity ds :=
  (unionDSA_sizes hu).1

theorem union_valid_iff {ds out : DSA} {n1 n2 : Int}
    (hu : unionDSA n1 n2 ds = some out) (v : Int) : Valid out v ↔ Valid ds v := by
  simp only [Valid, union_capacity hu]

theorem LinkEffect.rootSteps_forward {ds out : DSA} {losing surviving v r : Int}
    {k : Nat} (effect : LinkEffect ds out losing surviving)
    (hl : SelfRoot ds losing) (hw : SelfRoot ds surviving) (hne : losing ≠ surviving)
    (path : RootSteps ds v r k) :
    RootSteps out v (renameRoot losing surviving r)
      (k + if r = losing then 1 else 0) := by
  induction path with
  | @root r read =>
      by_cases hr : r = losing
      · subst r
        have hnl : readCell out.namesA losing = some surviving := by
          rw [effect.parent_reads, ite_eq_left rfl]
        have hnw : readCell out.namesA surviving = some surviving := by
          rw [effect.parent_reads, ite_eq_right (Ne.symm hne)]
          exact hw
        simpa [renameRoot] using
          (RootSteps.step hnl (Ne.symm hne) (RootSteps.root hnw))
      · have hnr : readCell out.namesA r = some r := by
          rw [effect.parent_reads, ite_eq_right hr]
          exact read
        simpa only [renameRoot, ite_eq_right hr, Nat.zero_add] using RootSteps.root hnr
  | @step v p r k read nonself tail ih =>
      have hv : v ≠ losing := by
        intro he
        subst v
        exact nonself (Option.some.inj (read.symm.trans hl))
      have hnr : readCell out.namesA v = some p := by
        rw [effect.parent_reads, ite_eq_right hv]
        exact read
      have he : k + 1 + (if r = losing then 1 else 0) =
          k + (if r = losing then 1 else 0) + 1 := by omega
      rw [he]
      exact RootSteps.step hnr nonself ih

theorem LinkEffect.root_forward {ds out : DSA} {losing surviving v r : Int}
    (effect : LinkEffect ds out losing surviving)
    (hl : SelfRoot ds losing) (hw : SelfRoot ds surviving) (hne : losing ≠ surviving)
    (hr : Root ds v r) : Root out v (renameRoot losing surviving r) := by
  obtain ⟨k, hk⟩ := hr
  exact ⟨k + if r = losing then 1 else 0, effect.rootSteps_forward hl hw hne hk⟩

theorem LinkEffect.root_iff {ds out : DSA} {losing surviving : Int}
    (effect : LinkEffect ds out losing surviving) (hF : Forest ds)
    (hl : SelfRoot ds losing) (hw : SelfRoot ds surviving) (hne : losing ≠ surviving)
    (v r : Int) : Root out v r ↔
      ∃ q, Root ds v q ∧ renameRoot losing surviving q = r := by
  constructor
  · intro hr
    have hv := (effect.valid_iff v).mp hr.valid_start
    obtain ⟨q, hq⟩ := hF.valid_root_exists hv
    have hq' := effect.root_forward hl hw hne hq
    exact ⟨q, hq, hq'.unique hr⟩
  · rintro ⟨q, hq, he⟩
    rw [← he]
    exact effect.root_forward hl hw hne hq

theorem LinkEffect.selfRoot_iff {ds out : DSA} {losing surviving : Int}
    (effect : LinkEffect ds out losing surviving) (hne : losing ≠ surviving)
    (r : Int) : SelfRoot out r ↔ SelfRoot ds r ∧ r ≠ losing := by
  by_cases hr : r = losing
  · subst r
    simp [SelfRoot, effect.parent_reads, Ne.symm hne]
  · simp [SelfRoot, effect.parent_reads, hr]

private theorem mem_component_iff_Root (ds : DSA) (v r : Int) :
    v ∈ componentVertices ds r ↔ Root ds v r := by
  rw [mem_componentVertices]
  exact ⟨And.right, fun h => ⟨h.valid_start, h⟩⟩

theorem LinkEffect.component_winner {ds out : DSA} {losing surviving : Int}
    (effect : LinkEffect ds out losing surviving) (hF : Forest ds)
    (hl : SelfRoot ds losing) (hw : SelfRoot ds surviving) (hne : losing ≠ surviving)
    (v : Int) : v ∈ componentVertices out surviving ↔
      v ∈ componentVertices ds losing ∨ v ∈ componentVertices ds surviving := by
  simp only [mem_component_iff_Root]
  rw [effect.root_iff hF hl hw hne]
  constructor
  · rintro ⟨q, hq, he⟩
    by_cases hq' : q = losing
    · subst q
      exact Or.inl hq
    · have heq : q = surviving := by simpa only [renameRoot, ite_eq_right hq'] using he
      subst q
      exact Or.inr hq
  · rintro (hr | hr)
    · exact ⟨losing, hr, by simp [renameRoot]⟩
    · exact ⟨surviving, hr, by simp [renameRoot, Ne.symm hne]⟩

theorem LinkEffect.component_other {ds out : DSA} {losing surviving r : Int}
    (effect : LinkEffect ds out losing surviving) (hF : Forest ds)
    (hl : SelfRoot ds losing) (hw : SelfRoot ds surviving) (hne : losing ≠ surviving)
    (hrl : r ≠ losing) (hrw : r ≠ surviving) (v : Int) :
    v ∈ componentVertices out r ↔ v ∈ componentVertices ds r := by
  simp only [mem_component_iff_Root]
  rw [effect.root_iff hF hl hw hne]
  constructor
  · rintro ⟨q, hq, he⟩
    by_cases hq' : q = losing
    · subst q
      have heq : surviving = r := by simpa [renameRoot] using he
      exact False.elim (hrw heq.symm)
    · have heq : q = r := by simpa only [renameRoot, ite_eq_right hq'] using he
      subst q
      exact hq
  · intro hr
    exact ⟨r, hr, by simp only [renameRoot, ite_eq_right hrl]⟩

theorem LinkEffect.componentCard_winner {ds out : DSA} {losing surviving : Int}
    (effect : LinkEffect ds out losing surviving) (hF : Forest ds)
    (hl : SelfRoot ds losing) (hw : SelfRoot ds surviving) (hne : losing ≠ surviving) :
    componentCard out surviving = componentCard ds losing + componentCard ds surviving := by
  have hp : (componentVertices out surviving).Perm
      (componentVertices ds losing ++ componentVertices ds surviving) := by
    apply (List.perm_ext_iff_of_nodup (componentVertices_nodup _ _)
      (componentVertices_append_nodup ds losing surviving hne)).mpr
    intro v
    rw [List.mem_append]
    exact effect.component_winner hF hl hw hne v
  simpa only [List.length_append, componentCard] using hp.length_eq

theorem LinkEffect.componentCard_other {ds out : DSA} {losing surviving r : Int}
    (effect : LinkEffect ds out losing surviving) (hF : Forest ds)
    (hl : SelfRoot ds losing) (hw : SelfRoot ds surviving) (hne : losing ≠ surviving)
    (hrl : r ≠ losing) (hrw : r ≠ surviving) :
    componentCard out r = componentCard ds r := by
  have hp : (componentVertices out r).Perm (componentVertices ds r) := by
    apply (List.perm_ext_iff_of_nodup (componentVertices_nodup _ _)
      (componentVertices_nodup _ _)).mpr
    exact effect.component_other hF hl hw hne hrl hrw
  exact hp.length_eq

private theorem LinkEffect.old_nonself_read {ds out : DSA}
    {losing surviving v p : Int} (effect : LinkEffect ds out losing surviving)
    (hw : SelfRoot ds surviving) (hp : readCell out.namesA v = some p)
    (nonself : p ≠ v) (hv : v ≠ losing) :
    readCell ds.namesA v = some p ∧ v ≠ surviving := by
  have hold : readCell ds.namesA v = some p := by
    rw [effect.parent_reads, ite_eq_right hv] at hp
    exact hp
  refine ⟨hold, ?_⟩
  intro he
  subst v
  exact nonself (Option.some.inj (hold.symm.trans hw))

theorem LinkEffect.forest {ds out : DSA} {losing surviving : Int}
    (effect : LinkEffect ds out losing surviving) (hF : Forest ds)
    (hexact : RootSizesExact ds) (hl : SelfRoot ds losing)
    (hw : SelfRoot ds surviving) (hne : losing ≠ surviving) : Forest out := by
  have hlv := valid_of_parent_read hl
  have hwv := valid_of_parent_read hw
  have hlp := hF.cache_positive losing hlv
  have hwp := hF.cache_positive surviving hwv
  have hbound := root_cache_add_le_capacity hexact hl hw hne
  change cache ds losing + cache ds surviving ≤ (capacity ds : Int) at hbound
  constructor
  · exact effect.cache_size.trans (hF.dimensions.trans effect.parent_size.symm)
  · intro v p hv hp
    have hvo := (effect.valid_iff v).mp hv
    by_cases he : v = losing
    · subst v
      rw [effect.parent_reads, ite_eq_left rfl] at hp
      have hep : p = surviving := Option.some.inj hp.symm
      subst p
      exact (effect.valid_iff surviving).mpr hwv
    · rw [effect.parent_reads, ite_eq_right he] at hp
      exact (effect.valid_iff p).mpr (hF.parents_valid v p hvo hp)
  · intro v hv
    have hvo := (effect.valid_iff v).mp hv
    rw [effect.cache_eq]
    by_cases he : v = surviving
    · rw [ite_eq_left he]
      omega
    · rw [ite_eq_right he]
      exact hF.cache_positive v hvo
  · intro v hv
    have hvo := (effect.valid_iff v).mp hv
    rw [effect.cache_eq]
    by_cases he : v = surviving
    · rw [ite_eq_left he]
      simpa only [capacity, effect.parent_size] using hbound
    · rw [ite_eq_right he]
      simpa only [capacity, effect.parent_size] using hF.cache_bounded v hvo
  · intro v p hv hp nonself
    have hvo := (effect.valid_iff v).mp hv
    by_cases he : v = losing
    · subst v
      rw [effect.parent_reads, ite_eq_left rfl] at hp
      have hep : p = surviving := Option.some.inj hp.symm
      subst p
      rw [effect.cache_eq losing, ite_eq_right hne, effect.cache_eq surviving, ite_eq_left rfl]
      omega
    · obtain ⟨hold, hvw⟩ := effect.old_nonself_read hw hp nonself he
      have hg := hF.cache_grows v p hvo hold nonself
      have hm := effect.cache_mono (by omega) p
      rw [effect.cache_eq v, ite_eq_right hvw]
      omega

theorem LinkEffect.weightedForest {ds out : DSA} {losing surviving : Int}
    (effect : LinkEffect ds out losing surviving) (hW : WeightedForest ds)
    (hexact : RootSizesExact ds) (hl : SelfRoot ds losing)
    (hw : SelfRoot ds surviving) (hne : losing ≠ surviving)
    (hle : cache ds losing ≤ cache ds surviving) : WeightedForest out := by
  refine ⟨effect.forest hW.toForest hexact hl hw hne, ?_⟩
  have hlp := hW.cache_positive losing (valid_of_parent_read hl)
  intro v p hv hp nonself
  have hvo := (effect.valid_iff v).mp hv
  by_cases he : v = losing
  · subst v
    rw [effect.parent_reads, ite_eq_left rfl] at hp
    have hep : p = surviving := Option.some.inj hp.symm
    subst p
    rw [effect.cache_eq losing, ite_eq_right hne, effect.cache_eq surviving, ite_eq_left rfl]
    omega
  · obtain ⟨hold, hvw⟩ := effect.old_nonself_read hw hp nonself he
    have hd := hW.cache_doubles v p hvo hold nonself
    have hm := effect.cache_mono (by omega) p
    rw [effect.cache_eq v, ite_eq_right hvw]
    omega

theorem LinkEffect.rootSizesExact {ds out : DSA} {losing surviving : Int}
    (effect : LinkEffect ds out losing surviving) (hF : Forest ds)
    (hexact : RootSizesExact ds) (hl : SelfRoot ds losing)
    (hw : SelfRoot ds surviving) (hne : losing ≠ surviving) : RootSizesExact out := by
  intro r hr
  have hro := (effect.selfRoot_iff hne r).mp hr
  by_cases he : r = surviving
  · subst r
    rw [effect.cache_eq surviving, ite_eq_left rfl, hexact losing hl, hexact surviving hw,
      effect.componentCard_winner hF hl hw hne]
    rfl
  · rw [effect.cache_eq r, ite_eq_right he,
      effect.componentCard_other hF hl hw hne hro.2 he]
    exact hexact r hro.1

theorem LinkEffect.find_map {ds out : DSA} {losing surviving : Int}
    (effect : LinkEffect ds out losing surviving) (hF : Forest ds)
    (hexact : RootSizesExact ds) (hl : SelfRoot ds losing)
    (hw : SelfRoot ds surviving) (hne : losing ≠ surviving) (v : Int) :
    findDSA out v = (findDSA ds v).map (renameRoot losing surviving) := by
  have hout := effect.forest hF hexact hl hw hne
  cases hf : findDSA ds v with
  | none =>
      have hv := (hF.find_none_iff_invalid v).mp hf
      have hvo : ¬ Valid out v := fun h => hv ((effect.valid_iff v).mp h)
      exact findDSA_invalid hvo
  | some r =>
      have hr := (hF.findDSA_iff_Root v r).mp hf
      have hr' := effect.root_forward hl hw hne hr
      exact (hout.findDSA_iff_Root v (renameRoot losing surviving r)).mpr hr'

theorem union_forest {ds out : DSA} {n1 n2 : Int}
    (hF : Forest ds) (hexact : RootSizesExact ds)
    (h1 : SelfRoot ds n1) (h2 : SelfRoot ds n2) (hne : n1 ≠ n2)
    (hu : unionDSA n1 n2 ds = some out) : Forest out := by
  have effect := union_linkEffect hF h1 h2 hne hu
  obtain ⟨hl, hw, hne', _⟩ := union_orientation h1 h2 hne
  exact effect.forest hF hexact hl hw hne'

theorem union_weightedForest {ds out : DSA} {n1 n2 : Int}
    (hW : WeightedForest ds) (hexact : RootSizesExact ds)
    (h1 : SelfRoot ds n1) (h2 : SelfRoot ds n2) (hne : n1 ≠ n2)
    (hu : unionDSA n1 n2 ds = some out) : WeightedForest out := by
  have effect := union_linkEffect hW.toForest h1 h2 hne hu
  obtain ⟨hl, hw, hne', hle⟩ := union_orientation h1 h2 hne
  exact effect.weightedForest hW hexact hl hw hne' hle

theorem union_rootSizesExact {ds out : DSA} {n1 n2 : Int}
    (hF : Forest ds) (hexact : RootSizesExact ds)
    (h1 : SelfRoot ds n1) (h2 : SelfRoot ds n2) (hne : n1 ≠ n2)
    (hu : unionDSA n1 n2 ds = some out) : RootSizesExact out := by
  have effect := union_linkEffect hF h1 h2 hne hu
  obtain ⟨hl, hw, hne', _⟩ := union_orientation h1 h2 hne
  exact effect.rootSizesExact hF hexact hl hw hne'

theorem union_selfRoot {ds out : DSA} {n1 n2 : Int}
    (hF : Forest ds) (h1 : SelfRoot ds n1) (h2 : SelfRoot ds n2) (hne : n1 ≠ n2)
    (hu : unionDSA n1 n2 ds = some out) (r : Int) :
    SelfRoot out r ↔ SelfRoot ds r ∧ r ≠ loser ds n1 n2 := by
  have effect := union_linkEffect hF h1 h2 hne hu
  exact effect.selfRoot_iff (union_orientation h1 h2 hne).2.2.1 r

theorem union_find {ds out : DSA} {n1 n2 : Int}
    (hF : Forest ds) (hexact : RootSizesExact ds)
    (h1 : SelfRoot ds n1) (h2 : SelfRoot ds n2) (hne : n1 ≠ n2)
    (hu : unionDSA n1 n2 ds = some out) (v : Int) :
    findDSA out v = (findDSA ds v).map
      (renameRoot (loser ds n1 n2) (winner ds n1 n2)) := by
  have effect := union_linkEffect hF h1 h2 hne hu
  obtain ⟨hl, hw, hne', _⟩ := union_orientation h1 h2 hne
  exact effect.find_map hF hexact hl hw hne' v

private theorem renameRoot_eq_iff {losing surviving q s : Int}
    (hne : losing ≠ surviving) :
    renameRoot losing surviving q = renameRoot losing surviving s ↔
      q = s ∨ (q = losing ∧ s = surviving) ∨ (q = surviving ∧ s = losing) := by
  by_cases hq : q = losing <;> by_cases hs : s = losing <;>
    simp_all [renameRoot] <;> omega

private theorem sameComponent_selfRoot_right {ds : DSA} {r v : Int}
    (hr : SelfRoot ds r) : SameComponent ds v r ↔ Root ds v r := by
  constructor
  · rintro ⟨q, hvq, hrq⟩
    have he : q = r := hrq.unique (root_self hr)
    subst q
    exact hvq
  · intro h
    exact ⟨r, h, root_self hr⟩

private theorem sameComponent_selfRoot_left {ds : DSA} {r v : Int}
    (hr : SelfRoot ds r) : SameComponent ds r v ↔ Root ds v r := by
  constructor
  · intro h
    exact (sameComponent_selfRoot_right hr).mp (sameComponent_symm h)
  · intro h
    exact sameComponent_symm ((sameComponent_selfRoot_right hr).mpr h)

theorem LinkEffect.sameComponent_iff {ds out : DSA} {losing surviving : Int}
    (effect : LinkEffect ds out losing surviving) (hF : Forest ds)
    (hl : SelfRoot ds losing) (hw : SelfRoot ds surviving) (hne : losing ≠ surviving)
    (u v : Int) : SameComponent out u v ↔ SameComponent ds u v ∨
      (SameComponent ds u losing ∧ SameComponent ds surviving v) ∨
      (SameComponent ds u surviving ∧ SameComponent ds losing v) := by
  rw [sameComponent_selfRoot_right hl, sameComponent_selfRoot_left hw,
    sameComponent_selfRoot_right hw, sameComponent_selfRoot_left hl]
  constructor
  · rintro ⟨r, hu, hv⟩
    obtain ⟨q, hqu, hqr⟩ := (effect.root_iff hF hl hw hne u r).mp hu
    obtain ⟨s, hsv, hsr⟩ := (effect.root_iff hF hl hw hne v r).mp hv
    have he := (renameRoot_eq_iff hne).mp (hqr.trans hsr.symm)
    rcases he with he | ⟨hql, hsw⟩ | ⟨hqw, hsl⟩
    · subst s
      exact Or.inl ⟨q, hqu, hsv⟩
    · subst q
      subst s
      exact Or.inr (Or.inl ⟨hqu, hsv⟩)
    · subst q
      subst s
      exact Or.inr (Or.inr ⟨hqu, hsv⟩)
  · rintro (hold | ⟨hul, hvw⟩ | ⟨huw, hvl⟩)
    · obtain ⟨r, hu, hv⟩ := hold
      exact ⟨renameRoot losing surviving r, effect.root_forward hl hw hne hu,
        effect.root_forward hl hw hne hv⟩
    · refine ⟨surviving, ?_, ?_⟩
      · simpa [renameRoot] using effect.root_forward hl hw hne hul
      · simpa [renameRoot, Ne.symm hne] using effect.root_forward hl hw hne hvw
    · refine ⟨surviving, ?_, ?_⟩
      · simpa [renameRoot, Ne.symm hne] using effect.root_forward hl hw hne huw
      · simpa [renameRoot] using effect.root_forward hl hw hne hvl

theorem union_sameComponent {ds out : DSA} {n1 n2 : Int}
    (hF : Forest ds) (h1 : SelfRoot ds n1) (h2 : SelfRoot ds n2) (hne : n1 ≠ n2)
    (hu : unionDSA n1 n2 ds = some out) (u v : Int) :
    SameComponent out u v ↔ SameComponent ds u v ∨
      (SameComponent ds u n1 ∧ SameComponent ds n2 v) ∨
      (SameComponent ds u n2 ∧ SameComponent ds n1 v) := by
  have effect := union_linkEffect hF h1 h2 hne hu
  obtain ⟨hl, hw, hne', _⟩ := union_orientation h1 h2 hne
  have he := effect.sameComponent_iff hF hl hw hne' u v
  by_cases hlt : cache ds n1 < cache ds n2
  · simpa only [loser, winner, ite_eq_left hlt] using he
  · simpa only [loser, winner, ite_eq_right hlt, or_comm] using he

end Connectivity.ParentUnion
