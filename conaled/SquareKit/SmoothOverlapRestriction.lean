import SquareKit.SmoothPrincipalOverlap

/-! Experimental inverse-graph restrictions of algebraic overlap arrows. -/
noncomputable section
open scoped ContDiff Topology
namespace SquareKit.SmoothAlgebra.PresentedLocalization
variable {n m : ℕ}

private def overlapCoordinates (q : Free n) : Fin (n+1) → Free (n+1) :=
  Fin.snoc (fun i => generator i.castSucc) (Localization.extend q * generator (Fin.last n))
private def overlapSubstitute (q : Free n) : Hom (Free (n+1)) (Free (n+1)) :=
  pullback (overlapCoordinates q)

private theorem overlap_inverse (r : Fin m → Free n) (p q : Free n) :
    overlapLeft r p q (inverse r p) = base r (p*q) (Presentation.projection r q)*inverse r (p*q) := by
  apply Localization.inverse_unique (a := base r (p*q) (Presentation.projection r p))
  · have h := congrArg (overlapLeft r p q).toAlgHom (inverse_relation r p)
    simp only [map_mul,map_one] at h
    have hb := congrArg (fun h : Hom (Presentation.Carrier r) (Carrier r (p*q)) => h (Presentation.projection r p)) (overlapLeft_base r p q)
    change overlapLeft r p q (base r p (Presentation.projection r p)) = _ at hb
    change overlapLeft r p q (base r p (Presentation.projection r p))*overlapLeft r p q (inverse r p)=1 at h
    rw [hb] at h
    exact h
  · rw [← mul_assoc,← (base r (p*q)).map_mul,← (Presentation.projection r).map_mul]
    exact inverse_relation r (p*q)

private theorem overlap_substitute (r : Fin m → Free n) (p q : Free n) :
    Hom.comp (overlapLeft r p q) (Presentation.projection (Presentation.relations r (equation p))) =
      Hom.comp (Presentation.projection (Presentation.relations r (equation (p*q)))) (overlapSubstitute q) := by
  apply hom_ext_generators
  intro j
  refine Fin.lastCases ?_ (fun i => ?_) j
  · change overlapLeft r p q (inverse r p) = _
    rw [overlap_inverse]
    change _ = Presentation.projection _ (overlapSubstitute q (generator (Fin.last n)))
    rw [show overlapSubstitute q (generator (Fin.last n)) = Localization.extend q * generator (Fin.last n) from
      (pullback_generator (overlapCoordinates q) (Fin.last n)).trans (Fin.snoc_last _ _)]
    rw [(Presentation.projection _).map_mul]
    rfl
  · have hb := congrArg (fun h : Hom (Presentation.Carrier r) (Carrier r (p*q)) => h (Presentation.projection r (generator i))) (overlapLeft_base r p q)
    change overlapLeft r p q (base r p (Presentation.projection r (generator i))) = base r (p*q) (Presentation.projection r (generator i)) at hb
    change overlapLeft r p q (base r p (Presentation.projection r (generator i))) = _
    rw [hb]
    change _ = Presentation.projection _ (overlapSubstitute q (generator i.castSucc))
    rw [show overlapSubstitute q (generator i.castSucc) = generator i.castSucc from
      (pullback_generator (overlapCoordinates q) i.castSucc).trans (Fin.snoc_castSucc _ _ i)]
    rfl

private theorem overlap_right_inverse (r : Fin m → Free n) (p q : Free n) :
    overlapRight r p q (inverse r q) = base r (p*q) (Presentation.projection r p)*inverse r (p*q) := by
  apply Localization.inverse_unique (a := base r (p*q) (Presentation.projection r q))
  · have h := congrArg (overlapRight r p q).toAlgHom (inverse_relation r q)
    simp only [map_mul,map_one] at h
    have hb := congrArg (fun h : Hom (Presentation.Carrier r) (Carrier r (p*q)) => h (Presentation.projection r q)) (overlapRight_base r p q)
    change overlapRight r p q (base r q (Presentation.projection r q)) = _ at hb
    change overlapRight r p q (base r q (Presentation.projection r q))*overlapRight r p q (inverse r q)=1 at h
    rw [hb] at h
    exact h
  · rw [← mul_assoc,← (base r (p*q)).map_mul,← (Presentation.projection r).map_mul]
    rw [mul_comm q p]
    exact inverse_relation r (p*q)

private theorem overlap_right_substitute (r : Fin m → Free n) (p q : Free n) :
    Hom.comp (overlapRight r p q) (Presentation.projection (Presentation.relations r (equation q))) =
      Hom.comp (Presentation.projection (Presentation.relations r (equation (p*q)))) (overlapSubstitute p) := by
  apply hom_ext_generators
  intro j
  refine Fin.lastCases ?_ (fun i => ?_) j
  · change overlapRight r p q (inverse r q) = _
    rw [overlap_right_inverse]
    change _ = Presentation.projection _ (overlapSubstitute p (generator (Fin.last n)))
    rw [show overlapSubstitute p (generator (Fin.last n)) = Localization.extend p * generator (Fin.last n) from
      (pullback_generator (overlapCoordinates p) (Fin.last n)).trans (Fin.snoc_last _ _)]
    rw [(Presentation.projection _).map_mul]
    rfl
  · have hb := congrArg (fun h : Hom (Presentation.Carrier r) (Carrier r (p*q)) => h (Presentation.projection r (generator i))) (overlapRight_base r p q)
    change overlapRight r p q (base r q (Presentation.projection r (generator i))) = base r (p*q) (Presentation.projection r (generator i)) at hb
    change overlapRight r p q (base r q (Presentation.projection r (generator i))) = _
    rw [hb]
    change _ = Presentation.projection _ (overlapSubstitute p (generator i.castSucc))
    rw [show overlapSubstitute p (generator i.castSucc) = generator i.castSucc from
      (pullback_generator (overlapCoordinates p) i.castSucc).trans (Fin.snoc_castSucc _ _ i)]
    rfl

private theorem substitute_graph (p q : Free n) (H : Free (n+1)) (x : Fin n → ℝ)
    (hx : (p*q).val x ≠ 0) : graphValue (p*q) (overlapSubstitute q H) x = graphValue p H x := by
  apply congrArg H.val
  funext j
  refine Fin.lastCases ?_ (fun i => ?_) j
  · simp only [overlapCoordinates,Fin.snoc_last]
    change q.val (SmoothInverseGraph.base (SmoothInverseGraph.graph (p*q).val x)) *
      SmoothInverseGraph.graph (p*q).val x (Fin.last n) = SmoothInverseGraph.graph p.val x (Fin.last n)
    rw [SmoothInverseGraph.base_graph,SmoothInverseGraph.graph_last,SmoothInverseGraph.graph_last]
    change q.val x*(p.val x*q.val x)⁻¹=(p.val x)⁻¹
    have hp := left_ne_zero_of_mul hx
    have hq := right_ne_zero_of_mul hx
    field_simp
  -- The original coordinates are unchanged by the substitution.
  · simp only [overlapCoordinates,Fin.snoc_castSucc]
    change SmoothInverseGraph.graph (p*q).val x i.castSucc = SmoothInverseGraph.graph p.val x i.castSucc
    simp [SmoothInverseGraph.graph]

/-- An overlap image has the same local coefficient class as the original inverse-graph section. -/
theorem overlap_graph (r : Fin m → Free n) (p q : Free n) (H K : Free (n+1))
    (hk : overlapLeft r p q (Presentation.projection (Presentation.relations r (equation p)) H) =
      Presentation.projection (Presentation.relations r (equation (p*q))) K)
    (x : Fin n → ℝ) (hx : (p*q).val x ≠ 0) :
    LocalIdeal.Mem r (fun y => graphValue p H y-graphValue (p*q) K y) x := by
  have he := congrArg (fun h : Hom (Free (n+1)) (Carrier r (p*q)) => h H) (overlap_substitute r p q)
  change overlapLeft r p q (Presentation.projection _ H) = Presentation.projection _ (overlapSubstitute q H) at he
  have hz : Presentation.projection (Presentation.relations r (equation (p*q))) (overlapSubstitute q H-K)=0 := by
    change (Presentation.projection (Presentation.relations r (equation (p*q)))).toAlgHom (overlapSubstitute q H-K)=0
    rw [map_sub,sub_eq_zero]
    exact he.symm.trans hk
  have hm := (zero_iff_local r (p*q) (overlapSubstitute q H-K)).mp hz x hx
  apply LocalIdeal.congr hm
  have hU := (isOpen_ne_fun (show ContDiff ℝ ∞ (p*q).val from (p*q).property).continuous continuous_const).mem_nhds hx
  filter_upwards [hU] with y hy
  change graphValue (p*q) (overlapSubstitute q H) y-graphValue (p*q) K y = _
  rw [substitute_graph p q H y hy]

/-- Compatibility on the actual algebra overlap gives equality of local ideal classes. -/
theorem overlap_compatible_local (r : Fin m → Free n) (p q : Free n) (H K : Free (n+1))
    (hk : overlapLeft r p q (Presentation.projection (Presentation.relations r (equation p)) H) =
      overlapRight r p q (Presentation.projection (Presentation.relations r (equation q)) K))
    (x : Fin n → ℝ) (hp : p.val x ≠ 0) (hq : q.val x ≠ 0) :
    LocalIdeal.Mem r (fun y => graphValue p H y-graphValue q K y) x := by
  have hr : Hom.comp (overlapRight r p q) (Presentation.projection (Presentation.relations r (equation q))) =
      Hom.comp (Presentation.projection (Presentation.relations r (equation (p*q)))) (overlapSubstitute p) := by
    exact overlap_right_substitute r p q
  have hkr := congrArg (fun h : Hom (Free (n+1)) (Carrier r (p*q)) => h K) hr
  change overlapRight r p q (Presentation.projection _ K) = Presentation.projection _ (overlapSubstitute p K) at hkr
  have hm := overlap_graph r p q H (overlapSubstitute p K) (hk.trans hkr) x (mul_ne_zero hp hq)
  apply LocalIdeal.congr hm
  have hU := (isOpen_ne_fun (show ContDiff ℝ ∞ (p*q).val from (p*q).property).continuous continuous_const).mem_nhds (mul_ne_zero hp hq)
  filter_upwards [hU] with y hy
  have he : graphValue (p*q) (overlapSubstitute p K) y = graphValue q K y := by
    simpa only [mul_comm q p] using substitute_graph q p K y (by simpa only [mul_comm q p] using hy)
  rw [he]


end SquareKit.SmoothAlgebra.PresentedLocalization
