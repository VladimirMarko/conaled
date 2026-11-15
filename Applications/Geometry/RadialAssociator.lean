import Applications.Geometry.RadialDisplacementRemainder

/-! Cubic estimates for parenthesized applications of the actual displacement. -/
noncomputable section
namespace RadialMetric
open Set Metric Complex Asymptotics
open scoped Topology ComplexConjugate

def cubicCorrection (p : State) : ℂ := conj p.1*p.2^2+conj p.1*p.1*p.2

private theorem triple_difference {E : Type*} [NormedAddCommGroup E]
    {a b c d e f : E → ℂ}
    (ha : a =O[𝓝 0] (fun p => ‖p‖))
    (hb : b =O[𝓝 0] (fun p => ‖p‖))
    (hc : c =O[𝓝 0] (fun p => ‖p‖))
    (hd : d =O[𝓝 0] (fun p => ‖p‖))
    (he : e =O[𝓝 0] (fun p => ‖p‖))
    (had : (fun p => a p-d p) =O[𝓝 0] (fun p => ‖p‖^3))
    (hbe : (fun p => b p-e p) =O[𝓝 0] (fun p => ‖p‖^3))
    (hcf : (fun p => c p-f p) =O[𝓝 0] (fun p => ‖p‖^3)) :
    (fun p => a p*b p*c p-d p*e p*f p) =O[𝓝 0] (fun p => ‖p‖^5) := by
  have h1 : (fun p => (a p-d p)*b p*c p) =O[𝓝 0] (fun p => ‖p‖^5) := by
    convert (had.mul hb).mul hc using 1
    funext p; ring
  have h2 : (fun p => d p*(b p-e p)*c p) =O[𝓝 0] (fun p => ‖p‖^5) := by
    convert (hd.mul hbe).mul hc using 1
    funext p; ring
  have h3 : (fun p => d p*e p*(c p-f p)) =O[𝓝 0] (fun p => ‖p‖^5) := by
    convert (hd.mul he).mul hcf using 1
    funext p; ring
  apply ((h1.add h2).add h3).congr_left
  intro p; ring

theorem cubicCorrection_bigO {E : Type*} [NormedAddCommGroup E] {α : E → State}
    (h : α =O[𝓝 0] (fun p => ‖p‖)) :
    (fun p => cubicCorrection (α p)) =O[𝓝 0] (fun p => ‖p‖^3) := by
  have hz := complexConjugate_bigO h.prod_left_fst
  have h1 : (fun p => conj (α p).1*(α p).2^2) =O[𝓝 0] (fun p => ‖p‖^3) := by
    convert hz.mul (h.prod_left_snd.pow 2) using 1
    funext p; ring
  have h2 : (fun p => conj (α p).1*(α p).1*(α p).2) =O[𝓝 0] (fun p => ‖p‖^3) := by
    convert (hz.mul h.prod_left_fst).mul h.prod_left_snd using 1
    funext p; ring
  exact h1.add h2

theorem cubicCorrection_difference {E : Type*} [NormedAddCommGroup E] {α β : E → State}
    (ha : α =O[𝓝 0] (fun p => ‖p‖)) (hb : β =O[𝓝 0] (fun p => ‖p‖))
    (hd : (fun p => α p-β p) =O[𝓝 0] (fun p => ‖p‖^3)) :
    (fun p => cubicCorrection (α p)-cubicCorrection (β p)) =O[𝓝 0] (fun p => ‖p‖^5) := by
  have hdz : (fun p => conj (α p).1-conj (β p).1) =O[𝓝 0] (fun p => ‖p‖^3) := by
    simpa only [Prod.fst_sub,map_sub] using complexConjugate_bigO hd.prod_left_fst
  have h1 := triple_difference (complexConjugate_bigO ha.prod_left_fst)
    ha.prod_left_snd ha.prod_left_snd (complexConjugate_bigO hb.prod_left_fst)
    hb.prod_left_snd hdz hd.prod_left_snd hd.prod_left_snd
  have h2 := triple_difference (complexConjugate_bigO ha.prod_left_fst)
    ha.prod_left_fst ha.prod_left_snd (complexConjugate_bigO hb.prod_left_fst)
    hb.prod_left_fst hdz hd.prod_left_fst hd.prod_left_snd
  apply (h1.add h2).congr_left
  intro p
  simp only [cubicCorrection]
  ring

theorem displacement_cubic_error : (fun p : State => displacement p-p.1-p.2+cubicCorrection p)
    =O[𝓝 0] (fun p => ‖p‖^5) := by
  apply displacement_remainder.congr_left
  intro p
  rw [normSq_eq_conj_mul_self]
  simp [cubicCorrection]
  ring

theorem displacement_deviation : (fun p : State => displacement p-(p.1+p.2))
    =O[𝓝 0] (fun p => ‖p‖^3) := by
  have he := displacement_cubic_error.trans
    (isLittleO_norm_pow_norm_pow (E' := State) (by norm_num : 3 < 5)).isBigO
  have hc := cubicCorrection_bigO ((isBigO_refl (fun p : State => p) (𝓝 0)).norm_right)
  apply (he.sub hc).congr_left
  intro p
  ring

end RadialMetric
