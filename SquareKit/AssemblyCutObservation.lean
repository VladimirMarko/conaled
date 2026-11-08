import SquareKit.AssemblyCutPrograms

/-! Self-reference forces finite observations to persist along larger cuts. -/
namespace Realizability.Assembly
open Encodable Denumerable
open Nat.Partrec (Code)

private theorem partrec_if_some {α : Type} [Primcodable α]
    {p : α → Prop} [DecidablePred p] (hp : PrimrecPred p)
    {f : α → Nat} (hf : Computable f) {g : α → Part Nat} (hg : Partrec g) :
    Partrec (fun a => if p a then Part.some (f a) else g a) := by
  have hc : Computable (fun a => if p a then 0 else 1) :=
    (Primrec.ite hp (Primrec.const 0) (Primrec.const 1)).to_comp
  exact (Partrec.nat_casesOn_right hc hf (hg.comp Computable.fst).to₂).of_eq
    (fun a => by by_cases h : p a <;> simp [h])

/-- If observing the finite cut forces a value, the same observation can be
made on any primitive-recursive larger cut. This includes the full cut. -/
theorem cut_growth (q : Nat → Part Nat) (hq : Partrec q)
    (n v : Nat) (P : Nat → Prop) [DecidablePred P] (hP : PrimrecPred P)
    (hn : ∀ k, k < n → P k)
    (hforce : ∀ e, Cut e n → v ∈ q e) :
    ∃ e, (∀ k, ((ofNat Code e).eval k).Dom ↔ P k) ∧ v ∈ q e := by
  let body : Code → Nat → Part Nat := fun c k =>
    if k < n then Part.some 0 else
      (q (encode c)).bind fun w => Part.ofOption (if P k ∧ w = v then some 0 else none)
  have hb : Partrec₂ body := by
    apply partrec_if_some (Primrec.nat_lt.comp Primrec.snd (Primrec.const n)) (Computable.const 0)
    apply Partrec.bind (hq.comp (Computable.encode.comp Computable.fst))
    apply Computable.ofOption
    exact (Primrec.ite
      ((hP.comp (Primrec.snd.comp Primrec.fst)).and
        (Primrec.eq.comp Primrec.snd (Primrec.const v)))
      (Primrec.const (some 0)) (Primrec.const none)).to_comp
  obtain ⟨c, hc⟩ := Code.fixed_point₂ hb
  have hd (k : Nat) : (c.eval k).Dom ↔ k < n ∨ (P k ∧ v ∈ q (encode c)) := by
    rw [congrFun hc k]
    dsimp [body]
    split_ifs with h
    · simp [h]
    · simp only [Part.bind_dom, Part.ofOption_dom, Option.isSome_ite]
      constructor
      · rintro ⟨hq', ht⟩
        have hv : P k ∧ (q (encode c)).get hq' = v := by simpa using ht
        exact Or.inr ⟨hv.1, ⟨hq', hv.2⟩⟩
      · rintro (hk | ⟨hp, hmem⟩)
        · exact (h hk).elim
        · obtain ⟨hdom, hval⟩ := hmem
          exact ⟨hdom, by simp [hp, hval]⟩
  have hv : v ∈ q (encode c) := by
    by_contra hv
    apply hv
    apply hforce
    intro k
    simpa [hv] using hd k
  refine ⟨encode c, ?_, hv⟩
  intro k
  simpa only [ofNat_encode] using (hd k).trans
    (by simp only [hv, and_true]; exact ⟨fun h => h.elim (hn k) id, Or.inr⟩)

/-- A value forced on the full cut already occurs on some finite cut.
The finite bound is extracted by proof; the observer never receives it. -/
theorem cut_finite_witness (q : Nat → Part Nat) (hq : Partrec q) (v : Nat)
    (hforce : ∀ e, FullCut e → v ∈ q e) :
    ∃ e n, Cut e n ∧ v ∈ q e := by
  obtain ⟨Q, hQ⟩ := Code.exists_code.mp (Partrec.nat_iff.mp hq)
  let body : Code → Nat → Part Nat := fun c k =>
    Part.ofOption (if Code.evaln k Q (encode c) = some v then none else some 0)
  have hb : Partrec₂ body := by
    apply Computable.ofOption
    exact (Primrec.ite (Primrec.eq.comp
      (Code.primrec_evaln.comp ((Primrec.snd.pair (Primrec.const Q)).pair
        (Primrec.encode.comp Primrec.fst))) (Primrec.const (some v)))
      (Primrec.const none) (Primrec.const (some 0))).to_comp
  obtain ⟨c, hc⟩ := Code.fixed_point₂ hb
  have hd (k : Nat) : (c.eval k).Dom ↔ Code.evaln k Q (encode c) ≠ some v := by
    rw [congrFun hc k]
    dsimp [body]
    split_ifs <;> simp_all
  have hv : v ∈ q (encode c) := by
    by_contra hv
    apply hv
    apply hforce
    intro k
    simp only [ofNat_encode]
    apply (hd k).mpr
    intro hk
    apply hv
    rw [← hQ]
    exact Code.evaln_sound (by simpa using hk)
  have hex : ∃ k, Code.evaln k Q (encode c) = some v := by
    have hv' : v ∈ Q.eval (encode c) := by simpa [hQ] using hv
    simpa using Code.evaln_complete.mp hv'
  let b := Nat.find hex
  have hbval : Code.evaln b Q (encode c) = some v := Nat.find_spec hex
  refine ⟨encode c, b, ?_, hv⟩
  intro k
  simp only [ofNat_encode]
  rw [hd]
  constructor
  · intro hk
    by_contra hkb
    apply hk
    exact Code.evaln_mono (show b ≤ k by omega) (by simpa using hbval)
  · intro hkb hk
    exact Nat.find_min hex hkb hk

end Realizability.Assembly
