import Applications.Parallel.FFTLayers
import Applications.Parallel.ComplexFFT
import Mathlib.Data.List.OfFn

/-! Native complete FFT layers, lifted into independent register slices. -/
namespace Applications.Parallel.FFTUnitary
open scoped BigOperators Matrix

namespace Round

variable {N M K : ℕ}

theorem get_disjoint (r : Round N) (i j : Fin r.gates.length) (hne : i ≠ j)
    (a b : Fin 2) : (r.gates.get i).coordinate a ≠ (r.gates.get j).coordinate b := by
  rcases lt_or_gt_of_ne hne with h | h
  · exact (List.pairwise_iff_get.mp r.disjoint i j h) a b
  · exact Ne.symm ((List.pairwise_iff_get.mp r.disjoint j i h) b a)

/-- Independent copies use disjoint slices of one unchanged register set. -/
noncomputable def copyGate (e : Fin M × Fin N ≃ Fin K) (copy : Fin M)
    (g : Gate N) : Gate K :=
  Gate.ofPair ⟨fun i => e (copy,g.coordinate i), by
    intro i j h
    exact g.coordinate_injective (congrArg Prod.snd (e.injective h))⟩ g.block

@[simp] theorem copyGate_coordinate (e : Fin M × Fin N ≃ Fin K) (copy : Fin M)
    (g : Gate N) (i : Fin 2) : (copyGate e copy g).coordinate i = e (copy,g.coordinate i) := by
  exact Gate.ofPair_coordinate _ _ _

noncomputable def copies (e : Fin M × Fin N ≃ Fin K) (r : Round N) : Round K where
  gates := List.ofFn (fun i : Fin (M * r.gates.length) =>
    let p := finProdFinEquiv.symm i
    copyGate e p.1 (r.gates.get p.2))
  disjoint := by
    rw [List.pairwise_ofFn]
    intro i j hij a b eq
    simp only [copyGate_coordinate] at eq
    have same := e.injective eq
    have hc := congrArg Prod.fst same
    have hp := congrArg Prod.snd same
    have hg : (finProdFinEquiv.symm i).2 ≠ (finProdFinEquiv.symm j).2 := by
      intro h
      have whole : finProdFinEquiv.symm i = finProdFinEquiv.symm j := Prod.ext hc h
      exact (ne_of_lt hij) (finProdFinEquiv.symm.injective whole)
    exact r.get_disjoint _ _ hg a b hp

@[simp] theorem copies_gateCount (e : Fin M × Fin N ≃ Fin K) (r : Round N) :
    (copies e r).gateCount = M * r.gateCount := by simp [copies,gateCount]

theorem copies_complete (e : Fin M × Fin N ≃ Fin K) (r : Round N) (hr : r.Complete) :
    (copies e r).Complete := by
  intro k
  obtain ⟨g,hg,t,ht⟩ := hr (e.symm k).2
  obtain ⟨j,hj⟩ := List.mem_iff_get.mp hg
  refine ⟨copyGate e (e.symm k).1 g,?_,t,?_⟩
  · rw [copies,List.mem_ofFn]
    refine ⟨finProdFinEquiv ((e.symm k).1,j),?_⟩
    simp only [Equiv.symm_apply_apply,hj]
  · simp only [copyGate_coordinate,ht,Prod.mk.eta,Equiv.apply_symm_apply]

/-- A lifted matching reads precisely the original inputs from its own slice. -/
theorem copies_mul_coordinate (e : Fin M × Fin N ≃ Fin K) (r : Round N)
    (copy : Fin M) (g : Gate N) (hg : g ∈ r.gates) (t : Fin 2)
    (A : Matrix (Fin K) (Fin K) ℂ) (j : Fin K) :
    (((copies e r).unitary : Matrix (Fin K) (Fin K) ℂ) * A) (e (copy,g.coordinate t)) j =
      ∑ b, g.block t b * A (e (copy,g.coordinate b)) j := by
  have mem : copyGate e copy g ∈ (copies e r).gates := by
    obtain ⟨i,hi⟩ := List.mem_iff_get.mp hg
    rw [copies,List.mem_ofFn]
    exact ⟨finProdFinEquiv (copy,i),by simpa only [Equiv.symm_apply_apply] using congrArg (copyGate e copy) hi⟩
  have block : (copyGate e copy g).block = g.block := rfl
  simpa only [copyGate_coordinate,block,unitary] using
    matching_mul_coordinate _ (copies e r).disjoint (copyGate e copy g) mem t A j

/-- Copy lifting preserves the exact row action, rather than only gate counts. -/
theorem copies_mulVec (e : Fin M × Fin N ≃ Fin K) (r : Round N) (hr : r.Complete)
    (x : Fin K → ℂ) (copy : Fin M) (i : Fin N) :
    (((copies e r).unitary : Matrix (Fin K) (Fin K) ℂ) *ᵥ x) (e (copy,i)) =
      ((r.unitary : Matrix (Fin N) (Fin N) ℂ) *ᵥ fun j => x (e (copy,j))) i := by
  obtain ⟨g,hg,t,rfl⟩ := hr i
  have lhs := copies_mul_coordinate e r copy g hg t (fun a _ => x a) (e (copy,g.coordinate t))
  have rhs := matching_mul_coordinate _ r.disjoint g hg t
    (fun a _ => x (e (copy,a))) (g.coordinate t)
  exact lhs.trans rhs.symm

end Round
namespace Step
variable {N M K : ℕ}
noncomputable def copies (e : Fin M × Fin N ≃ Fin K) : Step N → Step K
  | .round r => .round (r.copies e)
  | .permute p => .permute ((e.symm.trans (Equiv.prodCongr (Equiv.refl _) p)).trans e)

def Complete : Step N → Prop | .round r => r.Complete | .permute _ => True

theorem copies_mulVec (e : Fin M × Fin N ≃ Fin K) (s : Step N) (hs : s.Complete)
    (x : Fin K → ℂ) (copy : Fin M) (i : Fin N) :
    (((copies e s).unitary : Matrix (Fin K) (Fin K) ℂ) *ᵥ x) (e (copy,i)) =
      ((s.unitary : Matrix (Fin N) (Fin N) ℂ) *ᵥ fun j => x (e (copy,j))) i := by
  cases s with
  | round r => exact r.copies_mulVec e hs x copy i
  | permute p => simp [copies,unitary,Matrix.mulVec, dotProduct, Matrix.submatrix_apply, Matrix.one_apply]

@[simp] theorem copies_gateCount (e : Fin M × Fin N ≃ Fin K) (s : Step N) :
    (copies e s).gateCount = M * s.gateCount := by cases s <;> simp [copies,gateCount]
@[simp] theorem copies_roundCount (e : Fin M × Fin N ≃ Fin K) (s : Step N) :
    (copies e s).roundCount = s.roundCount := by cases s <;> rfl

theorem copies_complete (e : Fin M × Fin N ≃ Fin K) (s : Step N) (h : s.Complete) :
    (copies e s).Complete := by
  cases s with
  | round r => exact r.copies_complete e h
  | permute p => trivial
end Step

namespace Program
variable {N M K : ℕ}
def Complete (p : Program N) : Prop := ∀ s ∈ p, s.Complete
noncomputable def copies (e : Fin M × Fin N ≃ Fin K) (p : Program N) : Program K :=
  p.map (Step.copies e)

theorem copies_mulVec (e : Fin M × Fin N ≃ Fin K) (p : Program N) (hp : p.Complete)
    (x : Fin K → ℂ) (copy : Fin M) (i : Fin N) :
    (((copies e p).unitary : Matrix (Fin K) (Fin K) ℂ) *ᵥ x) (e (copy,i)) =
      ((p.unitary : Matrix (Fin N) (Fin N) ℂ) *ᵥ fun j => x (e (copy,j))) i := by
  induction p generalizing x with
  | nil => simp [copies,unitary]
  | cons s ss ih =>
    simp only [copies,List.map_cons,unitary,Submonoid.coe_mul,← Matrix.mulVec_mulVec]
    change (((copies e ss).unitary : Matrix (Fin K) (Fin K) ℂ) *ᵥ
      ((Step.copies e s).unitary : Matrix (Fin K) (Fin K) ℂ) *ᵥ x) (e (copy,i)) = _
    rw [ih (fun t ht => hp t (List.mem_cons_of_mem s ht))]
    congr 1
    funext j
    exact Step.copies_mulVec e s (hp s (by simp)) x copy j

@[simp] theorem copies_gateCount (e : Fin M × Fin N ≃ Fin K) (p : Program N) :
    (copies e p).gateCount = M * p.gateCount := by
  induction p with
  | nil => simp [copies,gateCount]
  | cons s ss ih => simpa [copies,gateCount,Nat.mul_add] using congrArg (M*s.gateCount + ·) ih
@[simp] theorem copies_roundCount (e : Fin M × Fin N ≃ Fin K) (p : Program N) :
    (copies e p).roundCount = p.roundCount := by simp [copies,roundCount,List.map_map,Function.comp_def]

theorem copies_complete (e : Fin M × Fin N ≃ Fin K) (p : Program N) (hp : p.Complete) :
    (copies e p).Complete := by
  intro s hs
  obtain ⟨t,ht,rfl⟩ := List.mem_map.mp hs
  exact Step.copies_complete e t (hp t ht)
/-- Attach input phases to the first complete round, commuting them through
any leading free permutations. No phase is an extra machine instruction. -/
noncomputable def absorb (d : Fin N → _root_.unitary ℂ) : Program N → Program N
  | [] => []
  | .round r :: ss => .round (r.absorb d) :: ss
  | .permute q :: ss => .permute q :: absorb (fun i => d (q i)) ss

@[simp] theorem absorb_gateCount (d : Fin N → _root_.unitary ℂ) (p : Program N) :
    (absorb d p).gateCount = p.gateCount := by
  induction p generalizing d with
  | nil => rfl
  | cons s ss ih =>
    cases s with
    | round r => simp [absorb,gateCount,Step.gateCount]
    | permute q => simpa [absorb,gateCount,Step.gateCount] using ih (fun i => d (q i))
@[simp] theorem absorb_roundCount (d : Fin N → _root_.unitary ℂ) (p : Program N) :
    (absorb d p).roundCount = p.roundCount := by
  induction p generalizing d with
  | nil => rfl
  | cons s ss ih =>
    cases s with
    | round r => rfl
    | permute q => simpa [absorb,roundCount,Step.roundCount] using ih (fun i => d (q i))

theorem absorb_complete (d : Fin N → _root_.unitary ℂ) (p : Program N) (hp : p.Complete) :
    (absorb d p).Complete := by
  induction p generalizing d with
  | nil => simp [Complete,absorb]
  | cons s ss ih =>
    have head := hp s (by simp)
    have tail : Complete ss := fun t ht => hp t (List.mem_cons_of_mem s ht)
    cases s with
    | round r =>
      intro t ht
      rcases List.mem_cons.mp ht with rfl | ht
      · exact Round.absorb_complete d r head
      · exact tail t ht
    | permute q =>
      intro t ht
      rcases List.mem_cons.mp ht with rfl | ht
      · trivial
      · exact ih _ tail t ht

theorem absorb_mulVec (d : Fin N → _root_.unitary ℂ) (p : Program N) (hp : p.Complete)
    (empty : p.roundCount = 0 → ∀ i, d i = 1) (x : Fin N → ℂ) :
    ((absorb d p).unitary : Matrix (Fin N) (Fin N) ℂ) *ᵥ x =
      (p.unitary : Matrix (Fin N) (Fin N) ℂ) *ᵥ (fun i => (d i : ℂ) * x i) := by
  induction p generalizing d x with
  | nil => simp [absorb,unitary,empty rfl]
  | cons s ss ih =>
    have head := hp s (by simp)
    have tail : Complete ss := fun t ht => hp t (List.mem_cons_of_mem s ht)
    cases s with
    | round r =>
      simp only [absorb,unitary,Step.unitary,Round.absorb_unitary d r head,Submonoid.coe_mul,
        ← Matrix.mulVec_mulVec]
      congr 1
      simp only [diagonalUnitary,← Matrix.mulVec_mulVec]
      congr 1
      funext i
      simp [Matrix.mulVec,dotProduct,Matrix.diagonal_apply]
    | permute q =>
      simp only [absorb,unitary,Submonoid.coe_mul,← Matrix.mulVec_mulVec]
      rw [ih _ tail (by intro h i; exact empty (by simpa [roundCount,Step.roundCount] using h) (q i))]
      congr 1
      funext i
      simp [Step.unitary,Matrix.mulVec,dotProduct,Matrix.submatrix_apply,Matrix.one_apply]

@[simp] theorem unitary_append (p q : Program N) : (p ++ q).unitary = q.unitary * p.unitary := by
  induction p with
  | nil => simp [unitary]
  | cons s ss ih => simp only [List.cons_append,unitary,ih,mul_assoc]
@[simp] theorem gateCount_append (p q : Program N) : (p ++ q).gateCount = p.gateCount + q.gateCount := by
  simp [gateCount]
@[simp] theorem roundCount_append (p q : Program N) : (p ++ q).roundCount = p.roundCount + q.roundCount := by
  simp [roundCount]
theorem complete_append (p q : Program N) (hp : p.Complete) (hq : q.Complete) :
    (p ++ q).Complete := by
  intro s hs
  exact (List.mem_append.mp hs).elim (hp s) (hq s)

end Program

end Applications.Parallel.FFTUnitary
