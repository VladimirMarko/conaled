import Applications.Probability.SamplerWork

/-! A reverse traversal with a carried total avoids repeated prefix summation. -/
namespace Applications.Probability.LinearRowSelector
open scoped BigOperators ENNReal
open SamplerWork

/-- `total` is runtime data. Its equality proof is erased; no sum is computed
while traversing. Each visited entry reads one weight and subtracts it from the
remaining total before comparing the ticket with the resulting cut. -/
def select (τ : Tariff) : (m : ℕ) → (w : Fin m → ℕ) →
    (total : ℕ) → total=∑ i,w i → Fin total → ((i : Fin m) × Fin (w i)) × ℕ
  | 0,_,_,h,k => Fin.elim0 (Fin.cast (h.trans (by simp)) k)
  | m+1,w,total,ht,k =>
    let last := w (Fin.last m)
    let cut := total-last
    have hc : cut=∑ i : Fin m,w i.castSucc := by
      simp only [cut,last,ht,Fin.sum_univ_castSucc,Nat.add_sub_cancel]
    if h : k.val<cut then
      let r := select τ m (fun i => w i.castSucc) cut hc ⟨k.val,h⟩
      (⟨r.1.1.castSucc,r.1.2⟩,r.2+τ.lookup+2*τ.arithmetic)
    else
      (⟨Fin.last m,⟨k.val-cut,by
        have hk := k.isLt
        have he : total=cut+last := by rw [hc,ht,Fin.sum_univ_castSucc]
        omega⟩⟩,τ.lookup+3*τ.arithmetic)

theorem select_encode (τ : Tariff) (m : ℕ) (w : Fin m → ℕ)
    (total : ℕ) (ht : total=∑ i,w i) (k : Fin total) :
    finSigmaFinEquiv (select τ m w total ht k).1=Fin.cast ht k := by
  induction m generalizing total with
  | zero => exact Fin.elim0 (Fin.cast (ht.trans (by simp)) k)
  | succ m ih =>
    simp only [select]
    split
    · rename_i h
      apply Fin.ext
      have hi := congrArg Fin.val (ih (fun i => w i.castSucc) _ (by rw [ht,Fin.sum_univ_castSucc,Nat.add_sub_cancel]) ⟨k.val,h⟩)
      simp only [finSigmaFinEquiv_apply,Fin.val_cast] at hi ⊢
      convert hi using 1
      congr 1
    · rename_i h
      apply Fin.ext
      rw [finSigmaFinEquiv_apply]
      change (∑ i : Fin m,w i.castSucc)+(k.val-(total-w (Fin.last m)))=k.val
      have hc : total-w (Fin.last m)=∑ i : Fin m,w i.castSucc := by
        rw [ht,Fin.sum_univ_castSucc,Nat.add_sub_cancel]
      omega

theorem select_value (τ : Tariff) (m : ℕ) (w : Fin m → ℕ)
    (total : ℕ) (ht : total=∑ i,w i) (k : Fin total) :
    (select τ m w total ht k).1=finSigmaFinEquiv.symm (Fin.cast ht k) :=
  finSigmaFinEquiv.injective ((select_encode τ m w total ht k).trans
    (finSigmaFinEquiv.apply_symm_apply _).symm)

theorem select_bound (τ : Tariff) (m : ℕ) (w : Fin m → ℕ)
    (total : ℕ) (ht : total=∑ i,w i) (k : Fin total) :
    (select τ m w total ht k).2≤m*(τ.lookup+2*τ.arithmetic)+τ.arithmetic := by
  induction m generalizing total with
  | zero => exact Fin.elim0 (Fin.cast (ht.trans (by simp)) k)
  | succ m ih =>
    simp only [select]
    split
    · rename_i h
      have hi := ih (fun i => w i.castSucc) _ (by rw [ht,Fin.sum_univ_castSucc,Nat.add_sub_cancel]) ⟨k.val,h⟩
      nlinarith
    · dsimp
      nlinarith

def rowSelect {β : Type} (p : PreparedRow β) (τ : Tariff) (k : Fin p.total) : β × ℕ :=
  let r := select τ p.size p.weight p.total p.total_eq k
  (p.outcome r.1.1,r.2+τ.outcome)

theorem rowSelect_value {β : Type} (p : PreparedRow β) (τ : Tariff) (k : Fin p.total) :
    (rowSelect p τ k).1=p.select k := by
  simp [rowSelect,select_value,PreparedRow.select]

theorem rowSelect_bound {β : Type} (p : PreparedRow β) (τ : Tariff) (k : Fin p.total) :
    (rowSelect p τ k).2≤p.size*(τ.lookup+2*τ.arithmetic)+τ.arithmetic+τ.outcome :=
  Nat.add_le_add_right (select_bound τ _ _ _ _ _) _

/-- Exact interval identity implies the complete multiplicity law, including
repeated outcomes and zero-weight intervals. -/
theorem sum_rowSelect {β : Type} (p : PreparedRow β) (τ : Tariff) (f : β → ℝ≥0∞) :
    ∑ k : Fin p.total, f (rowSelect p τ k).1=∑ i,(p.weight i : ℝ≥0∞)*f (p.outcome i) := by
  simp_rw [rowSelect_value]
  exact p.sum_select f
end Applications.Probability.LinearRowSelector
