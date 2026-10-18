import SquareKit.SmoothLocalization

/-! Experimental finite smooth presentations and adjoining one related coordinate.
The construction is an actual ordinary-ideal quotient with its inherited smooth operations. -/
noncomputable section
namespace SquareKit.SmoothAlgebra.Presentation
variable {n m : ℕ}

def ideal (r : Fin m → Free n) := Ideal.span (Set.range r)
abbrev Carrier (r : Fin m → Free n) := Free n ⧸ ideal r
instance (r : Fin m → Free n) : CommRing (Carrier r) := inferInstance
instance (r : Fin m → Free n) : Algebra ℝ (Carrier r) := inferInstance
instance (r : Fin m → Free n) : Structure (Carrier r) := inferInstance

def projection (r : Fin m → Free n) : Hom (Free n) (Carrier r) := Quotient.projection (ideal r)

def relations (r : Fin m → Free n) (q : Free (n+1)) : Fin (m+1) → Free (n+1) :=
  Fin.snoc (fun j => Localization.extend (k := 1) (r j)) q
abbrev Adjoin (r : Fin m → Free n) (q : Free (n+1)) := Carrier (relations r q)

theorem relation_zero (r : Fin m → Free n) (j : Fin m) : projection r (r j) = 0 :=
  Ideal.Quotient.eq_zero_iff_mem.mpr (Ideal.subset_span ⟨j,rfl⟩)

def inclusion (r : Fin m → Free n) (q : Free (n+1)) : Hom (Carrier r) (Adjoin r q) :=
  Quotient.lift (ideal r) (Hom.comp (projection (relations r q)) (Localization.extend (k := 1))) (by
    have hi : ideal r ≤ RingHom.ker (Hom.comp (projection (relations r q)) (Localization.extend (k := 1))).toAlgHom := by
      apply Ideal.span_le.mpr
      rintro p ⟨j,rfl⟩
      change projection (relations r q) (Localization.extend (r j)) = 0
      simpa [relations] using relation_zero (relations r q) j.castSucc
    exact fun p hp => hi hp)

def coordinate (r : Fin m → Free n) (q : Free (n+1)) : Adjoin r q :=
  projection (relations r q) (generator (Fin.last n))

theorem inclusion_projection (r : Fin m → Free n) (q : Free (n+1)) :
    Hom.comp (inclusion r q) (projection r) = Hom.comp (projection (relations r q)) Localization.extend :=
  Quotient.lift_projection _ _ _

theorem adjoin_relation (r : Fin m → Free n) (q : Free (n+1)) : projection (relations r q) q = 0 := by
  simpa [relations] using relation_zero (relations r q) (Fin.last m)

variable {B : Type*} [CommRing B] [Algebra ℝ B] [Structure B]

def coordinates (r : Fin m → Free n) (h : Hom (Carrier r) B) (b : B) : Fin (n+1) → B :=
  Fin.snoc (fun i => h (projection r (generator i))) b

theorem evaluate_extend (r : Fin m → Free n) (h : Hom (Carrier r) B) (b : B) (p : Free n) :
    evaluate (coordinates r h b) (Localization.extend (k := 1) p) = h (projection r p) := by
  have he := congrArg (fun k : Hom (Free n) B => k p)
    (evaluate_pullback (fun i => SmoothAlgebra.projection (Fin.castAdd 1 i)) (coordinates r h b))
  change evaluate (coordinates r h b) (Localization.extend p) =
    evaluate (fun i => act (SmoothAlgebra.projection (Fin.castAdd 1 i)) (coordinates r h b)) p at he
  simp only [Structure.projection] at he
  have hc : (fun i => coordinates r h b (Fin.castAdd 1 i)) = fun i => (Hom.comp h (projection r)) (generator i) := by
    funext i
    exact Fin.snoc_castSucc _ _ i
  rw [hc,evaluate_unique] at he
  exact he

def lift (r : Fin m → Free n) (q : Free (n+1)) (h : Hom (Carrier r) B) (b : B)
    (he : evaluate (coordinates r h b) q = 0) : Hom (Adjoin r q) B :=
  Quotient.lift (ideal (relations r q)) (evaluate (coordinates r h b)) (by
    have hi : ideal (relations r q) ≤ RingHom.ker (evaluate (coordinates r h b)).toAlgHom := by
      apply Ideal.span_le.mpr
      rintro p ⟨j,rfl⟩
      refine Fin.lastCases ?_ (fun i => ?_) j
      · simp only [relations,Fin.snoc_last]
        exact he
      · simp only [relations,Fin.snoc_castSucc]
        change evaluate (coordinates r h b) (Localization.extend (r i)) = 0
        rw [evaluate_extend,relation_zero]
        exact h.toAlgHom.map_zero
    exact fun p hp => hi hp)

theorem lift_inclusion (r : Fin m → Free n) (q : Free (n+1)) (h : Hom (Carrier r) B) (b : B)
    (he : evaluate (coordinates r h b) q = 0) : Hom.comp (lift r q h b he) (inclusion r q) = h := by
  apply Quotient.unique (ideal r)
  apply Hom.ext
  intro p
  exact evaluate_extend r h b p

theorem lift_coordinate (r : Fin m → Free n) (q : Free (n+1)) (h : Hom (Carrier r) B) (b : B)
    (he : evaluate (coordinates r h b) q = 0) : lift r q h b he (coordinate r q) = b := by
  exact (evaluate_generator (coordinates r h b) (Fin.last n)).trans (Fin.snoc_last _ _)

theorem unique (r : Fin m → Free n) (q : Free (n+1)) (h k : Hom (Adjoin r q) B)
    (hb : Hom.comp h (inclusion r q) = Hom.comp k (inclusion r q))
    (hv : h (coordinate r q) = k (coordinate r q)) : h=k := by
  apply Quotient.unique (ideal (relations r q))
  apply hom_ext_generators
  intro i
  refine Fin.lastCases hv (fun j => ?_) i
  exact congrArg (fun l : Hom (Carrier r) B => l (projection r (generator j))) hb

end SquareKit.SmoothAlgebra.Presentation
