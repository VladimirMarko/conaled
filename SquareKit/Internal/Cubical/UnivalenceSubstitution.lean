import SquareKit.Internal.Cubical.Univalence
import SquareKit.Internal.Cubical.HomotopyEquivalenceSubstitution
import SquareKit.Internal.Cubical.HomotopyIsoSubstitution
import SquareKit.Internal.Cubical.GlueEliminationSubstitution

/-! Substitution of the univalence code preserves the selected equivalence data. -/
set_option autoImplicit false
set_option warningAsError true
namespace SquareKit.Cubical.Presheaf
open CategoryTheory
universe u

namespace DisjointCover

/-- Transport retains the chosen contraction on each disjoint branch. -/
theorem contractible_transport {Γ : Context.{u}} (φ ψ : Cofibration Γ)
    (cover : ∀ x : Γ.Elements, φ.full x ∨ ψ.full x)
    (disjoint : ∀ x : Γ.Elements, φ.full x → ψ.full x → False)
    {A B : Family Γ} (e : A ≅ B)
    (a : HomotopyContractible (reindex A (restrictInclusion φ)))
    (b : HomotopyContractible (reindex A (restrictInclusion ψ))) :
    (contractible φ ψ cover disjoint a b).transport e =
      contractible φ ψ cover disjoint
        (a.transport (Functor.isoWhiskerLeft (restrictInclusion φ).mapElements e))
        (b.transport (Functor.isoWhiskerLeft (restrictInclusion ψ).mapElements e)) := by
  let a' := a.transport (Functor.isoWhiskerLeft (restrictInclusion φ).mapElements e)
  let b' := b.transport (Functor.isoWhiskerLeft (restrictInclusion ψ).mapElements e)
  apply HomotopyContractible.ext_pathApp
  · apply Term.ext
    intro x
    rcases cover x with hx | hx
    · exact (congrArg (e.hom.app x)
        (section_left φ ψ cover disjoint (PartialSection.ofRestricted a.center)
          (PartialSection.ofRestricted b.center) x hx)).trans
        (section_left φ ψ cover disjoint (PartialSection.ofRestricted a'.center)
          (PartialSection.ofRestricted b'.center) x hx).symm
    · exact (congrArg (e.hom.app x)
        (section_right φ ψ cover disjoint (PartialSection.ofRestricted a.center)
          (PartialSection.ofRestricted b.center) x hx)).trans
        (section_right φ ψ cover disjoint (PartialSection.ofRestricted a'.center)
          (PartialSection.ofRestricted b'.center) x hx).symm
  · apply Term.ext
    intro x
    let y : Γ.Elements := Γ.elementsMk x.obj x.val.1.1
    let z : (total (interval (total A))).Elements :=
      (total (interval (total A))).elementsMk x.obj
        ⟨⟨x.val.1.1,e.inv.app y x.val.1.2⟩,x.val.2⟩
    change e.hom.app y ((contractionSection φ ψ cover disjoint a b).val z) =
      (contractionSection φ ψ cover disjoint a' b').val x
    rcases cover y with hx | hx
    · exact (congrArg (e.hom.app y)
        (contractionSection_left φ ψ cover disjoint a b z hx)).trans
        (contractionSection_left φ ψ cover disjoint a' b' x hx).symm
    · exact (congrArg (e.hom.app y)
        (contractionSection_right φ ψ cover disjoint a b z hx)).trans
        (contractionSection_right φ ψ cover disjoint a' b' x hx).symm

end DisjointCover

namespace CodeSystem.Maps
variable {Γ Δ : Context.{u}} {φ ψ : Cofibration Γ}
  {A B : Family (restrictContext (φ.join ψ))}
  (a : reindex A (includeLeft φ ψ) ⟶ reindex B (includeLeft φ ψ))
  (b : reindex A (includeRight φ ψ) ⟶ reindex B (includeRight φ ψ))
  (disjoint : ∀ x : Γ.Elements, φ.full x → ψ.full x → False)
  (σ : Δ ⟶ Γ)

theorem disjointGlue_reindex :
    Functor.whiskerLeft (restrictSubstitution (φ.join ψ) σ).mapElements
      (glue a b (disjointCompatible a b disjoint)) =
    glue (φ := φ.reindex σ) (ψ := ψ.reindex σ)
      (A := reindex A (restrictSubstitution (φ.join ψ) σ))
      (B := reindex B (restrictSubstitution (φ.join ψ) σ)) (Functor.whiskerLeft (restrictSubstitution φ σ).mapElements a)
      (Functor.whiskerLeft (restrictSubstitution ψ σ).mapElements b)
      (disjointCompatible _ _ (fun x => disjoint (σ.mapElements.obj x))) := rfl

private theorem equivalenceCast_reindex {Ξ Ω : Context.{u}} {C D : Family Ξ}
    {f g : C ⟶ D} (h : f = g) (E : HomotopyEquivalence f) (τ : Ω ⟶ Ξ) :
    (h ▸ E).reindex τ =
      (congrArg (Functor.whiskerLeft τ.mapElements) h ▸ E.reindex τ) := by
  cases h
  rfl

theorem leftEquivalence_reindex (ea : HomotopyEquivalence a) :
    (leftEquivalence a b disjoint ea).reindex (restrictSubstitution φ σ) =
      leftEquivalence (φ := φ.reindex σ) (ψ := ψ.reindex σ)
      (A := reindex A (restrictSubstitution (φ.join ψ) σ))
      (B := reindex B (restrictSubstitution (φ.join ψ) σ))
        (Functor.whiskerLeft (restrictSubstitution φ σ).mapElements a)
        (Functor.whiskerLeft (restrictSubstitution ψ σ).mapElements b)
        (fun x => disjoint (σ.mapElements.obj x))
        (ea.reindex (restrictSubstitution φ σ)) := by
  exact equivalenceCast_reindex
    (C := reindex A (includeLeft φ ψ))
    (D := reindex B (includeLeft φ ψ))
    (glue_left a b (disjointCompatible a b disjoint)).symm ea
    (restrictSubstitution φ σ)

theorem rightEquivalence_reindex (eb : HomotopyEquivalence b) :
    (rightEquivalence a b disjoint eb).reindex (restrictSubstitution ψ σ) =
      rightEquivalence (φ := φ.reindex σ) (ψ := ψ.reindex σ)
      (A := reindex A (restrictSubstitution (φ.join ψ) σ))
      (B := reindex B (restrictSubstitution (φ.join ψ) σ))
        (Functor.whiskerLeft (restrictSubstitution φ σ).mapElements a)
        (Functor.whiskerLeft (restrictSubstitution ψ σ).mapElements b)
        (fun x => disjoint (σ.mapElements.obj x))
        (eb.reindex (restrictSubstitution ψ σ)) := by
  exact equivalenceCast_reindex
    (C := reindex A (includeRight φ ψ))
    (D := reindex B (includeRight φ ψ))
    (glue_right a b (disjointCompatible a b disjoint)).symm eb
    (restrictSubstitution ψ σ)

private noncomputable def branchFibers {Ξ : Context.{u}} (α β : Cofibration Ξ)
    {C D : Family (restrictContext (α.join β))}
    (d : ∀ x : Ξ.Elements, α.full x → β.full x → False) (f : C ⟶ D)
    (l : HomotopyEquivalence (Functor.whiskerLeft (includeLeft α β).mapElements f))
    (r : HomotopyEquivalence (Functor.whiskerLeft (includeRight α β).mapElements f)) :
    HomotopyContractible (homotopyFiber (Functor.whiskerLeft (projection D).mapElements f) (generic D)) :=
  DisjointCover.contractible (α.reindex (targetBase D)) (β.reindex (targetBase D))
    (fun x => (Cofibration.full_join α β ((targetBase D).mapElements.obj x)).mp x.val.1.property)
    (fun x => d ((targetBase D).mapElements.obj x))
    ((l.fibers.transport (genericFiberReindexIso f (includeLeft α β)).symm).reindex (leftTarget D))
    ((r.fibers.transport (genericFiberReindexIso f (includeRight α β)).symm).reindex (rightTarget D))

private theorem inverse_square {C : Type*} [Category C] {A B D E : C}
    (i : A ≅ B) (k : B ≅ E) (j : A ≅ D) (l : D ≅ E)
    (h : i ≪≫ k = j ≪≫ l) : i.symm ≪≫ j = k ≪≫ l.symm := by
  apply Iso.ext
  apply (cancel_epi i.hom).mp
  apply (cancel_mono l.hom).mp
  simpa only [Iso.trans_hom, Iso.symm_hom, Category.assoc, Iso.hom_inv_id_assoc,
    Iso.inv_hom_id, Category.comp_id] using (congrArg Iso.hom h).symm

private theorem inverse_square_hom {C : Type*} [Category C] {A B D E : C}
    (i : A ≅ B) (k : B ≅ E) (j : A ≅ D) (l : D ≅ E)
    (h : i ≪≫ k = j ≪≫ l) : (i.symm ≪≫ j).hom = (k ≪≫ l.symm).hom :=
  congrArg Iso.hom (inverse_square i k j l h)

private theorem iso_heq_of_hom {Ξ : Context.{u}} {A A' B B' : Family Ξ}
    (hA : A = A') (hB : B = B') (e : A ≅ B) (d : A' ≅ B')
    (h : HEq e.hom d.hom) : HEq e d := by
  cases hA
  cases hB
  exact heq_of_eq (Iso.ext (eq_of_heq h))

private theorem leftFiber_forward (f : A ⟶ B) :
    let τ := restrictSubstitution (φ.join ψ) σ;
    let ρ := restrictSubstitution φ σ;
    let ι := includeLeft φ ψ;
    let ι' := includeLeft (φ.reindex σ) (ψ.reindex σ);
    let μ := restrictSubstitution (φ.reindex (targetBase B)) (liftSub B τ);
    let κ := leftTarget B;
    let ν := leftTarget (φ := φ.reindex σ) (ψ := ψ.reindex σ) (reindex B τ);
    let P := genericFiberReindexIso f ι;
    let Q := genericFiberReindexIso
      (A := reindex A ι) (B := reindex B ι) (Functor.whiskerLeft ι.mapElements f) ρ;
    let R := genericFiberReindexIso
      (A := reindex A τ) (B := reindex B τ) (Functor.whiskerLeft τ.mapElements f) ι';
    let i := Functor.isoWhiskerLeft (μ ≫ κ).mapElements P;
    let j := Functor.isoWhiskerLeft
      (restrictInclusion ((φ.reindex σ).reindex
        (targetBase (φ := φ.reindex σ) (ψ := ψ.reindex σ) (reindex B τ)))).mapElements
      (genericFiberReindexIso f τ);
    let k := Functor.isoWhiskerLeft ν.mapElements Q;
    let l := Functor.isoWhiskerLeft ν.mapElements R;
    i ≪≫ k = j ≪≫ l := by
  dsimp only
  apply Iso.ext
  apply NatTrans.ext
  funext x
  apply ConcreteCategory.hom_ext
  intro z
  apply Sigma.ext
  · rfl
  · apply heq_of_eq
    apply Subtype.ext
    apply PiElement.ext
    intro y g r
    rfl

private theorem transport_congr {Ξ : Context.{u}} {C D : Family Ξ}
    (c : HomotopyContractible C) {e d : C ≅ D} (h : e = d) :
    c.transport e = c.transport d := congrArg (@HomotopyContractible.transport Ξ C D c) h

private theorem reindex_transport_congr {Ξ Ω : Context.{u}} {C : Family Ξ} {D : Family Ω}
    (c : HomotopyContractible C) {σ τ : Ω ⟶ Ξ} (h : σ = τ)
    (e : reindex C σ ≅ D) (d : reindex C τ ≅ D) (he : HEq e d) :
    (c.reindex σ).transport e = (c.reindex τ).transport d := by
  cases h
  cases he
  rfl

private theorem reindex_transport_heq {Ξ Ω : Context.{u}} {C : Family Ξ}
    {D D' : Family Ω} (c : HomotopyContractible C) {σ τ : Ω ⟶ Ξ}
    (h : σ = τ) (hD : D = D') (e : reindex C σ ≅ D) (d : reindex C τ ≅ D')
    (he : HEq e d) : HEq ((c.reindex σ).transport e) ((c.reindex τ).transport d) := by
  cases h
  cases hD
  cases he
  rfl

private theorem transport_pull_twice {Ξ Ω Ζ : Context.{u}} {C D : Family Ξ}
    {F : Family Ζ} (c : HomotopyContractible C) (P : C ≅ D)
    (κ : Ω ⟶ Ξ) (μ : Ζ ⟶ Ω) (j : reindex D (μ ≫ κ) ≅ F) :
    (((c.transport P).reindex κ).reindex μ).transport j =
      (c.reindex (μ ≫ κ)).transport
        (Functor.isoWhiskerLeft (μ ≫ κ).mapElements P ≪≫ j) :=
  (congrArg (fun d => d.transport j) ((c.transport P).reindex_comp κ μ)).trans
    ((congrArg (fun d => d.transport j) (c.transport_reindex P (μ ≫ κ))).trans
      (HomotopyContractible.transport_trans (c.reindex (μ ≫ κ))
        (Functor.isoWhiskerLeft (μ ≫ κ).mapElements P) j))

private theorem pull_transport_twice {Ξ Ω Ζ : Context.{u}} {C : Family Ξ}
    {D F : Family Ω} (c : HomotopyContractible C) (σ : Ω ⟶ Ξ)
    (Q : reindex C σ ≅ D) (R : D ≅ F) (ν : Ζ ⟶ Ω) :
    (((c.reindex σ).transport Q).transport R).reindex ν =
      (c.reindex (ν ≫ σ)).transport
        (Functor.isoWhiskerLeft ν.mapElements Q ≪≫ Functor.isoWhiskerLeft ν.mapElements R) :=
  (congrArg (fun d => d.reindex ν)
    (HomotopyContractible.transport_trans (c.reindex σ) Q R)).trans
    (((c.reindex σ).transport_reindex (Q ≪≫ R) ν).trans
      (congrArg (fun d => d.transport
        (Functor.isoWhiskerLeft ν.mapElements Q ≪≫ Functor.isoWhiskerLeft ν.mapElements R))
          (c.reindex_comp σ ν)))

private theorem transport_inverse_pull_twice {Ξ Ω Ζ : Context.{u}} {C D : Family Ξ}
    {F : Family Ζ} (c : HomotopyContractible C) (P : D ≅ C)
    (κ : Ω ⟶ Ξ) (μ : Ζ ⟶ Ω) (j : reindex D (μ ≫ κ) ≅ F) :
    (((c.transport P.symm).reindex κ).reindex μ).transport j =
      (c.reindex (μ ≫ κ)).transport
        ((Functor.isoWhiskerLeft (μ ≫ κ).mapElements P).symm ≪≫ j) :=
  transport_pull_twice c P.symm κ μ j

private theorem pull_transport_inverse {Ξ Ω Ζ : Context.{u}} {C : Family Ξ}
    {D F : Family Ω} (c : HomotopyContractible C) (σ : Ω ⟶ Ξ)
    (Q : reindex C σ ≅ D) (R : F ≅ D) (ν : Ζ ⟶ Ω) :
    (((c.reindex σ).transport Q).transport R.symm).reindex ν =
      (c.reindex (ν ≫ σ)).transport
        (Functor.isoWhiskerLeft ν.mapElements Q ≪≫ (Functor.isoWhiskerLeft ν.mapElements R).symm) :=
  pull_transport_twice c σ Q R.symm ν

-- The native fiber types need this bounded kernel-checking budget; see the #420 handoff.
set_option maxHeartbeats 400000 in
private theorem leftFiber_inverse_hom (f : A ⟶ B) :
    let τ := restrictSubstitution (φ.join ψ) σ;
    let ρ := restrictSubstitution φ σ;
    let ι := includeLeft φ ψ;
    let ι' := includeLeft (φ.reindex σ) (ψ.reindex σ);
    let μ := restrictSubstitution (φ.reindex (targetBase B)) (liftSub B τ);
    let κ := leftTarget B;
    let ν := leftTarget (φ := φ.reindex σ) (ψ := ψ.reindex σ) (reindex B τ);
    let P := genericFiberReindexIso f ι;
    let Q := genericFiberReindexIso
      (A := reindex A ι) (B := reindex B ι) (Functor.whiskerLeft ι.mapElements f) ρ;
    let R := genericFiberReindexIso
      (A := reindex A τ) (B := reindex B τ) (Functor.whiskerLeft τ.mapElements f) ι';
    let i := Functor.isoWhiskerLeft (μ ≫ κ).mapElements P;
    let j := Functor.isoWhiskerLeft
      (restrictInclusion ((φ.reindex σ).reindex
        (targetBase (φ := φ.reindex σ) (ψ := ψ.reindex σ) (reindex B τ)))).mapElements
      (genericFiberReindexIso f τ);
    let k := Functor.isoWhiskerLeft ν.mapElements Q;
    let l := Functor.isoWhiskerLeft ν.mapElements R;
    (i.symm ≪≫ j).hom = (k ≪≫ l.symm).hom := by
  let τ := restrictSubstitution (φ.join ψ) σ
  let ρ := restrictSubstitution φ σ
  let ι := includeLeft φ ψ
  let ι' := includeLeft (φ.reindex σ) (ψ.reindex σ)
  let μ := restrictSubstitution (φ.reindex (targetBase B)) (liftSub B τ)
  let κ := leftTarget B
  let ν := leftTarget (φ := φ.reindex σ) (ψ := ψ.reindex σ) (reindex B τ)
  let P := genericFiberReindexIso f ι
  let Q := genericFiberReindexIso
    (A := reindex A ι) (B := reindex B ι) (Functor.whiskerLeft ι.mapElements f) ρ
  let R := genericFiberReindexIso
    (A := reindex A τ) (B := reindex B τ) (Functor.whiskerLeft τ.mapElements f) ι'
  let i := Functor.isoWhiskerLeft (μ ≫ κ).mapElements P
  let j := Functor.isoWhiskerLeft
    (restrictInclusion ((φ.reindex σ).reindex
      (targetBase (φ := φ.reindex σ) (ψ := ψ.reindex σ) (reindex B τ)))).mapElements
    (genericFiberReindexIso f τ)
  let k := Functor.isoWhiskerLeft ν.mapElements Q
  let l := Functor.isoWhiskerLeft ν.mapElements R
  have square : i ≪≫ k = j ≪≫ l :=
    leftFiber_forward (φ := φ) (ψ := ψ) (A := A) (B := B) σ f
  exact inverse_square_hom i k j l square

private theorem leftFiber_inverse_heq (f : A ⟶ B) :
    let τ := restrictSubstitution (φ.join ψ) σ;
    let ρ := restrictSubstitution φ σ;
    let ι := includeLeft φ ψ;
    let ι' := includeLeft (φ.reindex σ) (ψ.reindex σ);
    let μ := restrictSubstitution (φ.reindex (targetBase B)) (liftSub B τ);
    let κ := leftTarget B;
    let ν := leftTarget (φ := φ.reindex σ) (ψ := ψ.reindex σ) (reindex B τ);
    let P := genericFiberReindexIso f ι;
    let Q := genericFiberReindexIso
      (A := reindex A ι) (B := reindex B ι) (Functor.whiskerLeft ι.mapElements f) ρ;
    let R := genericFiberReindexIso
      (A := reindex A τ) (B := reindex B τ) (Functor.whiskerLeft τ.mapElements f) ι';
    let i := Functor.isoWhiskerLeft (μ ≫ κ).mapElements P;
    let j := Functor.isoWhiskerLeft
      (restrictInclusion ((φ.reindex σ).reindex
        (targetBase (φ := φ.reindex σ) (ψ := ψ.reindex σ) (reindex B τ)))).mapElements
      (genericFiberReindexIso f τ);
    let k := Functor.isoWhiskerLeft ν.mapElements Q;
    let l := Functor.isoWhiskerLeft ν.mapElements R;
    HEq (i.symm ≪≫ j) (k ≪≫ l.symm) := by
  let τ := restrictSubstitution (φ.join ψ) σ
  let ρ := restrictSubstitution φ σ
  let ι := includeLeft φ ψ
  let ι' := includeLeft (φ.reindex σ) (ψ.reindex σ)
  let μ := restrictSubstitution (φ.reindex (targetBase B)) (liftSub B τ)
  let κ := leftTarget B
  let ν := leftTarget (φ := φ.reindex σ) (ψ := ψ.reindex σ) (reindex B τ)
  let P := genericFiberReindexIso f ι
  let Q := genericFiberReindexIso
    (A := reindex A ι) (B := reindex B ι) (Functor.whiskerLeft ι.mapElements f) ρ
  let R := genericFiberReindexIso
    (A := reindex A τ) (B := reindex B τ) (Functor.whiskerLeft τ.mapElements f) ι'
  let i := Functor.isoWhiskerLeft (μ ≫ κ).mapElements P
  let j := Functor.isoWhiskerLeft
    (restrictInclusion ((φ.reindex σ).reindex
      (targetBase (φ := φ.reindex σ) (ψ := ψ.reindex σ) (reindex B τ)))).mapElements
    (genericFiberReindexIso f τ)
  let k := Functor.isoWhiskerLeft ν.mapElements Q
  let l := Functor.isoWhiskerLeft ν.mapElements R
  have hom := leftFiber_inverse_hom (φ := φ) (ψ := ψ) (A := A) (B := B) σ f
  have hbase : μ ≫ κ = ν ≫ liftSub (reindex B ι) ρ := rfl
  have hD : reindex
      (homotopyFiber (Functor.whiskerLeft (projection (reindex B τ)).mapElements
        (Functor.whiskerLeft τ.mapElements f)) (generic (reindex B τ)))
      (restrictInclusion ((φ.reindex σ).reindex
        (targetBase (φ := φ.reindex σ) (ψ := ψ.reindex σ) (reindex B τ)))) =
    reindex (reindex
      (homotopyFiber (Functor.whiskerLeft (projection (reindex B τ)).mapElements
        (Functor.whiskerLeft τ.mapElements f)) (generic (reindex B τ)))
      (liftSub (reindex B τ) ι')) ν := rfl
  have hSource := congrArg
    (fun ξ => reindex
      (homotopyFiber (Functor.whiskerLeft (projection (reindex B ι)).mapElements
        (Functor.whiskerLeft ι.mapElements f)) (generic (reindex B ι))) ξ) hbase
  have he : HEq (i.symm ≪≫ j) (k ≪≫ l.symm) :=
    iso_heq_of_hom hSource hD (i.symm ≪≫ j) (k ≪≫ l.symm)
      (heq_of_eq hom)
  exact he

private theorem leftFiber_reindex (f : A ⟶ B)
    (L : HomotopyEquivalence (Functor.whiskerLeft (includeLeft φ ψ).mapElements f)) :
    (((L.fibers.transport (genericFiberReindexIso f (includeLeft φ ψ)).symm).reindex
      (leftTarget B)).reindex
      (restrictSubstitution (φ.reindex (targetBase B))
        (liftSub B (restrictSubstitution (φ.join ψ) σ)))).transport
      (Functor.isoWhiskerLeft
        (restrictInclusion ((φ.reindex σ).reindex
          (targetBase (φ := φ.reindex σ) (ψ := ψ.reindex σ)
            (reindex B (restrictSubstitution (φ.join ψ) σ))))).mapElements
        (genericFiberReindexIso f (restrictSubstitution (φ.join ψ) σ))) =
    (((L.reindex (restrictSubstitution φ σ)).fibers.transport
      (genericFiberReindexIso
        (Functor.whiskerLeft (restrictSubstitution (φ.join ψ) σ).mapElements f)
        (includeLeft (φ.reindex σ) (ψ.reindex σ))).symm).reindex
      (leftTarget (φ := φ.reindex σ) (ψ := ψ.reindex σ)
        (reindex B (restrictSubstitution (φ.join ψ) σ)))) := by
  let τ := restrictSubstitution (φ.join ψ) σ
  let ρ := restrictSubstitution φ σ
  let ι := includeLeft φ ψ
  let ι' := includeLeft (φ.reindex σ) (ψ.reindex σ)
  let μ := restrictSubstitution (φ.reindex (targetBase B)) (liftSub B τ)
  let κ := leftTarget B
  let ν := leftTarget (φ := φ.reindex σ) (ψ := ψ.reindex σ) (reindex B τ)
  let P := genericFiberReindexIso f ι
  let Q := genericFiberReindexIso
    (A := reindex A ι) (B := reindex B ι) (Functor.whiskerLeft ι.mapElements f) ρ
  let R := genericFiberReindexIso
    (A := reindex A τ) (B := reindex B τ) (Functor.whiskerLeft τ.mapElements f) ι'
  let i := Functor.isoWhiskerLeft (μ ≫ κ).mapElements P
  let j := Functor.isoWhiskerLeft
    (restrictInclusion ((φ.reindex σ).reindex
      (targetBase (φ := φ.reindex σ) (ψ := ψ.reindex σ) (reindex B τ)))).mapElements
    (genericFiberReindexIso f τ)
  let k := Functor.isoWhiskerLeft ν.mapElements Q
  let l := Functor.isoWhiskerLeft ν.mapElements R
  have hL := transport_inverse_pull_twice L.fibers P κ μ j
  have hR := pull_transport_inverse L.fibers (liftSub (reindex B ι) ρ) Q R ν
  have hbase : μ ≫ κ = ν ≫ liftSub (reindex B ι) ρ := rfl
  have hD : reindex
      (homotopyFiber (Functor.whiskerLeft (projection (reindex B τ)).mapElements
        (Functor.whiskerLeft τ.mapElements f)) (generic (reindex B τ)))
      (restrictInclusion ((φ.reindex σ).reindex
        (targetBase (φ := φ.reindex σ) (ψ := ψ.reindex σ) (reindex B τ)))) =
    reindex (reindex
      (homotopyFiber (Functor.whiskerLeft (projection (reindex B τ)).mapElements
        (Functor.whiskerLeft τ.mapElements f)) (generic (reindex B τ)))
      (liftSub (reindex B τ) ι')) ν := rfl
  have he : HEq (i.symm ≪≫ j) (k ≪≫ l.symm) :=
    leftFiber_inverse_heq (φ := φ) (ψ := ψ) (A := A) (B := B) σ f
  have hBase := @reindex_transport_heq
    (total (reindex B ι))
    (restrictContext ((φ.reindex σ).reindex
      (targetBase (φ := φ.reindex σ) (ψ := ψ.reindex σ) (reindex B τ))))
    (homotopyFiber (Functor.whiskerLeft (projection (reindex B ι)).mapElements
      (Functor.whiskerLeft ι.mapElements f)) (generic (reindex B ι)))
    (reindex (homotopyFiber (Functor.whiskerLeft (projection (reindex B τ)).mapElements
      (Functor.whiskerLeft τ.mapElements f)) (generic (reindex B τ)))
      (restrictInclusion ((φ.reindex σ).reindex
        (targetBase (φ := φ.reindex σ) (ψ := ψ.reindex σ) (reindex B τ)))))
    (reindex (reindex
      (homotopyFiber (Functor.whiskerLeft (projection (reindex B τ)).mapElements
        (Functor.whiskerLeft τ.mapElements f)) (generic (reindex B τ)))
      (liftSub (reindex B τ) ι')) ν)
    L.fibers (μ ≫ κ) (ν ≫ liftSub (reindex B ι) ρ) hbase hD
    (i.symm ≪≫ j) (k ≪≫ l.symm) he
  have hFinish := hBase.trans (heq_of_eq hR.symm)
  have hWhole := (heq_of_eq hL).trans hFinish
  exact eq_of_heq hWhole

private theorem rightFiber_forward (f : A ⟶ B) :
    let τ := restrictSubstitution (φ.join ψ) σ;
    let ρ := restrictSubstitution ψ σ;
    let ι := includeRight φ ψ;
    let ι' := includeRight (φ.reindex σ) (ψ.reindex σ);
    let μ := restrictSubstitution (ψ.reindex (targetBase B)) (liftSub B τ);
    let κ := rightTarget B;
    let ν := rightTarget (φ := φ.reindex σ) (ψ := ψ.reindex σ) (reindex B τ);
    let P := genericFiberReindexIso f ι;
    let Q := genericFiberReindexIso
      (A := reindex A ι) (B := reindex B ι) (Functor.whiskerLeft ι.mapElements f) ρ;
    let R := genericFiberReindexIso
      (A := reindex A τ) (B := reindex B τ) (Functor.whiskerLeft τ.mapElements f) ι';
    let i := Functor.isoWhiskerLeft (μ ≫ κ).mapElements P;
    let j := Functor.isoWhiskerLeft
      (restrictInclusion ((ψ.reindex σ).reindex
        (targetBase (φ := φ.reindex σ) (ψ := ψ.reindex σ) (reindex B τ)))).mapElements
      (genericFiberReindexIso f τ);
    let k := Functor.isoWhiskerLeft ν.mapElements Q;
    let l := Functor.isoWhiskerLeft ν.mapElements R;
    i ≪≫ k = j ≪≫ l := by
  dsimp only
  apply Iso.ext
  apply NatTrans.ext
  funext x
  apply ConcreteCategory.hom_ext
  intro z
  apply Sigma.ext
  · rfl
  · apply heq_of_eq
    apply Subtype.ext
    apply PiElement.ext
    intro y g r
    rfl

-- The native fiber types need this bounded kernel-checking budget; see the #420 handoff.
set_option maxHeartbeats 400000 in
private theorem rightFiber_inverse_hom (f : A ⟶ B) :
    let τ := restrictSubstitution (φ.join ψ) σ;
    let ρ := restrictSubstitution ψ σ;
    let ι := includeRight φ ψ;
    let ι' := includeRight (φ.reindex σ) (ψ.reindex σ);
    let μ := restrictSubstitution (ψ.reindex (targetBase B)) (liftSub B τ);
    let κ := rightTarget B;
    let ν := rightTarget (φ := φ.reindex σ) (ψ := ψ.reindex σ) (reindex B τ);
    let P := genericFiberReindexIso f ι;
    let Q := genericFiberReindexIso
      (A := reindex A ι) (B := reindex B ι) (Functor.whiskerLeft ι.mapElements f) ρ;
    let R := genericFiberReindexIso
      (A := reindex A τ) (B := reindex B τ) (Functor.whiskerLeft τ.mapElements f) ι';
    let i := Functor.isoWhiskerLeft (μ ≫ κ).mapElements P;
    let j := Functor.isoWhiskerLeft
      (restrictInclusion ((ψ.reindex σ).reindex
        (targetBase (φ := φ.reindex σ) (ψ := ψ.reindex σ) (reindex B τ)))).mapElements
      (genericFiberReindexIso f τ);
    let k := Functor.isoWhiskerLeft ν.mapElements Q;
    let l := Functor.isoWhiskerLeft ν.mapElements R;
    (i.symm ≪≫ j).hom = (k ≪≫ l.symm).hom := by
  let τ := restrictSubstitution (φ.join ψ) σ
  let ρ := restrictSubstitution ψ σ
  let ι := includeRight φ ψ
  let ι' := includeRight (φ.reindex σ) (ψ.reindex σ)
  let μ := restrictSubstitution (ψ.reindex (targetBase B)) (liftSub B τ)
  let κ := rightTarget B
  let ν := rightTarget (φ := φ.reindex σ) (ψ := ψ.reindex σ) (reindex B τ)
  let P := genericFiberReindexIso f ι
  let Q := genericFiberReindexIso
    (A := reindex A ι) (B := reindex B ι) (Functor.whiskerLeft ι.mapElements f) ρ
  let R := genericFiberReindexIso
    (A := reindex A τ) (B := reindex B τ) (Functor.whiskerLeft τ.mapElements f) ι'
  let i := Functor.isoWhiskerLeft (μ ≫ κ).mapElements P
  let j := Functor.isoWhiskerLeft
    (restrictInclusion ((ψ.reindex σ).reindex
      (targetBase (φ := φ.reindex σ) (ψ := ψ.reindex σ) (reindex B τ)))).mapElements
    (genericFiberReindexIso f τ)
  let k := Functor.isoWhiskerLeft ν.mapElements Q
  let l := Functor.isoWhiskerLeft ν.mapElements R
  have square : i ≪≫ k = j ≪≫ l :=
    rightFiber_forward (φ := φ) (ψ := ψ) (A := A) (B := B) σ f
  exact inverse_square_hom i k j l square

private theorem rightFiber_inverse_heq (f : A ⟶ B) :
    let τ := restrictSubstitution (φ.join ψ) σ;
    let ρ := restrictSubstitution ψ σ;
    let ι := includeRight φ ψ;
    let ι' := includeRight (φ.reindex σ) (ψ.reindex σ);
    let μ := restrictSubstitution (ψ.reindex (targetBase B)) (liftSub B τ);
    let κ := rightTarget B;
    let ν := rightTarget (φ := φ.reindex σ) (ψ := ψ.reindex σ) (reindex B τ);
    let P := genericFiberReindexIso f ι;
    let Q := genericFiberReindexIso
      (A := reindex A ι) (B := reindex B ι) (Functor.whiskerLeft ι.mapElements f) ρ;
    let R := genericFiberReindexIso
      (A := reindex A τ) (B := reindex B τ) (Functor.whiskerLeft τ.mapElements f) ι';
    let i := Functor.isoWhiskerLeft (μ ≫ κ).mapElements P;
    let j := Functor.isoWhiskerLeft
      (restrictInclusion ((ψ.reindex σ).reindex
        (targetBase (φ := φ.reindex σ) (ψ := ψ.reindex σ) (reindex B τ)))).mapElements
      (genericFiberReindexIso f τ);
    let k := Functor.isoWhiskerLeft ν.mapElements Q;
    let l := Functor.isoWhiskerLeft ν.mapElements R;
    HEq (i.symm ≪≫ j) (k ≪≫ l.symm) := by
  let τ := restrictSubstitution (φ.join ψ) σ
  let ρ := restrictSubstitution ψ σ
  let ι := includeRight φ ψ
  let ι' := includeRight (φ.reindex σ) (ψ.reindex σ)
  let μ := restrictSubstitution (ψ.reindex (targetBase B)) (liftSub B τ)
  let κ := rightTarget B
  let ν := rightTarget (φ := φ.reindex σ) (ψ := ψ.reindex σ) (reindex B τ)
  let P := genericFiberReindexIso f ι
  let Q := genericFiberReindexIso
    (A := reindex A ι) (B := reindex B ι) (Functor.whiskerLeft ι.mapElements f) ρ
  let R := genericFiberReindexIso
    (A := reindex A τ) (B := reindex B τ) (Functor.whiskerLeft τ.mapElements f) ι'
  let i := Functor.isoWhiskerLeft (μ ≫ κ).mapElements P
  let j := Functor.isoWhiskerLeft
    (restrictInclusion ((ψ.reindex σ).reindex
      (targetBase (φ := φ.reindex σ) (ψ := ψ.reindex σ) (reindex B τ)))).mapElements
    (genericFiberReindexIso f τ)
  let k := Functor.isoWhiskerLeft ν.mapElements Q
  let l := Functor.isoWhiskerLeft ν.mapElements R
  have hom := rightFiber_inverse_hom (φ := φ) (ψ := ψ) (A := A) (B := B) σ f
  have hbase : μ ≫ κ = ν ≫ liftSub (reindex B ι) ρ := rfl
  have hD : reindex
      (homotopyFiber (Functor.whiskerLeft (projection (reindex B τ)).mapElements
        (Functor.whiskerLeft τ.mapElements f)) (generic (reindex B τ)))
      (restrictInclusion ((ψ.reindex σ).reindex
        (targetBase (φ := φ.reindex σ) (ψ := ψ.reindex σ) (reindex B τ)))) =
    reindex (reindex
      (homotopyFiber (Functor.whiskerLeft (projection (reindex B τ)).mapElements
        (Functor.whiskerLeft τ.mapElements f)) (generic (reindex B τ)))
      (liftSub (reindex B τ) ι')) ν := rfl
  have hSource := congrArg
    (fun ξ => reindex
      (homotopyFiber (Functor.whiskerLeft (projection (reindex B ι)).mapElements
        (Functor.whiskerLeft ι.mapElements f)) (generic (reindex B ι))) ξ) hbase
  have he : HEq (i.symm ≪≫ j) (k ≪≫ l.symm) :=
    iso_heq_of_hom hSource hD (i.symm ≪≫ j) (k ≪≫ l.symm)
      (heq_of_eq hom)
  exact he

private theorem rightFiber_reindex (f : A ⟶ B)
    (L : HomotopyEquivalence (Functor.whiskerLeft (includeRight φ ψ).mapElements f)) :
    (((L.fibers.transport (genericFiberReindexIso f (includeRight φ ψ)).symm).reindex
      (rightTarget B)).reindex
      (restrictSubstitution (ψ.reindex (targetBase B))
        (liftSub B (restrictSubstitution (φ.join ψ) σ)))).transport
      (Functor.isoWhiskerLeft
        (restrictInclusion ((ψ.reindex σ).reindex
          (targetBase (φ := φ.reindex σ) (ψ := ψ.reindex σ)
            (reindex B (restrictSubstitution (φ.join ψ) σ))))).mapElements
        (genericFiberReindexIso f (restrictSubstitution (φ.join ψ) σ))) =
    (((L.reindex (restrictSubstitution ψ σ)).fibers.transport
      (genericFiberReindexIso
        (Functor.whiskerLeft (restrictSubstitution (φ.join ψ) σ).mapElements f)
        (includeRight (φ.reindex σ) (ψ.reindex σ))).symm).reindex
      (rightTarget (φ := φ.reindex σ) (ψ := ψ.reindex σ)
        (reindex B (restrictSubstitution (φ.join ψ) σ)))) := by
  let τ := restrictSubstitution (φ.join ψ) σ
  let ρ := restrictSubstitution ψ σ
  let ι := includeRight φ ψ
  let ι' := includeRight (φ.reindex σ) (ψ.reindex σ)
  let μ := restrictSubstitution (ψ.reindex (targetBase B)) (liftSub B τ)
  let κ := rightTarget B
  let ν := rightTarget (φ := φ.reindex σ) (ψ := ψ.reindex σ) (reindex B τ)
  let P := genericFiberReindexIso f ι
  let Q := genericFiberReindexIso
    (A := reindex A ι) (B := reindex B ι) (Functor.whiskerLeft ι.mapElements f) ρ
  let R := genericFiberReindexIso
    (A := reindex A τ) (B := reindex B τ) (Functor.whiskerLeft τ.mapElements f) ι'
  let i := Functor.isoWhiskerLeft (μ ≫ κ).mapElements P
  let j := Functor.isoWhiskerLeft
    (restrictInclusion ((ψ.reindex σ).reindex
      (targetBase (φ := φ.reindex σ) (ψ := ψ.reindex σ) (reindex B τ)))).mapElements
    (genericFiberReindexIso f τ)
  let k := Functor.isoWhiskerLeft ν.mapElements Q
  let l := Functor.isoWhiskerLeft ν.mapElements R
  have hL := transport_inverse_pull_twice L.fibers P κ μ j
  have hR := pull_transport_inverse L.fibers (liftSub (reindex B ι) ρ) Q R ν
  have hbase : μ ≫ κ = ν ≫ liftSub (reindex B ι) ρ := rfl
  have hD : reindex
      (homotopyFiber (Functor.whiskerLeft (projection (reindex B τ)).mapElements
        (Functor.whiskerLeft τ.mapElements f)) (generic (reindex B τ)))
      (restrictInclusion ((ψ.reindex σ).reindex
        (targetBase (φ := φ.reindex σ) (ψ := ψ.reindex σ) (reindex B τ)))) =
    reindex (reindex
      (homotopyFiber (Functor.whiskerLeft (projection (reindex B τ)).mapElements
        (Functor.whiskerLeft τ.mapElements f)) (generic (reindex B τ)))
      (liftSub (reindex B τ) ι')) ν := rfl
  have he : HEq (i.symm ≪≫ j) (k ≪≫ l.symm) :=
    rightFiber_inverse_heq (φ := φ) (ψ := ψ) (A := A) (B := B) σ f
  have hBase := @reindex_transport_heq
    (total (reindex B ι))
    (restrictContext ((ψ.reindex σ).reindex
      (targetBase (φ := φ.reindex σ) (ψ := ψ.reindex σ) (reindex B τ))))
    (homotopyFiber (Functor.whiskerLeft (projection (reindex B ι)).mapElements
      (Functor.whiskerLeft ι.mapElements f)) (generic (reindex B ι)))
    (reindex (homotopyFiber (Functor.whiskerLeft (projection (reindex B τ)).mapElements
      (Functor.whiskerLeft τ.mapElements f)) (generic (reindex B τ)))
      (restrictInclusion ((ψ.reindex σ).reindex
        (targetBase (φ := φ.reindex σ) (ψ := ψ.reindex σ) (reindex B τ)))))
    (reindex (reindex
      (homotopyFiber (Functor.whiskerLeft (projection (reindex B τ)).mapElements
        (Functor.whiskerLeft τ.mapElements f)) (generic (reindex B τ)))
      (liftSub (reindex B τ) ι')) ν)
    L.fibers (μ ≫ κ) (ν ≫ liftSub (reindex B ι) ρ) hbase hD
    (i.symm ≪≫ j) (k ≪≫ l.symm) he
  have hFinish := hBase.trans (heq_of_eq hR.symm)
  have hWhole := (heq_of_eq hL).trans hFinish
  exact eq_of_heq hWhole

private theorem branchFibers_reindex (f : A ⟶ B)
    (L : HomotopyEquivalence (Functor.whiskerLeft (includeLeft φ ψ).mapElements f))
    (R : HomotopyEquivalence (Functor.whiskerLeft (includeRight φ ψ).mapElements f)) :
    ((branchFibers φ ψ disjoint f L R).reindex
      (liftSub B (restrictSubstitution (φ.join ψ) σ))).transport
      (genericFiberReindexIso f (restrictSubstitution (φ.join ψ) σ)) =
    branchFibers (φ.reindex σ) (ψ.reindex σ)
      (C := reindex A (restrictSubstitution (φ.join ψ) σ))
      (D := reindex B (restrictSubstitution (φ.join ψ) σ))
      (fun x => disjoint (σ.mapElements.obj x))
      (Functor.whiskerLeft (restrictSubstitution (φ.join ψ) σ).mapElements f)
      (L.reindex (restrictSubstitution φ σ)) (R.reindex (restrictSubstitution ψ σ)) := by
  let τ := restrictSubstitution (φ.join ψ) σ
  let π := liftSub B τ
  let α := φ.reindex (targetBase B)
  let β := ψ.reindex (targetBase B)
  let cover : ∀ x, α.full x ∨ β.full x :=
    fun x => (Cofibration.full_join φ ψ ((targetBase B).mapElements.obj x)).mp x.val.1.property
  let d : ∀ x, α.full x → β.full x → False := fun x => disjoint ((targetBase B).mapElements.obj x)
  let CL := (L.fibers.transport (genericFiberReindexIso f (includeLeft φ ψ)).symm).reindex (leftTarget B)
  let CR := (R.fibers.transport (genericFiberReindexIso f (includeRight φ ψ)).symm).reindex (rightTarget B)
  let J := genericFiberReindexIso f τ
  have h1 := congrArg (fun c => c.transport J)
    (DisjointCover.contractible_reindex α β cover d CL CR π)
  have h2 := DisjointCover.contractible_transport (α.reindex π) (β.reindex π)
    (fun x => cover (π.mapElements.obj x)) (fun x => d (π.mapElements.obj x)) J
    (CL.reindex (restrictSubstitution α π)) (CR.reindex (restrictSubstitution β π))
  have h3 := congrArg₂
    (DisjointCover.contractible (α.reindex π) (β.reindex π)
      (fun x => cover (π.mapElements.obj x)) (fun x => d (π.mapElements.obj x)))
    (leftFiber_reindex (φ := φ) (ψ := ψ) (A := A) (B := B) σ f L)
    (rightFiber_reindex (φ := φ) (ψ := ψ) (A := A) (B := B) σ f R)
  exact (h1.trans h2).trans h3

theorem disjointEquivalence_reindex (ea : HomotopyEquivalence a)
    (eb : HomotopyEquivalence b) :
    (disjointEquivalence a b disjoint ea eb).reindex (restrictSubstitution (φ.join ψ) σ) =
    disjointEquivalence (φ := φ.reindex σ) (ψ := ψ.reindex σ)
      (A := reindex A (restrictSubstitution (φ.join ψ) σ))
      (B := reindex B (restrictSubstitution (φ.join ψ) σ))
      (Functor.whiskerLeft (restrictSubstitution φ σ).mapElements a)
      (Functor.whiskerLeft (restrictSubstitution ψ σ).mapElements b)
      (fun x => disjoint (σ.mapElements.obj x))
      (ea.reindex (restrictSubstitution φ σ)) (eb.reindex (restrictSubstitution ψ σ)) := by
  have hL := leftEquivalence_reindex (A := A) (B := B) a b disjoint σ ea
  have hR := rightEquivalence_reindex (A := A) (B := B) a b disjoint σ eb
  let f' := Functor.whiskerLeft (restrictSubstitution (φ.join ψ) σ).mapElements
    (glue a b (disjointCompatible a b disjoint))
  have hk := congrArg₂
    (branchFibers (φ.reindex σ) (ψ.reindex σ)
      (C := reindex A (restrictSubstitution (φ.join ψ) σ))
      (D := reindex B (restrictSubstitution (φ.join ψ) σ))
      (fun x => disjoint (σ.mapElements.obj x)) f') hL hR
  apply HomotopyEquivalence.ext
  exact (branchFibers_reindex (φ := φ) (ψ := ψ) (A := A) (B := B) disjoint σ
    (glue a b (disjointCompatible a b disjoint))
    (leftEquivalence a b disjoint ea) (rightEquivalence a b disjoint eb)).trans hk

end CodeSystem.Maps

namespace Univalence
variable {Γ Δ : Context.{u}} (a b : raisedContext Γ ⟶ smallFamilyCodes.{u})
  (σ : Δ ⟶ Γ)

theorem boundary_reindex :
    raisedSub (restrictSubstitution face (liftSub (interval Γ) σ)) ≫ CodeSystem.boundary a b =
      CodeSystem.boundary (raisedSub σ ≫ a) (raisedSub σ ≫ b) :=
  CodeSystem.glue_reindex _ _ _ (liftSub (interval Γ) σ)

private theorem reindex_eqToHom {Ξ Ω : Context.{u}} {A B : Family Ξ}
    (h : A = B) (τ : Ω ⟶ Ξ) :
    Functor.whiskerLeft τ.mapElements (eqToHom h) =
      eqToHom (congrArg (fun X => reindex X τ) h) := by
  cases h
  rfl

private theorem sourceCast_heq {Ξ : Context.{u}} {A A' B C : Family Ξ}
    (h : A = A') (q : A = B) (q' : A' = B) (f : B ⟶ C) :
    HEq (eqToHom q ≫ f) (eqToHom q' ≫ f) := by
  cases h
  rfl

private def codeMapReindex (f : decode a ⟶ decode b) :
    decode (raisedSub σ ≫ a) ⟶ decode (raisedSub σ ≫ b) :=
  Functor.whiskerLeft σ.mapElements f

theorem boundaryLeft_reindex (f : decode a ⟶ decode b) :
    HEq (Functor.whiskerLeft
      (restrictSubstitution (intervalFace Γ false) (liftSub (interval Γ) σ)).mapElements
      (boundaryLeft a b f))
      (boundaryLeft (Γ := Δ) (raisedSub σ ≫ a) (raisedSub σ ≫ b)
        (codeMapReindex a b σ f)) := by
  let τ := restrictSubstitution (intervalFace Γ false) (liftSub (interval Γ) σ)
  change HEq (Functor.whiskerLeft τ.mapElements (eqToHom (boundary_left a b)) ≫
    Functor.whiskerLeft
      (restrictInclusion (intervalFace Δ false) ≫ projection (interval Δ) ≫ σ).mapElements f) _
  rw [reindex_eqToHom]
  have hC : reindex (decode (CodeSystem.boundary a b))
      (restrictSubstitution face (liftSub (interval Γ) σ)) =
      decode (CodeSystem.boundary (raisedSub σ ≫ a) (raisedSub σ ≫ b)) :=
    (decode_reindex (CodeSystem.boundary a b)
      (restrictSubstitution face (liftSub (interval Γ) σ))).symm.trans
      (congrArg (@decode (restrictContext (face (Γ := Δ)))) (boundary_reindex a b σ))
  have hS := congrArg
    (fun C : Family (restrictContext (face (Γ := Δ))) =>
      reindex C (CodeSystem.includeLeft (intervalFace Δ false) (intervalFace Δ true))) hC
  exact sourceCast_heq hS
    (congrArg (fun C => reindex C τ) (boundary_left a b))
    (boundary_left (raisedSub σ ≫ a) (raisedSub σ ≫ b))
    (Functor.whiskerLeft
      (restrictInclusion (intervalFace Δ false) ≫ projection (interval Δ) ≫ σ).mapElements f)

private theorem eqToHom_heq {Ξ : Context.{u}} {A A' B : Family Ξ}
    (h : A = A') (q : A = B) (q' : A' = B) : HEq (eqToHom q) (eqToHom q') := by
  cases h
  rfl

theorem boundaryRight_reindex :
    HEq (Functor.whiskerLeft
      (restrictSubstitution (intervalFace Γ true) (liftSub (interval Γ) σ)).mapElements
      (boundaryRight a b))
      (boundaryRight (Γ := Δ) (raisedSub σ ≫ a) (raisedSub σ ≫ b)) := by
  let τ := restrictSubstitution (intervalFace Γ true) (liftSub (interval Γ) σ)
  change HEq (Functor.whiskerLeft τ.mapElements (eqToHom (boundary_right a b))) _
  rw [reindex_eqToHom]
  have hC : reindex (decode (CodeSystem.boundary a b))
      (restrictSubstitution face (liftSub (interval Γ) σ)) =
      decode (CodeSystem.boundary (raisedSub σ ≫ a) (raisedSub σ ≫ b)) :=
    (decode_reindex (CodeSystem.boundary a b)
      (restrictSubstitution face (liftSub (interval Γ) σ))).symm.trans
      (congrArg (@decode (restrictContext (face (Γ := Δ)))) (boundary_reindex a b σ))
  have hS := congrArg
    (fun C : Family (restrictContext (face (Γ := Δ))) =>
      reindex C (CodeSystem.includeRight (intervalFace Δ false) (intervalFace Δ true))) hC
  exact eqToHom_heq hS
    (congrArg (fun C => reindex C τ) (boundary_right a b))
    (boundary_right (raisedSub σ ≫ a) (raisedSub σ ≫ b))

private theorem glue_source_heq {Ξ : Context.{u}} {φ ψ : Cofibration Ξ}
    {A A' B : Family (restrictContext (φ.join ψ))} (h : A = A')
    (l : reindex A (CodeSystem.includeLeft φ ψ) ⟶ reindex B (CodeSystem.includeLeft φ ψ))
    (r : reindex A (CodeSystem.includeRight φ ψ) ⟶ reindex B (CodeSystem.includeRight φ ψ))
    (l' : reindex A' (CodeSystem.includeLeft φ ψ) ⟶ reindex B (CodeSystem.includeLeft φ ψ))
    (r' : reindex A' (CodeSystem.includeRight φ ψ) ⟶ reindex B (CodeSystem.includeRight φ ψ))
    (c : CodeSystem.Maps.Compatible l r) (c' : CodeSystem.Maps.Compatible l' r')
    (hl : HEq l l') (hr : HEq r r') :
    HEq (CodeSystem.Maps.glue l r c) (CodeSystem.Maps.glue l' r' c') := by
  cases h
  cases eq_of_heq hl
  cases eq_of_heq hr
  rfl

theorem boundaryMap_reindex (f : decode a ⟶ decode b) :
    HEq (Functor.whiskerLeft (restrictSubstitution face (liftSub (interval Γ) σ)).mapElements
      (boundaryMap a b f))
      (boundaryMap (raisedSub σ ≫ a) (raisedSub σ ≫ b) (codeMapReindex a b σ f)) := by
  have hC : reindex (decode (CodeSystem.boundary a b))
      (restrictSubstitution face (liftSub (interval Γ) σ)) =
      decode (CodeSystem.boundary (raisedSub σ ≫ a) (raisedSub σ ≫ b)) :=
    (decode_reindex (CodeSystem.boundary a b)
      (restrictSubstitution face (liftSub (interval Γ) σ))).symm.trans
      (congrArg (@decode (restrictContext (face (Γ := Δ)))) (boundary_reindex a b σ))
  let l := Functor.whiskerLeft
    (restrictSubstitution (intervalFace Γ false) (liftSub (interval Γ) σ)).mapElements
    (boundaryLeft a b f)
  let r := Functor.whiskerLeft
    (restrictSubstitution (intervalFace Γ true) (liftSub (interval Γ) σ)).mapElements
    (boundaryRight a b)
  let l' := boundaryLeft (raisedSub σ ≫ a) (raisedSub σ ≫ b) (codeMapReindex a b σ f)
  let r' := boundaryRight (raisedSub σ ≫ a) (raisedSub σ ≫ b)
  exact @glue_source_heq (total (interval Δ)) (intervalFace Δ false) (intervalFace Δ true)
    (reindex (decode (CodeSystem.boundary a b))
      (restrictSubstitution face (liftSub (interval Γ) σ)))
    (decode (CodeSystem.boundary (raisedSub σ ≫ a) (raisedSub σ ≫ b)))
    (reindex (decode (ambient (raisedSub σ ≫ b))) (restrictInclusion face))
    hC l r l' r' (CodeSystem.Maps.disjointCompatible
      (φ := intervalFace Δ false) (ψ := intervalFace Δ true)
      (A := reindex (decode (CodeSystem.boundary a b))
        (restrictSubstitution face (liftSub (interval Γ) σ)))
      (B := reindex (decode (ambient (raisedSub σ ≫ b))) (restrictInclusion face))
      l r intervalFace_disjoint)
    (CodeSystem.Maps.disjointCompatible l' r' intervalFace_disjoint)
    (boundaryLeft_reindex a b σ f) (boundaryRight_reindex a b σ)

private def sourceEquivalence {Ξ : Context.{u}} {A B C : Family Ξ}
    (h : A = B) (f : B ⟶ C) (E : HomotopyEquivalence f) :
    HomotopyEquivalence (eqToHom h ≫ f) := by
  subst B
  exact E

private theorem sourceEquivalence_reindex {Ξ Ω : Context.{u}} {A B C : Family Ξ}
    (h : A = B) (f : B ⟶ C) (E : HomotopyEquivalence f) (τ : Ω ⟶ Ξ) :
    HEq ((sourceEquivalence h f E).reindex τ)
      (sourceEquivalence (congrArg (fun X => reindex X τ) h)
        (Functor.whiskerLeft τ.mapElements f) (E.reindex τ)) := by
  cases h
  rfl

private theorem sourceEquivalence_congr {Ξ : Context.{u}} {A A' B C : Family Ξ}
    (h : A = A') (q : A = B) (q' : A' = B) (f : B ⟶ C) (E : HomotopyEquivalence f) :
    HEq (sourceEquivalence q f E) (sourceEquivalence q' f E) := by
  cases h
  rfl

theorem boundaryLeftEquivalence_reindex (f : decode a ⟶ decode b)
    (H : HomotopyEquivalence f) :
    HEq ((boundaryLeftEquivalence a b f H).reindex
      (restrictSubstitution (intervalFace Γ false) (liftSub (interval Γ) σ)))
      (boundaryLeftEquivalence (Γ := Δ) (raisedSub σ ≫ a) (raisedSub σ ≫ b)
        (codeMapReindex a b σ f) (H.reindex σ)) := by
  let τ := restrictSubstitution (intervalFace Γ false) (liftSub (interval Γ) σ)
  let p := restrictInclusion (intervalFace Γ false) ≫ projection (interval Γ)
  let q := restrictInclusion (intervalFace Δ false) ≫ projection (interval Δ)
  let f' := Functor.whiskerLeft (q ≫ σ).mapElements f
  have hc : (H.reindex p).reindex τ = (H.reindex σ).reindex q :=
    (H.reindex_comp p τ).trans (H.reindex_comp σ q).symm
  have h1 := sourceEquivalence_reindex (boundary_left a b)
    (Functor.whiskerLeft p.mapElements f) (H.reindex p) τ
  have h2 := congrArg (sourceEquivalence (congrArg (fun C => reindex C τ) (boundary_left a b)) f') hc
  have hC : reindex (decode (CodeSystem.boundary a b))
      (restrictSubstitution face (liftSub (interval Γ) σ)) =
      decode (CodeSystem.boundary (raisedSub σ ≫ a) (raisedSub σ ≫ b)) :=
    (decode_reindex (CodeSystem.boundary a b)
      (restrictSubstitution face (liftSub (interval Γ) σ))).symm.trans
      (congrArg (@decode (restrictContext (face (Γ := Δ)))) (boundary_reindex a b σ))
  have hS := congrArg
    (fun C : Family (restrictContext (face (Γ := Δ))) =>
      reindex C (CodeSystem.includeLeft (intervalFace Δ false) (intervalFace Δ true))) hC
  exact h1.trans ((heq_of_eq h2).trans
    (sourceEquivalence_congr hS
      (congrArg (fun C => reindex C τ) (boundary_left a b))
      (boundary_left (raisedSub σ ≫ a) (raisedSub σ ≫ b)) f' ((H.reindex σ).reindex q)))

private theorem identityEquivalence_reindex {Ξ Ω : Context.{u}} {A B : Family Ξ}
    (h : A = B) (τ : Ω ⟶ Ξ) :
    HEq ((HomotopyEquivalence.ofIso (eqToIso h)).reindex τ)
      (HomotopyEquivalence.ofIso (eqToIso (congrArg (fun C => reindex C τ) h))) := by
  cases h
  exact heq_of_eq (HomotopyEquivalence.ofIso_reindex (Iso.refl A) τ)

private theorem identityEquivalence_congr {Ξ : Context.{u}} {A A' B : Family Ξ}
    (h : A = A') (q : A = B) (q' : A' = B) :
    HEq (HomotopyEquivalence.ofIso (eqToIso q)) (HomotopyEquivalence.ofIso (eqToIso q')) := by
  cases h
  rfl

theorem boundaryRightEquivalence_reindex :
    HEq ((boundaryRightEquivalence a b).reindex
      (restrictSubstitution (intervalFace Γ true) (liftSub (interval Γ) σ)))
      (boundaryRightEquivalence (raisedSub σ ≫ a) (raisedSub σ ≫ b)) := by
  let τ := restrictSubstitution (intervalFace Γ true) (liftSub (interval Γ) σ)
  have hC : reindex (decode (CodeSystem.boundary a b))
      (restrictSubstitution face (liftSub (interval Γ) σ)) =
      decode (CodeSystem.boundary (raisedSub σ ≫ a) (raisedSub σ ≫ b)) :=
    (decode_reindex (CodeSystem.boundary a b)
      (restrictSubstitution face (liftSub (interval Γ) σ))).symm.trans
      (congrArg (@decode (restrictContext (face (Γ := Δ)))) (boundary_reindex a b σ))
  have hS := congrArg
    (fun C : Family (restrictContext (face (Γ := Δ))) =>
      reindex C (CodeSystem.includeRight (intervalFace Δ false) (intervalFace Δ true))) hC
  exact (identityEquivalence_reindex (boundary_right a b) τ).trans
    (identityEquivalence_congr hS
      (congrArg (fun C => reindex C τ) (boundary_right a b))
      (boundary_right (raisedSub σ ≫ a) (raisedSub σ ≫ b)))

private theorem disjointEquivalence_source_heq {Ξ : Context.{u}} {φ ψ : Cofibration Ξ}
    {A A' B : Family (restrictContext (φ.join ψ))} (h : A = A')
    (l : reindex A (CodeSystem.includeLeft φ ψ) ⟶ reindex B (CodeSystem.includeLeft φ ψ))
    (r : reindex A (CodeSystem.includeRight φ ψ) ⟶ reindex B (CodeSystem.includeRight φ ψ))
    (l' : reindex A' (CodeSystem.includeLeft φ ψ) ⟶ reindex B (CodeSystem.includeLeft φ ψ))
    (r' : reindex A' (CodeSystem.includeRight φ ψ) ⟶ reindex B (CodeSystem.includeRight φ ψ))
    (d : ∀ x : Ξ.Elements, φ.full x → ψ.full x → False)
    (L : HomotopyEquivalence l) (R : HomotopyEquivalence r)
    (L' : HomotopyEquivalence l') (R' : HomotopyEquivalence r')
    (hl : HEq l l') (hr : HEq r r') (hL : HEq L L') (hR : HEq R R') :
    HEq (CodeSystem.Maps.disjointEquivalence l r d L R)
      (CodeSystem.Maps.disjointEquivalence l' r' d L' R') := by
  cases h
  cases eq_of_heq hl
  cases eq_of_heq hr
  cases eq_of_heq hL
  cases eq_of_heq hR
  rfl

theorem boundaryEquivalence_reindex (f : decode a ⟶ decode b) (H : HomotopyEquivalence f) :
    HEq ((boundaryEquivalence a b f H).reindex
      (restrictSubstitution face (liftSub (interval Γ) σ)))
      (boundaryEquivalence (raisedSub σ ≫ a) (raisedSub σ ≫ b)
        (codeMapReindex a b σ f) (H.reindex σ)) := by
  have hC : reindex (decode (CodeSystem.boundary a b))
      (restrictSubstitution face (liftSub (interval Γ) σ)) =
      decode (CodeSystem.boundary (raisedSub σ ≫ a) (raisedSub σ ≫ b)) :=
    (decode_reindex (CodeSystem.boundary a b)
      (restrictSubstitution face (liftSub (interval Γ) σ))).symm.trans
      (congrArg (@decode (restrictContext (face (Γ := Δ)))) (boundary_reindex a b σ))
  let l := Functor.whiskerLeft
    (restrictSubstitution (intervalFace Γ false) (liftSub (interval Γ) σ)).mapElements
    (boundaryLeft a b f)
  let r := Functor.whiskerLeft
    (restrictSubstitution (intervalFace Γ true) (liftSub (interval Γ) σ)).mapElements
    (boundaryRight a b)
  let l' := boundaryLeft (raisedSub σ ≫ a) (raisedSub σ ≫ b) (codeMapReindex a b σ f)
  let r' := boundaryRight (raisedSub σ ≫ a) (raisedSub σ ≫ b)
  have h1 := CodeSystem.Maps.disjointEquivalence_reindex
    (φ := intervalFace Γ false) (ψ := intervalFace Γ true)
    (A := decode (CodeSystem.boundary a b))
    (B := reindex (decode (ambient b)) (restrictInclusion face))
    (boundaryLeft a b f) (boundaryRight a b) intervalFace_disjoint
    (liftSub (interval Γ) σ) (boundaryLeftEquivalence a b f H) (boundaryRightEquivalence a b)
  exact (heq_of_eq h1).trans
    (@disjointEquivalence_source_heq (total (interval Δ)) (intervalFace Δ false) (intervalFace Δ true)
      (reindex (decode (CodeSystem.boundary a b))
        (restrictSubstitution face (liftSub (interval Γ) σ)))
      (decode (CodeSystem.boundary (raisedSub σ ≫ a) (raisedSub σ ≫ b)))
      (reindex (decode (ambient (raisedSub σ ≫ b))) (restrictInclusion face))
      hC l r l' r' intervalFace_disjoint
      ((boundaryLeftEquivalence a b f H).reindex
        (restrictSubstitution (intervalFace Γ false) (liftSub (interval Γ) σ)))
      ((boundaryRightEquivalence a b).reindex
        (restrictSubstitution (intervalFace Γ true) (liftSub (interval Γ) σ)))
      (boundaryLeftEquivalence (raisedSub σ ≫ a) (raisedSub σ ≫ b)
        (codeMapReindex a b σ f) (H.reindex σ))
      (boundaryRightEquivalence (raisedSub σ ≫ a) (raisedSub σ ≫ b))
      (boundaryLeft_reindex a b σ f) (boundaryRight_reindex a b σ)
      (boundaryLeftEquivalence_reindex a b σ f H) (boundaryRightEquivalence_reindex a b σ))

/-- Substitution preserves the entire selected univalence code, including its filling data. -/
theorem uaCode_reindex (f : decode a ⟶ decode b) (H : HomotopyEquivalence f) :
    raisedSub (liftSub (interval Γ) σ) ≫ uaCode a b f H =
      uaCode (raisedSub σ ≫ a) (raisedSub σ ≫ b)
        (Functor.whiskerLeft σ.mapElements f) (H.reindex σ) := by
  exact (Glue.code_substitution face (ambient b) (CodeSystem.boundary a b)
    (boundaryMap a b f) (boundaryEquivalence a b f H) (liftSub (interval Γ) σ)).trans
    (Glue.code_congr face (ambient (raisedSub σ ≫ b))
      (raisedSub (restrictSubstitution face (liftSub (interval Γ) σ)) ≫ CodeSystem.boundary a b)
      (CodeSystem.boundary (raisedSub σ ≫ a) (raisedSub σ ≫ b)) (boundary_reindex a b σ)
      (Functor.whiskerLeft (restrictSubstitution face (liftSub (interval Γ) σ)).mapElements
        (boundaryMap a b f))
      (boundaryMap (raisedSub σ ≫ a) (raisedSub σ ≫ b) (codeMapReindex a b σ f))
      (boundaryMap_reindex a b σ f)
      ((boundaryEquivalence a b f H).reindex (restrictSubstitution face (liftSub (interval Γ) σ)))
      (boundaryEquivalence (raisedSub σ ≫ a) (raisedSub σ ≫ b)
        (codeMapReindex a b σ f) (H.reindex σ))
      (boundaryEquivalence_reindex a b σ f H))

end Univalence
end SquareKit.Cubical.Presheaf
