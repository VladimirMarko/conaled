import SquareKit.Internal.Cubical.CartesianGlue
import SquareKit.Internal.Cubical.CartesianDependentFilling
import SquareKit.Internal.Cubical.CartesianEquivalenceExtension
import SquareKit.Internal.Cubical.CartesianSmallFamilyClassification

/-! Repairing a preliminary Glue filler to retain the supplied whole-face operation. -/
set_option autoImplicit false
set_option warningAsError true
namespace SquareKit.Cubical.Cartesian
open CategoryTheory
universe u

def PartialSection.ofTerm {Γ : Context.{u}} {A : Family Γ}
    (φ : Subcontext Γ) (t : Term A) : PartialSection A φ where
  val x _ := t.val x
  natural f _ := t.property f

def Filling.backwardComp {Γ : Context.{u}} {A : Family Γ} (F : Filling A)
    (φ : Subcontext Γ) (b : OpenBox (Cartesian.reindex A (projection (interval Γ))) φ (endpoint Γ true)) : Term A :=
  F.comp (projection (interval Γ)) φ (endpoint Γ true) (endpoint Γ false) b

theorem Filling.backwardComp_reindex {Γ Δ : Context.{u}} {A : Family Γ} {F : Filling A}
    (hF : F.Lawful) (φ : Subcontext Γ)
    (b : OpenBox (Cartesian.reindex A (projection (interval Γ))) φ (endpoint Γ true)) (σ : Δ ⟶ Γ) :
    (F.reindex σ).backwardComp (φ.reindex σ) (b.reindex σ) = Term.reindex (F.backwardComp φ b) σ :=
  congrArg (fun t => Term.reindex t (endpointSub Δ false))
    (hF.uniform (projection (interval Γ)) φ (endpoint Γ true) b σ)

namespace Glue
abbrev intervalAll {Γ : Context.{u}} (φ : Subcontext (total (interval Γ))) := φ.forallInterval

theorem intervalAll_specialize {Γ : Context.{u}} (φ : Subcontext (total (interval Γ)))
    (x : Γ.Elements) (h : (intervalAll φ).Holds x) (r : (interval Γ).obj x) :
    φ.Holds (extendObj (interval Γ) x r) :=
  (Subcontext.forallInterval_iff φ x).mp h (𝟙 _) r

variable {Γ : Context.{u}} {A : Family (total (interval Γ))}
  {φ ψ : Subcontext Γ} {r : Term (interval Γ)}

/-- Enlarge a box by a compatible selected whole tube. -/
noncomputable def addTube (b : OpenBox A φ r)
    (t : PartialSection A (ψ.reindex (projection (interval Γ))))
    (h : b.tube.Compatible t)
    (h₀ : ∀ x hx, t.val ((graph r).mapElements.obj x) hx = b.base.val x) :
    OpenBox A (φ.join ψ) r where
  tube := b.tube.glue t h
  base := b.base
  boundary x hx := by
    rcases hx with hp | hq
    · exact (glueValue_left b.tube t ((graph r).mapElements.obj x) (Or.inl hp) hp).trans
        (b.boundary x hp)
    · exact (glueValue_right b.tube t h ((graph r).mapElements.obj x) (Or.inr hq) hq).trans
        (h₀ x hq)

theorem addTube_reindex (b : OpenBox A φ r)
    (t : PartialSection A (ψ.reindex (projection (interval Γ))))
    (h : b.tube.Compatible t)
    (h₀ : ∀ x hx, t.val ((graph r).mapElements.obj x) hx = b.base.val x)
    {Θ : Context.{u}} (σ : Θ ⟶ Γ) :
    (addTube b t h h₀).reindex σ =
      addTube (ψ := ψ.reindex σ) (b.reindex σ) (t.reindex (intervalSub σ))
        (h.reindex (intervalSub σ)) (fun x hx => h₀ (σ.mapElements.obj x) hx) := by
  apply OpenBox.ext
  · exact PartialSection.glue_reindex b.tube t h (intervalSub σ)
  · rfl

theorem addTube_preserves_whole {Δ : Context.{u}} {B : Family Δ}
    (F : Filling B) (hF : F.Lawful) (p : total (interval Γ) ⟶ Δ)
    (b : OpenBox (reindex B p) φ r)
    (t : PartialSection (reindex B p) (ψ.reindex (projection (interval Γ))))
    (h : b.tube.Compatible t)
    (h₀ : ∀ x hx, t.val ((graph r).mapElements.obj x) hx = b.base.val x)
    (x : (total (interval Γ)).Elements) (hx : (ψ.reindex (projection (interval Γ))).Holds x) :
    (F.fill p (φ.join ψ) r (addTube b t h h₀)).val x = t.val x hx := by
  have hu : ((φ.join ψ).reindex (projection (interval Γ))).Holds x :=
    Or.inr hx
  exact ((hF.fills p (φ.join ψ) r (addTube b t h h₀)).2 x hu).trans
    (glueValue_right b.tube t h x hu hx)

end Glue

namespace Glue
variable {Γ Δ : Context.{u}} (φ : Subcontext Γ)
  (A : Family Γ) (T : Family (restrictContext φ))
  (e : T ⟶ reindex A (restrictInclusion φ))
  (p : total (interval Δ) ⟶ Γ)

/-- A line on the universal face stays inside the original gluing face. -/
def wholeFaceLine : total (interval (restrictContext (intervalAll (φ.reindex p)))) ⟶
    restrictContext φ where
  app I := TypeCat.ofHom (fun z => ⟨p.app I ⟨z.1.val,z.2⟩,
    intervalAll_specialize (φ.reindex p) (Δ.elementsMk I z.1.val) z.1.property z.2⟩)
  naturality I J f := by
    apply ConcreteCategory.hom_ext
    intro z
    apply Subtype.ext
    exact p.naturality_apply f ⟨z.1.val,z.2⟩

theorem wholeFaceLine_inclusion :
    wholeFaceLine φ p ≫ restrictInclusion φ =
      intervalSub (restrictInclusion (intervalAll (φ.reindex p))) ≫ p := rfl

/-- The full-face equality transports the whole chosen filler, including its tube. -/
noncomputable def wholeFaceIso :
    reindex (family φ A T e)
      (intervalSub (restrictInclusion (intervalAll (φ.reindex p))) ≫ p) ≅
    reindex T (wholeFaceLine φ p) :=
  eqToIso (congrArg (fun B => reindex B (wholeFaceLine φ p)) (family_full φ A T e))

noncomputable def selectedFaceFill (F : Filling T) (ψ : Subcontext Δ) (r : Term (interval Δ))
    (b : OpenBox (reindex (family φ A T e) p) ψ r) :
    Term (reindex (family φ A T e)
      (intervalSub (restrictInclusion (intervalAll (φ.reindex p))) ≫ p)) :=
  Term.map (wholeFaceIso φ A T e p).inv
    (F.fill (wholeFaceLine φ p) (ψ.reindex (restrictInclusion (intervalAll (φ.reindex p))))
      (Term.reindex r (restrictInclusion (intervalAll (φ.reindex p))))
      ((b.reindex (restrictInclusion (intervalAll (φ.reindex p)))).map
        (wholeFaceIso φ A T e p).hom))

noncomputable def selectedFaceTube (F : Filling T) (ψ : Subcontext Δ) (r : Term (interval Δ))
    (b : OpenBox (reindex (family φ A T e) p) ψ r) :
    PartialSection (reindex (family φ A T e) p)
      ((intervalAll (φ.reindex p)).reindex (projection (interval Δ))) :=
  PartialSection.ofRestricted
    (Term.reindex (selectedFaceFill φ A T e p F ψ r b) (restrictedInterval (intervalAll (φ.reindex p))))

theorem selectedFaceFill_fills (F : Filling T) (hF : F.Lawful) (ψ : Subcontext Δ) (r : Term (interval Δ))
    (b : OpenBox (reindex (family φ A T e) p) ψ r) :
    (b.reindex (restrictInclusion (intervalAll (φ.reindex p)))).Fills
      (selectedFaceFill φ A T e p F ψ r b) := by
  let i := restrictInclusion (intervalAll (φ.reindex p))
  let q := wholeFaceIso φ A T e p
  have h := hF.fills (wholeFaceLine φ p) (ψ.reindex i) (Term.reindex r i) ((b.reindex i).map q.hom)
  constructor
  · apply Term.ext
    intro x
    exact (congrArg (q.inv.app ((graph (Term.reindex r i)).mapElements.obj x))
      (congrArg (fun t => t.val x) h.1)).trans
        (congrArg (fun f => f.app ((graph (Term.reindex r i)).mapElements.obj x)
          ((b.reindex i).base.val x)) q.hom_inv_id)
  · intro x hx
    exact (congrArg (q.inv.app x) (h.2 x hx)).trans
      (congrArg (fun f => f.app x ((b.reindex i).tube.val x hx)) q.hom_inv_id)

theorem selectedFaceTube_compatible (F : Filling T) (hF : F.Lawful) (ψ : Subcontext Δ) (r : Term (interval Δ))
    (b : OpenBox (reindex (family φ A T e) p) ψ r) :
    b.tube.Compatible (selectedFaceTube φ A T e p F ψ r b) := by
  intro x hp hq
  rcases x with @⟨I,⟨γ,z⟩⟩
  exact ((selectedFaceFill_fills φ A T e p F hF ψ r b).2
    ((total (interval (restrictContext (intervalAll (φ.reindex p))))).elementsMk I
      ⟨⟨γ,hq⟩,z⟩) hp).symm

theorem selectedFaceTube_zero (F : Filling T) (hF : F.Lawful) (ψ : Subcontext Δ) (r : Term (interval Δ))
    (b : OpenBox (reindex (family φ A T e) p) ψ r)
    (x : Δ.Elements) (hx : (intervalAll (φ.reindex p)).Holds x) :
    (selectedFaceTube φ A T e p F ψ r b).val ((graph r).mapElements.obj x) hx =
      b.base.val x := by
  exact congrArg (fun t => t.val
    ((restrictContext (intervalAll (φ.reindex p))).elementsMk x.obj ⟨x.val,hx⟩))
    (selectedFaceFill_fills φ A T e p F hF ψ r b).1

/-- A preliminary lawful filler can be repaired to retain the selected whole face filler. -/
noncomputable def preserveSelectedFace (F : Filling T) (hF : F.Lawful)
    (H : Filling (family φ A T e)) (ψ : Subcontext Δ) (r : Term (interval Δ))
    (b : OpenBox (reindex (family φ A T e) p) ψ r) : Term (reindex (family φ A T e) p) :=
  H.fill p (ψ.join (intervalAll (φ.reindex p))) r
    (addTube b (selectedFaceTube φ A T e p F ψ r b)
      (selectedFaceTube_compatible φ A T e p F hF ψ r b)
      (selectedFaceTube_zero φ A T e p F hF ψ r b))

theorem preserveSelectedFace_fills (F : Filling T) (hF : F.Lawful)
    (H : Filling (family φ A T e)) (hH : H.Lawful) (ψ : Subcontext Δ) (r : Term (interval Δ))
    (b : OpenBox (reindex (family φ A T e) p) ψ r) :
    b.Fills (preserveSelectedFace φ A T e p F hF H ψ r b) := by
  let t := selectedFaceTube φ A T e p F ψ r b
  let h := selectedFaceTube_compatible φ A T e p F hF ψ r b
  let h₀ := selectedFaceTube_zero φ A T e p F hF ψ r b
  have hf := hH.fills p (ψ.join (intervalAll (φ.reindex p))) r (addTube b t h h₀)
  constructor
  · exact hf.1
  · intro x hx
    have hu : ((ψ.join (intervalAll (φ.reindex p))).reindex (projection (interval Δ))).Holds x :=
      Or.inl hx
    exact (hf.2 x hu).trans (glueValue_left b.tube t x hu hx)

theorem preserveSelectedFace_whole (F : Filling T) (hF : F.Lawful)
    (H : Filling (family φ A T e)) (hH : H.Lawful) (ψ : Subcontext Δ) (r : Term (interval Δ))
    (b : OpenBox (reindex (family φ A T e) p) ψ r)
    (x : (total (interval Δ)).Elements)
    (hx : ((intervalAll (φ.reindex p)).reindex (projection (interval Δ))).Holds x) :
    (preserveSelectedFace φ A T e p F hF H ψ r b).val x =
      (selectedFaceTube φ A T e p F ψ r b).val x hx :=
  addTube_preserves_whole H hH p b (selectedFaceTube φ A T e p F ψ r b)
    (selectedFaceTube_compatible φ A T e p F hF ψ r b)
    (selectedFaceTube_zero φ A T e p F hF ψ r b) x hx

section FlexibleFace
variable (δ : Subcontext Δ)
  (hδ : ∀ (x : Δ.Elements), δ.Holds x → ∀ r : (interval Δ).obj x,
    (φ.reindex p).Holds (extendObj (interval Δ) x r))

/-- A supplied face whose lines stay inside the gluing face. -/
def wholeFaceLineOn : total (interval (restrictContext δ)) ⟶
    restrictContext φ where
  app I := TypeCat.ofHom (fun z => ⟨p.app I ⟨z.1.val,z.2⟩,
    hδ (Δ.elementsMk I z.1.val) z.1.property z.2⟩)
  naturality I J f := by
    apply ConcreteCategory.hom_ext
    intro z
    apply Subtype.ext
    exact p.naturality_apply f ⟨z.1.val,z.2⟩

theorem wholeFaceLine_inclusionOn :
    wholeFaceLineOn φ p δ hδ ≫ restrictInclusion φ =
      intervalSub (restrictInclusion δ) ≫ p := rfl

/-- The full-face equality transports the whole chosen filler, including its tube. -/
noncomputable def wholeFaceIsoOn :
    reindex (family φ A T e)
      (intervalSub (restrictInclusion δ) ≫ p) ≅
    reindex T (wholeFaceLineOn φ p δ hδ) :=
  eqToIso (congrArg (fun B => reindex B (wholeFaceLineOn φ p δ hδ)) (family_full φ A T e))

noncomputable def selectedFaceFillOn (F : Filling T) (ψ : Subcontext Δ) (r : Term (interval Δ))
    (b : OpenBox (reindex (family φ A T e) p) ψ r) :
    Term (reindex (family φ A T e)
      (intervalSub (restrictInclusion δ) ≫ p)) :=
  Term.map (wholeFaceIsoOn φ A T e p δ hδ).inv
    (F.fill (wholeFaceLineOn φ p δ hδ) (ψ.reindex (restrictInclusion δ)) (Term.reindex r (restrictInclusion δ))
      ((b.reindex (restrictInclusion δ)).map
        (wholeFaceIsoOn φ A T e p δ hδ).hom))

noncomputable def selectedFaceTubeOn (F : Filling T) (ψ : Subcontext Δ) (r : Term (interval Δ))
    (b : OpenBox (reindex (family φ A T e) p) ψ r) :
    PartialSection (reindex (family φ A T e) p)
      (δ.reindex (projection (interval Δ))) :=
  PartialSection.ofRestricted
    (Term.reindex (selectedFaceFillOn φ A T e p δ hδ F ψ r b) (restrictedInterval δ))

theorem selectedFaceFill_fillsOn (F : Filling T) (hF : F.Lawful) (ψ : Subcontext Δ) (r : Term (interval Δ))
    (b : OpenBox (reindex (family φ A T e) p) ψ r) :
    (b.reindex (restrictInclusion δ)).Fills
      (selectedFaceFillOn φ A T e p δ hδ F ψ r b) := by
  let i := restrictInclusion δ
  let q := wholeFaceIsoOn φ A T e p δ hδ
  have h := hF.fills (wholeFaceLineOn φ p δ hδ) (ψ.reindex i) (Term.reindex r i) ((b.reindex i).map q.hom)
  constructor
  · apply Term.ext
    intro x
    exact (congrArg (q.inv.app ((graph (Term.reindex r i)).mapElements.obj x))
      (congrArg (fun t => t.val x) h.1)).trans
        (congrArg (fun f => f.app ((graph (Term.reindex r i)).mapElements.obj x)
          ((b.reindex i).base.val x)) q.hom_inv_id)
  · intro x hx
    exact (congrArg (q.inv.app x) (h.2 x hx)).trans
      (congrArg (fun f => f.app x ((b.reindex i).tube.val x hx)) q.hom_inv_id)

theorem selectedFaceTube_compatibleOn (F : Filling T) (hF : F.Lawful) (ψ : Subcontext Δ) (r : Term (interval Δ))
    (b : OpenBox (reindex (family φ A T e) p) ψ r) :
    b.tube.Compatible (selectedFaceTubeOn φ A T e p δ hδ F ψ r b) := by
  intro x hp hq
  rcases x with @⟨I,⟨γ,z⟩⟩
  exact ((selectedFaceFill_fillsOn φ A T e p δ hδ F hF ψ r b).2
    ((total (interval (restrictContext δ))).elementsMk I
      ⟨⟨γ,hq⟩,z⟩) hp).symm

theorem selectedFaceTube_zeroOn (F : Filling T) (hF : F.Lawful) (ψ : Subcontext Δ) (r : Term (interval Δ))
    (b : OpenBox (reindex (family φ A T e) p) ψ r)
    (x : Δ.Elements) (hx : δ.Holds x) :
    (selectedFaceTubeOn φ A T e p δ hδ F ψ r b).val ((graph r).mapElements.obj x) hx =
      b.base.val x := by
  exact congrArg (fun t => t.val
    ((restrictContext δ).elementsMk x.obj ⟨x.val,hx⟩))
    (selectedFaceFill_fillsOn φ A T e p δ hδ F hF ψ r b).1

/-- A preliminary lawful filler can be repaired to retain the selected whole face filler. -/
noncomputable def preserveSelectedFaceOn (F : Filling T) (hF : F.Lawful)
    (H : Filling (family φ A T e)) (ψ : Subcontext Δ) (r : Term (interval Δ))
    (b : OpenBox (reindex (family φ A T e) p) ψ r) : Term (reindex (family φ A T e) p) :=
  H.fill p (ψ.join δ) r
    (addTube b (selectedFaceTubeOn φ A T e p δ hδ F ψ r b)
      (selectedFaceTube_compatibleOn φ A T e p δ hδ F hF ψ r b)
      (selectedFaceTube_zeroOn φ A T e p δ hδ F hF ψ r b))

theorem preserveSelectedFace_fillsOn (F : Filling T) (hF : F.Lawful)
    (H : Filling (family φ A T e)) (hH : H.Lawful) (ψ : Subcontext Δ) (r : Term (interval Δ))
    (b : OpenBox (reindex (family φ A T e) p) ψ r) :
    b.Fills (preserveSelectedFaceOn φ A T e p δ hδ F hF H ψ r b) := by
  let t := selectedFaceTubeOn φ A T e p δ hδ F ψ r b
  let h := selectedFaceTube_compatibleOn φ A T e p δ hδ F hF ψ r b
  let h₀ := selectedFaceTube_zeroOn φ A T e p δ hδ F hF ψ r b
  have hf := hH.fills p (ψ.join δ) r (addTube b t h h₀)
  constructor
  · exact hf.1
  · intro x hx
    have hu : ((ψ.join δ).reindex (projection (interval Δ))).Holds x :=
      Or.inl hx
    exact (hf.2 x hu).trans (glueValue_left b.tube t x hu hx)

theorem preserveSelectedFace_wholeOn (F : Filling T) (hF : F.Lawful)
    (H : Filling (family φ A T e)) (hH : H.Lawful) (ψ : Subcontext Δ) (r : Term (interval Δ))
    (b : OpenBox (reindex (family φ A T e) p) ψ r)
    (x : (total (interval Δ)).Elements)
    (hx : (δ.reindex (projection (interval Δ))).Holds x) :
    (preserveSelectedFaceOn φ A T e p δ hδ F hF H ψ r b).val x =
      (selectedFaceTubeOn φ A T e p δ hδ F ψ r b).val x hx :=
  addTube_preserves_whole H hH p b (selectedFaceTubeOn φ A T e p δ hδ F ψ r b)
    (selectedFaceTube_compatibleOn φ A T e p δ hδ F hF ψ r b)
    (selectedFaceTube_zeroOn φ A T e p δ hδ F hF ψ r b) x hx


theorem reindex_eqToIso {Ξ Ω : Context.{u}} (B C : Family Ξ) (h : B = C) (σ : Ω ⟶ Ξ) :
    eqToIso (congrArg (fun D => reindex D σ) h) = Functor.isoWhiskerLeft σ.mapElements (eqToIso h) := by
  cases h
  rfl

theorem wholeFaceIsoOn_reindex {Θ : Context.{u}} (σ : Θ ⟶ Δ) :
    wholeFaceIsoOn φ A T e (intervalSub σ ≫ p) (δ.reindex σ)
      (fun x hx r => hδ (σ.mapElements.obj x) hx r) =
    Functor.isoWhiskerLeft (intervalSub (restrictSubstitution δ σ)).mapElements
      (wholeFaceIsoOn φ A T e p δ hδ) := by
  have ho := reindex_eqToIso _ _ (family_full φ A T e) (wholeFaceLineOn φ p δ hδ)
  have hn := reindex_eqToIso _ _ (family_full φ A T e)
    (wholeFaceLineOn φ (intervalSub σ ≫ p) (δ.reindex σ)
      (fun x hx r => hδ (σ.mapElements.obj x) hx r))
  exact hn.trans (congrArg
    (Functor.isoWhiskerLeft (intervalSub (restrictSubstitution δ σ)).mapElements) ho.symm)

theorem selectedFaceFillOn_reindex (F : Filling T) (hF : F.Lawful) (ψ : Subcontext Δ) (r : Term (interval Δ))
    (b : OpenBox (reindex (family φ A T e) p) ψ r) {Θ : Context.{u}} (σ : Θ ⟶ Δ) :
    selectedFaceFillOn φ A T e (intervalSub σ ≫ p) (δ.reindex σ)
      (fun x hx r => hδ (σ.mapElements.obj x) hx r) F (ψ.reindex σ) (Term.reindex r σ) (b.reindex σ) =
    Term.reindex (selectedFaceFillOn φ A T e p δ hδ F ψ r b)
      (intervalSub (restrictSubstitution δ σ)) := by
  let ρ := restrictSubstitution δ σ
  let q₀ := wholeFaceIsoOn φ A T e p δ hδ
  let q₁ := wholeFaceIsoOn φ A T e (intervalSub σ ≫ p) (δ.reindex σ)
    (fun x hx r => hδ (σ.mapElements.obj x) hx r)
  let b₀ := (b.reindex (restrictInclusion δ)).map q₀.hom
  let b₁ := ((b.reindex σ).reindex (restrictInclusion (δ.reindex σ))).map q₁.hom
  have hb : b₁ = b₀.reindex ρ :=
    congrArg (fun η => ((b.reindex σ).reindex (restrictInclusion (δ.reindex σ))).map η)
      (congrArg Iso.hom (wholeFaceIsoOn_reindex φ A T e p δ hδ σ))
  have hf := (congrArg (F.fill
    (wholeFaceLineOn φ (intervalSub σ ≫ p) (δ.reindex σ)
      (fun x hx r => hδ (σ.mapElements.obj x) hx r))
    ((ψ.reindex σ).reindex (restrictInclusion (δ.reindex σ)))
    (Term.reindex (Term.reindex r σ) (restrictInclusion (δ.reindex σ)))) hb).trans
      (hF.uniform (wholeFaceLineOn φ p δ hδ) (ψ.reindex (restrictInclusion δ)) (Term.reindex r (restrictInclusion δ)) b₀ ρ)
  exact (congrArg (fun η => Term.map η (F.fill
    (wholeFaceLineOn φ (intervalSub σ ≫ p) (δ.reindex σ)
      (fun x hx r => hδ (σ.mapElements.obj x) hx r))
    ((ψ.reindex σ).reindex (restrictInclusion (δ.reindex σ)))
    (Term.reindex (Term.reindex r σ) (restrictInclusion (δ.reindex σ))) b₁))
      (congrArg Iso.inv (wholeFaceIsoOn_reindex φ A T e p δ hδ σ))).trans
        (congrArg (Term.map (Functor.whiskerLeft
          (intervalSub ρ).mapElements q₀.inv)) hf)

theorem selectedFaceTubeOn_reindex (F : Filling T) (hF : F.Lawful) (ψ : Subcontext Δ) (r : Term (interval Δ))
    (b : OpenBox (reindex (family φ A T e) p) ψ r) {Θ : Context.{u}} (σ : Θ ⟶ Δ) :
    selectedFaceTubeOn φ A T e (intervalSub σ ≫ p) (δ.reindex σ)
      (fun x hx r => hδ (σ.mapElements.obj x) hx r) F (ψ.reindex σ) (Term.reindex r σ) (b.reindex σ) =
    (selectedFaceTubeOn φ A T e p δ hδ F ψ r b).reindex (intervalSub σ) := by
  apply PartialSection.ext
  intro x hx
  exact congrArg (fun t => t.val
    ((total (interval (restrictContext (δ.reindex σ)))).elementsMk x.obj ⟨⟨x.val.1,hx⟩,x.val.2⟩))
    (selectedFaceFillOn_reindex φ A T e p δ hδ F hF ψ r b σ)

theorem addTube_congr {Ω : Context.{u}} {B : Family (total (interval Ω))}
    {χ η : Subcontext Ω} {r : Term (interval Ω)} (b : OpenBox B χ r)
    (t t' : PartialSection B (η.reindex (projection (interval Ω)))) (ht : t = t')
    (h : b.tube.Compatible t) (h' : b.tube.Compatible t')
    (h₀ : ∀ x hx, t.val ((graph r).mapElements.obj x) hx = b.base.val x)
    (h₀' : ∀ x hx, t'.val ((graph r).mapElements.obj x) hx = b.base.val x) :
    addTube b t h h₀ = addTube b t' h' h₀' := by
  cases ht
  rfl

theorem preserveSelectedFaceOn_reindex (F : Filling T) (hF : F.Lawful)
    (H : Filling (family φ A T e)) (hH : H.Lawful) (ψ : Subcontext Δ) (r : Term (interval Δ))
    (b : OpenBox (reindex (family φ A T e) p) ψ r) {Θ : Context.{u}} (σ : Θ ⟶ Δ) :
    preserveSelectedFaceOn φ A T e (intervalSub σ ≫ p) (δ.reindex σ)
      (fun x hx r => hδ (σ.mapElements.obj x) hx r) F hF H (ψ.reindex σ) (Term.reindex r σ) (b.reindex σ) =
    Term.reindex (preserveSelectedFaceOn φ A T e p δ hδ F hF H ψ r b) (intervalSub σ) := by
  let t := selectedFaceTubeOn φ A T e p δ hδ F ψ r b
  let hc := selectedFaceTube_compatibleOn φ A T e p δ hδ F hF ψ r b
  let hz := selectedFaceTube_zeroOn φ A T e p δ hδ F hF ψ r b
  let t' := selectedFaceTubeOn φ A T e (intervalSub σ ≫ p) (δ.reindex σ)
    (fun x hx r => hδ (σ.mapElements.obj x) hx r) F (ψ.reindex σ) (Term.reindex r σ) (b.reindex σ)
  let hc' := selectedFaceTube_compatibleOn φ A T e (intervalSub σ ≫ p) (δ.reindex σ)
    (fun x hx r => hδ (σ.mapElements.obj x) hx r) F hF (ψ.reindex σ) (Term.reindex r σ) (b.reindex σ)
  let hz' := selectedFaceTube_zeroOn φ A T e (intervalSub σ ≫ p) (δ.reindex σ)
    (fun x hx r => hδ (σ.mapElements.obj x) hx r) F hF (ψ.reindex σ) (Term.reindex r σ) (b.reindex σ)
  have hb : addTube (b.reindex σ) t' hc' hz' = (addTube b t hc hz).reindex σ :=
    (addTube_congr (b.reindex σ) t' (t.reindex (intervalSub σ))
      (selectedFaceTubeOn_reindex φ A T e p δ hδ F hF ψ r b σ)
      hc' (hc.reindex (intervalSub σ)) hz' (fun x hx => hz (σ.mapElements.obj x) hx)).trans
        (addTube_reindex b t hc hz σ).symm
  exact (congrArg (H.fill (intervalSub σ ≫ p) ((ψ.join δ).reindex σ) (Term.reindex r σ)) hb).trans
    (hH.uniform p (ψ.join δ) r (addTube b t hc hz) σ)

theorem preserveSelectedFaceOn_congr (δ' : Subcontext Δ)
    (hδ' : ∀ (x : Δ.Elements), δ'.Holds x → ∀ r : (interval Δ).obj x,
      (φ.reindex p).Holds (extendObj (interval Δ) x r)) (he : δ = δ')
    (F : Filling T) (hF : F.Lawful) (H : Filling (family φ A T e)) (ψ : Subcontext Δ) (r : Term (interval Δ))
    (b : OpenBox (reindex (family φ A T e) p) ψ r) :
    preserveSelectedFaceOn φ A T e p δ hδ F hF H ψ r b =
      preserveSelectedFaceOn φ A T e p δ' hδ' F hF H ψ r b := by
  cases he
  rfl

end FlexibleFace

theorem preserveSelectedFace_reindex (F : Filling T) (hF : F.Lawful)
    (H : Filling (family φ A T e)) (hH : H.Lawful) (ψ : Subcontext Δ) (r : Term (interval Δ))
    (b : OpenBox (reindex (family φ A T e) p) ψ r) {Θ : Context.{u}} (σ : Θ ⟶ Δ) :
    preserveSelectedFace φ A T e (intervalSub σ ≫ p) F hF H (ψ.reindex σ) (Term.reindex r σ) (b.reindex σ) =
      Term.reindex (preserveSelectedFace φ A T e p F hF H ψ r b) (intervalSub σ) :=
  (preserveSelectedFaceOn_congr φ A T e (intervalSub σ ≫ p)
    (intervalAll (φ.reindex (intervalSub σ ≫ p)))
    (intervalAll_specialize (φ.reindex (intervalSub σ ≫ p)))
    ((intervalAll (φ.reindex p)).reindex σ)
    (fun x hx r => intervalAll_specialize (φ.reindex p) (σ.mapElements.obj x) hx r)
    (Subcontext.forallInterval_reindex (φ.reindex p) σ) F hF H (ψ.reindex σ) (Term.reindex r σ) (b.reindex σ)).trans
      (preserveSelectedFaceOn_reindex φ A T e p (intervalAll (φ.reindex p))
        (intervalAll_specialize (φ.reindex p)) F hF H hH ψ r b σ)

/-- Align any lawful preliminary operation with the selected whole-face operation. -/
noncomputable def alignedFilling (F : Filling T) (hF : F.Lawful)
    (H : Filling (family φ A T e)) : Filling (family φ A T e) where
  fill q ψ r b := preserveSelectedFace φ A T e q F hF H ψ r b

theorem alignedFilling_lawful (F : Filling T) (hF : F.Lawful)
    (H : Filling (family φ A T e)) (hH : H.Lawful) :
    (alignedFilling φ A T e F hF H).Lawful where
  fills q ψ r b := preserveSelectedFace_fills φ A T e q F hF H hH ψ r b
  uniform q ψ r b σ := preserveSelectedFace_reindex φ A T e q F hF H hH ψ r b σ

theorem alignedFilling_restrict_line (F : Filling T) (hF : F.Lawful)
    (H : Filling (family φ A T e)) (hH : H.Lawful)
    (ψ : Subcontext Δ) (r : Term (interval Δ))
    (b : OpenBox (reindex (family φ A T e) p) ψ r) :
    Term.reindex ((alignedFilling φ A T e F hF H).fill p ψ r b)
      (intervalSub (restrictInclusion (intervalAll (φ.reindex p)))) =
    selectedFaceFill φ A T e p F ψ r b := by
  apply Term.ext
  intro x
  exact preserveSelectedFace_whole φ A T e p F hF H hH ψ r b
    ((intervalSub (restrictInclusion (intervalAll (φ.reindex p)))).mapElements.obj x)
    x.val.1.property

def fullLineSection (q : total (interval Δ) ⟶ restrictContext φ) :
    Δ ⟶ restrictContext (intervalAll (φ.reindex (q ≫ restrictInclusion φ))) where
  app I := TypeCat.ofHom (fun γ => ⟨γ,
    (q.mapElements.obj (freshExtension (Δ.elementsMk I γ))).val.property⟩)
  naturality _ _ _ := rfl

theorem fullLineSection_inclusion (q : total (interval Δ) ⟶ restrictContext φ) :
    fullLineSection φ q ≫ restrictInclusion (intervalAll (φ.reindex (q ≫ restrictInclusion φ))) = 𝟙 Δ := rfl

theorem fullLineSection_line (q : total (interval Δ) ⟶ restrictContext φ) :
    intervalSub
      (fullLineSection φ q) ≫ wholeFaceLine φ (q ≫ restrictInclusion φ) = q := rfl

theorem fullLineSection_iso (q : total (interval Δ) ⟶ restrictContext φ) :
    Functor.isoWhiskerLeft
      (intervalSub
        (fullLineSection φ q)).mapElements (wholeFaceIso φ A T e (q ≫ restrictInclusion φ)) =
      Functor.isoWhiskerLeft q.mapElements (eqToIso (family_full φ A T e)) :=
  congrArg (Functor.isoWhiskerLeft
    (intervalSub
      (fullLineSection φ q)).mapElements)
      (reindex_eqToIso _ _ (family_full φ A T e) (wholeFaceLine φ (q ≫ restrictInclusion φ)))

theorem selectedFaceFill_full (F : Filling T) (hF : F.Lawful)
    (q : total (interval Δ) ⟶ restrictContext φ) (ψ : Subcontext Δ) (r : Term (interval Δ))
    (b : OpenBox (reindex (family φ A T e) (q ≫ restrictInclusion φ)) ψ r) :
    Term.reindex (selectedFaceFill φ A T e (q ≫ restrictInclusion φ) F ψ r b)
      (intervalSub
        (fullLineSection φ q)) =
    Term.map (Functor.whiskerLeft q.mapElements (eqToIso (family_full φ A T e)).inv)
      (F.fill q ψ r (b.map (Functor.whiskerLeft q.mapElements (eqToIso (family_full φ A T e)).hom))) := by
  let δ := intervalAll (φ.reindex (q ≫ restrictInclusion φ))
  let τ := intervalSub (fullLineSection φ q)
  let q₀ := wholeFaceIso φ A T e (q ≫ restrictInclusion φ)
  let q₁ := Functor.isoWhiskerLeft q.mapElements (eqToIso (family_full φ A T e))
  let b₀ := (b.reindex (restrictInclusion δ)).map q₀.hom
  have hb : b₀.reindex (fullLineSection φ q) = b.map q₁.hom :=
    congrArg (fun η => b.map η) (congrArg Iso.hom (fullLineSection_iso φ A T e q))
  have hf := (hF.uniform (wholeFaceLine φ (q ≫ restrictInclusion φ))
    (ψ.reindex (restrictInclusion δ)) (Term.reindex r (restrictInclusion δ)) b₀ (fullLineSection φ q)).symm.trans
      (congrArg (F.fill q ψ r) hb)
  exact (congrArg (fun η => Term.map η
    (Term.reindex (F.fill (wholeFaceLine φ (q ≫ restrictInclusion φ)) (ψ.reindex (restrictInclusion δ)) (Term.reindex r (restrictInclusion δ)) b₀) τ))
      (congrArg Iso.inv (fullLineSection_iso φ A T e q))).trans
        (congrArg (Term.map q₁.inv) hf)


theorem alignedFilling_full_line (F : Filling T) (hF : F.Lawful)
    (H : Filling (family φ A T e)) (hH : H.Lawful)
    (q : total (interval Δ) ⟶ restrictContext φ) (ψ : Subcontext Δ) (r : Term (interval Δ))
    (b : OpenBox (reindex (family φ A T e) (q ≫ restrictInclusion φ)) ψ r) :
    (alignedFilling φ A T e F hF H).fill (q ≫ restrictInclusion φ) ψ r b =
    Term.map (Functor.whiskerLeft q.mapElements (eqToIso (family_full φ A T e)).inv)
      (F.fill q ψ r (b.map (Functor.whiskerLeft q.mapElements (eqToIso (family_full φ A T e)).hom))) := by
  have h := congrArg (fun t => Term.reindex t (intervalSub (fullLineSection φ q)))
    (alignedFilling_restrict_line φ A T e (q ≫ restrictInclusion φ) F hF H hH ψ r b)
  exact h.trans (selectedFaceFill_full φ A T e F hF q ψ r b)

/-- Restriction retains every selected output, not merely the endpoint values. -/
theorem alignedFilling_full (F : Filling T) (hF : F.Lawful)
    (H : Filling (family φ A T e)) (hH : H.Lawful) :
    ((alignedFilling φ A T e F hF H).reindex (restrictInclusion φ)).transport
      (eqToIso (family_full φ A T e)) = F := by
  apply Filling.ext
  intro Ξ q ψ r b
  let i := Functor.isoWhiskerLeft q.mapElements (eqToIso (family_full φ A T e))
  have h := alignedFilling_full_line φ A T e F hF H hH q ψ r (b.map i.inv)
  exact (congrArg (Term.map i.hom) h).trans
    ((Term.map_iso_roundtrip i.symm _).trans
      (congrArg (F.fill q ψ r) (OpenBox.map_iso_roundtrip i b)))

/-- Read the face component of partial compatible Glue data. -/
def compatiblePartialFace {Ξ : Context.{u}} (θ : Subcontext Ξ) (B : Family Ξ)
    (U : Family (restrictContext θ)) (f : U ⟶ reindex B (restrictInclusion θ))
    {χ : Subcontext Ξ} (s : PartialSection (compatibleFamily θ B U f) χ) :
    PartialSection U (χ.reindex (restrictInclusion θ)) where
  val x hx := (s.val ((restrictInclusion θ).mapElements.obj x) hx).face (𝟙 _) x.val.property
  natural {x y} g hx := by
    let k := (restrictInclusion θ).mapElements.map g
    have ht := (s.val ((restrictInclusion θ).mapElements.obj x) hx).naturality
      (𝟙 _) k x.val.property
    have hs := congrArg (fun z => z.face (𝟙 _) y.val.property) (s.natural k hx)
    change (s.val ((restrictInclusion θ).mapElements.obj x) hx).face (k ≫ 𝟙 _) _ =
      (s.val ((restrictInclusion θ).mapElements.obj y) _).face (𝟙 _) _ at hs
    exact ht.trans (by simpa only [Category.id_comp, Category.comp_id] using hs)

theorem compatiblePartialFace_image {Ξ : Context.{u}} (θ : Subcontext Ξ) (B : Family Ξ)
    (U : Family (restrictContext θ)) (f : U ⟶ reindex B (restrictInclusion θ))
    {χ : Subcontext Ξ} (s : PartialSection (compatibleFamily θ B U f) χ) :
    (compatiblePartialFace θ B U f s).map f =
      (s.map (compatibleUnglue θ B U f)).reindex (restrictInclusion θ) := by
  apply PartialSection.ext
  intro x hx
  exact ((s.val ((restrictInclusion θ).mapElements.obj x) hx).compatible (𝟙 _) x.val.property).trans
    (ConcreteCategory.congr_hom (B.map_id _) _)

/-- A path defined on a face supplies an actual partial tube in the ambient family. -/
def restrictedPathTube {Ξ : Context.{u}} {B : Family Ξ} (θ : Subcontext Ξ)
    (a : Term B) (t : Term (reindex B (restrictInclusion θ)))
    (q : Term (homogeneousPath (reindex B (restrictInclusion θ))
      t (Term.reindex a (restrictInclusion θ)))) :
    PartialSection (reindex B (projection (interval Ξ)))
      (θ.reindex (projection (interval Ξ))) :=
  PartialSection.ofRestricted (Term.reindex (pathApp q) (restrictedInterval θ))

theorem restrictedPathTube_source {Ξ : Context.{u}} {B : Family Ξ} (θ : Subcontext Ξ)
    (a : Term B) (t : Term (reindex B (restrictInclusion θ)))
    (q : Term (homogeneousPath (reindex B (restrictInclusion θ))
      t (Term.reindex a (restrictInclusion θ)))) (x : Ξ.Elements) (hx : θ.Holds x) :
    (restrictedPathTube θ a t q).val ((endpointSub Ξ true).mapElements.obj x) hx = a.val x :=
  congrArg (fun s => s.val (faceObj θ x hx)) (pathApp_one q)

theorem restrictedPathTube_target {Ξ : Context.{u}} {B : Family Ξ} (θ : Subcontext Ξ)
    (a : Term B) (t : Term (reindex B (restrictInclusion θ)))
    (q : Term (homogeneousPath (reindex B (restrictInclusion θ))
      t (Term.reindex a (restrictInclusion θ)))) (x : Ξ.Elements) (hx : θ.Holds x) :
    (restrictedPathTube θ a t q).val ((endpointSub Ξ false).mapElements.obj x) hx =
      t.val (faceObj θ x hx) :=
  congrArg (fun s => s.val (faceObj θ x hx)) (pathApp_zero q)

/-- Correct ambient values along a face path while fixing a prescribed boundary. -/
noncomputable def correctionBox {Ξ : Context.{u}} {B : Family Ξ}
    (θ χ : Subcontext Ξ) (a : Term B) (t : Term (reindex B (restrictInclusion θ)))
    (q : Term (homogeneousPath (reindex B (restrictInclusion θ))
      t (Term.reindex a (restrictInclusion θ))))
    (h : (restrictedPathTube θ a t q).Compatible
      (PartialSection.ofTerm (χ.reindex (projection (interval Ξ)))
        (Term.reindex a (projection (interval Ξ))))) :
    OpenBox (reindex B (projection (interval Ξ))) (θ.join χ) (endpoint Ξ true) where
  tube := (restrictedPathTube θ a t q).glue (PartialSection.ofTerm _ _) h
  base := a
  boundary x hx := by
    rcases hx with ht | hc
    · exact (glueValue_left (restrictedPathTube θ a t q)
        (PartialSection.ofTerm (χ.reindex (projection (interval Ξ))) (Term.reindex a (projection (interval Ξ))))
        ((endpointSub Ξ true).mapElements.obj x) (Or.inl ht) ht).trans
          (restrictedPathTube_source θ a t q x ht)
    · exact glueValue_right (restrictedPathTube θ a t q) _ h
        ((endpointSub Ξ true).mapElements.obj x) (Or.inr hc) hc

noncomputable def correctAmbient {Ξ : Context.{u}} {B : Family Ξ} (F : Filling B)
    (θ χ : Subcontext Ξ) (a : Term B) (t : Term (reindex B (restrictInclusion θ)))
    (q : Term (homogeneousPath (reindex B (restrictInclusion θ))
      t (Term.reindex a (restrictInclusion θ))))
    (h : (restrictedPathTube θ a t q).Compatible
      (PartialSection.ofTerm (χ.reindex (projection (interval Ξ)))
        (Term.reindex a (projection (interval Ξ))))) : Term B :=
  F.comp (projection (interval Ξ)) (θ.join χ) (endpoint Ξ true) (endpoint Ξ false) (correctionBox θ χ a t q h)

theorem correctAmbient_face {Ξ : Context.{u}} {B : Family Ξ} (F : Filling B) (hF : F.Lawful)
    (θ χ : Subcontext Ξ) (a : Term B) (t : Term (reindex B (restrictInclusion θ)))
    (q : Term (homogeneousPath (reindex B (restrictInclusion θ))
      t (Term.reindex a (restrictInclusion θ))))
    (h : (restrictedPathTube θ a t q).Compatible
      (PartialSection.ofTerm (χ.reindex (projection (interval Ξ)))
        (Term.reindex a (projection (interval Ξ))))) (x : Ξ.Elements) (hx : θ.Holds x) :
    (correctAmbient F θ χ a t q h).val x = t.val (faceObj θ x hx) := by
  have hu : (θ.join χ).Holds x := Or.inl hx
  exact ((hF.fills (projection (interval Ξ)) (θ.join χ) (endpoint Ξ true) (correctionBox θ χ a t q h)).2 ((endpointSub Ξ false).mapElements.obj x) hu).trans
    ((glueValue_left (restrictedPathTube θ a t q)
        (PartialSection.ofTerm (χ.reindex (projection (interval Ξ))) (Term.reindex a (projection (interval Ξ)))) ((endpointSub Ξ false).mapElements.obj x)
      hu hx).trans (restrictedPathTube_target θ a t q x hx))

theorem correctAmbient_fixed {Ξ : Context.{u}} {B : Family Ξ} (F : Filling B) (hF : F.Lawful)
    (θ χ : Subcontext Ξ) (a : Term B) (t : Term (reindex B (restrictInclusion θ)))
    (q : Term (homogeneousPath (reindex B (restrictInclusion θ))
      t (Term.reindex a (restrictInclusion θ))))
    (h : (restrictedPathTube θ a t q).Compatible
      (PartialSection.ofTerm (χ.reindex (projection (interval Ξ)))
        (Term.reindex a (projection (interval Ξ))))) (x : Ξ.Elements) (hx : χ.Holds x) :
    (correctAmbient F θ χ a t q h).val x = a.val x := by
  have hu : (θ.join χ).Holds x := Or.inr hx
  exact ((hF.fills (projection (interval Ξ)) (θ.join χ) (endpoint Ξ true) (correctionBox θ χ a t q h)).2 ((endpointSub Ξ false).mapElements.obj x) hu).trans
    (glueValue_right (restrictedPathTube θ a t q) _ h ((endpointSub Ξ false).mapElements.obj x) hu hx)


theorem correctAmbient_congr {Ξ : Context.{u}} {B : Family Ξ} (F : Filling B)
    (θ χ : Subcontext Ξ) (a : Term B)
    (t t' : Term (reindex B (restrictInclusion θ)))
    (q : Term (homogeneousPath (reindex B (restrictInclusion θ))
      t (Term.reindex a (restrictInclusion θ))))
    (q' : Term (homogeneousPath (reindex B (restrictInclusion θ))
      t' (Term.reindex a (restrictInclusion θ))))
    (h : (restrictedPathTube θ a t q).Compatible
      (PartialSection.ofTerm (χ.reindex (projection (interval Ξ)))
        (Term.reindex a (projection (interval Ξ)))))
    (h' : (restrictedPathTube θ a t' q').Compatible
      (PartialSection.ofTerm (χ.reindex (projection (interval Ξ)))
        (Term.reindex a (projection (interval Ξ)))))
    (ht : t = t') (hq : HEq q q') :
    correctAmbient F θ χ a t q h = correctAmbient F θ χ a t' q' h' := by
  cases ht
  cases hq
  rfl

theorem Datum.nativeIso_full {Γ : Context.{u}} (D : Datum Γ) :
    (Functor.isoWhiskerLeft (restrictInclusion D.face).mapElements D.nativeIso) ≪≫
      eqToIso D.smallFamily_full = eqToIso (family_full D.face D.ambient D.faceFamily D.map) := by
  apply Iso.ext
  apply NatTrans.ext
  funext x
  apply ConcreteCategory.hom_ext
  intro a
  have hc : ∀ {B C : Family (restrictContext D.face)} (h : B = C) (z : B.obj x),
      HEq ((eqToHom h).app x z) z := by
    intro B C h z
    cases h
    rfl
  let t := (eqToHom (family_full D.face D.ambient D.faceFamily D.map)).app x a
  have ha : HEq a t := (hc _ a).symm
  have hf := fiberEquiv_full D.face D.ambient D.faceFamily D.map x.val.property a t ha
  have hr := congrArg (fun z : D.compatible.obj ((restrictInclusion D.face).mapElements.obj x) =>
    z.face (𝟙 _) x.val.property) hf
  exact eq_of_heq ((hc D.smallFamily_full _).trans
    ((D.smallFiberEquiv_symm_full x.val.property
      (fiberEquiv D.face D.ambient D.faceFamily D.map _ a)).trans
        (heq_of_eq (hr.trans (fromFace_read D.face D.ambient D.faceFamily D.map x.val.property t)))))

noncomputable def Datum.alignedSmallFilling {Γ : Context.{u}} (D : Datum Γ)
    (F : Filling D.faceFamily) (hF : F.Lawful)
    (H : Filling (family D.face D.ambient D.faceFamily D.map)) : Filling D.smallFamily :=
  (alignedFilling D.face D.ambient D.faceFamily D.map F hF H).transport D.nativeIso

theorem Datum.alignedSmallFilling_lawful {Γ : Context.{u}} (D : Datum Γ)
    (F : Filling D.faceFamily) (hF : F.Lawful)
    (H : Filling (family D.face D.ambient D.faceFamily D.map)) (hH : H.Lawful) :
    (D.alignedSmallFilling F hF H).Lawful :=
  Filling.transport_lawful _ _ (alignedFilling_lawful D.face D.ambient D.faceFamily D.map F hF H hH)

theorem Datum.alignedSmallFilling_full {Γ : Context.{u}} (D : Datum Γ)
    (F : Filling D.faceFamily) (hF : F.Lawful)
    (H : Filling (family D.face D.ambient D.faceFamily D.map)) (hH : H.Lawful) :
    ((D.alignedSmallFilling F hF H).reindex (restrictInclusion D.face)).transport
      (eqToIso D.smallFamily_full) = F := by
  let K := alignedFilling D.face D.ambient D.faceFamily D.map F hF H
  exact (congrArg (fun i => (K.reindex (restrictInclusion D.face)).transport i)
    D.nativeIso_full).trans (alignedFilling_full D.face D.ambient D.faceFamily D.map F hF H hH)

abbrev genericFiberPathFamily {Γ : Context.{u}} {A B : Family Γ} (f : A ⟶ B) :=
  homogeneousPath (reindex (reindex B (projection B)) (projection (reindex A (projection B))))
    (Term.map (Functor.whiskerLeft (projection (reindex A (projection B))).mapElements
      (Functor.whiskerLeft (projection B).mapElements f)) (generic (reindex A (projection B))))
    (Term.reindex (generic B) (projection (reindex A (projection B))))

/-- The path component of a generic fiber at a specified domain section. -/
def genericFiberPathIso {Γ Δ : Context.{u}} {A B : Family Γ} (f : A ⟶ B)
    (σ : Δ ⟶ total B) (a : Term (reindex A (σ ≫ projection B))) :
    reindex (genericFiberPathFamily f) (pair σ a) ≅
      homogeneousPath (reindex B (σ ≫ projection B))
        (Term.map (Functor.whiskerLeft (σ ≫ projection B).mapElements f) a)
        (Term.reindex (generic B) σ) :=
  pathReindexIso
    (reindex (reindex (reindex B (projection B)) (projection (reindex A (projection B))))
      (projection (interval (total (reindex A (projection B))))))
    (Term.map (Functor.whiskerLeft (projection (reindex A (projection B))).mapElements
      (Functor.whiskerLeft (projection B).mapElements f)) (generic (reindex A (projection B))))
    (Term.reindex (generic B) (projection (reindex A (projection B)))) (pair σ a)

/-- Introduce a generic-target fiber after an arbitrary context substitution. -/
def genericFiberIntro {Γ Δ : Context.{u}} {A B : Family Γ} (f : A ⟶ B)
    (σ : Δ ⟶ total B) (a : Term (reindex A (σ ≫ projection B)))
    (p : Term (homogeneousPath (reindex B (σ ≫ projection B))
      (Term.map (Functor.whiskerLeft (σ ≫ projection B).mapElements f) a)
      (Term.reindex (generic B) σ))) :
    Term (reindex (Homotopy.fiber (Functor.whiskerLeft (projection B).mapElements f)
      (generic B)) σ) :=
  sigmaIntro (B := reindex (genericFiberPathFamily f) (liftSub (reindex A (projection B)) σ)) a
    (Term.map (genericFiberPathIso f σ a).inv p)

/-- Read the domain component after target substitution. -/
def genericFiberFst {Γ Δ : Context.{u}} {A B : Family Γ} (f : A ⟶ B)
    (σ : Δ ⟶ total B)
    (z : Term (reindex (Homotopy.fiber (Functor.whiskerLeft (projection B).mapElements f)
      (generic B)) σ)) : Term (reindex A (σ ≫ projection B)) :=
  sigmaFst (B := reindex (genericFiberPathFamily f) (liftSub (reindex A (projection B)) σ)) z

/-- Read the native path component after an arbitrary target substitution. -/
def genericFiberPath {Γ Δ : Context.{u}} {A B : Family Γ} (f : A ⟶ B)
    (σ : Δ ⟶ total B)
    (z : Term (reindex (Homotopy.fiber (Functor.whiskerLeft (projection B).mapElements f)
      (generic B)) σ)) :
    Term (homogeneousPath (reindex B (σ ≫ projection B))
      (Term.map (Functor.whiskerLeft (σ ≫ projection B).mapElements f) (genericFiberFst f σ z))
      (Term.reindex (generic B) σ)) :=
  Term.map (genericFiberPathIso f σ (genericFiberFst f σ z)).hom
    (sigmaSnd (B := reindex (genericFiberPathFamily f) (liftSub (reindex A (projection B)) σ)) z)

/-- A partial domain section lying exactly over the target gives reflexive fiber data. -/
def genericFiberPartialIntro {Γ Δ : Context.{u}} {A B : Family Γ} (f : A ⟶ B)
    (σ : Δ ⟶ total B) {φ : Subcontext Δ}
    (a : PartialSection (Cartesian.reindex A (σ ≫ projection B)) φ)
    (h : a.map (Functor.whiskerLeft (σ ≫ projection B).mapElements f) =
      PartialSection.ofTerm φ (Term.reindex (generic B) σ)) :
    PartialSection (Cartesian.reindex (Homotopy.fiber (Functor.whiskerLeft (projection B).mapElements f)
      (generic B)) σ) φ :=
  PartialSection.ofRestricted (genericFiberIntro f (restrictInclusion φ ≫ σ) a.toRestricted
    (pathLam
      (Term.reindex (Term.map (Functor.whiskerLeft (restrictInclusion φ ≫ σ ≫ projection B).mapElements f)
        a.toRestricted) (projection (interval (restrictContext φ)))) rfl
      (congrArg PartialSection.toRestricted h)))

/-- The domain component retains the prescribed partial section literally. -/
theorem genericFiberPartialIntro_fst {Γ Δ : Context.{u}} {A B : Family Γ} (f : A ⟶ B)
    (σ : Δ ⟶ total B) {φ : Subcontext Δ}
    (a : PartialSection (Cartesian.reindex A (σ ≫ projection B)) φ)
    (h : a.map (Functor.whiskerLeft (σ ≫ projection B).mapElements f) =
      PartialSection.ofTerm φ (Term.reindex (generic B) σ)) (x : Δ.Elements) (hx : φ.Holds x) :
    ((genericFiberPartialIntro f σ a h).val x hx).1 = a.val x hx := rfl

/-- Reflexive partial fiber data is constant along every generalized path coordinate. -/
theorem genericFiberPartialIntro_path {Γ Δ : Context.{u}} {A B : Family Γ} (f : A ⟶ B)
    (σ : Δ ⟶ total B) {φ : Subcontext Δ}
    (a : PartialSection (Cartesian.reindex A (σ ≫ projection B)) φ)
    (h : a.map (Functor.whiskerLeft (σ ≫ projection B).mapElements f) =
      PartialSection.ofTerm φ (Term.reindex (generic B) σ)) (x : Δ.Elements) (hx : φ.Holds x)
    {y : (total (Cartesian.reindex A (projection B))).Elements}
    (g : extendObj (Cartesian.reindex A (projection B)) (σ.mapElements.obj x) (a.val x hx) ⟶ y)
    (r : (interval (total (Cartesian.reindex A (projection B)))).obj y) :
    ((genericFiberPartialIntro f σ a h).val x hx).2.val.val g r = y.val.1.2 := by
  let τ := pair (A := Cartesian.reindex A (projection B)) (restrictInclusion φ ≫ σ) a.toRestricted
  let z := (restrictContext φ).elementsMk x.obj ⟨x.val,hx⟩
  obtain ⟨⟨y',g'⟩,hg⟩ := (substitutionArrowEquiv τ z).surjective ⟨y,g⟩
  change (⟨τ.mapElements.obj y',τ.mapElements.map g'⟩ : Σ y, τ.mapElements.obj z ⟶ y) = ⟨y,g⟩ at hg
  cases hg
  change piInverseValue τ _ (τ.mapElements.map g') r = _
  exact (piInverseValue_map τ _ g' r).trans
    (congrArg (fun s => s.val ((restrictInclusion φ).mapElements.obj y') y'.val.property) h)

theorem extendAlong_path_boundary {Γ Δ : Context.{u}} {A B : Family Γ}
    {f : A ⟶ B} (E : HomotopyEquivalence f)
    (F : Filling A) (hF : F.Lawful) (G : Filling B) (hG : G.Lawful)
    (σ : Δ ⟶ total B) {φ : Subcontext Δ}
    (a : PartialSection (Cartesian.reindex A (σ ≫ projection B)) φ)
    (h : a.map (Functor.whiskerLeft (σ ≫ projection B).mapElements f) =
      PartialSection.ofTerm φ (Term.reindex (generic B) σ)) (x : Δ.Elements) (hx : φ.Holds x)
    (r : (interval Δ).obj x) :
    (pathApp (genericFiberPath f σ
      (E.extendAlong F hF G hG σ (genericFiberPartialIntro f σ a h)))).val
        (extendObj (interval Δ) x r) = (Term.reindex (generic B) σ).val x := by
  let r' := r
  have hb := E.extendAlong_boundary F hF G hG σ (genericFiberPartialIntro f σ a h) x hx
  change ((E.extendAlong F hF G hG σ (genericFiberPartialIntro f σ a h)).val x).2.val.val
    (𝟙 _) r' = _
  exact (congrArg (fun z => (show B.obj ((σ ≫ projection B).mapElements.obj x) from
    z.2.val.val (𝟙 _) r')) hb).trans
    (genericFiberPartialIntro_path f σ a h x hx (𝟙 _) r')

theorem genericFiberPartialIntro_reindex {Γ Δ Θ : Context.{u}} {A B : Family Γ} (f : A ⟶ B)
    (σ : Δ ⟶ total B) {φ : Subcontext Δ}
    (a : PartialSection (Cartesian.reindex A (σ ≫ projection B)) φ)
    (h : a.map (Functor.whiskerLeft (σ ≫ projection B).mapElements f) =
      PartialSection.ofTerm φ (Term.reindex (generic B) σ)) (τ : Θ ⟶ Δ) :
    genericFiberPartialIntro f (τ ≫ σ) (a.reindex τ) (congrArg (fun s => s.reindex τ) h) =
      (genericFiberPartialIntro f σ a h).reindex τ := by
  apply PartialSection.ext
  intro x hx
  apply Sigma.ext
  · rfl
  apply heq_of_eq
  apply Subtype.ext
  apply PiElement.ext
  intro y g r
  exact (genericFiberPartialIntro_path f (τ ≫ σ) (a.reindex τ)
    (congrArg (fun s => s.reindex τ) h) x hx g r).trans
      (genericFiberPartialIntro_path f σ a h (τ.mapElements.obj x) hx g r).symm

theorem genericFiberPath_reindex {Γ Δ Θ : Context.{u}} {A B : Family Γ} (f : A ⟶ B)
    (σ : Δ ⟶ total B)
    (z : Term (Cartesian.reindex (Homotopy.fiber (Functor.whiskerLeft (projection B).mapElements f)
      (generic B)) σ)) (τ : Θ ⟶ Δ) :
    pathApp (genericFiberPath f (τ ≫ σ) (Term.reindex z τ)) =
      Term.reindex (pathApp (genericFiberPath f σ z)) (intervalSub τ) := rfl


namespace AmbientExtension
variable {Ξ Ω : Context.{u}} (θ : Subcontext Ξ) (B : Family Ξ)
  (U : Family (restrictContext θ)) (f : U ⟶ reindex B (restrictInclusion θ)) (p : Ω ⟶ Ξ)

abbrev pulledCompatible := compatibleFamily (θ.reindex p) (reindex B p)
  (reindex U (restrictSubstitution θ p)) (Functor.whiskerLeft (restrictSubstitution θ p).mapElements f)

def faceSection {χ : Subcontext Ω} (s : PartialSection (pulledCompatible θ B U f p) χ) :=
  compatiblePartialFace (θ.reindex p) (reindex B p) (reindex U (restrictSubstitution θ p))
    (Functor.whiskerLeft (restrictSubstitution θ p).mapElements f) s

def target (a : Term (reindex B p)) : restrictContext (θ.reindex p) ⟶ total (reindex B (restrictInclusion θ)) :=
  pair (restrictSubstitution θ p) (Term.reindex a (restrictInclusion (θ.reindex p)))

theorem faceSection_image {χ : Subcontext Ω} (s : PartialSection (pulledCompatible θ B U f p) χ)
    (a : Term (reindex B p))
    (h : s.map (compatibleUnglue (θ.reindex p) (reindex B p) (reindex U (restrictSubstitution θ p))
      (Functor.whiskerLeft (restrictSubstitution θ p).mapElements f)) = PartialSection.ofTerm χ a) :
    (faceSection θ B U f p s).map (Functor.whiskerLeft (restrictSubstitution θ p).mapElements f) =
      PartialSection.ofTerm (χ.reindex (restrictInclusion (θ.reindex p)))
        (Term.reindex a (restrictInclusion (θ.reindex p))) :=
  (compatiblePartialFace_image (θ.reindex p) (reindex B p) (reindex U (restrictSubstitution θ p))
    (Functor.whiskerLeft (restrictSubstitution θ p).mapElements f) s).trans
    (congrArg (fun t => t.reindex (restrictInclusion (θ.reindex p))) h)

noncomputable def fiber (E : HomotopyEquivalence f) (F : Filling U) (hF : F.Lawful)
    (G : Filling B) (hG : G.Lawful) {χ : Subcontext Ω}
    (s : PartialSection (pulledCompatible θ B U f p) χ) (a : Term (reindex B p))
    (h : s.map (compatibleUnglue (θ.reindex p) (reindex B p) (reindex U (restrictSubstitution θ p))
      (Functor.whiskerLeft (restrictSubstitution θ p).mapElements f)) = PartialSection.ofTerm χ a) :=
  E.extendAlong F hF (G.reindex (restrictInclusion θ)) (hG.reindex _) (target θ B p a)
    (genericFiberPartialIntro f (target θ B p a) (faceSection θ B U f p s)
      (faceSection_image θ B U f p s a h))

noncomputable def extendedFace (E : HomotopyEquivalence f) (F : Filling U) (hF : F.Lawful)
    (G : Filling B) (hG : G.Lawful) {χ : Subcontext Ω}
    (s : PartialSection (pulledCompatible θ B U f p) χ) (a : Term (reindex B p))
    (h : s.map (compatibleUnglue (θ.reindex p) (reindex B p) (reindex U (restrictSubstitution θ p))
      (Functor.whiskerLeft (restrictSubstitution θ p).mapElements f)) = PartialSection.ofTerm χ a) :
    Term (reindex U (restrictSubstitution θ p)) :=
  genericFiberFst f (target θ B p a) (fiber θ B U f p E F hF G hG s a h)

noncomputable def extensionPath (E : HomotopyEquivalence f) (F : Filling U) (hF : F.Lawful)
    (G : Filling B) (hG : G.Lawful) {χ : Subcontext Ω}
    (s : PartialSection (pulledCompatible θ B U f p) χ) (a : Term (reindex B p))
    (h : s.map (compatibleUnglue (θ.reindex p) (reindex B p) (reindex U (restrictSubstitution θ p))
      (Functor.whiskerLeft (restrictSubstitution θ p).mapElements f)) = PartialSection.ofTerm χ a) :=
  genericFiberPath f (target θ B p a) (fiber θ B U f p E F hF G hG s a h)

theorem extendedFace_boundary (E : HomotopyEquivalence f) (F : Filling U) (hF : F.Lawful)
    (G : Filling B) (hG : G.Lawful) {χ : Subcontext Ω}
    (s : PartialSection (pulledCompatible θ B U f p) χ) (a : Term (reindex B p))
    (h : s.map (compatibleUnglue (θ.reindex p) (reindex B p) (reindex U (restrictSubstitution θ p))
      (Functor.whiskerLeft (restrictSubstitution θ p).mapElements f)) = PartialSection.ofTerm χ a)
    (x : (restrictContext (θ.reindex p)).Elements) (hx : (χ.reindex (restrictInclusion (θ.reindex p))).Holds x) :
    (extendedFace θ B U f p E F hF G hG s a h).val x = (faceSection θ B U f p s).val x hx :=
  congrArg Sigma.fst (E.extendAlong_boundary F hF (G.reindex (restrictInclusion θ)) (hG.reindex _)
    (target θ B p a) (genericFiberPartialIntro f (target θ B p a) (faceSection θ B U f p s)
      (faceSection_image θ B U f p s a h)) x hx)

def substitutePartial {Λ : Context.{u}} (τ : Λ ⟶ Ω) {χ : Subcontext Ω}
    (s : PartialSection (pulledCompatible θ B U f p) χ) :
    PartialSection (pulledCompatible θ B U f (τ ≫ p)) (χ.reindex τ) :=
  (s.reindex τ).map (compatibleReindexMap (θ.reindex p) (reindex B p)
    (reindex U (restrictSubstitution θ p)) (Functor.whiskerLeft (restrictSubstitution θ p).mapElements f) τ)

theorem faceSection_reindex {Λ : Context.{u}} (τ : Λ ⟶ Ω) {χ : Subcontext Ω}
    (s : PartialSection (pulledCompatible θ B U f p) χ) :
    faceSection θ B U f (τ ≫ p) (substitutePartial θ B U f p τ s) =
      (faceSection θ B U f p s).reindex (restrictSubstitution (θ.reindex p) τ) := rfl

theorem fiber_reindex (E : HomotopyEquivalence f) (F : Filling U) (hF : F.Lawful)
    (G : Filling B) (hG : G.Lawful) {χ : Subcontext Ω}
    (s : PartialSection (pulledCompatible θ B U f p) χ) (a : Term (reindex B p))
    (h : s.map (compatibleUnglue (θ.reindex p) (reindex B p) (reindex U (restrictSubstitution θ p))
      (Functor.whiskerLeft (restrictSubstitution θ p).mapElements f)) = PartialSection.ofTerm χ a)
    {Λ : Context.{u}} (τ : Λ ⟶ Ω) :
    fiber θ B U f (τ ≫ p) E F hF G hG (substitutePartial θ B U f p τ s) (Term.reindex a τ)
      (congrArg (fun t => t.reindex τ) h) =
    Term.reindex (fiber θ B U f p E F hF G hG s a h) (restrictSubstitution (θ.reindex p) τ) := by
  exact (congrArg (E.extendAlong F hF (G.reindex (restrictInclusion θ)) (hG.reindex _)
    (restrictSubstitution (θ.reindex p) τ ≫ target θ B p a))
      (genericFiberPartialIntro_reindex f (target θ B p a) (faceSection θ B U f p s)
        (faceSection_image θ B U f p s a h) (restrictSubstitution (θ.reindex p) τ))).trans
    (E.extendAlong_reindex F hF (G.reindex (restrictInclusion θ)) (hG.reindex _)
      (target θ B p a) (genericFiberPartialIntro f (target θ B p a) (faceSection θ B U f p s)
        (faceSection_image θ B U f p s a h)) (restrictSubstitution (θ.reindex p) τ))

section Assembly
variable (E : HomotopyEquivalence f) (F : Filling U) (hF : F.Lawful)
  (G : Filling B) (hG : G.Lawful) {χ : Subcontext Ω}
  (s : PartialSection (pulledCompatible θ B U f p) χ) (a : Term (reindex B p))
  (h : s.map (compatibleUnglue (θ.reindex p) (reindex B p) (reindex U (restrictSubstitution θ p))
    (Functor.whiskerLeft (restrictSubstitution θ p).mapElements f)) = PartialSection.ofTerm χ a)

theorem correction_compatible :
    (restrictedPathTube (θ.reindex p) a
      (Term.map (Functor.whiskerLeft (restrictSubstitution θ p).mapElements f)
        (extendedFace θ B U f p E F hF G hG s a h))
      (extensionPath θ B U f p E F hF G hG s a h)).Compatible
        (PartialSection.ofTerm (χ.reindex (projection (interval Ω)))
          (Term.reindex a (projection (interval Ω)))) := by
  intro x ht hc
  rcases x with @⟨I,⟨γ,r⟩⟩
  exact extendAlong_path_boundary E F hF (G.reindex (restrictInclusion θ)) (hG.reindex _)
    (target θ B p a) (faceSection θ B U f p s) (faceSection_image θ B U f p s a h)
    ((restrictContext (θ.reindex p)).elementsMk I ⟨γ,ht⟩) hc r

noncomputable def corrected : Term (reindex B p) :=
  correctAmbient (G.reindex p) (θ.reindex p) χ a
    (Term.map (Functor.whiskerLeft (restrictSubstitution θ p).mapElements f)
      (extendedFace θ B U f p E F hF G hG s a h))
    (extensionPath θ B U f p E F hF G hG s a h)
    (correction_compatible θ B U f p E F hF G hG s a h)

theorem corrected_face :
    Term.map (Functor.whiskerLeft (restrictSubstitution θ p).mapElements f)
      (extendedFace θ B U f p E F hF G hG s a h) =
    Term.reindex (corrected θ B U f p E F hF G hG s a h) (restrictInclusion (θ.reindex p)) := by
  apply Term.ext
  intro x
  exact (correctAmbient_face (G.reindex p) (hG.reindex p) (θ.reindex p) χ a _ _
    (correction_compatible θ B U f p E F hF G hG s a h)
      ((restrictInclusion (θ.reindex p)).mapElements.obj x) x.val.property).symm

noncomputable def extendSection : Term (pulledCompatible θ B U f p) :=
  compatibleIntro (θ.reindex p) (reindex B p) (reindex U (restrictSubstitution θ p))
    (Functor.whiskerLeft (restrictSubstitution θ p).mapElements f)
    (extendedFace θ B U f p E F hF G hG s a h)
    (corrected θ B U f p E F hF G hG s a h)
    (corrected_face θ B U f p E F hF G hG s a h)

theorem extendSection_boundary (x : Ω.Elements) (hx : χ.Holds x) :
    (extendSection θ B U f p E F hF G hG s a h).val x = s.val x hx := by
  apply CompatibleElement.ext
  · exact (correctAmbient_fixed (G.reindex p) (hG.reindex p) (θ.reindex p) χ a _ _
      (correction_compatible θ B U f p E F hF G hG s a h) x hx).trans
        (congrArg (fun t => t.val x hx) h).symm
  · intro y k hy
    have he := extendedFace_boundary θ B U f p E F hF G hG s a h
      (faceObj (θ.reindex p) y hy) (χ.natural k hx)
    have hs := congrArg (fun z => z.face (𝟙 _) hy) (s.natural k hx)
    change (s.val x hx).face (k ≫ 𝟙 _) hy = (s.val y _).face (𝟙 _) hy at hs
    exact he.trans (by
      change (s.val y _).face (𝟙 _) hy = (s.val x hx).face k hy
      simpa only [Category.comp_id] using hs.symm)

theorem extendedFace_reindex {Λ : Context.{u}} (τ : Λ ⟶ Ω) :
    extendedFace θ B U f (τ ≫ p) E F hF G hG (substitutePartial θ B U f p τ s) (Term.reindex a τ)
      (congrArg (fun t => t.reindex τ) h) =
    Term.reindex (extendedFace θ B U f p E F hF G hG s a h) (restrictSubstitution (θ.reindex p) τ) :=
  congrArg (genericFiberFst f (target θ B (τ ≫ p) (Term.reindex a τ)))
    (fiber_reindex θ B U f p E F hF G hG s a h τ)

theorem correctionTube_reindex {Λ : Context.{u}} (τ : Λ ⟶ Ω) :
    restrictedPathTube (θ.reindex (τ ≫ p)) (Term.reindex a τ)
      (Term.map (Functor.whiskerLeft (restrictSubstitution θ (τ ≫ p)).mapElements f)
        (extendedFace θ B U f (τ ≫ p) E F hF G hG (substitutePartial θ B U f p τ s) (Term.reindex a τ)
          (congrArg (fun t => t.reindex τ) h)))
      (extensionPath θ B U f (τ ≫ p) E F hF G hG (substitutePartial θ B U f p τ s) (Term.reindex a τ)
        (congrArg (fun t => t.reindex τ) h)) =
    (restrictedPathTube (θ.reindex p) a
      (Term.map (Functor.whiskerLeft (restrictSubstitution θ p).mapElements f)
        (extendedFace θ B U f p E F hF G hG s a h))
      (extensionPath θ B U f p E F hF G hG s a h)).reindex (intervalSub τ) := by
  have hp := (congrArg (fun z => pathApp (genericFiberPath f (target θ B (τ ≫ p) (Term.reindex a τ)) z))
      (fiber_reindex θ B U f p E F hF G hG s a h τ)).trans
        (genericFiberPath_reindex f (target θ B p a) (fiber θ B U f p E F hF G hG s a h)
          (restrictSubstitution (θ.reindex p) τ))
  apply PartialSection.ext
  intro x hx
  exact congrArg (fun t => t.val
    ((total (interval (restrictContext (θ.reindex (τ ≫ p))))).elementsMk x.obj
      ⟨⟨x.val.1,hx⟩,x.val.2⟩)) hp

noncomputable def correctionInput :
    OpenBox (reindex (reindex B p) (projection (interval Ω))) ((θ.reindex p).join χ) (endpoint Ω true) :=
  correctionBox (θ.reindex p) χ a
    (Term.map (Functor.whiskerLeft (restrictSubstitution θ p).mapElements f)
      (extendedFace θ B U f p E F hF G hG s a h))
    (extensionPath θ B U f p E F hF G hG s a h)
    (correction_compatible θ B U f p E F hF G hG s a h)

theorem correctionInput_reindex {Λ : Context.{u}} (τ : Λ ⟶ Ω) :
    correctionInput θ B U f (τ ≫ p) E F hF G hG (substitutePartial θ B U f p τ s) (Term.reindex a τ)
      (congrArg (fun t => t.reindex τ) h) =
    (correctionInput θ B U f p E F hF G hG s a h).reindex τ := by
  apply OpenBox.ext
  · apply PartialSection.ext
    intro x hx
    have ht := correctionTube_reindex θ B U f p E F hF G hG s a h τ
    let t₀ := restrictedPathTube (θ.reindex p) a
      (Term.map (Functor.whiskerLeft (restrictSubstitution θ p).mapElements f)
        (extendedFace θ B U f p E F hF G hG s a h))
      (extensionPath θ B U f p E F hF G hG s a h)
    let t₁ := restrictedPathTube (θ.reindex (τ ≫ p)) (Term.reindex a τ)
      (Term.map (Functor.whiskerLeft (restrictSubstitution θ (τ ≫ p)).mapElements f)
        (extendedFace θ B U f (τ ≫ p) E F hF G hG (substitutePartial θ B U f p τ s) (Term.reindex a τ)
          (congrArg (fun t => t.reindex τ) h)))
      (extensionPath θ B U f (τ ≫ p) E F hF G hG (substitutePartial θ B U f p τ s) (Term.reindex a τ)
        (congrArg (fun t => t.reindex τ) h))
    let c₀ := PartialSection.ofTerm (χ.reindex (projection (interval Ω))) (Term.reindex a (projection (interval Ω)))
    let c₁ := PartialSection.ofTerm ((χ.reindex τ).reindex (projection (interval Λ)))
      (Term.reindex (Term.reindex a τ) (projection (interval Λ)))
    change glueValue t₁ c₁ x hx = glueValue t₀ c₀ ((intervalSub τ).mapElements.obj x) hx
    by_cases hp : ((θ.reindex (τ ≫ p)).reindex (projection (interval Λ))).Holds x
    · exact (glueValue_left t₁ c₁ x hx hp).trans
        ((congrArg (fun t => t.val x hp) ht).trans
          (glueValue_left t₀ c₀ ((intervalSub τ).mapElements.obj x) hx hp).symm)
    · have hp₀ : ¬ ((θ.reindex p).reindex (projection (interval Ω))).Holds
          ((intervalSub τ).mapElements.obj x) := hp
      simp only [glueValue, dite_eq_right hp, dite_eq_right hp₀]
      rfl
  · rfl

theorem corrected_reindex {Λ : Context.{u}} (τ : Λ ⟶ Ω) :
    corrected θ B U f (τ ≫ p) E F hF G hG (substitutePartial θ B U f p τ s) (Term.reindex a τ)
      (congrArg (fun t => t.reindex τ) h) =
    Term.reindex (corrected θ B U f p E F hF G hG s a h) τ :=
  (congrArg ((G.reindex (τ ≫ p)).backwardComp (((θ.reindex p).join χ).reindex τ))
    (correctionInput_reindex θ B U f p E F hF G hG s a h τ)).trans
      (Filling.backwardComp_reindex (hG.reindex p) ((θ.reindex p).join χ)
        (correctionInput θ B U f p E F hF G hG s a h) τ)

theorem extendSection_reindex {Λ : Context.{u}} (τ : Λ ⟶ Ω) :
    extendSection θ B U f (τ ≫ p) E F hF G hG (substitutePartial θ B U f p τ s) (Term.reindex a τ)
      (congrArg (fun t => t.reindex τ) h) =
    Term.map (compatibleReindexMap (θ.reindex p) (reindex B p) (reindex U (restrictSubstitution θ p))
      (Functor.whiskerLeft (restrictSubstitution θ p).mapElements f) τ)
      (Term.reindex (extendSection θ B U f p E F hF G hG s a h) τ) := by
  apply Term.ext
  intro x
  apply CompatibleElement.ext
  · exact congrArg (fun t => t.val x) (corrected_reindex θ B U f p E F hF G hG s a h τ)
  · intro y k hy
    exact congrArg (fun t => t.val (faceObj (θ.reindex (τ ≫ p)) y hy))
      (extendedFace_reindex θ B U f p E F hF G hG s a h τ)

theorem extendSection_congr (s' : PartialSection (pulledCompatible θ B U f p) χ)
    (a' : Term (reindex B p))
    (h' : s'.map (compatibleUnglue (θ.reindex p) (reindex B p) (reindex U (restrictSubstitution θ p))
      (Functor.whiskerLeft (restrictSubstitution θ p).mapElements f)) = PartialSection.ofTerm χ a')
    (hs : s = s') (ha : a = a') :
    extendSection θ B U f p E F hF G hG s a h = extendSection θ B U f p E F hF G hG s' a' h' := by
  cases hs
  cases ha
  rfl


end Assembly
end AmbientExtension
abbrev sourceFace {Θ : Context.{u}} (r : Term (interval Θ)) : Subcontext (total (interval Θ)) :=
  Subcontext.intervalEq (generic (interval Θ)) (Term.reindex r (projection (interval Θ)))

theorem sourceFace_inclusion {Θ : Context.{u}} (r : Term (interval Θ)) :
    (restrictInclusion (sourceFace r) ≫ projection (interval Θ)) ≫ graph r =
      restrictInclusion (sourceFace r) := by
  ext I z
  change (⟨z.val.1,r.val (Θ.elementsMk I z.val.1)⟩ : (total (interval Θ)).obj I) = z.val
  exact congrArg (fun t => (⟨z.val.1,t⟩ : (total (interval Θ)).obj I)) z.property.symm

def sourceSection {Θ : Context.{u}} (B : Family (total (interval Θ))) (r : Term (interval Θ))
    (a : Term (reindex B (graph r))) : PartialSection B (sourceFace r) :=
  PartialSection.ofRestricted (Term.convert (congrArg (fun σ => reindex B σ) (sourceFace_inclusion r))
    (Term.reindex a (restrictInclusion (sourceFace r) ≫ projection (interval Θ))))

theorem sourceSection_val {Θ : Context.{u}} (B : Family (total (interval Θ))) (r : Term (interval Θ))
    (a : Term (reindex B (graph r))) (x : (total (interval Θ)).Elements) (h : (sourceFace r).Holds x) :
    HEq ((sourceSection B r a).val x h) (a.val ((projection (interval Θ)).mapElements.obj x)) :=
  Term.convert_val_heq _ _ ((restrictContext (sourceFace r)).elementsMk x.obj ⟨x.val,h⟩)

theorem sourceSection_reindex {Θ Λ : Context.{u}} (B : Family (total (interval Θ))) (r : Term (interval Θ))
    (a : Term (reindex B (graph r))) (σ : Λ ⟶ Θ) :
    (sourceSection B r a).reindex (intervalSub σ) =
      sourceSection (reindex B (intervalSub σ)) (Term.reindex r σ) (Term.reindex a σ) := by
  apply PartialSection.ext
  intro x h
  exact eq_of_heq ((sourceSection_val B r a ((intervalSub σ).mapElements.obj x) h).trans
    (sourceSection_val (reindex B (intervalSub σ)) (Term.reindex r σ) (Term.reindex a σ) x h).symm)

theorem sourceSection_map {Θ : Context.{u}} {B C : Family (total (interval Θ))}
    (η : B ⟶ C) (r : Term (interval Θ)) (a : Term (reindex B (graph r))) :
    (sourceSection B r a).map η = sourceSection C r (Term.map (Functor.whiskerLeft (graph r).mapElements η) a) := by
  apply PartialSection.ext
  intro x hx
  rcases x with @⟨I,⟨γ,t⟩⟩
  change t = r.val (Θ.elementsMk I γ) at hx
  subst t
  exact (congrArg (η.app _) (eq_of_heq (sourceSection_val B r a ((graph r).mapElements.obj (Θ.elementsMk I γ)) rfl))).trans
    (eq_of_heq (sourceSection_val C r (Term.map (Functor.whiskerLeft (graph r).mapElements η) a) ((graph r).mapElements.obj (Θ.elementsMk I γ)) rfl)).symm

abbrev boxFace {Θ : Context.{u}} (ψ : Subcontext Θ) (r : Term (interval Θ)) :=
  (ψ.reindex (projection (interval Θ))).join (sourceFace r)

theorem source_compatible {Θ : Context.{u}} {B : Family (total (interval Θ))}
    {ψ : Subcontext Θ} {r : Term (interval Θ)} (b : OpenBox B ψ r) : b.tube.Compatible (sourceSection B r b.base) := by
  intro x ht hs
  rcases x with @⟨I,⟨γ,t⟩⟩
  change t = r.val (Θ.elementsMk I γ) at hs
  subst t
  exact (b.boundary (Θ.elementsMk I γ) ht).trans (eq_of_heq (sourceSection_val B r b.base ((graph r).mapElements.obj (Θ.elementsMk I γ)) rfl)).symm

noncomputable def boxPartial {Θ : Context.{u}} {B : Family (total (interval Θ))}
    {ψ : Subcontext Θ} {r : Term (interval Θ)} (b : OpenBox B ψ r) : PartialSection B (boxFace ψ r) :=
  b.tube.glue (sourceSection B r b.base) (source_compatible b)

theorem boxPartial_image_filled {Θ : Context.{u}} {B C : Family (total (interval Θ))}
    (η : B ⟶ C) {ψ : Subcontext Θ} {r : Term (interval Θ)} (b : OpenBox B ψ r) (a : Term C)
    (ha : (b.map η).Fills a) :
    (boxPartial b).map η = PartialSection.ofTerm (boxFace ψ r) a := by
  apply PartialSection.ext
  intro x hx
  rcases hx with ht | hc
  · exact (congrArg (η.app x)
      (glueValue_left b.tube (sourceSection B r b.base) x (Or.inl ht) ht)).trans (ha.2 x ht).symm
  · rcases x with @⟨I,⟨γ,z⟩⟩
    change z = r.val (Θ.elementsMk I γ) at hc
    subst z
    have he := eq_of_heq (sourceSection_val B r b.base ((graph r).mapElements.obj (Θ.elementsMk I γ)) rfl)
    exact (congrArg (η.app _) ((glueValue_right b.tube (sourceSection B r b.base)
      (source_compatible b) ((graph r).mapElements.obj (Θ.elementsMk I γ)) (Or.inr rfl) rfl).trans he)).trans
        (congrArg (fun t => t.val (Θ.elementsMk I γ)) ha.1).symm

theorem fills_of_boxPartial {Θ : Context.{u}} {B : Family (total (interval Θ))}
    {ψ : Subcontext Θ} {r : Term (interval Θ)} (b : OpenBox B ψ r) (a : Term B)
    (h : ∀ x hx, a.val x = (boxPartial b).val x hx) : b.Fills a := by
  constructor
  · apply Term.ext
    intro x
    let y := (graph r).mapElements.obj x
    have hz : (sourceFace r).Holds y := rfl
    have hu : (boxFace ψ r).Holds y := Or.inr hz
    exact (h y hu).trans ((glueValue_right b.tube (sourceSection B r b.base)
      ((source_compatible b)) y hu hz).trans (eq_of_heq (sourceSection_val B r b.base y hz)))
  · intro x hx
    have hu : (boxFace ψ r).Holds x := Or.inl hx
    exact (h x hu).trans (glueValue_left b.tube (sourceSection B r b.base) x hu hx)

theorem partialGlue_map {Θ : Context.{u}} {B C : Family Θ} (η : B ⟶ C)
    {ψ χ : Subcontext Θ} (b : PartialSection B ψ) (c : PartialSection B χ)
    (h : b.Compatible c) :
    (b.glue c h).map η = (b.map η).glue (c.map η) (fun x hp hq => congrArg (η.app x) (h x hp hq)) := by
  apply PartialSection.ext
  intro x hx
  rcases hx with hp | hq
  · exact (congrArg (η.app x) (glueValue_left b c x (Or.inl hp) hp)).trans
      (glueValue_left (b.map η) (c.map η) x (Or.inl hp) hp).symm
  · exact (congrArg (η.app x) (glueValue_right b c h x (Or.inr hq) hq)).trans
      (glueValue_right (b.map η) (c.map η) (fun y hp hq => congrArg (η.app y) (h y hp hq)) x (Or.inr hq) hq).symm

theorem boxPartial_map {Θ : Context.{u}} {B C : Family (total (interval Θ))}
    (η : B ⟶ C) {ψ : Subcontext Θ} {r : Term (interval Θ)} (b : OpenBox B ψ r) :
    boxPartial (b.map η) = (boxPartial b).map η :=
  (PartialSection.glue_congr rfl (sourceSection_map η r b.base).symm _ _).trans
    (partialGlue_map η b.tube (sourceSection B r b.base) (source_compatible b)).symm

theorem boxPartial_reindex {Θ Λ : Context.{u}} {B : Family (total (interval Θ))}
    {ψ : Subcontext Θ} {r : Term (interval Θ)} (b : OpenBox B ψ r) (σ : Λ ⟶ Θ) :
    boxPartial (b.reindex σ) = (boxPartial b).reindex (intervalSub σ) :=
  ((PartialSection.glue_reindex b.tube (sourceSection B r b.base) (source_compatible b)
    (intervalSub σ)).trans
      (PartialSection.glue_congr rfl (sourceSection_reindex B r b.base σ) _ _)).symm

noncomputable def inputIso : reindex (family φ A T e) p ≅
    AmbientExtension.pulledCompatible φ A T e p :=
  (Functor.isoWhiskerLeft p.mapElements (familyIso φ A T e)) ≪≫ compatibleReindexIso φ A T e p

noncomputable def preliminaryCompatibleFill (E : HomotopyEquivalence e)
    (F : Filling T) (hF : F.Lawful) (G : Filling A) (hG : G.Lawful)
    (ψ : Subcontext Δ) (r : Term (interval Δ)) (b : OpenBox (reindex (family φ A T e) p) ψ r) :=
  let b' := b.map (inputIso φ A T e p).hom
  let m := compatibleUnglue (φ.reindex p) (reindex A p) (reindex T (restrictSubstitution φ p))
    (Functor.whiskerLeft (restrictSubstitution φ p).mapElements e)
  AmbientExtension.extendSection φ A T e p E F hF G hG (boxPartial b') (G.fill p ψ r (b'.map m))
    (boxPartial_image_filled m b' _ (hG.fills p ψ r (b'.map m)))

theorem preliminaryCompatibleFill_fills (E : HomotopyEquivalence e)
    (F : Filling T) (hF : F.Lawful) (G : Filling A) (hG : G.Lawful)
    (ψ : Subcontext Δ) (r : Term (interval Δ)) (b : OpenBox (reindex (family φ A T e) p) ψ r) :
    (b.map (inputIso φ A T e p).hom).Fills (preliminaryCompatibleFill φ A T e p E F hF G hG ψ r b) := by
  apply fills_of_boxPartial
  intro x hx
  exact AmbientExtension.extendSection_boundary φ A T e p E F hF G hG _ _ _ x hx

/-- The preliminary whole filler is constructed from the two supplied lawful fillers and equivalence. -/
noncomputable def preliminaryFill (E : HomotopyEquivalence e)
    (F : Filling T) (hF : F.Lawful) (G : Filling A) (hG : G.Lawful)
    (ψ : Subcontext Δ) (r : Term (interval Δ)) (b : OpenBox (reindex (family φ A T e) p) ψ r) :
    Term (reindex (family φ A T e) p) :=
  Term.map (inputIso φ A T e p).inv (preliminaryCompatibleFill φ A T e p E F hF G hG ψ r b)

theorem preliminaryFill_fills (E : HomotopyEquivalence e)
    (F : Filling T) (hF : F.Lawful) (G : Filling A) (hG : G.Lawful)
    (ψ : Subcontext Δ) (r : Term (interval Δ)) (b : OpenBox (reindex (family φ A T e) p) ψ r) :
    b.Fills (preliminaryFill φ A T e p E F hF G hG ψ r b) := by
  let q := inputIso φ A T e p
  have h := preliminaryCompatibleFill_fills φ A T e p E F hF G hG ψ r b
  constructor
  · apply Term.ext
    intro x
    exact (congrArg (q.inv.app ((graph r).mapElements.obj x))
      (congrArg (fun t => t.val x) h.1)).trans
        (congrArg (fun f => f.app ((graph r).mapElements.obj x) (b.base.val x)) q.hom_inv_id)
  · intro x hx
    exact (congrArg (q.inv.app x) (h.2 x hx)).trans
      (congrArg (fun f => f.app x (b.tube.val x hx)) q.hom_inv_id)

def inputComparison {Θ : Context.{u}} (σ : Θ ⟶ Δ) :=
  compatibleReindexMap (φ.reindex p) (reindex A p) (reindex T (restrictSubstitution φ p))
    (Functor.whiskerLeft (restrictSubstitution φ p).mapElements e) (intervalSub σ)

theorem inputIso_natural {Θ : Context.{u}} (σ : Θ ⟶ Δ) :
    (inputIso φ A T e (intervalSub σ ≫ p)).hom =
      Functor.whiskerLeft (intervalSub σ).mapElements (inputIso φ A T e p).hom ≫
        inputComparison φ A T e p σ := rfl

theorem inputBox_natural (ψ : Subcontext Δ) (r : Term (interval Δ)) (b : OpenBox (reindex (family φ A T e) p) ψ r)
    {Θ : Context.{u}} (σ : Θ ⟶ Δ) :
    (b.reindex σ).map (inputIso φ A T e (intervalSub σ ≫ p)).hom =
      ((b.map (inputIso φ A T e p).hom).reindex σ).map (inputComparison φ A T e p σ) := rfl

theorem inputPartial_natural (ψ : Subcontext Δ) (r : Term (interval Δ)) (b : OpenBox (reindex (family φ A T e) p) ψ r)
    {Θ : Context.{u}} (σ : Θ ⟶ Δ) :
    boxPartial ((b.reindex σ).map (inputIso φ A T e (intervalSub σ ≫ p)).hom) =
      AmbientExtension.substitutePartial φ A T e p (intervalSub σ)
        (boxPartial (b.map (inputIso φ A T e p).hom)) :=
  (boxPartial_map (inputComparison φ A T e p σ) ((b.map (inputIso φ A T e p).hom).reindex σ)).trans
    (congrArg (PartialSection.map (inputComparison φ A T e p σ))
      (boxPartial_reindex (b.map (inputIso φ A T e p).hom) σ))

theorem preliminaryCompatibleFill_reindex (E : HomotopyEquivalence e)
    (F : Filling T) (hF : F.Lawful) (G : Filling A) (hG : G.Lawful)
    (ψ : Subcontext Δ) (r : Term (interval Δ)) (b : OpenBox (reindex (family φ A T e) p) ψ r)
    {Θ : Context.{u}} (σ : Θ ⟶ Δ) :
    preliminaryCompatibleFill φ A T e (intervalSub σ ≫ p) E F hF G hG (ψ.reindex σ) (Term.reindex r σ) (b.reindex σ) =
      Term.map (inputComparison φ A T e p σ)
        (Term.reindex (preliminaryCompatibleFill φ A T e p E F hF G hG ψ r b) (intervalSub σ)) := by
  let τ := intervalSub σ
  let b₀ := b.map (inputIso φ A T e p).hom
  let b₁ := (b.reindex σ).map (inputIso φ A T e (τ ≫ p)).hom
  let m₀ := compatibleUnglue (φ.reindex p) (reindex A p) (reindex T (restrictSubstitution φ p))
    (Functor.whiskerLeft (restrictSubstitution φ p).mapElements e)
  let m₁ := compatibleUnglue (φ.reindex (τ ≫ p)) (reindex A (τ ≫ p))
    (reindex T (restrictSubstitution φ (τ ≫ p)))
    (Functor.whiskerLeft (restrictSubstitution φ (τ ≫ p)).mapElements e)
  let a₀ := G.fill p ψ r (b₀.map m₀)
  let a₁ := G.fill (τ ≫ p) (ψ.reindex σ) (Term.reindex r σ) (b₁.map m₁)
  have h₀ := boxPartial_image_filled m₀ b₀ a₀ (hG.fills p ψ r (b₀.map m₀))
  have h₁ := boxPartial_image_filled m₁ b₁ a₁ (hG.fills (τ ≫ p) (ψ.reindex σ) (Term.reindex r σ) (b₁.map m₁))
  have hs : boxPartial b₁ = AmbientExtension.substitutePartial φ A T e p τ (boxPartial b₀) :=
    inputPartial_natural φ A T e p ψ r b σ
  have ha : a₁ = Term.reindex a₀ τ := hG.uniform p ψ r (b₀.map m₀) σ
  exact (AmbientExtension.extendSection_congr φ A T e (τ ≫ p) E F hF G hG
    (boxPartial b₁) a₁ h₁ (AmbientExtension.substitutePartial φ A T e p τ (boxPartial b₀))
      (Term.reindex a₀ τ) (congrArg (fun s => s.reindex τ) h₀) hs ha).trans
    (AmbientExtension.extendSection_reindex φ A T e p E F hF G hG (boxPartial b₀) a₀ h₀ τ)

theorem inputIso_inverse_natural {Θ : Context.{u}} (σ : Θ ⟶ Δ) :
    inputComparison φ A T e p σ ≫ (inputIso φ A T e (intervalSub σ ≫ p)).inv =
      Functor.whiskerLeft (intervalSub σ).mapElements (inputIso φ A T e p).inv :=
  (Iso.comp_inv_eq (inputIso φ A T e (intervalSub σ ≫ p))).mpr
    ((Iso.eq_inv_comp (Functor.isoWhiskerLeft (intervalSub σ).mapElements
      (inputIso φ A T e p))).mpr (inputIso_natural φ A T e p σ).symm)

theorem preliminaryFill_reindex (E : HomotopyEquivalence e)
    (F : Filling T) (hF : F.Lawful) (G : Filling A) (hG : G.Lawful)
    (ψ : Subcontext Δ) (r : Term (interval Δ)) (b : OpenBox (reindex (family φ A T e) p) ψ r)
    {Θ : Context.{u}} (σ : Θ ⟶ Δ) :
    preliminaryFill φ A T e (intervalSub σ ≫ p) E F hF G hG (ψ.reindex σ) (Term.reindex r σ) (b.reindex σ) =
      Term.reindex (preliminaryFill φ A T e p E F hF G hG ψ r b) (intervalSub σ) :=
  (congrArg (Term.map (inputIso φ A T e (intervalSub σ ≫ p)).inv)
    (preliminaryCompatibleFill_reindex φ A T e p E F hF G hG ψ r b σ)).trans
      (congrArg (fun η => Term.map η
        (Term.reindex (preliminaryCompatibleFill φ A T e p E F hF G hG ψ r b) (intervalSub σ)))
        (inputIso_inverse_natural φ A T e p σ))

/-- A lawful preliminary Glue filling, before repairing its selected full-face structure. -/
noncomputable def preliminaryFilling (E : HomotopyEquivalence e)
    (F : Filling T) (hF : F.Lawful) (G : Filling A) (hG : G.Lawful) : Filling (family φ A T e) where
  fill q ψ r b := preliminaryFill φ A T e q E F hF G hG ψ r b

theorem preliminaryFilling_lawful (E : HomotopyEquivalence e)
    (F : Filling T) (hF : F.Lawful) (G : Filling A) (hG : G.Lawful) :
    (preliminaryFilling φ A T e E F hF G hG).Lawful where
  fills q ψ r b := preliminaryFill_fills φ A T e q E F hF G hG ψ r b
  uniform q ψ r b σ := preliminaryFill_reindex φ A T e q E F hF G hG ψ r b σ

/-- Glue filling constructed from the actual equivalence and selected input operations. -/
noncomputable def filling (E : HomotopyEquivalence e)
    (F : Filling T) (hF : F.Lawful) (G : Filling A) (hG : G.Lawful) : Filling (family φ A T e) :=
  alignedFilling φ A T e F hF (preliminaryFilling φ A T e E F hF G hG)

theorem filling_lawful (E : HomotopyEquivalence e)
    (F : Filling T) (hF : F.Lawful) (G : Filling A) (hG : G.Lawful) :
    (filling φ A T e E F hF G hG).Lawful :=
  alignedFilling_lawful φ A T e F hF _ (preliminaryFilling_lawful φ A T e E F hF G hG)

theorem filling_full (E : HomotopyEquivalence e)
    (F : Filling T) (hF : F.Lawful) (G : Filling A) (hG : G.Lawful) :
    ((filling φ A T e E F hF G hG).reindex (restrictInclusion φ)).transport
      (eqToIso (family_full φ A T e)) = F :=
  alignedFilling_full φ A T e F hF _ (preliminaryFilling_lawful φ A T e E F hF G hG)

noncomputable def Datum.smallFilling {Γ : Context.{u}} (D : Datum Γ)
    (E : HomotopyEquivalence D.map) (F : Filling D.faceFamily) (hF : F.Lawful)
    (G : Filling D.ambient) (hG : G.Lawful) : Filling D.smallFamily :=
  D.alignedSmallFilling F hF (preliminaryFilling D.face D.ambient D.faceFamily D.map E F hF G hG)

theorem Datum.smallFilling_lawful {Γ : Context.{u}} (D : Datum Γ)
    (E : HomotopyEquivalence D.map) (F : Filling D.faceFamily) (hF : F.Lawful)
    (G : Filling D.ambient) (hG : G.Lawful) : (D.smallFilling E F hF G hG).Lawful :=
  D.alignedSmallFilling_lawful F hF _ (preliminaryFilling_lawful D.face D.ambient D.faceFamily D.map E F hF G hG)

theorem Datum.smallFilling_full {Γ : Context.{u}} (D : Datum Γ)
    (E : HomotopyEquivalence D.map) (F : Filling D.faceFamily) (hF : F.Lawful)
    (G : Filling D.ambient) (hG : G.Lawful) :
    ((D.smallFilling E F hF G hG).reindex (restrictInclusion D.face)).transport
      (eqToIso D.smallFamily_full) = F :=
  D.alignedSmallFilling_full F hF _ (preliminaryFilling_lawful D.face D.ambient D.faceFamily D.map E F hF G hG)

theorem genericFiberPartialIntro_input_reindex {Γ Δ Θ : Context.{u}} {A B : Family Γ}
    (f : A ⟶ B) (σ : Δ ⟶ Γ) (ρ : Θ ⟶ total (Cartesian.reindex B σ)) {φ : Subcontext Θ}
    (a : PartialSection (Cartesian.reindex A (ρ ≫ liftSub B σ ≫ projection B)) φ)
    (h : a.map (Functor.whiskerLeft (ρ ≫ liftSub B σ ≫ projection B).mapElements f) =
      PartialSection.ofTerm φ (Term.reindex (generic B) (ρ ≫ liftSub B σ))) :
    genericFiberPartialIntro (Functor.whiskerLeft σ.mapElements f) ρ a h =
      (genericFiberPartialIntro f (ρ ≫ liftSub B σ) a h).map
        (Functor.whiskerLeft ρ.mapElements (genericFiberReindexIso f σ).hom) := by
  apply PartialSection.ext
  intro x hx
  apply congrArg (Sigma.mk (a.val x hx))
  apply Subtype.ext
  apply PiElement.ext
  intro y g r
  exact (genericFiberPartialIntro_path (Functor.whiskerLeft σ.mapElements f) ρ a h x hx g r).trans
    (genericFiberPartialIntro_path f (ρ ≫ liftSub B σ) a h x hx
      ((liftSub (Cartesian.reindex A (projection B)) (liftSub B σ)).mapElements.map g) r).symm

theorem genericFiberPath_input_reindex {Γ Δ Θ : Context.{u}} {A B : Family Γ}
    (f : A ⟶ B) (σ : Δ ⟶ Γ) (ρ : Θ ⟶ total (Cartesian.reindex B σ))
    (z : Term (Cartesian.reindex
      (Homotopy.fiber (Functor.whiskerLeft (projection B).mapElements f) (generic B))
      (ρ ≫ liftSub B σ))) :
    genericFiberPath (Functor.whiskerLeft σ.mapElements f) ρ
      (Term.map (Functor.whiskerLeft ρ.mapElements (genericFiberReindexIso f σ).hom) z) =
    genericFiberPath f (ρ ≫ liftSub B σ) z := rfl

namespace AmbientExtension
variable {Ξ Ω : Context.{u}} (θ : Subcontext Ξ) (B : Family Ξ)
  (U : Family (restrictContext θ)) (f : U ⟶ reindex B (restrictInclusion θ))
section InputSubstitution
variable {Ξ' : Context.{u}} (σ : Ξ' ⟶ Ξ) (q : Ω ⟶ Ξ')
  (E : HomotopyEquivalence f) (F : Filling U) (hF : F.Lawful)
  (G : Filling B) (hG : G.Lawful) {χ : Subcontext Ω}
  (s : PartialSection (pulledCompatible θ B U f (q ≫ σ)) χ)
  (a : Term (reindex B (q ≫ σ)))
  (h : s.map (compatibleUnglue (θ.reindex (q ≫ σ)) (reindex B (q ≫ σ))
    (reindex U (restrictSubstitution θ (q ≫ σ)))
    (Functor.whiskerLeft (restrictSubstitution θ (q ≫ σ)).mapElements f)) =
      PartialSection.ofTerm χ a)

theorem fiber_input_reindex :
    fiber (θ.reindex σ) (reindex B σ) (reindex U (restrictSubstitution θ σ))
      (Functor.whiskerLeft (restrictSubstitution θ σ).mapElements f) q
      (E.reindex (restrictSubstitution θ σ)) (F.reindex (restrictSubstitution θ σ))
      (hF.reindex _) (G.reindex σ) (hG.reindex _) s a h =
    Term.map (Functor.whiskerLeft (target (θ.reindex σ) (reindex B σ) q a).mapElements
      (genericFiberReindexIso f (restrictSubstitution θ σ)).hom)
      (fiber θ B U f (q ≫ σ) E F hF G hG s a h) := by
  let τ := restrictSubstitution θ σ
  let ρ := target (θ.reindex σ) (reindex B σ) q a
  have hi := genericFiberPartialIntro_input_reindex f τ ρ
    (faceSection θ B U f (q ≫ σ) s) (faceSection_image θ B U f (q ≫ σ) s a h)
  exact (congrArg ((E.reindex τ).extendAlong (F.reindex τ) (hF.reindex _)
    ((G.reindex (restrictInclusion θ)).reindex τ) ((hG.reindex _).reindex _) ρ) hi).trans
      (E.extendAlong_input_reindex F hF (G.reindex (restrictInclusion θ)) (hG.reindex _)
        τ ρ _)

theorem extendedFace_input_reindex :
    extendedFace (θ.reindex σ) (reindex B σ) (reindex U (restrictSubstitution θ σ))
      (Functor.whiskerLeft (restrictSubstitution θ σ).mapElements f) q
      (E.reindex (restrictSubstitution θ σ)) (F.reindex (restrictSubstitution θ σ))
      (hF.reindex _) (G.reindex σ) (hG.reindex _) s a h =
    extendedFace θ B U f (q ≫ σ) E F hF G hG s a h := by
  exact congrArg (genericFiberFst (Functor.whiskerLeft (restrictSubstitution θ σ).mapElements f)
    (target (θ.reindex σ) (reindex B σ) q a))
      (fiber_input_reindex θ B U f σ q E F hF G hG s a h)


theorem extensionPath_input_reindex :
    HEq (extensionPath (θ.reindex σ) (reindex B σ) (reindex U (restrictSubstitution θ σ))
      (Functor.whiskerLeft (restrictSubstitution θ σ).mapElements f) q
      (E.reindex (restrictSubstitution θ σ)) (F.reindex (restrictSubstitution θ σ))
      (hF.reindex _) (G.reindex σ) (hG.reindex _) s a h)
    (extensionPath θ B U f (q ≫ σ) E F hF G hG s a h) := by
  unfold extensionPath
  rw [fiber_input_reindex θ B U f σ q E F hF G hG s a h]
  rfl

theorem corrected_input_reindex :
    corrected (θ.reindex σ) (reindex B σ) (reindex U (restrictSubstitution θ σ))
      (Functor.whiskerLeft (restrictSubstitution θ σ).mapElements f) q
      (E.reindex (restrictSubstitution θ σ)) (F.reindex (restrictSubstitution θ σ))
      (hF.reindex _) (G.reindex σ) (hG.reindex _) s a h =
    corrected θ B U f (q ≫ σ) E F hF G hG s a h := by
  exact correctAmbient_congr (G.reindex (q ≫ σ)) (θ.reindex (q ≫ σ)) χ a _ _ _ _ _ _
    (congrArg (Term.map (Functor.whiskerLeft (restrictSubstitution θ (q ≫ σ)).mapElements f))
      (extendedFace_input_reindex θ B U f σ q E F hF G hG s a h))
    (extensionPath_input_reindex θ B U f σ q E F hF G hG s a h)

theorem extendSection_input_reindex :
    extendSection (θ.reindex σ) (reindex B σ) (reindex U (restrictSubstitution θ σ))
      (Functor.whiskerLeft (restrictSubstitution θ σ).mapElements f) q
      (E.reindex (restrictSubstitution θ σ)) (F.reindex (restrictSubstitution θ σ))
      (hF.reindex _) (G.reindex σ) (hG.reindex _) s a h =
    extendSection θ B U f (q ≫ σ) E F hF G hG s a h := by
  apply Term.ext
  intro x
  apply CompatibleElement.ext
  · exact congrArg (fun t => t.val x) (corrected_input_reindex θ B U f σ q E F hF G hG s a h)
  · intro y k hy
    exact congrArg (fun t => t.val (faceObj (θ.reindex (q ≫ σ)) y hy))
      (extendedFace_input_reindex θ B U f σ q E F hF G hG s a h)

end InputSubstitution
end AmbientExtension
section SourceSubstitution
variable {Γ' : Context.{u}} (σ : Γ' ⟶ Γ) (q : total (interval Δ) ⟶ Γ')

theorem inputIso_input_reindex :
    Functor.whiskerLeft q.mapElements (reindexIso φ A T e σ).hom ≫
      (inputIso (φ.reindex σ) (reindex A σ) (reindex T (restrictSubstitution φ σ))
        (Functor.whiskerLeft (restrictSubstitution φ σ).mapElements e) q).hom =
    (inputIso φ A T e (q ≫ σ)).hom := by
  ext x z
  let i := familyIso (φ.reindex σ) (reindex A σ) (reindex T (restrictSubstitution φ σ))
    (Functor.whiskerLeft (restrictSubstitution φ σ).mapElements e)
  let z' := (compatibleReindexIso φ A T e σ).hom.app (q.mapElements.obj x)
    ((familyIso φ A T e).hom.app ((q ≫ σ).mapElements.obj x) z)
  exact congrArg ((compatibleReindexMap (φ.reindex σ) (reindex A σ)
    (reindex T (restrictSubstitution φ σ))
    (Functor.whiskerLeft (restrictSubstitution φ σ).mapElements e) q).app x)
      (congrArg (fun m => m.app (q.mapElements.obj x) z') i.inv_hom_id)


theorem inputBox_input_reindex (ψ : Subcontext Δ) (s₀ : Term (interval Δ))
    (b : OpenBox (reindex (family φ A T e) (q ≫ σ)) ψ s₀) :
    (b.map (Functor.whiskerLeft q.mapElements (reindexIso φ A T e σ).hom)).map
      (inputIso (φ.reindex σ) (reindex A σ) (reindex T (restrictSubstitution φ σ))
        (Functor.whiskerLeft (restrictSubstitution φ σ).mapElements e) q).hom =
    b.map (inputIso φ A T e (q ≫ σ)).hom :=
  congrArg b.map (inputIso_input_reindex φ A T e σ q)

theorem preliminaryCompatibleFill_input_reindex (E : HomotopyEquivalence e)
    (F : Filling T) (hF : F.Lawful) (G : Filling A) (hG : G.Lawful)
    (ψ : Subcontext Δ) (s₀ : Term (interval Δ)) (b : OpenBox (reindex (family φ A T e) (q ≫ σ)) ψ s₀) :
    preliminaryCompatibleFill (φ.reindex σ) (reindex A σ) (reindex T (restrictSubstitution φ σ))
      (Functor.whiskerLeft (restrictSubstitution φ σ).mapElements e) q
      (E.reindex (restrictSubstitution φ σ)) (F.reindex (restrictSubstitution φ σ))
      (hF.reindex _) (G.reindex σ) (hG.reindex _) ψ s₀
      (b.map (Functor.whiskerLeft q.mapElements (reindexIso φ A T e σ).hom)) =
    preliminaryCompatibleFill φ A T e (q ≫ σ) E F hF G hG ψ s₀ b := by
  let m := compatibleUnglue (φ.reindex (q ≫ σ)) (reindex A (q ≫ σ))
    (reindex T (restrictSubstitution φ (q ≫ σ)))
    (Functor.whiskerLeft (restrictSubstitution φ (q ≫ σ)).mapElements e)
  let K (c : OpenBox (AmbientExtension.pulledCompatible φ A T e (q ≫ σ)) ψ s₀) :=
    AmbientExtension.extendSection (φ.reindex σ) (reindex A σ)
      (reindex T (restrictSubstitution φ σ))
      (Functor.whiskerLeft (restrictSubstitution φ σ).mapElements e) q
      (E.reindex (restrictSubstitution φ σ)) (F.reindex (restrictSubstitution φ σ))
      (hF.reindex _) (G.reindex σ) (hG.reindex _) (boxPartial c)
      (G.fill (q ≫ σ) ψ s₀ (c.map m))
      (boxPartial_image_filled m c _ (hG.fills (q ≫ σ) ψ s₀ (c.map m)))
  exact (congrArg K (inputBox_input_reindex φ A T e σ q ψ s₀ b)).trans
    (AmbientExtension.extendSection_input_reindex φ A T e σ q E F hF G hG _ _ _)


theorem inputIso_inverse_input_reindex :
    (inputIso (φ.reindex σ) (reindex A σ) (reindex T (restrictSubstitution φ σ))
      (Functor.whiskerLeft (restrictSubstitution φ σ).mapElements e) q).inv =
    (inputIso φ A T e (q ≫ σ)).inv ≫
      Functor.whiskerLeft q.mapElements (reindexIso φ A T e σ).hom :=
  (Iso.eq_inv_comp (inputIso φ A T e (q ≫ σ))).mpr
    ((Iso.comp_inv_eq (inputIso (φ.reindex σ) (reindex A σ)
      (reindex T (restrictSubstitution φ σ))
      (Functor.whiskerLeft (restrictSubstitution φ σ).mapElements e) q)).mpr
        (inputIso_input_reindex φ A T e σ q).symm)

theorem preliminaryFill_input_reindex (E : HomotopyEquivalence e)
    (F : Filling T) (hF : F.Lawful) (G : Filling A) (hG : G.Lawful)
    (ψ : Subcontext Δ) (s₀ : Term (interval Δ)) (b : OpenBox (reindex (family φ A T e) (q ≫ σ)) ψ s₀) :
    preliminaryFill (φ.reindex σ) (reindex A σ) (reindex T (restrictSubstitution φ σ))
      (Functor.whiskerLeft (restrictSubstitution φ σ).mapElements e) q
      (E.reindex (restrictSubstitution φ σ)) (F.reindex (restrictSubstitution φ σ))
      (hF.reindex _) (G.reindex σ) (hG.reindex _) ψ s₀
      (b.map (Functor.whiskerLeft q.mapElements (reindexIso φ A T e σ).hom)) =
    Term.map (Functor.whiskerLeft q.mapElements (reindexIso φ A T e σ).hom)
      (preliminaryFill φ A T e (q ≫ σ) E F hF G hG ψ s₀ b) :=
  (congrArg (Term.map (inputIso (φ.reindex σ) (reindex A σ)
    (reindex T (restrictSubstitution φ σ))
    (Functor.whiskerLeft (restrictSubstitution φ σ).mapElements e) q).inv)
      (preliminaryCompatibleFill_input_reindex φ A T e σ q E F hF G hG ψ s₀ b)).trans
    (congrArg (fun η => Term.map η (preliminaryCompatibleFill φ A T e (q ≫ σ) E F hF G hG ψ s₀ b))
      (inputIso_inverse_input_reindex φ A T e σ q))


theorem reindexIso_full :
    Functor.whiskerLeft (restrictInclusion (φ.reindex σ)).mapElements (reindexIso φ A T e σ).hom ≫
      (eqToIso (family_full (φ.reindex σ) (reindex A σ) (reindex T (restrictSubstitution φ σ))
        (Functor.whiskerLeft (restrictSubstitution φ σ).mapElements e))).hom =
    Functor.whiskerLeft (restrictSubstitution φ σ).mapElements (eqToIso (family_full φ A T e)).hom := by
  ext x z
  have hc : ∀ {Ω : Context.{u}} {B C : Family Ω} (h : B = C) (y : Ω.Elements) (a : B.obj y),
      HEq ((eqToHom h).app y a) a := by
    intro Ω B C h y a
    cases h
    rfl
  let y := (restrictSubstitution φ σ).mapElements.obj x
  let t := (eqToHom (family_full φ A T e)).app y z
  have hf := fiberEquiv_full φ A T e
    (x := (restrictInclusion φ).mapElements.obj y) x.val.property z t (hc (family_full φ A T e) y z).symm
  let c := (compatibleReindexMap φ A T e σ).app
    ((restrictInclusion (φ.reindex σ)).mapElements.obj x) ((fiberEquiv φ A T e _) z)
  have hr : c.face (𝟙 _) x.val.property = t := by
    exact (congrArg (fun v : CompatibleElement φ A T e ((restrictInclusion φ).mapElements.obj y) =>
      v.face (𝟙 _) x.val.property) hf).trans (fromFace_read φ A T e (x := (restrictInclusion φ).mapElements.obj y) x.val.property t)
  exact eq_of_heq ((hc (family_full (φ.reindex σ) (reindex A σ)
    (reindex T (restrictSubstitution φ σ))
    (Functor.whiskerLeft (restrictSubstitution φ σ).mapElements e)) x _).trans
    ((fiberEquiv_symm_full (φ.reindex σ) (reindex A σ) (reindex T (restrictSubstitution φ σ))
      (Functor.whiskerLeft (restrictSubstitution φ σ).mapElements e) x.val.property c).trans
        (heq_of_eq hr)))


theorem wholeFaceIso_input_reindex :
    Functor.whiskerLeft
      (intervalSub (restrictInclusion (intervalAll (φ.reindex (q ≫ σ)) )) ≫ q).mapElements
      (reindexIso φ A T e σ).hom ≫
      (wholeFaceIso (φ.reindex σ) (reindex A σ) (reindex T (restrictSubstitution φ σ))
        (Functor.whiskerLeft (restrictSubstitution φ σ).mapElements e) q).hom =
    (wholeFaceIso φ A T e (q ≫ σ)).hom := by
  let l := wholeFaceLine (φ.reindex σ) q
  let r := intervalSub (restrictInclusion (intervalAll (φ.reindex (q ≫ σ)))) ≫ q
  have hn := congrArg Iso.hom (reindex_eqToIso _ _
    (family_full (φ.reindex σ) (reindex A σ) (reindex T (restrictSubstitution φ σ))
      (Functor.whiskerLeft (restrictSubstitution φ σ).mapElements e)) l)
  have ho := congrArg Iso.hom (reindex_eqToIso _ _
    (family_full φ A T e) (wholeFaceLine φ (q ≫ σ)))
  exact (congrArg (fun η => Functor.whiskerLeft r.mapElements (reindexIso φ A T e σ).hom ≫ η) hn).trans
    ((congrArg (Functor.whiskerLeft l.mapElements) (reindexIso_full φ A T e σ)).trans ho.symm)


theorem selectedFaceFill_input_reindex (F : Filling T) (ψ : Subcontext Δ) (s₀ : Term (interval Δ))
    (b : OpenBox (reindex (family φ A T e) (q ≫ σ)) ψ s₀) :
    selectedFaceFill (φ.reindex σ) (reindex A σ) (reindex T (restrictSubstitution φ σ))
      (Functor.whiskerLeft (restrictSubstitution φ σ).mapElements e) q
      (F.reindex (restrictSubstitution φ σ)) ψ s₀
      (b.map (Functor.whiskerLeft q.mapElements (reindexIso φ A T e σ).hom)) =
    Term.map (Functor.whiskerLeft
      (intervalSub (restrictInclusion (intervalAll (φ.reindex (q ≫ σ)))) ≫ q).mapElements
      (reindexIso φ A T e σ).hom) (selectedFaceFill φ A T e (q ≫ σ) F ψ s₀ b) := by
  let δ := intervalAll (φ.reindex (q ≫ σ))
  let r := Functor.whiskerLeft (intervalSub (restrictInclusion δ) ≫ q).mapElements
    (reindexIso φ A T e σ).hom
  let i₀ := wholeFaceIso φ A T e (q ≫ σ)
  let i₁ := wholeFaceIso (φ.reindex σ) (reindex A σ) (reindex T (restrictSubstitution φ σ))
    (Functor.whiskerLeft (restrictSubstitution φ σ).mapElements e) q
  have hi : i₁.inv = i₀.inv ≫ r :=
    (Iso.eq_inv_comp i₀).mpr ((Iso.comp_inv_eq i₁).mpr (wholeFaceIso_input_reindex φ A T e σ q).symm)
  have hb := congrArg (fun η => (b.reindex (restrictInclusion δ)).map η)
    (wholeFaceIso_input_reindex φ A T e σ q)
  exact (congrArg (fun c => Term.map i₁.inv
    (F.fill (wholeFaceLine φ (q ≫ σ)) (ψ.reindex (restrictInclusion δ)) (Term.reindex s₀ (restrictInclusion δ)) c)) hb).trans
      (congrArg (fun η => Term.map η (F.fill (wholeFaceLine φ (q ≫ σ))
        (ψ.reindex (restrictInclusion δ)) (Term.reindex s₀ (restrictInclusion δ)) ((b.reindex (restrictInclusion δ)).map i₀.hom))) hi)


theorem selectedFaceTube_input_reindex (F : Filling T) (ψ : Subcontext Δ) (s₀ : Term (interval Δ))
    (b : OpenBox (reindex (family φ A T e) (q ≫ σ)) ψ s₀) :
    selectedFaceTube (φ.reindex σ) (reindex A σ) (reindex T (restrictSubstitution φ σ))
      (Functor.whiskerLeft (restrictSubstitution φ σ).mapElements e) q
      (F.reindex (restrictSubstitution φ σ)) ψ s₀
      (b.map (Functor.whiskerLeft q.mapElements (reindexIso φ A T e σ).hom)) =
    (selectedFaceTube φ A T e (q ≫ σ) F ψ s₀ b).map
      (Functor.whiskerLeft q.mapElements (reindexIso φ A T e σ).hom) := by
  apply PartialSection.ext
  intro x hx
  exact congrArg (fun t => t.val
    ((total (interval (restrictContext (intervalAll (φ.reindex (q ≫ σ)))))).elementsMk x.obj
      ⟨⟨x.val.1,hx⟩,x.val.2⟩)) (selectedFaceFill_input_reindex φ A T e σ q F ψ s₀ b)

theorem filling_input_reindex (E : HomotopyEquivalence e)
    (F : Filling T) (hF : F.Lawful) (G : Filling A) (hG : G.Lawful)
    (ψ : Subcontext Δ) (s₀ : Term (interval Δ)) (b : OpenBox (reindex (family φ A T e) (q ≫ σ)) ψ s₀) :
    (filling (φ.reindex σ) (reindex A σ) (reindex T (restrictSubstitution φ σ))
      (Functor.whiskerLeft (restrictSubstitution φ σ).mapElements e)
      (E.reindex (restrictSubstitution φ σ)) (F.reindex (restrictSubstitution φ σ))
      (hF.reindex _) (G.reindex σ) (hG.reindex _)).fill q ψ s₀
      (b.map (Functor.whiskerLeft q.mapElements (reindexIso φ A T e σ).hom)) =
    Term.map (Functor.whiskerLeft q.mapElements (reindexIso φ A T e σ).hom)
      ((filling φ A T e E F hF G hG).fill (q ≫ σ) ψ s₀ b) := by
  let r := Functor.whiskerLeft q.mapElements (reindexIso φ A T e σ).hom
  let t := selectedFaceTube φ A T e (q ≫ σ) F ψ s₀ b
  let hc := selectedFaceTube_compatible φ A T e (q ≫ σ) F hF ψ s₀ b
  let hz := selectedFaceTube_zero φ A T e (q ≫ σ) F hF ψ s₀ b
  let t' := selectedFaceTube (φ.reindex σ) (reindex A σ) (reindex T (restrictSubstitution φ σ))
    (Functor.whiskerLeft (restrictSubstitution φ σ).mapElements e) q
    (F.reindex (restrictSubstitution φ σ)) ψ s₀ (b.map r)
  let hc' := selectedFaceTube_compatible (φ.reindex σ) (reindex A σ)
    (reindex T (restrictSubstitution φ σ))
    (Functor.whiskerLeft (restrictSubstitution φ σ).mapElements e) q
    (F.reindex (restrictSubstitution φ σ)) (hF.reindex _) ψ s₀ (b.map r)
  let hz' := selectedFaceTube_zero (φ.reindex σ) (reindex A σ)
    (reindex T (restrictSubstitution φ σ))
    (Functor.whiskerLeft (restrictSubstitution φ σ).mapElements e) q
    (F.reindex (restrictSubstitution φ σ)) (hF.reindex _) ψ s₀ (b.map r)
  have hb : addTube (b.map r) t' hc' hz' = (addTube b t hc hz).map r := by
    apply OpenBox.ext
    · exact (PartialSection.glue_congr rfl (selectedFaceTube_input_reindex φ A T e σ q F ψ s₀ b)
        hc' (fun x hp hq => congrArg (r.app x) (hc x hp hq))).trans
        (partialGlue_map r b.tube t hc).symm
    · rfl
  exact (congrArg (preliminaryFill (φ.reindex σ) (reindex A σ)
    (reindex T (restrictSubstitution φ σ))
    (Functor.whiskerLeft (restrictSubstitution φ σ).mapElements e) q
    (E.reindex (restrictSubstitution φ σ)) (F.reindex (restrictSubstitution φ σ))
    (hF.reindex _) (G.reindex σ) (hG.reindex _) (ψ.join (intervalAll (φ.reindex (q ≫ σ)))) s₀) hb).trans
      (preliminaryFill_input_reindex φ A T e σ q E F hF G hG _ s₀ (addTube b t hc hz))

theorem filling_reindex_iso (E : HomotopyEquivalence e)
    (F : Filling T) (hF : F.Lawful) (G : Filling A) (hG : G.Lawful) :
    ((filling φ A T e E F hF G hG).reindex σ).transport (reindexIso φ A T e σ) =
    filling (φ.reindex σ) (reindex A σ) (reindex T (restrictSubstitution φ σ))
      (Functor.whiskerLeft (restrictSubstitution φ σ).mapElements e)
      (E.reindex (restrictSubstitution φ σ)) (F.reindex (restrictSubstitution φ σ))
      (hF.reindex _) (G.reindex σ) (hG.reindex _) := by
  apply Filling.ext
  intro Ω p ψ s₀ b
  let i := Functor.isoWhiskerLeft p.mapElements (reindexIso φ A T e σ)
  have h := filling_input_reindex φ A T e σ p E F hF G hG ψ s₀ (b.map i.inv)
  exact h.symm.trans (congrArg (fun c => (filling (φ.reindex σ) (reindex A σ)
    (reindex T (restrictSubstitution φ σ))
    (Functor.whiskerLeft (restrictSubstitution φ σ).mapElements e)
    (E.reindex (restrictSubstitution φ σ)) (F.reindex (restrictSubstitution φ σ))
    (hF.reindex _) (G.reindex σ) (hG.reindex _)).fill p ψ s₀ c) (OpenBox.map_iso_roundtrip i b))

end SourceSubstitution
theorem Datum.smallFilling_substitution {Γ Δ : Context.{u}} (D : Datum Γ)
    (E : HomotopyEquivalence D.map) (F : Filling D.faceFamily) (hF : F.Lawful)
    (G : Filling D.ambient) (hG : G.Lawful) (σ : Δ ⟶ Γ) :
    ((D.smallFilling E F hF G hG).reindex σ).transport (eqToIso (D.smallFamily_substitution σ)) =
      (D.reindex σ).smallFilling (E.reindex (restrictSubstitution D.face σ))
        (F.reindex (restrictSubstitution D.face σ)) (hF.reindex _) (G.reindex σ) (hG.reindex _) := by
  let H := filling D.face D.ambient D.faceFamily D.map E F hF G hG
  exact (congrArg (fun i => (H.reindex σ).transport i) (D.nativeIso_substitution σ)).trans
    (congrArg (fun K => K.transport (D.reindex σ).nativeIso)
      (filling_reindex_iso D.face D.ambient D.faceFamily D.map σ E F hF G hG))

end Glue
namespace LocalFamily

theorem eq_of_filling {Γ : Context.{u}} (A B : LocalFamily Γ)
    (h : A.family = B.family)
    (hf : A.toFilling.transport (eqToIso h) = B.toFilling) : A = B := by
  cases A with
  | mk family filling lawful =>
    cases B with
    | mk family' filling' lawful' =>
      dsimp at h
      subst family'
      have hlocal := congrArg Filling.toLocal hf
      change (filling.toFilling lawful).toLocal = (filling'.toFilling lawful').toLocal at hlocal
      rw [LocalFilling.toFilling_toLocal, LocalFilling.toFilling_toLocal] at hlocal
      cases hlocal
      rfl

noncomputable def normalizedGlue {Γ : Context.{u}} (φ : Subcontext Γ)
    (A : LocalFamily Γ) (T : LocalFamily (restrictContext φ))
    (e : T.family ⟶ Cartesian.reindex A.family (restrictInclusion φ)) (E : HomotopyEquivalence e) : LocalFamily Γ :=
  let D := Glue.Datum.mk φ A.family T.family e
  ofFilling D.smallFamily (D.smallFilling E T.toFilling T.toFilling_lawful A.toFilling A.toFilling_lawful)
    (D.smallFilling_lawful E T.toFilling T.toFilling_lawful A.toFilling A.toFilling_lawful)

theorem normalizedGlue_full {Γ : Context.{u}} (φ : Subcontext Γ)
    (A : LocalFamily Γ) (T : LocalFamily (restrictContext φ))
    (e : T.family ⟶ Cartesian.reindex A.family (restrictInclusion φ)) (E : HomotopyEquivalence e) :
    (normalizedGlue φ A T e E).reindex (restrictInclusion φ) = T := by
  let D := Glue.Datum.mk φ A.family T.family e
  apply eq_of_filling _ _ D.smallFamily_full
  have h : ((normalizedGlue φ A T e E).reindex (restrictInclusion φ)).toFilling =
      (D.smallFilling E T.toFilling T.toFilling_lawful A.toFilling A.toFilling_lawful).reindex (restrictInclusion φ) :=
    Filling.toLocal_toFilling _ ((D.smallFilling_lawful E T.toFilling T.toFilling_lawful A.toFilling A.toFilling_lawful).reindex _)
  exact (congrArg (fun F => F.transport (eqToIso D.smallFamily_full)) h).trans
    (D.smallFilling_full E T.toFilling T.toFilling_lawful A.toFilling A.toFilling_lawful)

theorem normalizedGlue_code_full {Γ : Context.{u}} (φ : Subcontext Γ)
    (A : LocalFamily Γ) (T : LocalFamily (restrictContext φ))
    (e : T.family ⟶ Cartesian.reindex A.family (restrictInclusion φ)) (E : HomotopyEquivalence e) :
    raisedSub (restrictInclusion φ) ≫ (normalizedGlue φ A T e E).code = T.code :=
  (code_reindex _ _).symm.trans (congrArg LocalFamily.code (normalizedGlue_full φ A T e E))

theorem toFilling_reindex {Γ Δ : Context.{u}} (A : LocalFamily Γ) (σ : Δ ⟶ Γ) :
    (A.reindex σ).toFilling = A.toFilling.reindex σ := rfl

theorem normalizedGlue_substitution {Γ Δ : Context.{u}} (φ : Subcontext Γ)
    (A : LocalFamily Γ) (T : LocalFamily (restrictContext φ))
    (e : T.family ⟶ Cartesian.reindex A.family (restrictInclusion φ)) (E : HomotopyEquivalence e)
    (σ : Δ ⟶ Γ) :
    (normalizedGlue φ A T e E).reindex σ =
      normalizedGlue (φ.reindex σ) (A.reindex σ) (T.reindex (restrictSubstitution φ σ))
        (Functor.whiskerLeft (restrictSubstitution φ σ).mapElements e) (E.reindex (restrictSubstitution φ σ)) := by
  let D := Glue.Datum.mk φ A.family T.family e
  apply eq_of_filling _ _ (D.smallFamily_substitution σ)
  have h : ((normalizedGlue φ A T e E).reindex σ).toFilling =
      (D.smallFilling E T.toFilling T.toFilling_lawful A.toFilling A.toFilling_lawful).reindex σ :=
    Filling.toLocal_toFilling _ ((D.smallFilling_lawful E T.toFilling T.toFilling_lawful A.toFilling A.toFilling_lawful).reindex σ)
  exact (congrArg (fun F => F.transport (eqToIso (D.smallFamily_substitution σ))) h).trans
    ((D.smallFilling_substitution E T.toFilling T.toFilling_lawful A.toFilling A.toFilling_lawful σ).trans
      (Filling.toLocal_toFilling _ ((D.reindex σ).smallFilling_lawful
        (E.reindex (restrictSubstitution φ σ)) (T.toFilling.reindex (restrictSubstitution φ σ))
        (T.toFilling_lawful.reindex _) (A.toFilling.reindex σ) (A.toFilling_lawful.reindex _))).symm)

end LocalFamily
end SquareKit.Cubical.Cartesian

namespace SquareKit.Cubical.Cartesian
open CategoryTheory Glue
universe u
theorem pathTerm_hext {Γ : Context.{u}} {B : Family (total (interval Γ))}
    {a₀ b₀ : Term (reindex B (endpointSub Γ false))}
    {a₁ b₁ : Term (reindex B (endpointSub Γ true))}
    (p : Term (path B a₀ a₁)) (q : Term (path B b₀ b₁)) (h : pathApp p = pathApp q) :
    HEq p q := by
  have hzero := (pathApp_zero p).symm.trans
    ((congrArg (fun t => Term.reindex t (endpointSub Γ false)) h).trans (pathApp_zero q))
  have hone := (pathApp_one p).symm.trans
    ((congrArg (fun t => Term.reindex t (endpointSub Γ true)) h).trans (pathApp_one q))
  subst b₀
  subst b₁
  exact heq_of_eq (pathApp_injective h)


theorem genericFiberIntro_eta {Γ Δ : Context.{u}} {A B : Family Γ}
 (f : A ⟶ B) (σ : Δ ⟶ total B) (z : Term (reindex (Homotopy.genericFiber f) σ)) :
 genericFiberIntro f σ (genericFiberFst f σ z) (genericFiberPath f σ z) = z :=
 Homotopy.fiberIntroOver_eta (Functor.whiskerLeft (projection B).mapElements f) (generic B) σ z

theorem genericFiberIntro_reindex {Γ Δ Θ : Context.{u}} {A B : Family Γ}
 (f : A ⟶ B) (σ : Δ ⟶ total B) (a : Term (reindex A (σ ≫ projection B)))
 (p : Term (homogeneousPath (reindex B (σ ≫ projection B))
  (Term.map (Functor.whiskerLeft (σ ≫ projection B).mapElements f) a) (Term.reindex (generic B) σ))) (τ : Θ ⟶ Δ) :
 Term.reindex (genericFiberIntro f σ a p) τ = genericFiberIntro f (τ ≫ σ) (Term.reindex a τ) (homogeneousReindex p τ) :=
 Homotopy.fiberIntroOver_reindex (Functor.whiskerLeft (projection B).mapElements f) (generic B) σ τ a p

theorem genericFiberIntro_congr {Γ Δ : Context.{u}} {A B : Family Γ}
 (f : A ⟶ B) (σ : Δ ⟶ total B) (a a' : Term (reindex A (σ ≫ projection B))) (ha : a = a')
 (p : Term (homogeneousPath (reindex B (σ ≫ projection B))
  (Term.map (Functor.whiskerLeft (σ ≫ projection B).mapElements f) a) (Term.reindex (generic B) σ)))
 (p' : Term (homogeneousPath (reindex B (σ ≫ projection B))
  (Term.map (Functor.whiskerLeft (σ ≫ projection B).mapElements f) a') (Term.reindex (generic B) σ))) (hp : HEq p p') :
 genericFiberIntro f σ a p = genericFiberIntro f σ a' p' := by
 subst a'; cases eq_of_heq hp; rfl

end SquareKit.Cubical.Cartesian

namespace SquareKit.Cubical.Cartesian.Glue
open CategoryTheory
universe u
noncomputable section

private theorem fiberIntro_path {Γ Δ : Context.{u}} {B D : Family Γ} (f : B ⟶ D)
    (σ : Δ ⟶ total D) (b : Term (reindex B (σ ≫ projection D)))
    (q : Term (homogeneousPath (reindex D (σ ≫ projection D))
      (Term.map (Functor.whiskerLeft (σ ≫ projection D).mapElements f) b)
      (Term.reindex (generic D) σ))) :
    genericFiberPath f σ (genericFiberIntro f σ b q) = q :=
  Term.map_iso_roundtrip (genericFiberPathIso f σ b).symm q

private theorem fiberIntro_reindex_eq {Γ Δ Ξ : Context.{u}} {B D : Family Γ}
    (f : B ⟶ D) (σ : Δ ⟶ total D) (a : Term (reindex B (σ ≫ projection D)))
    (p : Term (homogeneousPath (reindex D (σ ≫ projection D))
      (Term.map (Functor.whiskerLeft (σ ≫ projection D).mapElements f) a)
      (Term.reindex (generic D) σ))) (τ : Ξ ⟶ Δ)
    (z : Term (reindex (Homotopy.fiber (Functor.whiskerLeft (projection D).mapElements f)
      (generic D)) (τ ≫ σ)))
    (ha : Term.reindex a τ = genericFiberFst f (τ ≫ σ) z)
    (hp : Term.reindex (pathApp p) (liftSub (interval Δ) τ) = pathApp (genericFiberPath f (τ ≫ σ) z)) :
    Term.reindex (genericFiberIntro f σ a p) τ = z := by
  let q := homogeneousReindex p τ
  have hq : HEq q (genericFiberPath f (τ ≫ σ) z) :=
    pathTerm_hext q (genericFiberPath f (τ ≫ σ) z) hp
  have hc := genericFiberIntro_congr f (τ ≫ σ) (Term.reindex a τ) (genericFiberFst f (τ ≫ σ) z)
    ha q (genericFiberPath f (τ ≫ σ) z) hq
  exact (genericFiberIntro_reindex f σ a p τ).trans
    (hc.trans (genericFiberIntro_eta f (τ ≫ σ) z))

namespace UnglueFiber
variable {Γ Δ : Context.{u}} (φ : Subcontext Γ) (A : Family Γ)
  (T : Family (restrictContext φ)) (e : T ⟶ reindex A (restrictInclusion φ))
  (σ : Δ ⟶ total A)

abbrev glueFamily := family φ A T e
abbrev f := unglue φ A T e
abbrev fiber := Homotopy.fiber (Functor.whiskerLeft (projection A).mapElements (f φ A T e))
  (generic A)
abbrev face := φ.reindex (σ ≫ projection A)
abbrev target := Term.reindex (generic A) σ

variable {ψ : Subcontext Δ} (s : PartialSection (reindex (fiber φ A T e) σ) ψ)

def partialDomain := genericFiberFst (f φ A T e) (restrictInclusion ψ ≫ σ) s.toRestricted

def partialPath := genericFiberPath (f φ A T e) (restrictInclusion ψ ≫ σ) s.toRestricted

def partialTube : PartialSection (reindex A (projection (interval Δ) ≫ σ ≫ projection A))
    (ψ.reindex (projection (interval Δ))) :=
  restrictedPathTube ψ (target A σ)
    (Term.map (Functor.whiskerLeft (restrictInclusion ψ ≫ σ ≫ projection A).mapElements
      (f φ A T e)) (partialDomain φ A T e σ s))
    (partialPath φ A T e σ s)

def intersectionToPartial : restrictContext (ψ.reindex (restrictInclusion (face φ A σ))) ⟶
    restrictContext ψ where
  app _ := TypeCat.ofHom (fun z => ⟨z.val.val,z.property⟩)
  naturality _ _ _ := rfl

/-- Restrict a partial homotopy fiber to the gluing face. -/
def facePartial : PartialSection
    (reindex (Homotopy.fiber (Functor.whiskerLeft (projection (reindex A (restrictInclusion φ))).mapElements e)
      (generic (reindex A (restrictInclusion φ))))
      (AmbientExtension.target φ A (σ ≫ projection A) (target A σ)))
    (ψ.reindex (restrictInclusion (face φ A σ))) := by
  let θ := face φ A σ
  let χ := ψ.reindex (restrictInclusion θ)
  let r := intersectionToPartial φ A σ (ψ := ψ)
  let g := Term.reindex (partialDomain φ A T e σ s) r
  let p := restrictInclusion χ ≫ restrictInclusion θ ≫ σ ≫ projection A
  let c := Term.map (Functor.whiskerLeft p.mapElements (familyIso φ A T e).hom ≫
    compatibleReindexMap φ A T e p) g
  let t : Term (reindex T (restrictInclusion χ ≫ restrictSubstitution φ (σ ≫ projection A))) :=
    { val := fun x => (c.val x).face (𝟙 _) x.val.val.property
      property := by
        intro x y k
        have h := congrArg (fun z => z.face (𝟙 _) y.val.val.property) (c.property k)
        change (c.val x).face (k ≫ 𝟙 _) y.val.val.property = _ at h
        exact ((c.val x).naturality (𝟙 _) k x.val.val.property).trans (by
          simpa only [Category.id_comp, Category.comp_id] using h) }
  have ht : Term.map (Functor.whiskerLeft
      (restrictInclusion χ ≫ restrictSubstitution φ (σ ≫ projection A)).mapElements e) t =
      Term.map (Functor.whiskerLeft p.mapElements (f φ A T e)) g := by
    apply Term.ext
    intro x
    exact ((c.val x).compatible (𝟙 _) x.val.val.property).trans
      (ConcreteCategory.congr_hom ((reindex A p).map_id x) _)
  let q := homogeneousReindex (partialPath φ A T e σ s) r
  exact PartialSection.ofRestricted (genericFiberIntro e
    (restrictInclusion χ ≫ AmbientExtension.target φ A (σ ≫ projection A) (target A σ)) t
    (pathLam (pathApp q) ((pathApp_zero q).trans ht.symm) (pathApp_one q)))

variable (E : HomotopyEquivalence e) (F : Filling T) (hF : F.Lawful)
  (G : Filling A) (hG : G.Lawful)

noncomputable def faceFiber :=
  E.extendAlong F hF (G.reindex (restrictInclusion φ)) (hG.reindex _)
    (AmbientExtension.target φ A (σ ≫ projection A) (target A σ))
    (facePartial φ A T e σ s)

noncomputable def faceDomain :=
  genericFiberFst e (AmbientExtension.target φ A (σ ≫ projection A) (target A σ))
    (faceFiber φ A T e σ s E F hF G hG)

noncomputable def facePath :=
  genericFiberPath e
    (AmbientExtension.target φ A (σ ≫ projection A) (target A σ))
    (faceFiber φ A T e σ s E F hF G hG)

noncomputable def faceTube :=
  restrictedPathTube (face φ A σ) (target A σ)
    (Term.map (Functor.whiskerLeft (restrictSubstitution φ (σ ≫ projection A)).mapElements e)
      (faceDomain φ A T e σ s E F hF G hG))
    (facePath φ A T e σ s E F hF G hG)

theorem faceFiber_boundary :
    Term.reindex (faceFiber φ A T e σ s E F hF G hG)
      (restrictInclusion (ψ.reindex (restrictInclusion (face φ A σ)))) =
    (facePartial φ A T e σ s).toRestricted := by
  apply Term.ext
  intro x
  exact E.extendAlong_boundary F hF (G.reindex (restrictInclusion φ)) (hG.reindex _)
    _ _ ((restrictInclusion _).mapElements.obj x) x.val.property

theorem facePartial_path :
    pathApp (genericFiberPath e
      (restrictInclusion (ψ.reindex (restrictInclusion (face φ A σ))) ≫
        AmbientExtension.target φ A (σ ≫ projection A) (target A σ))
      (facePartial φ A T e σ s).toRestricted) =
    Term.reindex (pathApp (partialPath φ A T e σ s))
      (liftSub (interval (restrictContext ψ)) (intersectionToPartial φ A σ)) := by
  dsimp only [facePartial]
  exact congrArg pathApp (fiberIntro_path e _ _ _)

theorem tubes_compatible :
    (faceTube φ A T e σ s E F hF G hG).Compatible (partialTube φ A T e σ s) := by
  let χ := ψ.reindex (restrictInclusion (face φ A σ))
  have hp := congrArg (fun z => pathApp (genericFiberPath e
    (restrictInclusion χ ≫ AmbientExtension.target φ A (σ ≫ projection A) (target A σ)) z))
    (faceFiber_boundary φ A T e σ s E F hF G hG)
  have h := hp.trans (facePartial_path φ A T e σ s)
  intro x hx hy
  let y := (restrictContext χ).elementsMk x.obj ⟨⟨x.val.1,hx⟩,hy⟩
  exact congrArg (fun t => t.val
    (extendObj (interval (restrictContext χ)) y
      x.val.2)) h

noncomputable def box : OpenBox (reindex A (projection (interval Δ) ≫ σ ≫ projection A))
    ((face φ A σ).join ψ) (endpoint Δ true) where
  tube := (faceTube φ A T e σ s E F hF G hG).glue (partialTube φ A T e σ s)
    (tubes_compatible φ A T e σ s E F hF G hG)
  base := target A σ
  boundary x hx := by
    rcases (Subcontext.full_join _ _ x).mp hx with hφ | hψ
    · exact (glueValue_left (faceTube φ A T e σ s E F hF G hG)
        (partialTube φ A T e σ s) ((endpointSub Δ true).mapElements.obj x) hx hφ).trans
        (restrictedPathTube_source _ _ _ _ x hφ)
    · exact (glueValue_right (faceTube φ A T e σ s E F hF G hG)
        (partialTube φ A T e σ s) (tubes_compatible φ A T e σ s E F hF G hG)
        ((endpointSub Δ true).mapElements.obj x) hx hψ).trans
        (restrictedPathTube_source _ _ _ _ x hψ)

noncomputable def filled := G.fill (projection (interval Δ) ≫ σ ≫ projection A)
  ((face φ A σ).join ψ) (endpoint Δ true) (box φ A T e σ s E F hF G hG)

noncomputable def ambient := Term.reindex (filled φ A T e σ s E F hF G hG) (endpointSub Δ false)

theorem filled_face (x : (total (interval Δ)).Elements)
    (hx : ((face φ A σ).reindex (projection (interval Δ))).Holds x) :
    (filled φ A T e σ s E F hF G hG).val x =
    (faceTube φ A T e σ s E F hF G hG).val x hx := by
  have hu := (Subcontext.full_join (face φ A σ) ψ
    ((projection (interval Δ)).mapElements.obj x)).mpr (Or.inl hx)
  exact ((hG.fills _ _ _ (box φ A T e σ s E F hF G hG)).2 x hu).trans
    (glueValue_left _ _ x hu hx)

theorem filled_partial (x : (total (interval Δ)).Elements)
    (hx : (ψ.reindex (projection (interval Δ))).Holds x) :
    (filled φ A T e σ s E F hF G hG).val x =
    (partialTube φ A T e σ s).val x hx := by
  have hu := (Subcontext.full_join (face φ A σ) ψ
    ((projection (interval Δ)).mapElements.obj x)).mpr (Or.inr hx)
  exact ((hG.fills _ _ _ (box φ A T e σ s E F hF G hG)).2 x hu).trans
    (glueValue_right _ _ (tubes_compatible φ A T e σ s E F hF G hG) x hu hx)

theorem ambient_face :
    Term.map (Functor.whiskerLeft (restrictSubstitution φ (σ ≫ projection A)).mapElements e)
      (faceDomain φ A T e σ s E F hF G hG) =
    Term.reindex (ambient φ A T e σ s E F hF G hG) (restrictInclusion (face φ A σ)) := by
  apply Term.ext
  intro x
  exact ((filled_face φ A T e σ s E F hF G hG
    ((endpointSub Δ false).mapElements.obj ((restrictInclusion _).mapElements.obj x)) x.val.property).trans
    (restrictedPathTube_target _ _ _ _ ((restrictInclusion _).mapElements.obj x) x.val.property)).symm

noncomputable def domainCompatible :=
  compatibleIntro (face φ A σ) (reindex A (σ ≫ projection A))
    (reindex T (restrictSubstitution φ (σ ≫ projection A)))
    (Functor.whiskerLeft (restrictSubstitution φ (σ ≫ projection A)).mapElements e)
    (faceDomain φ A T e σ s E F hF G hG) (ambient φ A T e σ s E F hF G hG)
    (ambient_face φ A T e σ s E F hF G hG)

noncomputable def domain :=
  Term.map (Functor.whiskerLeft (σ ≫ projection A).mapElements (familyIso φ A T e).inv)
    (Term.map (compatibleReindexIso φ A T e (σ ≫ projection A)).inv
      (domainCompatible φ A T e σ s E F hF G hG))

theorem domain_image :
    Term.map (Functor.whiskerLeft (σ ≫ projection A).mapElements (f φ A T e))
      (domain φ A T e σ s E F hF G hG) = ambient φ A T e σ s E F hF G hG := by
  apply Term.ext
  intro x
  exact congrArg (fun z => z.ambient)
    (congrArg (fun η => η.app ((σ ≫ projection A).mapElements.obj x)
      ((compatibleReindexIso φ A T e (σ ≫ projection A)).inv.app x
        ((domainCompatible φ A T e σ s E F hF G hG).val x)))
      (familyIso φ A T e).inv_hom_id)

noncomputable def resultPath : Term (homogeneousPath (reindex A (σ ≫ projection A))
    (Term.map (Functor.whiskerLeft (σ ≫ projection A).mapElements (f φ A T e))
      (domain φ A T e σ s E F hF G hG)) (target A σ)) :=
  pathLam (filled φ A T e σ s E F hF G hG)
    (domain_image φ A T e σ s E F hF G hG).symm
    (hG.fills _ _ _ (box φ A T e σ s E F hF G hG)).1

noncomputable def extension := genericFiberIntro (f φ A T e) σ
  (domain φ A T e σ s E F hF G hG) (resultPath φ A T e σ s E F hF G hG)

theorem faceDomain_boundary (x : (restrictContext (face φ A σ)).Elements)
    (hx : (ψ.reindex (restrictInclusion (face φ A σ))).Holds x) :
    (faceDomain φ A T e σ s E F hF G hG).val x =
    ((familyIso φ A T e).hom.app ((σ ≫ projection A).mapElements.obj
      ((restrictInclusion (face φ A σ)).mapElements.obj x))
      (s.val ((restrictInclusion (face φ A σ)).mapElements.obj x) hx).1).face (𝟙 _) x.val.property := by
  exact congrArg Sigma.fst (E.extendAlong_boundary F hF
    (G.reindex (restrictInclusion φ)) (hG.reindex _) _ (facePartial φ A T e σ s) x hx)

theorem domainCompatible_boundary (x : Δ.Elements) (hx : ψ.Holds x) :
    (domainCompatible φ A T e σ s E F hF G hG).val x =
    (compatibleReindexMap φ A T e (σ ≫ projection A)).app x
      ((familyIso φ A T e).hom.app ((σ ≫ projection A).mapElements.obj x) (s.val x hx).1) := by
  apply CompatibleElement.ext
  · exact (filled_partial φ A T e σ s E F hF G hG
      ((endpointSub Δ false).mapElements.obj x) hx).trans
      (restrictedPathTube_target _ _ _ _ x hx)
  · intro y k hy
    have h := faceDomain_boundary φ A T e σ s E F hF G hG
      (faceObj (face φ A σ) y hy) (ψ.natural k hx)
    have hs := congrArg (fun z => ((familyIso φ A T e).hom.app
      ((σ ≫ projection A).mapElements.obj y) z).face (𝟙 _) hy)
      ((partialDomain φ A T e σ s).property (faceHom ψ k hx))
    have hn := congrArg (fun z => z.face (𝟙 _) hy)
      ((familyIso φ A T e).hom.naturality_apply ((σ ≫ projection A).mapElements.map k)
        (s.val x hx).1)
    apply h.trans
    apply hs.symm.trans
    change _ = ((familyIso φ A T e).hom.app ((σ ≫ projection A).mapElements.obj x)
      (s.val x hx).1).face ((σ ≫ projection A).mapElements.map k) hy
    change _ = ((familyIso φ A T e).hom.app ((σ ≫ projection A).mapElements.obj x)
      (s.val x hx).1).face (((σ ≫ projection A).mapElements.map k) ≫ 𝟙 _) hy at hn
    change ((familyIso φ A T e).hom.app ((σ ≫ projection A).mapElements.obj y)
      ((family φ A T e).map ((σ ≫ projection A).mapElements.map k) (s.val x hx).1)).face
      (𝟙 _) hy = _
    simpa only [Category.comp_id] using hn

theorem domain_boundary :
    Term.reindex (domain φ A T e σ s E F hF G hG) (restrictInclusion ψ) =
    partialDomain φ A T e σ s := by
  apply Term.ext
  intro x
  let y := (restrictInclusion ψ).mapElements.obj x
  have h := congrArg (fun z => (familyIso φ A T e).inv.app
    ((σ ≫ projection A).mapElements.obj y)
    ((compatibleReindexIso φ A T e (σ ≫ projection A)).inv.app y z))
    (domainCompatible_boundary φ A T e σ s E F hF G hG y x.val.property)
  exact h.trans ((congrArg ((familyIso φ A T e).inv.app ((σ ≫ projection A).mapElements.obj y))
    (congrArg (fun η => η.app y ((familyIso φ A T e).hom.app
      ((σ ≫ projection A).mapElements.obj y) (s.val y x.val.property).1))
      (compatibleReindexIso φ A T e (σ ≫ projection A)).hom_inv_id)).trans
    (congrArg (fun η => η.app ((σ ≫ projection A).mapElements.obj y)
      (s.val y x.val.property).1) (familyIso φ A T e).hom_inv_id))

theorem filled_partial_section :
    Term.reindex (filled φ A T e σ s E F hF G hG) (liftSub (interval Δ) (restrictInclusion ψ)) =
    pathApp (partialPath φ A T e σ s) := by
  apply Term.ext
  intro x
  exact filled_partial φ A T e σ s E F hF G hG
    ((liftSub (interval Δ) (restrictInclusion ψ)).mapElements.obj x) x.val.1.property

theorem resultPath_boundary :
    Term.reindex (pathApp (resultPath φ A T e σ s E F hF G hG))
      (liftSub (interval Δ) (restrictInclusion ψ)) = pathApp (partialPath φ A T e σ s) :=
  filled_partial_section φ A T e σ s E F hF G hG

theorem extension_restricted :
    Term.reindex (extension φ A T e σ s E F hF G hG) (restrictInclusion ψ) = s.toRestricted :=
  fiberIntro_reindex_eq (f φ A T e) σ (domain φ A T e σ s E F hF G hG)
    (resultPath φ A T e σ s E F hF G hG) (restrictInclusion ψ) s.toRestricted
    (domain_boundary φ A T e σ s E F hF G hG) (resultPath_boundary φ A T e σ s E F hF G hG)

theorem extension_boundary (x : Δ.Elements) (hx : ψ.Holds x) :
    (extension φ A T e σ s E F hF G hG).val x = s.val x hx :=
  congrArg (fun t => t.val ((restrictContext ψ).elementsMk x.obj ⟨x.val,hx⟩))
    (extension_restricted φ A T e σ s E F hF G hG)

end UnglueFiber

/-- Glue elimination has contractible native homotopy fibers. Both their center
and contraction are constructed from the supplied equivalence and lawful fillers. -/
noncomputable def unglueEquivalence {Γ : Context.{u}} (φ : Subcontext Γ) (A : Family Γ)
    (T : Family (restrictContext φ)) (e : T ⟶ reindex A (restrictInclusion φ))
    (E : HomotopyEquivalence e) (F : Filling T) (hF : F.Lawful)
    (G : Filling A) (hG : G.Lawful) : HomotopyEquivalence (unglue φ A T e) where
  fibers := Contractible.ofExtensions
    (fun σ _ s => UnglueFiber.extension φ A T e σ s E F hF G hG)
    (fun σ _ s x hx => UnglueFiber.extension_boundary φ A T e σ s E F hF G hG x hx)

end
end SquareKit.Cubical.Cartesian.Glue
