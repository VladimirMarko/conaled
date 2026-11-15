import SquareKit.Internal.Cubical.GlueSubstitution
import SquareKit.Internal.Cubical.CubeProductFunctor

/-! The interval-universal face used in Glue filling. The fresh coordinate
remains unspecified; checking only its two endpoints would be insufficient. -/
set_option autoImplicit false
set_option warningAsError true
namespace SquareKit.Cubical
open CategoryTheory
namespace Face

/-- Quantify a fresh interval coordinate in the finite face lattice. -/
def allFresh {n : Nat} (φ : Carrier (n+1)) : Carrier n where
  holds ρ := φ.holds (Fin.cases none ρ)
  stable ρ τ h hp := φ.stable _ _ (fun i => by
    cases i using Fin.cases with
    | zero => exact Or.inl rfl
    | succ i => exact h i) hp

theorem allFresh_iff {n : Nat} (φ : Carrier (n+1)) (ρ : Assignment n) :
    (allFresh φ).holds ρ = true ↔ ∀ r, φ.holds (Fin.cases r ρ) = true := by
  constructor
  · intro h r
    exact φ.stable _ _ (fun i => by
      cases i using Fin.cases with
      | zero => exact Or.inl rfl
      | succ i => exact Or.inr rfl) h
  · intro h
    exact h none

theorem assignmentMap_extension {I J : Cube} (f : I ⟶ J) (ρ : Assignment I.dimension)
    (r : PartialDimension.Carrier) :
    assignmentMap (Cube.extensionMap f) (Fin.cases r ρ) =
      Fin.cases r (assignmentMap f ρ) := by
  refine Quotient.inductionOn f ?_
  intro f
  funext i
  cases i using Fin.cases with
  | zero => rfl
  | succ i =>
    change PartialDimension.eval (Fin.cases r ρ) (Expr.subst (fun j => .var j.succ) (f i)) =
      PartialDimension.eval ρ (f i)
    exact PartialDimension.eval_subst _ _ _

theorem allFresh_substitute {I J : Cube} (f : I ⟶ J) (φ : Carrier (J.dimension+1)) :
    allFresh (substitute (Cube.extensionMap f) φ) = substitute f (allFresh φ) := by
  apply Carrier.ext
  intro ρ
  exact congrArg φ.holds (assignmentMap_extension f ρ none)

/-- Full endpoint boundary is still insufficient for interval universality. -/
theorem allFresh_boundary : allFresh (join (atom (0 : Fin 1) false) (atom 0 true)) = bot 0 := by
  apply Carrier.ext
  intro ρ
  rfl

theorem allFresh_full {n : Nat} (φ : Carrier (n+1)) : Full (allFresh φ) ↔ Full φ := by
  have h : (Fin.cases none (fun _ : Fin n => none) : Assignment (n+1)) = fun _ => none := by
    funext i
    cases i using Fin.cases <;> rfl
  change φ.holds _ = true ↔ φ.holds _ = true
  rw [h]

end Face
namespace Presheaf
universe u

/-- Fresh interval extension commutes with every generalized-element restriction. -/
def freshRestriction {Γ : Context.{u}} {x y : Γ.Elements} (f : x ⟶ y) :
    freshExtension x ⟶ freshExtension y :=
  Functor.Elements.homMk (Cube.extensionMap f.hom.unop).op (by
    have hc : dropOpp x.obj ≫ (Cube.extensionMap f.hom.unop).op =
        f.hom ≫ dropOpp y.obj :=
      congrArg (fun g => g.op) (Cube.extensionMap_drop f.hom.unop)
    have hb : Γ.map (Cube.extensionMap f.hom.unop).op (Γ.map (dropOpp x.obj) x.val) =
        Γ.map (dropOpp y.obj) y.val := by
      calc
        _ = Γ.map (dropOpp x.obj ≫ (Cube.extensionMap f.hom.unop).op) x.val :=
          (ConcreteCategory.congr_hom (Γ.map_comp _ _) x.val).symm
        _ = Γ.map (f.hom ≫ dropOpp y.obj) x.val := congrArg (fun g => Γ.map g x.val) hc
        _ = Γ.map (dropOpp y.obj) (Γ.map f.hom x.val) :=
          ConcreteCategory.congr_hom (Γ.map_comp _ _) x.val
        _ = Γ.map (dropOpp y.obj) y.val := congrArg (fun z => Γ.map (dropOpp y.obj) z) f.map_val
    change (⟨_,ULift.up (Cube.extensionMap f.hom.unop ≫ Cube.fresh x.obj.unop)⟩ :
      (total (interval Γ)).obj (Opposite.op (Cube.extend y.obj.unop))) =
      ⟨_,ULift.up (Cube.fresh y.obj.unop)⟩
    rw [Cube.extensionMap_fresh]
    exact congrArg (fun z => (⟨z,ULift.up (Cube.fresh y.obj.unop)⟩ :
      (total (interval Γ)).obj (Opposite.op (Cube.extend y.obj.unop)))) hb)

/-- The base face on which a face holds throughout the interval. -/
def intervalAll {Γ : Context.{u}} (φ : Cofibration (total (interval Γ))) : Cofibration Γ where
  app I := TypeCat.ofHom (fun γ => ⟨Face.allFresh
    (φ.app (Opposite.op (Cube.extend I.unop)) (freshExtension (Γ.elementsMk I γ)).val).down⟩)
  naturality I J f := by
    apply ConcreteCategory.hom_ext
    intro γ
    let q : Γ.elementsMk I γ ⟶ Γ.elementsMk J (Γ.map f γ) := Functor.Elements.homMk f rfl
    have h := congrArg ULift.down (φ.naturality_apply (freshRestriction q).hom (freshExtension (Γ.elementsMk I γ)).val)
    have he := (freshRestriction q).map_val
    change (φ.app _ ((total (interval Γ)).map (freshRestriction q).hom _)).down = _ at h
    rw [he] at h
    exact congrArg ULift.up ((congrArg Face.allFresh h).trans (Face.allFresh_substitute f.unop _))

theorem intervalAll_full {Γ : Context.{u}} (φ : Cofibration (total (interval Γ)))
    (x : Γ.Elements) : (intervalAll φ).full x ↔ φ.full (freshExtension x) :=
  Face.allFresh_full _

theorem intervalAll_specialize {Γ : Context.{u}} (φ : Cofibration (total (interval Γ)))
    (x : Γ.Elements) (h : (intervalAll φ).full x) (r : (interval Γ).obj x) :
    φ.full (extendObj (interval Γ) x r) :=
  φ.full_natural (specializeInterval x r) ((intervalAll_full φ x).mp h)

theorem intervalAll_reindex {Γ Δ : Context.{u}} (φ : Cofibration (total (interval Γ)))
    (σ : Δ ⟶ Γ) : intervalAll (φ.reindex (liftSub (interval Γ) σ)) =
      (intervalAll φ).reindex σ := by
  ext I γ
  change ULift.up (Face.allFresh (φ.app (Opposite.op (Cube.extend I.unop))
    ⟨σ.app _ (Δ.map (dropOpp I) γ),ULift.up (Cube.fresh I.unop)⟩).down) =
    ULift.up (Face.allFresh (φ.app (Opposite.op (Cube.extend I.unop))
      ⟨Γ.map (dropOpp I) (σ.app I γ),ULift.up (Cube.fresh I.unop)⟩).down)
  rw [σ.naturality_apply (dropOpp I) γ]

/-- The universal face tests all future restrictions and all interval values. -/
theorem intervalAll_spec {Γ : Context.{u}} (φ : Cofibration (total (interval Γ)))
    (x : Γ.Elements) : (intervalAll φ).full x ↔
      ∀ {y : Γ.Elements} (_f : x ⟶ y) (r : (interval Γ).obj y),
        φ.full (extendObj (interval Γ) y r) := by
  constructor
  · intro h y f r
    exact intervalAll_specialize φ y ((intervalAll φ).full_natural f h) r
  · intro h
    apply (intervalAll_full φ x).mpr
    let y := Γ.elementsMk (Opposite.op (Cube.extend x.obj.unop)) (Γ.map (dropOpp x.obj) x.val)
    let f : x ⟶ y := Functor.Elements.homMk (dropOpp x.obj) rfl
    exact h f (ULift.up (Cube.fresh x.obj.unop))

namespace Glue
variable {Γ : Context.{u}} {A : Family (total (interval Γ))}
  {φ ψ : Cofibration Γ}

/-- Enlarge a box by a compatible selected whole tube. -/
noncomputable def addTube (b : OpenBox A φ)
    (t : PartialSection A (ψ.reindex (projection (interval Γ))))
    (h : b.tube.Compatible t)
    (h₀ : ∀ x hx, t.val ((endpointSub Γ false).mapElements.obj x) hx = b.base.val x) :
    OpenBox A (φ.join ψ) where
  tube := b.tube.glue t h
  base := b.base
  boundary x hx := by
    rcases (Cofibration.full_join φ ψ x).mp hx with hp | hq
    · exact (glueValue_left b.tube t ((endpointSub Γ false).mapElements.obj x) hx hp).trans
        (b.boundary x hp)
    · exact (glueValue_right b.tube t h ((endpointSub Γ false).mapElements.obj x) hx hq).trans
        (h₀ x hq)

theorem addTube_reindex (b : OpenBox A φ)
    (t : PartialSection A (ψ.reindex (projection (interval Γ))))
    (h : b.tube.Compatible t)
    (h₀ : ∀ x hx, t.val ((endpointSub Γ false).mapElements.obj x) hx = b.base.val x)
    {Θ : Context.{u}} (σ : Θ ⟶ Γ) :
    (addTube b t h h₀).reindex σ =
      addTube (ψ := ψ.reindex σ) (b.reindex σ) (t.reindex (liftSub (interval Γ) σ))
        (h.reindex (liftSub (interval Γ) σ)) (fun x hx => h₀ (σ.mapElements.obj x) hx) := by
  apply OpenBox.ext
  · exact PartialSection.glue_reindex b.tube t h (liftSub (interval Γ) σ)
  · rfl

theorem addTube_preserves_whole {Δ : Context.{u}} {B : Family Δ}
    (F : Filling B) (hF : F.Lawful) (p : total (interval Γ) ⟶ Δ)
    (b : OpenBox (reindex B p) φ)
    (t : PartialSection (reindex B p) (ψ.reindex (projection (interval Γ))))
    (h : b.tube.Compatible t)
    (h₀ : ∀ x hx, t.val ((endpointSub Γ false).mapElements.obj x) hx = b.base.val x)
    (x : (total (interval Γ)).Elements) (hx : (ψ.reindex (projection (interval Γ))).full x) :
    (F.fill p (φ.join ψ) (addTube b t h h₀)).val x = t.val x hx := by
  have hu : ((φ.join ψ).reindex (projection (interval Γ))).full x :=
    (Cofibration.full_join φ ψ ((projection (interval Γ)).mapElements.obj x)).mpr (Or.inr hx)
  exact ((hF.fills p (φ.join ψ) (addTube b t h h₀)).2 x hu).trans
    (glueValue_right b.tube t h x hu hx)

/-- This equality concerns the entire section, not just the far endpoint. -/
theorem addTube_recovers_section {Δ : Context.{u}} {B : Family Δ}
    (F : Filling B) (hF : F.Lawful) (p : total (interval Γ) ⟶ Δ)
    (b : OpenBox (reindex B p) φ) (t : Term (reindex B p))
    (h : b.tube.Compatible (PartialSection.ofTerm
      ((Cofibration.top Γ).reindex (projection (interval Γ))) t))
    (h₀ : ∀ x hx, (PartialSection.ofTerm
      ((Cofibration.top Γ).reindex (projection (interval Γ))) t).val
        ((endpointSub Γ false).mapElements.obj x) hx = b.base.val x) :
    F.fill p (φ.join (Cofibration.top Γ))
      (addTube b (PartialSection.ofTerm _ t) h h₀) = t := by
  apply Term.ext
  intro x
  exact addTube_preserves_whole F hF p b (PartialSection.ofTerm _ t) h h₀ x rfl

/-- Read the face component of partial compatible Glue data. -/
def compatiblePartialFace {Ξ : Context.{u}} (θ : Cofibration Ξ) (B : Family Ξ)
    (U : Family (restrictContext θ)) (f : U ⟶ reindex B (restrictInclusion θ))
    {χ : Cofibration Ξ} (s : PartialSection (compatibleFamily θ B U f) χ) :
    PartialSection U (χ.reindex (restrictInclusion θ)) where
  val x hx := (s.val ((restrictInclusion θ).mapElements.obj x) hx).face (𝟙 _) x.val.property
  property {x y} g hx := by
    let k := (restrictInclusion θ).mapElements.map g
    have ht := (s.val ((restrictInclusion θ).mapElements.obj x) hx).naturality
      (𝟙 _) k x.val.property
    have hs := congrArg (fun z => z.face (𝟙 _) y.val.property) (s.property k hx)
    change (s.val ((restrictInclusion θ).mapElements.obj x) hx).face (k ≫ 𝟙 _) _ =
      (s.val ((restrictInclusion θ).mapElements.obj y) _).face (𝟙 _) _ at hs
    exact ht.trans (by simpa only [Category.id_comp, Category.comp_id] using hs)

theorem compatiblePartialFace_image {Ξ : Context.{u}} (θ : Cofibration Ξ) (B : Family Ξ)
    (U : Family (restrictContext θ)) (f : U ⟶ reindex B (restrictInclusion θ))
    {χ : Cofibration Ξ} (s : PartialSection (compatibleFamily θ B U f) χ) :
    (compatiblePartialFace θ B U f s).map f =
      (s.map (compatibleUnglue θ B U f)).reindex (restrictInclusion θ) := by
  apply PartialSection.ext
  intro x hx
  exact ((s.val ((restrictInclusion θ).mapElements.obj x) hx).compatible (𝟙 _) x.val.property).trans
    (ConcreteCategory.congr_hom (B.map_id _) _)

/-- A path defined on a face supplies an actual partial tube in the ambient family. -/
def restrictedPathTube {Ξ : Context.{u}} {B : Family Ξ} (θ : Cofibration Ξ)
    (a : Term B) (t : Term (reindex B (restrictInclusion θ)))
    (q : Term (homogeneousPath (reindex B (restrictInclusion θ))
      (a.reindex (restrictInclusion θ)) t)) :
    PartialSection (reindex B (projection (interval Ξ)))
      (θ.reindex (projection (interval Ξ))) :=
  PartialSection.ofRestricted ((pathApp q).reindex (restrictedInterval θ))

theorem restrictedPathTube_zero {Ξ : Context.{u}} {B : Family Ξ} (θ : Cofibration Ξ)
    (a : Term B) (t : Term (reindex B (restrictInclusion θ)))
    (q : Term (homogeneousPath (reindex B (restrictInclusion θ))
      (a.reindex (restrictInclusion θ)) t)) (x : Ξ.Elements) (hx : θ.full x) :
    (restrictedPathTube θ a t q).val ((endpointSub Ξ false).mapElements.obj x) hx = a.val x :=
  congrArg (fun s => s.val (faceObj θ x hx)) (pathApp_zero q)

theorem restrictedPathTube_one {Ξ : Context.{u}} {B : Family Ξ} (θ : Cofibration Ξ)
    (a : Term B) (t : Term (reindex B (restrictInclusion θ)))
    (q : Term (homogeneousPath (reindex B (restrictInclusion θ))
      (a.reindex (restrictInclusion θ)) t)) (x : Ξ.Elements) (hx : θ.full x) :
    (restrictedPathTube θ a t q).val ((endpointSub Ξ true).mapElements.obj x) hx =
      t.val (faceObj θ x hx) :=
  congrArg (fun s => s.val (faceObj θ x hx)) (pathApp_one q)

/-- Correct ambient values along a face path while fixing a prescribed boundary. -/
noncomputable def correctionBox {Ξ : Context.{u}} {B : Family Ξ}
    (θ χ : Cofibration Ξ) (a : Term B) (t : Term (reindex B (restrictInclusion θ)))
    (q : Term (homogeneousPath (reindex B (restrictInclusion θ))
      (a.reindex (restrictInclusion θ)) t))
    (h : (restrictedPathTube θ a t q).Compatible
      (PartialSection.ofTerm (χ.reindex (projection (interval Ξ)))
        (a.reindex (projection (interval Ξ))))) :
    OpenBox (reindex B (projection (interval Ξ))) (θ.join χ) where
  tube := (restrictedPathTube θ a t q).glue (PartialSection.ofTerm _ _) h
  base := a
  boundary x hx := by
    rcases (Cofibration.full_join θ χ x).mp hx with ht | hc
    · exact (glueValue_left (restrictedPathTube θ a t q)
        (PartialSection.ofTerm (χ.reindex (projection (interval Ξ))) (a.reindex (projection (interval Ξ))))
        ((endpointSub Ξ false).mapElements.obj x) hx ht).trans
          (restrictedPathTube_zero θ a t q x ht)
    · exact glueValue_right (restrictedPathTube θ a t q) _ h
        ((endpointSub Ξ false).mapElements.obj x) hx hc

noncomputable def correctAmbient {Ξ : Context.{u}} {B : Family Ξ} (F : Filling B)
    (θ χ : Cofibration Ξ) (a : Term B) (t : Term (reindex B (restrictInclusion θ)))
    (q : Term (homogeneousPath (reindex B (restrictInclusion θ))
      (a.reindex (restrictInclusion θ)) t))
    (h : (restrictedPathTube θ a t q).Compatible
      (PartialSection.ofTerm (χ.reindex (projection (interval Ξ)))
        (a.reindex (projection (interval Ξ))))) : Term B :=
  F.hcomp (θ.join χ) (correctionBox θ χ a t q h)

theorem correctAmbient_face {Ξ : Context.{u}} {B : Family Ξ} (F : Filling B) (hF : F.Lawful)
    (θ χ : Cofibration Ξ) (a : Term B) (t : Term (reindex B (restrictInclusion θ)))
    (q : Term (homogeneousPath (reindex B (restrictInclusion θ))
      (a.reindex (restrictInclusion θ)) t))
    (h : (restrictedPathTube θ a t q).Compatible
      (PartialSection.ofTerm (χ.reindex (projection (interval Ξ)))
        (a.reindex (projection (interval Ξ))))) (x : Ξ.Elements) (hx : θ.full x) :
    (correctAmbient F θ χ a t q h).val x = t.val (faceObj θ x hx) := by
  have hu := (Cofibration.full_join θ χ x).mpr (Or.inl hx)
  exact (Filling.hcomp_boundary hF _ (correctionBox θ χ a t q h) x hu).trans
    ((glueValue_left (restrictedPathTube θ a t q)
        (PartialSection.ofTerm (χ.reindex (projection (interval Ξ))) (a.reindex (projection (interval Ξ)))) ((endpointSub Ξ true).mapElements.obj x)
      hu hx).trans (restrictedPathTube_one θ a t q x hx))

theorem correctAmbient_fixed {Ξ : Context.{u}} {B : Family Ξ} (F : Filling B) (hF : F.Lawful)
    (θ χ : Cofibration Ξ) (a : Term B) (t : Term (reindex B (restrictInclusion θ)))
    (q : Term (homogeneousPath (reindex B (restrictInclusion θ))
      (a.reindex (restrictInclusion θ)) t))
    (h : (restrictedPathTube θ a t q).Compatible
      (PartialSection.ofTerm (χ.reindex (projection (interval Ξ)))
        (a.reindex (projection (interval Ξ))))) (x : Ξ.Elements) (hx : χ.full x) :
    (correctAmbient F θ χ a t q h).val x = a.val x := by
  have hu := (Cofibration.full_join θ χ x).mpr (Or.inr hx)
  exact (Filling.hcomp_boundary hF _ (correctionBox θ χ a t q h) x hu).trans
    (glueValue_right (restrictedPathTube θ a t q) _ h ((endpointSub Ξ true).mapElements.obj x) hu hx)


theorem correctAmbient_congr {Ξ : Context.{u}} {B : Family Ξ} (F : Filling B)
    (θ χ : Cofibration Ξ) (a : Term B)
    (t t' : Term (reindex B (restrictInclusion θ)))
    (q : Term (homogeneousPath (reindex B (restrictInclusion θ))
      (a.reindex (restrictInclusion θ)) t))
    (q' : Term (homogeneousPath (reindex B (restrictInclusion θ))
      (a.reindex (restrictInclusion θ)) t'))
    (h : (restrictedPathTube θ a t q).Compatible
      (PartialSection.ofTerm (χ.reindex (projection (interval Ξ)))
        (a.reindex (projection (interval Ξ)))))
    (h' : (restrictedPathTube θ a t' q').Compatible
      (PartialSection.ofTerm (χ.reindex (projection (interval Ξ)))
        (a.reindex (projection (interval Ξ)))))
    (ht : t = t') (hq : HEq q q') :
    correctAmbient F θ χ a t q h = correctAmbient F θ χ a t' q' h' := by
  cases ht
  cases hq
  rfl

namespace AmbientExtension
variable {Ξ Ω : Context.{u}} (θ : Cofibration Ξ) (B : Family Ξ)
  (U : Family (restrictContext θ)) (f : U ⟶ reindex B (restrictInclusion θ)) (p : Ω ⟶ Ξ)

abbrev pulledCompatible := compatibleFamily (θ.reindex p) (reindex B p)
  (reindex U (restrictSubstitution θ p)) (Functor.whiskerLeft (restrictSubstitution θ p).mapElements f)

def faceSection {χ : Cofibration Ω} (s : PartialSection (pulledCompatible θ B U f p) χ) :=
  compatiblePartialFace (θ.reindex p) (reindex B p) (reindex U (restrictSubstitution θ p))
    (Functor.whiskerLeft (restrictSubstitution θ p).mapElements f) s

def target (a : Term (reindex B p)) : restrictContext (θ.reindex p) ⟶ total (reindex B (restrictInclusion θ)) :=
  pair (restrictSubstitution θ p) (a.reindex (restrictInclusion (θ.reindex p)))

theorem faceSection_image {χ : Cofibration Ω} (s : PartialSection (pulledCompatible θ B U f p) χ)
    (a : Term (reindex B p))
    (h : s.map (compatibleUnglue (θ.reindex p) (reindex B p) (reindex U (restrictSubstitution θ p))
      (Functor.whiskerLeft (restrictSubstitution θ p).mapElements f)) = PartialSection.ofTerm χ a) :
    (faceSection θ B U f p s).map (Functor.whiskerLeft (restrictSubstitution θ p).mapElements f) =
      PartialSection.ofTerm (χ.reindex (restrictInclusion (θ.reindex p)))
        (a.reindex (restrictInclusion (θ.reindex p))) :=
  (compatiblePartialFace_image (θ.reindex p) (reindex B p) (reindex U (restrictSubstitution θ p))
    (Functor.whiskerLeft (restrictSubstitution θ p).mapElements f) s).trans
    (congrArg (fun t => t.reindex (restrictInclusion (θ.reindex p))) h)

noncomputable def fiber (E : HomotopyEquivalence f) (F : Filling U) (hF : F.Lawful)
    (G : Filling B) (hG : G.Lawful) {χ : Cofibration Ω}
    (s : PartialSection (pulledCompatible θ B U f p) χ) (a : Term (reindex B p))
    (h : s.map (compatibleUnglue (θ.reindex p) (reindex B p) (reindex U (restrictSubstitution θ p))
      (Functor.whiskerLeft (restrictSubstitution θ p).mapElements f)) = PartialSection.ofTerm χ a) :=
  E.extendAlong F hF (G.reindex (restrictInclusion θ)) (hG.reindex _) (target θ B p a)
    (genericFiberPartialIntro f (target θ B p a) (faceSection θ B U f p s)
      (faceSection_image θ B U f p s a h))

noncomputable def extendedFace (E : HomotopyEquivalence f) (F : Filling U) (hF : F.Lawful)
    (G : Filling B) (hG : G.Lawful) {χ : Cofibration Ω}
    (s : PartialSection (pulledCompatible θ B U f p) χ) (a : Term (reindex B p))
    (h : s.map (compatibleUnglue (θ.reindex p) (reindex B p) (reindex U (restrictSubstitution θ p))
      (Functor.whiskerLeft (restrictSubstitution θ p).mapElements f)) = PartialSection.ofTerm χ a) :
    Term (reindex U (restrictSubstitution θ p)) :=
  genericFiberFst f (target θ B p a) (fiber θ B U f p E F hF G hG s a h)

noncomputable def extensionPath (E : HomotopyEquivalence f) (F : Filling U) (hF : F.Lawful)
    (G : Filling B) (hG : G.Lawful) {χ : Cofibration Ω}
    (s : PartialSection (pulledCompatible θ B U f p) χ) (a : Term (reindex B p))
    (h : s.map (compatibleUnglue (θ.reindex p) (reindex B p) (reindex U (restrictSubstitution θ p))
      (Functor.whiskerLeft (restrictSubstitution θ p).mapElements f)) = PartialSection.ofTerm χ a) :=
  homogeneousReverse (genericFiberPath f (target θ B p a) (fiber θ B U f p E F hF G hG s a h))

theorem extendedFace_boundary (E : HomotopyEquivalence f) (F : Filling U) (hF : F.Lawful)
    (G : Filling B) (hG : G.Lawful) {χ : Cofibration Ω}
    (s : PartialSection (pulledCompatible θ B U f p) χ) (a : Term (reindex B p))
    (h : s.map (compatibleUnglue (θ.reindex p) (reindex B p) (reindex U (restrictSubstitution θ p))
      (Functor.whiskerLeft (restrictSubstitution θ p).mapElements f)) = PartialSection.ofTerm χ a)
    (x : (restrictContext (θ.reindex p)).Elements) (hx : (χ.reindex (restrictInclusion (θ.reindex p))).full x) :
    (extendedFace θ B U f p E F hF G hG s a h).val x = (faceSection θ B U f p s).val x hx :=
  congrArg Sigma.fst (E.extendAlong_boundary F hF (G.reindex (restrictInclusion θ)) (hG.reindex _)
    (target θ B p a) (genericFiberPartialIntro f (target θ B p a) (faceSection θ B U f p s)
      (faceSection_image θ B U f p s a h)) x hx)

def substitutePartial {Λ : Context.{u}} (τ : Λ ⟶ Ω) {χ : Cofibration Ω}
    (s : PartialSection (pulledCompatible θ B U f p) χ) :
    PartialSection (pulledCompatible θ B U f (τ ≫ p)) (χ.reindex τ) :=
  (s.reindex τ).map (compatibleReindexMap (θ.reindex p) (reindex B p)
    (reindex U (restrictSubstitution θ p)) (Functor.whiskerLeft (restrictSubstitution θ p).mapElements f) τ)

theorem faceSection_reindex {Λ : Context.{u}} (τ : Λ ⟶ Ω) {χ : Cofibration Ω}
    (s : PartialSection (pulledCompatible θ B U f p) χ) :
    faceSection θ B U f (τ ≫ p) (substitutePartial θ B U f p τ s) =
      (faceSection θ B U f p s).reindex (restrictSubstitution (θ.reindex p) τ) := rfl

theorem fiber_reindex (E : HomotopyEquivalence f) (F : Filling U) (hF : F.Lawful)
    (G : Filling B) (hG : G.Lawful) {χ : Cofibration Ω}
    (s : PartialSection (pulledCompatible θ B U f p) χ) (a : Term (reindex B p))
    (h : s.map (compatibleUnglue (θ.reindex p) (reindex B p) (reindex U (restrictSubstitution θ p))
      (Functor.whiskerLeft (restrictSubstitution θ p).mapElements f)) = PartialSection.ofTerm χ a)
    {Λ : Context.{u}} (τ : Λ ⟶ Ω) :
    fiber θ B U f (τ ≫ p) E F hF G hG (substitutePartial θ B U f p τ s) (a.reindex τ)
      (congrArg (fun t => t.reindex τ) h) =
    (fiber θ B U f p E F hF G hG s a h).reindex (restrictSubstitution (θ.reindex p) τ) := by
  exact (congrArg (E.extendAlong F hF (G.reindex (restrictInclusion θ)) (hG.reindex _)
    (restrictSubstitution (θ.reindex p) τ ≫ target θ B p a))
      (genericFiberPartialIntro_reindex f (target θ B p a) (faceSection θ B U f p s)
        (faceSection_image θ B U f p s a h) (restrictSubstitution (θ.reindex p) τ))).trans
    (E.extendAlong_reindex F hF (G.reindex (restrictInclusion θ)) (hG.reindex _)
      (target θ B p a) (genericFiberPartialIntro f (target θ B p a) (faceSection θ B U f p s)
        (faceSection_image θ B U f p s a h)) (restrictSubstitution (θ.reindex p) τ))

section Assembly
variable (E : HomotopyEquivalence f) (F : Filling U) (hF : F.Lawful)
  (G : Filling B) (hG : G.Lawful) {χ : Cofibration Ω}
  (s : PartialSection (pulledCompatible θ B U f p) χ) (a : Term (reindex B p))
  (h : s.map (compatibleUnglue (θ.reindex p) (reindex B p) (reindex U (restrictSubstitution θ p))
    (Functor.whiskerLeft (restrictSubstitution θ p).mapElements f)) = PartialSection.ofTerm χ a)

theorem correctionCompatible :
    (restrictedPathTube (θ.reindex p) a
      (Term.map (Functor.whiskerLeft (restrictSubstitution θ p).mapElements f)
        (extendedFace θ B U f p E F hF G hG s a h))
      (extensionPath θ B U f p E F hF G hG s a h)).Compatible
        (PartialSection.ofTerm (χ.reindex (projection (interval Ω)))
          (a.reindex (projection (interval Ω)))) := by
  intro x ht hc
  rcases x with @⟨I,⟨γ,r⟩⟩
  exact E.extendAlong_path_boundary F hF (G.reindex (restrictInclusion θ)) (hG.reindex _)
    (target θ B p a) (faceSection θ B U f p s) (faceSection_image θ B U f p s a h)
    ((restrictContext (θ.reindex p)).elementsMk I ⟨γ,ht⟩) hc r

noncomputable def corrected : Term (reindex B p) :=
  correctAmbient (G.reindex p) (θ.reindex p) χ a
    (Term.map (Functor.whiskerLeft (restrictSubstitution θ p).mapElements f)
      (extendedFace θ B U f p E F hF G hG s a h))
    (extensionPath θ B U f p E F hF G hG s a h)
    (correctionCompatible θ B U f p E F hF G hG s a h)

theorem corrected_face :
    Term.map (Functor.whiskerLeft (restrictSubstitution θ p).mapElements f)
      (extendedFace θ B U f p E F hF G hG s a h) =
    (corrected θ B U f p E F hF G hG s a h).reindex (restrictInclusion (θ.reindex p)) := by
  apply Term.ext
  intro x
  exact (correctAmbient_face (G.reindex p) (hG.reindex p) (θ.reindex p) χ a _ _
    (correctionCompatible θ B U f p E F hF G hG s a h)
      ((restrictInclusion (θ.reindex p)).mapElements.obj x) x.val.property).symm

noncomputable def extendSection : Term (pulledCompatible θ B U f p) :=
  compatibleIntro (θ.reindex p) (reindex B p) (reindex U (restrictSubstitution θ p))
    (Functor.whiskerLeft (restrictSubstitution θ p).mapElements f)
    (extendedFace θ B U f p E F hF G hG s a h)
    (corrected θ B U f p E F hF G hG s a h)
    (corrected_face θ B U f p E F hF G hG s a h)

theorem extendSection_boundary (x : Ω.Elements) (hx : χ.full x) :
    (extendSection θ B U f p E F hF G hG s a h).val x = s.val x hx := by
  apply CompatibleElement.ext
  · exact (correctAmbient_fixed (G.reindex p) (hG.reindex p) (θ.reindex p) χ a _ _
      (correctionCompatible θ B U f p E F hF G hG s a h) x hx).trans
        (congrArg (fun t => t.val x hx) h).symm
  · intro y k hy
    have he := extendedFace_boundary θ B U f p E F hF G hG s a h
      (faceObj (θ.reindex p) y hy) (χ.full_natural k hx)
    have hs := congrArg (fun z => z.face (𝟙 _) hy) (s.property k hx)
    change (s.val x hx).face (k ≫ 𝟙 _) hy = (s.val y _).face (𝟙 _) hy at hs
    exact he.trans (by
      change (s.val y _).face (𝟙 _) hy = (s.val x hx).face k hy
      simpa only [Category.comp_id] using hs.symm)

theorem extendedFace_reindex {Λ : Context.{u}} (τ : Λ ⟶ Ω) :
    extendedFace θ B U f (τ ≫ p) E F hF G hG (substitutePartial θ B U f p τ s) (a.reindex τ)
      (congrArg (fun t => t.reindex τ) h) =
    (extendedFace θ B U f p E F hF G hG s a h).reindex (restrictSubstitution (θ.reindex p) τ) :=
  congrArg (genericFiberFst f (target θ B (τ ≫ p) (a.reindex τ)))
    (fiber_reindex θ B U f p E F hF G hG s a h τ)

theorem correctionTube_reindex {Λ : Context.{u}} (τ : Λ ⟶ Ω) :
    restrictedPathTube (θ.reindex (τ ≫ p)) (a.reindex τ)
      (Term.map (Functor.whiskerLeft (restrictSubstitution θ (τ ≫ p)).mapElements f)
        (extendedFace θ B U f (τ ≫ p) E F hF G hG (substitutePartial θ B U f p τ s) (a.reindex τ)
          (congrArg (fun t => t.reindex τ) h)))
      (extensionPath θ B U f (τ ≫ p) E F hF G hG (substitutePartial θ B U f p τ s) (a.reindex τ)
        (congrArg (fun t => t.reindex τ) h)) =
    (restrictedPathTube (θ.reindex p) a
      (Term.map (Functor.whiskerLeft (restrictSubstitution θ p).mapElements f)
        (extendedFace θ B U f p E F hF G hG s a h))
      (extensionPath θ B U f p E F hF G hG s a h)).reindex (liftSub (interval Ω) τ) := by
  have hp := (congrArg (fun z => pathApp (homogeneousReverse
    (genericFiberPath f (target θ B (τ ≫ p) (a.reindex τ)) z)))
      (fiber_reindex θ B U f p E F hF G hG s a h τ)).trans
        (genericFiberReverse_reindex f (target θ B p a) (fiber θ B U f p E F hF G hG s a h)
          (restrictSubstitution (θ.reindex p) τ))
  apply PartialSection.ext
  intro x hx
  exact congrArg (fun t => t.val
    ((total (interval (restrictContext (θ.reindex (τ ≫ p))))).elementsMk x.obj
      ⟨⟨x.val.1,hx⟩,x.val.2⟩)) hp

noncomputable def correctionInput :
    OpenBox (reindex (reindex B p) (projection (interval Ω))) ((θ.reindex p).join χ) :=
  correctionBox (θ.reindex p) χ a
    (Term.map (Functor.whiskerLeft (restrictSubstitution θ p).mapElements f)
      (extendedFace θ B U f p E F hF G hG s a h))
    (extensionPath θ B U f p E F hF G hG s a h)
    (correctionCompatible θ B U f p E F hF G hG s a h)

theorem correctionInput_reindex {Λ : Context.{u}} (τ : Λ ⟶ Ω) :
    correctionInput θ B U f (τ ≫ p) E F hF G hG (substitutePartial θ B U f p τ s) (a.reindex τ)
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
    let t₁ := restrictedPathTube (θ.reindex (τ ≫ p)) (a.reindex τ)
      (Term.map (Functor.whiskerLeft (restrictSubstitution θ (τ ≫ p)).mapElements f)
        (extendedFace θ B U f (τ ≫ p) E F hF G hG (substitutePartial θ B U f p τ s) (a.reindex τ)
          (congrArg (fun t => t.reindex τ) h)))
      (extensionPath θ B U f (τ ≫ p) E F hF G hG (substitutePartial θ B U f p τ s) (a.reindex τ)
        (congrArg (fun t => t.reindex τ) h))
    let c₀ := PartialSection.ofTerm (χ.reindex (projection (interval Ω))) (a.reindex (projection (interval Ω)))
    let c₁ := PartialSection.ofTerm ((χ.reindex τ).reindex (projection (interval Λ)))
      ((a.reindex τ).reindex (projection (interval Λ)))
    change glueValue t₁ c₁ x hx = glueValue t₀ c₀ ((liftSub (interval Ω) τ).mapElements.obj x) hx
    by_cases hp : ((θ.reindex (τ ≫ p)).reindex (projection (interval Λ))).full x
    · exact (glueValue_left t₁ c₁ x hx hp).trans
        ((congrArg (fun t => t.val x hp) ht).trans
          (glueValue_left t₀ c₀ ((liftSub (interval Ω) τ).mapElements.obj x) hx hp).symm)
    · have hp₀ : ¬ ((θ.reindex p).reindex (projection (interval Ω))).full
          ((liftSub (interval Ω) τ).mapElements.obj x) := hp
      simp only [glueValue, dite_eq_right hp, dite_eq_right hp₀]
      rfl
  · rfl

theorem corrected_reindex {Λ : Context.{u}} (τ : Λ ⟶ Ω) :
    corrected θ B U f (τ ≫ p) E F hF G hG (substitutePartial θ B U f p τ s) (a.reindex τ)
      (congrArg (fun t => t.reindex τ) h) =
    (corrected θ B U f p E F hF G hG s a h).reindex τ :=
  (congrArg ((G.reindex (τ ≫ p)).hcomp (((θ.reindex p).join χ).reindex τ))
    (correctionInput_reindex θ B U f p E F hF G hG s a h τ)).trans
      (Filling.hcomp_reindex (hG.reindex p) ((θ.reindex p).join χ)
        (correctionInput θ B U f p E F hF G hG s a h) τ)

theorem extendSection_reindex {Λ : Context.{u}} (τ : Λ ⟶ Ω) :
    extendSection θ B U f (τ ≫ p) E F hF G hG (substitutePartial θ B U f p τ s) (a.reindex τ)
      (congrArg (fun t => t.reindex τ) h) =
    Term.map (compatibleReindexMap (θ.reindex p) (reindex B p) (reindex U (restrictSubstitution θ p))
      (Functor.whiskerLeft (restrictSubstitution θ p).mapElements f) τ)
      ((extendSection θ B U f p E F hF G hG s a h).reindex τ) := by
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


section InputSubstitution
variable {Ξ' : Context.{u}} (σ : Ξ' ⟶ Ξ) (q : Ω ⟶ Ξ')
  (E : HomotopyEquivalence f) (F : Filling U) (hF : F.Lawful)
  (G : Filling B) (hG : G.Lawful) {χ : Cofibration Ω}
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

end Glue

end Presheaf

end SquareKit.Cubical
