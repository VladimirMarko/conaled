import SquareKit.CoGrothendieckMap
import SquareKit.EquivalenceSquare

set_option autoImplicit false

/-! Heterogeneous maps between native CoGrothendieck totals. -/

open CategoryTheory Opposite Bicategory
open CategoryTheory.Pseudofunctor.CoGrothendieck CategoryTheory.Functor
open SquareKit.CoGrothendieckMap

namespace SquareKit.CoGrothendieckTransport

universe u v a b c d
variable {S : Type u} [Category.{v} S]
variable {F : LocallyDiscrete Sᵒᵖ ⥤ᵖ Cat.{b,a}}
variable {G : LocallyDiscrete Sᵒᵖ ⥤ᵖ Cat.{d,c}}

/-- Compatibility of ordinary fibre functors with substitution, allowing independent universes. -/
structure Comparison (E : ∀ s : S, F.obj ⟨op s⟩ ⥤ G.obj ⟨op s⟩) where
  naturality {r s : S} (f : r ⟶ s) :
    (F.map f.op.toLoc).toFunctor ⋙ E r ≅ E s ⋙ (G.map f.op.toLoc).toFunctor
  naturality_id (s : S) (x : F.obj ⟨op s⟩) :
    (E s).map ((F.mapId ⟨op s⟩).inv.toNatTrans.app x) ≫ (naturality (𝟙 s)).hom.app x =
      (G.mapId ⟨op s⟩).inv.toNatTrans.app ((E s).obj x)
  naturality_comp {r s q : S} (f : r ⟶ s) (g : s ⟶ q) (x : F.obj ⟨op q⟩) :
    (E r).map ((F.mapComp g.op.toLoc f.op.toLoc).inv.toNatTrans.app x) ≫
        (naturality (f ≫ g)).hom.app x =
      (naturality f).hom.app ((F.map g.op.toLoc).toFunctor.obj x) ≫
        (G.map f.op.toLoc).toFunctor.map ((naturality g).hom.app x) ≫
        (G.mapComp g.op.toLoc f.op.toLoc).inv.toNatTrans.app ((E q).obj x)

set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true

variable {E : ∀ s : S, F.obj ⟨op s⟩ ⥤ G.obj ⟨op s⟩} (α : Comparison E)

/-- Apply compatible fibre functors to all native total arrows. -/
def map : Pseudofunctor.CoGrothendieck F ⥤ Pseudofunctor.CoGrothendieck G where
  obj x := ⟨x.base, (E x.base).obj x.fiber⟩
  map {x y} f := ⟨f.base, (E x.base).map f.fiber ≫ (α.naturality f.base).hom.app y.fiber⟩
  map_id x := by
    apply Hom.ext _ _ (by rfl)
    dsimp
    simpa using α.naturality_id x.base x.fiber
  map_comp {x y z} f g := by
    apply Hom.ext _ _ (by rfl)
    dsimp
    simp only [Functor.map_comp, Category.assoc, Category.comp_id]
    rw [α.naturality_comp f.base g.base z.fiber]
    have hn := (α.naturality f.base).hom.naturality g.fiber
    dsimp at hn
    simp only [reassoc_of% hn]

@[simp] theorem map_base {x y : Pseudofunctor.CoGrothendieck F} (f : x ⟶ y) :
    ((map α).map f).base = f.base := rfl

@[simp] theorem map_fiber {x y : Pseudofunctor.CoGrothendieck F} (f : x ⟶ y) :
    ((map α).map f).fiber =
      (E x.base).map f.fiber ≫ (α.naturality f.base).hom.app y.fiber := rfl

@[simp] theorem map_comp_forget : map α ⋙ forget G = forget F := rfl

/-- Vertical arrows retain their original fibre functor action. -/
theorem map_ι_map (s : S) {x y : F.obj ⟨op s⟩} (f : x ⟶ y) :
    (map α).map ((ι F s).map f) = (ι G s).map ((E s).map f) := by
  apply Hom.ext _ _ (by rfl)
  dsimp [map, ι]
  simp only [Functor.map_comp, Category.assoc, Category.comp_id]
  rw [α.naturality_id]

/-- Full faithfulness is recovered separately over each unchanged base arrow. -/
def fullyFaithful (hE : ∀ s, (E s).FullyFaithful) : (map α).FullyFaithful where
  preimage {x y} f := ⟨f.base, (hE x.base).preimage
    (f.fiber ≫ (α.naturality f.base).inv.app y.fiber)⟩
  map_preimage {x y} f := by
    apply Hom.ext _ _ (by rfl)
    dsimp [map]
    simp
  preimage_map {x y} f := by
    apply Hom.ext _ _ (by rfl)
    dsimp [map]
    simp

@[simp] theorem fullyFaithful_preimage_base (hE : ∀ s, (E s).FullyFaithful)
    {x y : Pseudofunctor.CoGrothendieck F} (f : (map α).obj x ⟶ (map α).obj y) :
    ((fullyFaithful α hE).preimage f).base = f.base := rfl

/-- Native fibre maps over a fixed base arrow are recovered in both directions. -/
def fiberHomEquiv (hE : ∀ s, (E s).FullyFaithful) {r s : S} (f : r ⟶ s)
    (x : F.obj ⟨op r⟩) (y : F.obj ⟨op s⟩) :
    (x ⟶ (F.map f.op.toLoc).toFunctor.obj y) ≃
      ((E r).obj x ⟶ (G.map f.op.toLoc).toFunctor.obj ((E s).obj y)) where
  toFun k := (E r).map k ≫ (α.naturality f).hom.app y
  invFun k := (hE r).preimage (k ≫ (α.naturality f).inv.app y)
  left_inv k := by simp
  right_inv k := by simp

/-- A strong comparison sends each canonical cartesian lift to a cartesian arrow. -/
theorem map_cartesianLift (α : Comparison E) {R T : S} (a : F.obj ⟨op T⟩) (f : R ⟶ T) :
    (forget G).IsCartesian f ((map α).map (cartesianLift a f)) := by
  have : IsIso (((map α).map (cartesianLift a f)).fiber) := by
    change IsIso ((E R).map (𝟙 _) ≫
    (α.naturality f).hom.app a)
    rw [Functor.map_id, Category.id_comp]
    change IsIso ((α.naturality f).hom.app a)
    infer_instance
  exact cartesian_of_isIso_fiber (F := G) ((map α).map (cartesianLift a f))
/-- Strong naturality preserves arbitrary cartesian arrows, not only the selected lifts. -/
theorem map_cartesian (α : Comparison E) {x y : Pseudofunctor.CoGrothendieck F}
    (f : x ⟶ y) [(forget F).IsCartesian f.base f] :
    (forget G).IsCartesian f.base ((map α).map f) := by
  let T : BasedFunctor (BasedCategory.ofFunctor (forget F))
      (BasedCategory.ofFunctor (forget G)) := ⟨map α, rfl⟩
  have hcan : (forget F).IsCartesian f.base (cartesianLift y.fiber f.base) :=
    (isStronglyCartesian_homCartesianLift y.fiber f.base).isCartesian_of_isStronglyCartesian
  have htarget : (forget G).IsCartesian f.base (T.map (cartesianLift y.fiber f.base)) :=
    map_cartesianLift α y.fiber f.base
  exact T.map_isCartesian_of_map_isCartesian f.base (cartesianLift y.fiber f.base) f
    (hφ := hcan) (hψ := ‹(forget F).IsCartesian f.base f›) (hT := htarget)


theorem map_isHomLift {r s : S} (f : r ⟶ s)
    {x y : Pseudofunctor.CoGrothendieck F} (φ : x ⟶ y) [(forget F).IsHomLift f φ] :
    (forget G).IsHomLift f ((map α).map φ) := by
  cases (inferInstance : (forget F).IsHomLift f φ)
  exact IsHomLift.map (forget G) ((map α).map φ)

theorem isHomLift_of_map {r s : S} (f : r ⟶ s)
    {x y : Pseudofunctor.CoGrothendieck F} (φ : x ⟶ y)
    [(forget G).IsHomLift f ((map α).map φ)] : (forget F).IsHomLift f φ := by
  exact IsHomLift.of_fac (forget F) f φ
    (IsHomLift.domain_eq (forget G) f ((map α).map φ))
    (IsHomLift.codomain_eq (forget G) f ((map α).map φ))
    (IsHomLift.fac (forget G) f ((map α).map φ))

theorem cartesian_of_map (hE : ∀ s, (E s).FullyFaithful) {x y : Pseudofunctor.CoGrothendieck F} (f : x ⟶ y)
    [(forget G).IsCartesian f.base ((map α).map f)] : (forget F).IsCartesian f.base f where
  toIsHomLift := IsHomLift.map (forget F) f
  universal_property {z} g hg := by
    let T := map α
    let ff := fullyFaithful α hE
    have : (forget G).IsHomLift f.base (T.map g) := map_isHomLift α _ g
    obtain ⟨χ, ⟨hχ, hfac⟩, huniq⟩ :=
      IsCartesian.universal_property (p := forget G) (f := f.base) (φ := T.map f) (T.map g)
    have := hχ
    have hm : T.map (ff.preimage χ) = χ := ff.map_preimage χ
    have : (forget G).IsHomLift (𝟙 x.base) (T.map (ff.preimage χ)) := hm.symm ▸ hχ
    refine ⟨ff.preimage χ, ⟨isHomLift_of_map α _ _, ?_⟩, ?_⟩
    · apply ff.map_injective
      rw [T.map_comp, hm, hfac]
    · rintro ψ ⟨hψ, hψfac⟩
      apply ff.map_injective
      rw [hm]
      apply huniq
      refine ⟨map_isHomLift α _ ψ, ?_⟩
      rw [← T.map_comp, hψfac]

section Equivalence
variable (e : ∀ s : S, F.obj ⟨op s⟩ ≌ G.obj ⟨op s⟩)
variable (α : Comparison (fun s => (e s).functor))

/-- The inverse substitution comparison derived from the forward square. -/
noncomputable def inverseNaturality {r s : S} (f : r ⟶ s) :
    (G.map f.op.toLoc).toFunctor ⋙ (e r).inverse ≅
      (e s).inverse ⋙ (F.map f.op.toLoc).toFunctor :=
  inverseSquareAcross (e s) (e r) (G.map f.op.toLoc).toFunctor
    (F.map f.op.toLoc).toFunctor (α.naturality f).symm

/-- Compatibility with the original counit characterizes the inverse comparison. -/
@[reassoc] theorem inverseNaturality_counit {r s : S} (f : r ⟶ s)
    (x : G.obj ⟨op s⟩) :
    (e r).counitIso.inv.app ((G.map f.op.toLoc).toFunctor.obj x) ≫
        (e r).functor.map ((inverseNaturality e α f).hom.app x) =
      (G.map f.op.toLoc).toFunctor.map ((e s).counitIso.inv.app x) ≫
        (α.naturality f).inv.app ((e s).inverse.obj x) :=
  inverseSquareAcross_spec (e s) (e r) _ _ _ x

/-- Compatibility with the original unit is derived from the equivalence triangles. -/
theorem inverseNaturality_unit {r s : S} (f : r ⟶ s)
    (x : F.obj ⟨op s⟩) :
    (e r).inverse.map ((α.naturality f).inv.app x) ≫
        (e r).unitIso.inv.app ((F.map f.op.toLoc).toFunctor.obj x) =
      (inverseNaturality e α f).hom.app ((e s).functor.obj x) ≫
        (F.map f.op.toLoc).toFunctor.map ((e s).unitIso.inv.app x) :=
  inverseSquareAcross_canonical (e s) (e r) (G.map f.op.toLoc).toFunctor
    (F.map f.op.toLoc).toFunctor (α.naturality f).symm x

set_option backward.isDefEq.respectTransparency.types false in
/-- Inverse substitution comparisons preserve the selected identity constraints. -/
theorem inverseNaturality_id (s : S) (x : G.obj ⟨op s⟩) :
    (e s).inverse.map ((G.mapId ⟨op s⟩).inv.toNatTrans.app x) ≫
      (inverseNaturality e α (𝟙 s)).hom.app x =
      (F.mapId ⟨op s⟩).inv.toNatTrans.app ((e s).inverse.obj x) := by
  apply (e s).functor.map_injective
  apply (cancel_epi ((e s).counitIso.inv.app x)).mp
  rw [Functor.map_comp]
  have hn := (e s).counitIso.inv.naturality ((G.mapId ⟨op s⟩).inv.toNatTrans.app x)
  dsimp at hn
  rw [← Category.assoc, ← hn, Category.assoc]
  have hc := inverseNaturality_counit e α (𝟙 s) x
  simp only [op_id, Quiver.Hom.id_toLoc] at hc ⊢
  rw [hc]
  have hn' := (G.mapId ⟨op s⟩).inv.toNatTrans.naturality ((e s).counitIso.inv.app x)
  dsimp at hn'
  rw [← Category.assoc, ← hn', Category.assoc]
  rw [← α.naturality_id s ((e s).inverse.obj x)]
  simp only [Category.assoc, Iso.hom_inv_id_app]
  simp only [op_id, Quiver.Hom.id_toLoc, Functor.comp_obj, Category.comp_id]

/-- Inverse substitution comparisons preserve composition. -/
theorem inverseNaturality_comp {r s q : S} (f : r ⟶ s) (g : s ⟶ q)
    (x : G.obj ⟨op q⟩) :
    (e r).inverse.map ((G.mapComp g.op.toLoc f.op.toLoc).inv.toNatTrans.app x) ≫
        (inverseNaturality e α (f ≫ g)).hom.app x =
      (inverseNaturality e α f).hom.app ((G.map g.op.toLoc).toFunctor.obj x) ≫
        (F.map f.op.toLoc).toFunctor.map ((inverseNaturality e α g).hom.app x) ≫
        (F.mapComp g.op.toLoc f.op.toLoc).inv.toNatTrans.app ((e q).inverse.obj x) := by
  symm
  apply inverseSquareAcross_comp (e q) (e s) (e r)
    (G.map g.op.toLoc).toFunctor (G.map f.op.toLoc).toFunctor
    (G.map (f ≫ g).op.toLoc).toFunctor
    (F.map g.op.toLoc).toFunctor (F.map f.op.toLoc).toFunctor
    (F.map (f ≫ g).op.toLoc).toFunctor
    (α.naturality g).symm (α.naturality f).symm (α.naturality (f ≫ g)).symm
    (Cat.Hom.toNatIso (G.mapComp g.op.toLoc f.op.toLoc)).symm
    (Cat.Hom.toNatIso (F.mapComp g.op.toLoc f.op.toLoc)).symm
  intro y
  dsimp
  apply (cancel_mono ((α.naturality (f ≫ g)).hom.app y)).mp
  simp only [Category.assoc, Iso.inv_hom_id_app]
  rw [α.naturality_comp]
  simp only [Iso.inv_hom_id_app_assoc]
  rw [← Functor.map_comp_assoc]
  simp

/-- Coherence of the inverse is derived from the forward comparison and equivalence laws. -/
noncomputable def inverseComparison : Comparison (fun s => (e s).inverse) where
  naturality := inverseNaturality e α
  naturality_id := inverseNaturality_id e α
  naturality_comp := inverseNaturality_comp e α

/-- The chosen native inverse object keeps its context. -/
def inverseObj (x : Pseudofunctor.CoGrothendieck G) : Pseudofunctor.CoGrothendieck F :=
  ⟨x.base, (e x.base).inverse.obj x.fiber⟩

/-- The original fibre counit, included as a vertical total isomorphism. -/
def counitApp (x : Pseudofunctor.CoGrothendieck G) :
    (map α).obj (inverseObj e x) ≅ x :=
  (ι G x.base).mapIso ((e x.base).counitIso.app x.fiber)

/-- The inverse on arrows is the fixed-base preimage of counit conjugation. -/
def inverse : Pseudofunctor.CoGrothendieck G ⥤ Pseudofunctor.CoGrothendieck F where
  obj := inverseObj e
  map {x y} f := (fullyFaithful α (fun s => (e s).fullyFaithfulFunctor)).preimage
    ((counitApp e α x).hom ≫ f ≫ (counitApp e α y).inv)
  map_id x := by
    apply (fullyFaithful α (fun s => (e s).fullyFaithfulFunctor)).map_injective
    simp
  map_comp f g := by
    apply (fullyFaithful α (fun s => (e s).fullyFaithfulFunctor)).map_injective
    simp

@[simp] theorem inverse_map_base {x y : Pseudofunctor.CoGrothendieck G} (f : x ⟶ y) :
    ((inverse e α).map f).base = f.base := by
  simp [inverse, fullyFaithful, counitApp, ι]
  exact Category.id_comp _

@[simp] theorem inverse_comp_forget : inverse e α ⋙ forget F = forget G := by
  apply Functor.ext
  · simp
  · intro
    rfl

/-- The original counits are natural for the derived inverse functor. -/
def counitIso : inverse e α ⋙ map α ≅ 𝟭 _ :=
  NatIso.ofComponents (counitApp e α) (fun f => by
    change (map α).map ((inverse e α).map f) ≫ _ = _
    simp [inverse])

/-- The derived inverse comparison is compatible with the original total counit. -/
theorem inverseComparison_counit_naturality {x y : Pseudofunctor.CoGrothendieck G} (f : x ⟶ y) :
    (map α).map ((map (inverseComparison e α)).map f) ≫ (counitApp e α y).hom =
      (counitApp e α x).hom ≫ f := by
  rcases x with ⟨r, A⟩
  rcases y with ⟨s, B⟩
  rcases f with ⟨f, k⟩
  apply Hom.ext _ _ (by simp [map, counitApp, ι])
  dsimp [map, counitApp, ι]
  simp [G.mapComp_id_left_inv_app, G.mapComp_id_right_inv_app,
    Strict.leftUnitor_eqToIso, Strict.rightUnitor_eqToIso,
    PrelaxFunctor.map₂_eqToHom]
  simp only [← Functor.map_comp_assoc, ← Cat.Hom.toNatIso_inv, ← Cat.Hom.toNatIso_hom,
    Iso.inv_hom_id_app]
  simp only [inverseComparison]
  simp only [inverseNaturality_counit_assoc]
  simp only [Iso.inv_hom_id_app_assoc, ← Functor.map_comp_assoc]
  simp only [← NatTrans.naturality_assoc]
  dsimp +instances only [map]
  simp only [Functor.map_id, Functor.id_obj, Functor.id_map, Category.id_comp]
  have he := congrArg (fun q => (G.map q).toFunctor.obj B) (Strict.id_comp f.op.toLoc).symm
  have hn := (Cat.Hom.toNatIso (G.mapId ⟨op r⟩)).hom.naturality (eqToHom he)
  dsimp only [Functor.id_map] at hn
  simp only [eqToHom_map] at hn
  rw [hn]
  simp

/-- The chosen preimage inverse agrees with the inverse substitution comparison on all maps. -/
theorem inverse_eq_map : inverse e α = map (inverseComparison e α) := by
  refine Functor.ext (h_obj := fun _ => rfl) ?_
  intro x y f
  simp only [eqToHom_refl, Category.id_comp, Category.comp_id]
  apply (fullyFaithful α (fun s => (e s).fullyFaithfulFunctor)).map_injective
  apply (cancel_mono (counitApp e α y).hom).mp
  rw [inverseComparison_counit_naturality]
  exact (counitIso e α).hom.naturality f

/-- The inverse arrow formula retains the actual base map and its arbitrary fibre map. -/
theorem inverse_map {x y : Pseudofunctor.CoGrothendieck G} (f : x ⟶ y) :
    (inverse e α).map f =
      ⟨f.base, (e x.base).inverse.map f.fiber ≫
        (inverseNaturality e α f.base).hom.app y.fiber⟩ := by
  have h := Functor.congr_hom (inverse_eq_map e α) f
  simpa [map, inverseComparison] using h

/-- Recovery is determined by full faithfulness and the original fibre counit. -/
def unitIso : 𝟭 _ ≅ map α ⋙ inverse e α :=
  NatIso.ofComponents (fun x =>
    (fullyFaithful α (fun s => (e s).fullyFaithfulFunctor)).preimageIso
      ((counitApp e α ((map α).obj x)).symm)) (fun f => by
    apply (fullyFaithful α (fun s => (e s).fullyFaithfulFunctor)).map_injective
    simp [inverse])

/-- Total recovery retains the original fibre unit, including its identity comparison. -/
theorem unitIso_hom_app (x : Pseudofunctor.CoGrothendieck F) :
    (unitIso e α).hom.app x = (ι F x.base).map ((e x.base).unitIso.hom.app x.fiber) := by
  apply (fullyFaithful α (fun s => (e s).fullyFaithfulFunctor)).map_injective
  change (map α).map ((fullyFaithful α (fun s => (e s).fullyFaithfulFunctor)).preimage _) = _
  rw [Functor.FullyFaithful.map_preimage, map_ι_map]
  change (ι G x.base).map ((e x.base).counitIso.inv.app _) = _
  exact congrArg ((ι G x.base).map) ((e x.base).counitInv_app_functor x.fiber)

/-- The original fibre counit is retained without adjustment. -/
theorem counitIso_hom_app (x : Pseudofunctor.CoGrothendieck G) :
    (counitIso e α).hom.app x = (ι G x.base).map ((e x.base).counitIso.hom.app x.fiber) := rfl

theorem unitIso_app (x : Pseudofunctor.CoGrothendieck F) :
    (unitIso e α).app x = (ι F x.base).mapIso ((e x.base).unitIso.app x.fiber) :=
  Iso.ext (unitIso_hom_app e α x)

theorem counitIso_app (x : Pseudofunctor.CoGrothendieck G) :
    (counitIso e α).app x = (ι G x.base).mapIso ((e x.base).counitIso.app x.fiber) := rfl

@[simp] theorem counitIso_hom_base (x : Pseudofunctor.CoGrothendieck G) :
    ((counitIso e α).hom.app x).base = 𝟙 x.base := rfl

@[simp] theorem counitIso_inv_base (x : Pseudofunctor.CoGrothendieck G) :
    ((counitIso e α).inv.app x).base = 𝟙 x.base := rfl

@[simp] theorem unitIso_hom_base (x : Pseudofunctor.CoGrothendieck F) :
    ((unitIso e α).hom.app x).base = 𝟙 x.base := rfl

@[simp] theorem unitIso_inv_base (x : Pseudofunctor.CoGrothendieck F) :
    ((unitIso e α).inv.app x).base = 𝟙 x.base := rfl

/-- Fibre equivalences yield a total equivalence with the specified native inverse objects. -/
def equivalence : Pseudofunctor.CoGrothendieck F ≌ Pseudofunctor.CoGrothendieck G where
  functor := map α
  inverse := inverse e α
  unitIso := unitIso e α
  counitIso := counitIso e α
  functor_unitIso_comp x := by
    simp [unitIso, counitIso]

@[simp] theorem equivalence_unitIso_hom_base (x : Pseudofunctor.CoGrothendieck F) :
    ((equivalence e α).unitIso.hom.app x).base = 𝟙 x.base := rfl

@[simp] theorem equivalence_unitIso_inv_base (x : Pseudofunctor.CoGrothendieck F) :
    ((equivalence e α).unitIso.inv.app x).base = 𝟙 x.base := rfl

@[simp] theorem equivalence_counitIso_hom_base (x : Pseudofunctor.CoGrothendieck G) :
    ((equivalence e α).counitIso.hom.app x).base = 𝟙 x.base := rfl

@[simp] theorem equivalence_counitIso_inv_base (x : Pseudofunctor.CoGrothendieck G) :
    ((equivalence e α).counitIso.inv.app x).base = 𝟙 x.base := rfl

/-- The native inverse preserves every cartesian arrow. -/
theorem inverse_cartesian {x y : Pseudofunctor.CoGrothendieck G}
    (f : x ⟶ y) [(forget G).IsCartesian f.base f] :
    (forget F).IsCartesian f.base ((inverse e α).map f) := by
  have hx : (forget G).IsHomLift (𝟙 x.base) (counitApp e α x).hom :=
    IsHomLift.map (forget G) (counitApp e α x).hom
  have hy : (forget G).IsHomLift (𝟙 y.base) (counitApp e α y).symm.hom :=
    IsHomLift.map (forget G) (counitApp e α y).inv
  have hc : (forget G).IsCartesian f.base
      ((counitApp e α x).hom ≫ f ≫ (counitApp e α y).inv) := by
    have : (forget G).IsCartesian f.base (f ≫ (counitApp e α y).inv) :=
      IsCartesian.of_comp_iso (forget G) f.base f (counitApp e α y).symm
    exact IsCartesian.of_iso_comp (forget G) f.base _ (counitApp e α x)
  have hm : (map α).map ((inverse e α).map f) =
      (counitApp e α x).hom ≫ f ≫ (counitApp e α y).inv := by
    simp [inverse]
  have : (forget G).IsCartesian (((inverse e α).map f).base)
      ((map α).map ((inverse e α).map f)) := by
    rw [inverse_map_base, hm]
    exact hc
  simpa only [inverse_map_base] using
    cartesian_of_map α (fun s => (e s).fullyFaithfulFunctor) ((inverse e α).map f)

end Equivalence
end SquareKit.CoGrothendieckTransport
