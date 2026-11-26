import SquareKit.Internal.Cubical.ChosenInverseHomotopies
import SquareKit.Internal.Cubical.NativeUaEquivalence
import SquareKit.Internal.Cubical.HomotopyLevels
import SquareKit.Internal.Cubical.SigmaPaths
import SquareKit.Internal.Cubical.NativeUnivalenceTotals
import SquareKit.Internal.Cubical.ContractibleTotals
import SquareKit.Internal.Cubical.UniverseFilling

/-! Native dependent-total equivalences used by structured identity. -/
set_option autoImplicit false
set_option warningAsError true
namespace SquareKit.Cubical.Presheaf
open CategoryTheory Glue
universe u
namespace DependentTotalEquivalence
section BackwardTotal
variable {Γ Δ : Context.{u}} {B : Family Γ} {C : Family (total B)}
  (FC : Filling C) (hFC : FC.Lawful) (σ : total (interval Δ) ⟶ Γ) (φ : Cofibration Δ)
  (t : PartialSection (reindex (sigma B C) σ) (φ.reindex (projection (interval Δ))))
  (b : Term (reindex (sigma B C) (endpointSub Δ true ≫ σ)))
  (hb : ∀ x hx, t.val ((endpointSub Δ true).mapElements.obj x) hx = b.val x)
  (a : Term (reindex B σ)) (ha : a.reindex (endpointSub Δ true) = sigmaFst (B := reindex C (liftSub B (endpointSub Δ true ≫ σ))) b)
  (hat : ∀ x hx, a.val x = (t.val x hx).1)

noncomputable def backwardFieldTube := PartialSection.sigmaSnd
  (B := reindex C (liftSub B σ)) t a hat
noncomputable def backwardFieldCap := Term.sigmaSndOver
  (B := reindex C (liftSub B (endpointSub Δ true ≫ σ))) b
  (a.reindex (endpointSub Δ true)) ha

include hb in
theorem backwardFieldTube_boundary (x : Δ.Elements) (hx : φ.Full x) :
    (backwardFieldTube σ φ t a hat).val ((endpointSub Δ true).mapElements.obj x) hx =
      (backwardFieldCap σ b a ha).val x := by
  apply eq_of_heq
  exact (PartialSection.sigmaSnd_val (B := reindex C (liftSub B σ)) t a hat ((endpointSub Δ true).mapElements.obj x) hx).trans
    ((Sigma.mk.inj (hb x hx)).2.trans (Term.sigmaSndOver_val (B := reindex C (liftSub B (endpointSub Δ true ≫ σ))) b _ ha x).symm)

noncomputable def backwardTotal : Term (reindex (sigma B C) σ) :=
  sigmaIntro (B := reindex C (liftSub B σ)) a
    (IntervalTransport.backwardRelative (FC.reindex (pair σ a)) φ
      (backwardFieldTube σ φ t a hat) (backwardFieldCap σ b a ha)
      (backwardFieldTube_boundary σ φ t b hb a ha hat))

include hFC in
theorem backwardTotal_fills :
    (backwardTotal FC σ φ t b hb a ha hat).reindex (endpointSub Δ true) = b ∧
    ∀ x hx, (backwardTotal FC σ φ t b hb a ha hat).val x = t.val x hx := by
  constructor
  · apply Term.ext
    intro x
    apply Sigma.ext
    · exact congrArg (fun z => z.val x) ha
    · exact (heq_of_eq (congrArg (fun z => z.val x)
        (IntervalTransport.backwardRelative_one (FC.reindex (pair σ a)) (hFC.reindex _) φ
          (backwardFieldTube σ φ t a hat) (backwardFieldCap σ b a ha)
          (backwardFieldTube_boundary σ φ t b hb a ha hat)))).trans
        (Term.sigmaSndOver_val (B := reindex C (liftSub B (endpointSub Δ true ≫ σ))) b _ ha x)
  · intro x hx
    apply Sigma.ext (hat x hx)
    exact (heq_of_eq (IntervalTransport.backwardRelative_boundary
      (FC.reindex (pair σ a)) (hFC.reindex _) φ
      (backwardFieldTube σ φ t a hat) (backwardFieldCap σ b a ha)
      (backwardFieldTube_boundary σ φ t b hb a ha hat) x hx)).trans
      (PartialSection.sigmaSnd_val (B := reindex C (liftSub B σ)) t a hat x hx)
end BackwardTotal

variable {Γ Δ : Context.{u}} {A B : Family Γ} (f : A ⟶ B) (C : Family (total B))

def baseMap : total A ⟶ total B :=
  pair (projection A) (Term.map (Functor.whiskerLeft (projection A).mapElements f) (generic A))

abbrev source := sigma A (reindex C (baseMap f))
abbrev target := sigma B C

def map : source f C ⟶ target C where
  app x := TypeCat.ofHom (fun z => ⟨f.app x z.1, z.2⟩)
  naturality x y g := by
    apply ConcreteCategory.hom_ext
    intro z
    have h := sigmaMap_extendAlong B C g (a := f.app x z.1) (a' := f.app y (A.map g z.1)) (f.naturality_apply g z.1).symm z.2
    exact h.symm

def firstMap : target C ⟶ B where
  app _ := TypeCat.ofHom Sigma.fst
  naturality _ _ _ := rfl

def targetBase : total (target C) ⟶ total B :=
  pair (projection (target C)) (Term.map (Functor.whiskerLeft (projection (target C)).mapElements (firstMap C)) (generic (target C)))

abbrev fiber (σ : Δ ⟶ total (target C)) :=
  reindex (homotopyFiber (Functor.whiskerLeft (projection (target C)).mapElements (map f C))
    (generic (target C))) σ

/-- Project the entire native fiber path, not only its endpoints. -/
def projected (σ : Δ ⟶ total (target C)) (s : Term (fiber f C σ)) :
    Term (reindex (homotopyFiber (Functor.whiskerLeft (projection B).mapElements f)
      (generic B)) (σ ≫ targetBase C)) :=
  genericFiberIntro f (σ ≫ targetBase C)
    (Term.map (Functor.whiskerLeft (σ ≫ projection (target C)).mapElements (firstMap (reindex C (baseMap f)))) (genericFiberFst (map f C) σ s))
    (homogeneousPathMap (Functor.whiskerLeft (σ ≫ projection (target C)).mapElements (firstMap C))
      (genericFiberPath (map f C) σ s))

variable (E : HomotopyEquivalence f) (FA : Filling A) (hFA : FA.Lawful)
  (FB : Filling B) (hFB : FB.Lawful) (σ : Δ ⟶ total (target C))
  {φ : Cofibration Δ} (s : PartialSection (fiber f C σ) φ)

def partialBase : PartialSection
    (reindex (homotopyFiber (Functor.whiskerLeft (projection B).mapElements f)
      (generic B)) (σ ≫ targetBase C)) φ := PartialSection.ofRestricted
  (projected f C (restrictInclusion φ ≫ σ) s.toRestricted)

noncomputable def filledBase := E.extendAlong FA hFA FB hFB (σ ≫ targetBase C)
  (partialBase f C σ s)

noncomputable def sourcePoint := genericFiberFst f (σ ≫ targetBase C)
  (filledBase f C E FA hFA FB hFB σ s)

noncomputable def basePath := genericFiberPath f (σ ≫ targetBase C)
  (filledBase f C E FA hFA FB hFB σ s)

def targetPoint : Term (reindex (target C) (σ ≫ projection (target C))) :=
  Term.reindex (generic (target C)) σ

def tube : PartialSection (reindex (target C) (projection (interval Δ) ≫ σ ≫ projection (target C)))
    (φ.reindex (projection (interval Δ))) :=
  PartialSection.ofRestricted ((pathApp
    (genericFiberPath (map f C) (restrictInclusion φ ≫ σ) s.toRestricted)).reindex
    (restrictedInterval φ))

theorem tube_source (x : Δ.Elements) (hx : φ.Full x) :
    (tube f C σ s).val ((endpointSub Δ true).mapElements.obj x) hx =
      (targetPoint C σ).val x :=
  congrArg (fun t => t.val (faceObj φ x hx)) (pathApp_one
    (genericFiberPath (map f C) (restrictInclusion φ ≫ σ) s.toRestricted))

theorem tube_target (x : Δ.Elements) (hx : φ.Full x) :
    (tube f C σ s).val ((endpointSub Δ false).mapElements.obj x) hx =
      (Term.map (Functor.whiskerLeft (restrictInclusion φ ≫ σ ≫ projection (target C)).mapElements
        (map f C)) (genericFiberFst (map f C) (restrictInclusion φ ≫ σ) s.toRestricted)).val
        (faceObj φ x hx) :=
  congrArg (fun t => t.val (faceObj φ x hx)) (pathApp_zero
    (genericFiberPath (map f C) (restrictInclusion φ ≫ σ) s.toRestricted))

theorem filledBase_on_face :
    Term.reindex (filledBase f C E FA hFA FB hFB σ s) (restrictInclusion φ) =
      projected f C (restrictInclusion φ ≫ σ) s.toRestricted := by
  apply Term.ext
  intro x
  exact E.extendAlong_boundary FA hFA FB hFB (σ ≫ targetBase C)
    (partialBase f C σ s) ((restrictInclusion φ).mapElements.obj x) x.val.property

theorem basePath_on_face :
    Term.reindex (pathApp (basePath f C E FA hFA FB hFB σ s)) (liftSub (interval Δ) (restrictInclusion φ)) =
      pathApp (homogeneousPathMap
        (Functor.whiskerLeft (restrictInclusion φ ≫ σ ≫ projection (target C)).mapElements (firstMap C))
        (genericFiberPath (map f C) (restrictInclusion φ ≫ σ) s.toRestricted)) := by
  have h := congrArg (fun t => pathApp (genericFiberPath f
    (restrictInclusion φ ≫ σ ≫ targetBase C) t)) (filledBase_on_face f C E FA hFA FB hFB σ s)
  exact h.trans (congrArg pathApp (Term.map_iso_roundtrip
    (genericFiberPathIso f (restrictInclusion φ ≫ σ ≫ targetBase C) _).symm _))

theorem basePath_boundary (x : (total (interval Δ)).Elements)
    (hx : (φ.reindex (projection (interval Δ))).Full x) :
    (pathApp (basePath f C E FA hFA FB hFB σ s)).val x = ((tube f C σ s).val x hx).1 := by
  let y := (restrictedInterval φ).mapElements.obj
    ((restrictContext (φ.reindex (projection (interval Δ)))).elementsMk x.obj ⟨x.val,hx⟩)
  exact congrArg (fun t => t.val y) (basePath_on_face f C E FA hFA FB hFB σ s)

noncomputable def totalLine (FC : Filling C) :=
  backwardTotal FC (projection (interval Δ) ≫ σ ≫ projection (target C)) φ
    (tube f C σ s) (targetPoint C σ) (tube_source f C σ s)
    (pathApp (basePath f C E FA hFA FB hFB σ s))
    (pathApp_one (basePath f C E FA hFA FB hFB σ s))
    (basePath_boundary f C E FA hFA FB hFB σ s)

variable (FC : Filling C) (hFC : FC.Lawful)

include hFC in
theorem totalLine_fills :
    (totalLine f C E FA hFA FB hFB σ s FC).reindex (endpointSub Δ true) = targetPoint C σ ∧
    ∀ x hx, (totalLine f C E FA hFA FB hFB σ s FC).val x = (tube f C σ s).val x hx :=
  backwardTotal_fills FC hFC _ _ _ _ _ _ _ _

noncomputable def sourceImage := Term.reindex (totalLine f C E FA hFA FB hFB σ s FC)
  (endpointSub Δ false)

theorem sourceImage_base :
    Term.map (Functor.whiskerLeft (σ ≫ projection (target C)).mapElements f)
      (sourcePoint f C E FA hFA FB hFB σ s) =
      sigmaFst (B := reindex C (liftSub B (σ ≫ projection (target C))))
        (sourceImage f C E FA hFA FB hFB σ s FC) :=
  (pathApp_zero (basePath f C E FA hFA FB hFB σ s)).symm

noncomputable def sourceField := Term.sigmaSndOver
  (B := reindex C (liftSub B (σ ≫ projection (target C))))
  (sourceImage f C E FA hFA FB hFB σ s FC)
  (Term.map (Functor.whiskerLeft (σ ≫ projection (target C)).mapElements f)
    (sourcePoint f C E FA hFA FB hFB σ s))
  (sourceImage_base f C E FA hFA FB hFB σ s FC)

noncomputable def sourceSection : Term (reindex (source f C) (σ ≫ projection (target C))) :=
  sigmaIntro (B := reindex (reindex C (baseMap f)) (liftSub A (σ ≫ projection (target C))))
    (sourcePoint f C E FA hFA FB hFB σ s) (sourceField f C E FA hFA FB hFB σ s FC)

theorem sourceSection_image :
    Term.map (Functor.whiskerLeft (σ ≫ projection (target C)).mapElements (map f C))
      (sourceSection f C E FA hFA FB hFB σ s FC) = sourceImage f C E FA hFA FB hFB σ s FC := by
  apply Term.ext
  intro x
  apply Sigma.ext
  · exact congrArg (fun t => t.val x) (sourceImage_base f C E FA hFA FB hFB σ s FC)
  · exact Term.sigmaSndOver_val _ _ _ x

noncomputable def totalPath : Term (homogeneousPath
    (reindex (target C) (σ ≫ projection (target C)))
    (Term.map (Functor.whiskerLeft (σ ≫ projection (target C)).mapElements (map f C))
      (sourceSection f C E FA hFA FB hFB σ s FC)) (targetPoint C σ)) :=
  pathLam (totalLine f C E FA hFA FB hFB σ s FC)
    (sourceSection_image f C E FA hFA FB hFB σ s FC).symm
    (totalLine_fills f C E FA hFA FB hFB σ s FC hFC).1

noncomputable def extend : Term (fiber f C σ) :=
  genericFiberIntro (map f C) σ (sourceSection f C E FA hFA FB hFB σ s FC)
    (totalPath f C E FA hFA FB hFB σ s FC hFC)

include hFC in
theorem sourceSection_on_face :
    Term.reindex (sourceSection f C E FA hFA FB hFB σ s FC) (restrictInclusion φ) =
      genericFiberFst (map f C) (restrictInclusion φ ≫ σ) s.toRestricted := by
  apply Term.ext
  intro x
  let y := (restrictInclusion φ).mapElements.obj x
  have ha := congrArg Sigma.fst (E.extendAlong_boundary FA hFA FB hFB (σ ≫ targetBase C)
    (partialBase f C σ s) y x.val.property)
  have ht := (totalLine_fills f C E FA hFA FB hFB σ s FC hFC).2
    ((endpointSub Δ false).mapElements.obj y) x.val.property
  have hz := tube_target f C σ s y x.val.property
  apply Sigma.ext
  · exact ha
  · exact (Term.sigmaSndOver_val _ _ _ y).trans (Sigma.mk.inj (ht.trans hz)).2

theorem totalPath_on_face :
    pathApp (homogeneousReindex (totalPath f C E FA hFA FB hFB σ s FC hFC) (restrictInclusion φ)) =
      pathApp (genericFiberPath (map f C) (restrictInclusion φ ≫ σ) s.toRestricted) := by
  apply Term.ext
  intro x
  let y := (liftSub (interval Δ) (restrictInclusion φ)).mapElements.obj x
  exact (totalLine_fills f C E FA hFA FB hFB σ s FC hFC).2 y x.val.1.property

theorem extend_on_face :
    Term.reindex (extend f C E FA hFA FB hFB σ s FC hFC) (restrictInclusion φ) = s.toRestricted :=
  (genericFiberIntro_reindex (map f C) σ (sourceSection f C E FA hFA FB hFB σ s FC)
    (totalPath f C E FA hFA FB hFB σ s FC hFC) (restrictInclusion φ)).trans
    ((genericFiberIntro_congr (map f C) (restrictInclusion φ ≫ σ) _ _
      (sourceSection_on_face f C E FA hFA FB hFB σ s FC hFC) _ _
      (heq_of_pathApp_eq _ _ (totalPath_on_face f C E FA hFA FB hFB σ s FC hFC))).trans
      (genericFiberIntro_eta (map f C) (restrictInclusion φ ≫ σ) s.toRestricted))

theorem extend_boundary (x : Δ.Elements) (hx : φ.Full x) :
    (extend f C E FA hFA FB hFB σ s FC hFC).val x = s.val x hx :=
  congrArg (fun t => t.val ((restrictContext φ).elementsMk x.obj ⟨x.val,hx⟩))
    (extend_on_face f C E FA hFA FB hFB σ s FC hFC)

/-- Changing the base of a lawful dependent sum along a native equivalence
preserves the complete native homotopy fibers. -/
noncomputable def equivalence : HomotopyEquivalence (map f C) where
  fibers := HomotopyContractible.ofExtensions
    (fun σ _ s => extend f C E FA hFA FB hFB σ s FC hFC)
    (fun σ _ s x hx => extend_boundary f C E FA hFA FB hFB σ s FC hFC x hx)

end DependentTotalEquivalence
namespace StructuredIdentity
variable {Γ : Context.{u}} {A : Family Γ} (C : Family (total A))

/-- Keep the given base point while allowing every generalized source argument. -/
def constantMap (a : Term A) : A ⟶ A where
  app x := TypeCat.ofHom (fun _ => a.val x)
  naturality _ _ f := by
    apply ConcreteCategory.hom_ext
    intro _
    exact (a.property f).symm

/-- The base-change source is the full chosen fiber over every base argument. -/
def chosenFiberSourceIso (a : Term A) :
    DependentTotalEquivalence.source (constantMap a) C ≅
      sigma A (reindex (reindex C (pair (𝟙 Γ) a)) (projection A)) := Iso.refl _

/-- A lawful family over a contractible base needs a contraction at only one
chosen point; contractions of every fiber are derived. -/
noncomputable def totalContractibleOfFiber (cA : HomotopyContractible A) (a : Term A)
    (cC : HomotopyContractible (reindex C (pair (𝟙 Γ) a)))
    (FA : Filling A) (hFA : FA.Lawful) (FC : Filling C) (hFC : FC.Lawful) :
    HomotopyContractible (sigma A C) := by
  let f := constantMap a
  let e := HomotopyLevels.equivalenceOfContractible f cA cA FA hFA FA hFA
  let c : HomotopyContractible (DependentTotalEquivalence.source f C) :=
    HomotopyLevels.sigmaContractible cA (cC.reindex (projection A)) FA hFA
      (FC.reindex (projection A ≫ pair (𝟙 Γ) a)) (hFC.reindex _)
  exact HomotopyLevels.targetContractible
    (DependentTotalEquivalence.equivalence f C e FA hFA FA hFA FC hFC) c
    (sigmaFilling FA hFA FC) (sigmaFilling_lawful FA hFA FC hFC)

namespace FieldsAlong
variable {B : Family (total A)} (z₀ z₁ : Term (sigma A B))
  (p : Term (SigmaPaths.base z₀ z₁))

def evaluation : total (interval Γ) ⟶ total A :=
  pair (projection (interval Γ)) (pathApp p)

noncomputable def zero : Term (reindex B (endpointSub Γ false ≫ evaluation z₀ z₁ p)) :=
  Term.sigmaSndOver z₀ (Term.reindex (pathApp p) (endpointSub Γ false)) (pathApp_zero p)

noncomputable def one : Term (reindex B (endpointSub Γ true ≫ evaluation z₀ z₁ p)) :=
  Term.sigmaSndOver z₁ (Term.reindex (pathApp p) (endpointSub Γ true)) (pathApp_one p)

noncomputable def family : Family Γ :=
  path (reindex B (evaluation z₀ z₁ p)) (zero z₀ z₁ p) (one z₀ z₁ p)

noncomputable def filling (FB : Filling B) (hFB : FB.Lawful) : Filling (family z₀ z₁ p) :=
  pathFilling (FB.reindex (evaluation z₀ z₁ p)) (hFB.reindex _) _ _

theorem filling_lawful (FB : Filling B) (hFB : FB.Lawful) :
    (filling z₀ z₁ p FB hFB).Lawful :=
  pathFilling_lawful (FB.reindex (evaluation z₀ z₁ p)) (hFB.reindex _) _ _

end FieldsAlong

namespace StructuredPaths
variable {Γ : Context.{u}} {A : Family Γ} {B : Family (total A)}
  (z₀ z₁ : Term (sigma A B))
abbrev basePathFamily := SigmaPaths.base z₀ z₁
abbrev liftedB := reindex B (liftSub A (projection (basePathFamily z₀ z₁)))
def liftedZero : Term (sigma (reindex A (projection (basePathFamily z₀ z₁))) (liftedB z₀ z₁)) :=
  Term.reindex z₀ (projection (basePathFamily z₀ z₁))
def liftedOne : Term (sigma (reindex A (projection (basePathFamily z₀ z₁))) (liftedB z₀ z₁)) :=
  Term.reindex z₁ (projection (basePathFamily z₀ z₁))
def genericBase : Term (SigmaPaths.base (liftedZero z₀ z₁) (liftedOne z₀ z₁)) :=
  Term.map (pathReindexIso (reindex A (projection (interval Γ)))
    (sigmaFst z₀) (sigmaFst z₁) (projection (basePathFamily z₀ z₁))).hom (generic (basePathFamily z₀ z₁))
noncomputable def fields : Family (total (basePathFamily z₀ z₁)) :=
  FieldsAlong.family (liftedZero z₀ z₁) (liftedOne z₀ z₁) (genericBase z₀ z₁)
noncomputable def fieldsFilling (FB : Filling B) (hFB : FB.Lawful) : Filling (fields z₀ z₁) :=
  FieldsAlong.filling _ _ _ (FB.reindex (liftSub A (projection (basePathFamily z₀ z₁)))) (hFB.reindex _)
theorem fieldsFilling_lawful (FB : Filling B) (hFB : FB.Lawful) :
    (fieldsFilling z₀ z₁ FB hFB).Lawful := FieldsAlong.filling_lawful _ _ _ _ _

private theorem map_value_heq {Ξ : Context.{u}} (D : Family Ξ)
    {x x' y y' : Ξ.Elements} (hx : x = x') (hy : y = y')
    (f : x ⟶ y) (g : x' ⟶ y') (hfg : HEq f.hom g.hom)
    {v : D.obj x} {w : D.obj x'} (hvw : HEq v w) : HEq (D.map f v) (D.map g w) := by
  subst x'
  subst y'
  have h : f = g := Functor.Elements.Hom.ext (eq_of_heq hfg)
  subst g
  cases hvw
  rfl

private theorem pi_value_heq {Ξ : Context.{u}} {D : Family Ξ} {E : Family (total D)}
    {x y y' : Ξ.Elements} (q : PiElement D E x) (hy : y = y')
    (f : x ⟶ y) (g : x ⟶ y') (hfg : HEq f.hom g.hom)
    {r : D.obj y} {r' : D.obj y'} (hr : HEq r r') : HEq (q.val f r) (q.val g r') := by
  subst y'
  have h : f = g := Functor.Elements.Hom.ext (eq_of_heq hfg)
  subst g
  cases hr
  rfl

noncomputable def fieldValue {x y : Γ.Elements} (p : (basePathFamily z₀ z₁).obj x)
    (q : (fields z₀ z₁).obj (extendObj (basePathFamily z₀ z₁) x p)) (f : x ⟶ y) (r : (interval Γ).obj y) :
    B.obj (extendObj A y (p.val.val f r)) :=
  cast (congrArg (fun h : x ⟶ y => B.obj (extendObj A y (p.val.val h r))) (Category.comp_id f))
    (q.val.val (extendHom (basePathFamily z₀ z₁) f p) r)

theorem fieldValue_heq {x y : Γ.Elements} (p : (basePathFamily z₀ z₁).obj x)
    (q : (fields z₀ z₁).obj (extendObj (basePathFamily z₀ z₁) x p)) (f : x ⟶ y) (r : (interval Γ).obj y) :
    HEq (fieldValue z₀ z₁ p q f r) (q.val.val (extendHom (basePathFamily z₀ z₁) f p) r) := cast_heq _ _

noncomputable def fieldToDependent {x : Γ.Elements} (p : (basePathFamily z₀ z₁).obj x)
    (q : (fields z₀ z₁).obj (extendObj (basePathFamily z₀ z₁) x p)) : SigmaPaths.DependentPath z₀ z₁ p where
  val f r := fieldValue z₀ z₁ p q f r
  naturality {y w} f g r := by
    apply eq_of_heq
    have hn := q.val.naturality (extendHom (basePathFamily z₀ z₁) f p)
      (extendHom (basePathFamily z₀ z₁) g ((basePathFamily z₀ z₁).map f p)) r
    let k := (liftSub A (projection (basePathFamily z₀ z₁))).mapElements.map
      ((FieldsAlong.evaluation (liftedZero z₀ z₁) (liftedOne z₀ z₁) (genericBase z₀ z₁)).mapElements.map
        (extendHom (interval (total (basePathFamily z₀ z₁)))
          (extendHom (basePathFamily z₀ z₁) g ((basePathFamily z₀ z₁).map f p)) r))
    refine (map_value_heq B ?_ ?_ (extendAlong A g (p.val.naturality f g r)) k HEq.rfl (fieldValue_heq z₀ z₁ p q f r)).trans
      ((heq_of_eq hn).trans ?_)
    · exact congrArg (fun h : x ⟶ y => extendObj A y (p.val.val h r)) (Category.comp_id f).symm
    · exact congrArg (fun h : x ⟶ w => extendObj A w (p.val.val h ((interval Γ).map g r)))
        (congrArg (fun k => f ≫ k) (Category.comp_id g)).symm
    · refine (pi_value_heq q.val ?_
        (extendHom (basePathFamily z₀ z₁) f p ≫ extendHom (basePathFamily z₀ z₁) g ((basePathFamily z₀ z₁).map f p))
        (extendHom (basePathFamily z₀ z₁) (f ≫ g) p) HEq.rfl HEq.rfl).trans
        (fieldValue_heq z₀ z₁ p q (f ≫ g) ((interval Γ).map g r)).symm
      exact congrArg (extendObj (basePathFamily z₀ z₁) w)
        ((ConcreteCategory.congr_hom ((basePathFamily z₀ z₁).map_comp f g) p).symm)
  zero f := by
    apply Sigma.ext
    · exact (p.property f).1
    · exact (fieldValue_heq z₀ z₁ p q f _).trans
        ((heq_of_eq (q.property (extendHom (basePathFamily z₀ z₁) f p)).1).trans
          (Term.sigmaSndOver_val _ _ _ _))
  one f := by
    apply Sigma.ext
    · exact (p.property f).2
    · exact (fieldValue_heq z₀ z₁ p q f _).trans
        ((heq_of_eq (q.property (extendHom (basePathFamily z₀ z₁) f p)).2).trans
          (Term.sigmaSndOver_val _ _ _ _))

private theorem restricted_base {x : Γ.Elements} (p : (basePathFamily z₀ z₁).obj x)
    {y : (total (basePathFamily z₀ z₁)).Elements} (h : extendObj (basePathFamily z₀ z₁) x p ⟶ y) :
    (basePathFamily z₀ z₁).map ((projection (basePathFamily z₀ z₁)).mapElements.map h) p = y.val.2 := by
  exact (generic (basePathFamily z₀ z₁)).property h

private theorem restricted_value {x : Γ.Elements} (p : (basePathFamily z₀ z₁).obj x)
    {y : (total (basePathFamily z₀ z₁)).Elements} (h : extendObj (basePathFamily z₀ z₁) x p ⟶ y)
    (r : (interval (total (basePathFamily z₀ z₁))).obj y) :
    p.val.val ((projection (basePathFamily z₀ z₁)).mapElements.map h) r = y.val.2.val.val (𝟙 _) r := by
  have hp := restricted_base z₀ z₁ p h
  have hv := congrArg (fun q : (basePathFamily z₀ z₁).obj ((projection (basePathFamily z₀ z₁)).mapElements.obj y) =>
    q.val.val (𝟙 _) r) hp
  exact (congrArg (fun k : x ⟶ (projection (basePathFamily z₀ z₁)).mapElements.obj y => p.val.val k r) (Category.comp_id _)).symm.trans hv

noncomputable def dependentValue {x : Γ.Elements} (p : (basePathFamily z₀ z₁).obj x)
    (q : SigmaPaths.DependentPath z₀ z₁ p)
    {y : (total (basePathFamily z₀ z₁)).Elements} (h : extendObj (basePathFamily z₀ z₁) x p ⟶ y)
    (r : (interval (total (basePathFamily z₀ z₁))).obj y) :
    B.obj (extendObj A ((projection (basePathFamily z₀ z₁)).mapElements.obj y) (y.val.2.val.val (𝟙 _) r)) :=
  cast (congrArg (fun a => B.obj (extendObj A _ a)) (restricted_value z₀ z₁ p h r))
    (q.val ((projection (basePathFamily z₀ z₁)).mapElements.map h) r)

theorem dependentValue_heq {x : Γ.Elements} (p : (basePathFamily z₀ z₁).obj x)
    (q : SigmaPaths.DependentPath z₀ z₁ p)
    {y : (total (basePathFamily z₀ z₁)).Elements} (h : extendObj (basePathFamily z₀ z₁) x p ⟶ y)
    (r : (interval (total (basePathFamily z₀ z₁))).obj y) :
    HEq (dependentValue z₀ z₁ p q h r)
      (q.val ((projection (basePathFamily z₀ z₁)).mapElements.map h) r) := cast_heq _ _

noncomputable def dependentToField {x : Γ.Elements} (p : (basePathFamily z₀ z₁).obj x)
    (q : SigmaPaths.DependentPath z₀ z₁ p) :
    (fields z₀ z₁).obj (extendObj (basePathFamily z₀ z₁) x p) := by
  refine ⟨{ val := fun h r => dependentValue z₀ z₁ p q h r
            naturality := ?_ }, ?_⟩
  · intro y w f g r
    apply eq_of_heq
    let f' := (projection (basePathFamily z₀ z₁)).mapElements.map f
    let g' := (projection (basePathFamily z₀ z₁)).mapElements.map g
    let k := (liftSub A (projection (basePathFamily z₀ z₁))).mapElements.map
      ((FieldsAlong.evaluation (liftedZero z₀ z₁) (liftedOne z₀ z₁) (genericBase z₀ z₁)).mapElements.map
        (extendHom (interval (total (basePathFamily z₀ z₁))) g r))
    refine (map_value_heq B ?_ ?_ k (extendAlong A g' (p.val.naturality f' g' r))
      HEq.rfl (dependentValue_heq z₀ z₁ p q f r)).trans
      ((heq_of_eq (q.naturality f' g' r)).trans ?_)
    · exact congrArg (extendObj A _) (restricted_value z₀ z₁ p f r).symm
    · exact congrArg (extendObj A _) (restricted_value z₀ z₁ p (f ≫ g) ((interval (total (basePathFamily z₀ z₁))).map g r)).symm
    · exact (dependentValue_heq z₀ z₁ p q (f ≫ g) ((interval (total (basePathFamily z₀ z₁))).map g r)).symm
  · intro y f
    constructor
    · apply eq_of_heq
      exact (dependentValue_heq z₀ z₁ p q f _).trans
        ((Sigma.mk.inj (q.zero ((projection (basePathFamily z₀ z₁)).mapElements.map f))).2.trans
          (Term.sigmaSndOver_val (liftedZero z₀ z₁) _ _ y).symm)
    · apply eq_of_heq
      exact (dependentValue_heq z₀ z₁ p q f _).trans
        ((Sigma.mk.inj (q.one ((projection (basePathFamily z₀ z₁)).mapElements.map f))).2.trans
          (Term.sigmaSndOver_val (liftedOne z₀ z₁) _ _ y).symm)

theorem fieldToDependent_dependentToField {x : Γ.Elements} (p : (basePathFamily z₀ z₁).obj x)
    (q : SigmaPaths.DependentPath z₀ z₁ p) :
    fieldToDependent z₀ z₁ p (dependentToField z₀ z₁ p q) = q := by
  apply SigmaPaths.DependentPath.ext
  intro y f r
  apply eq_of_heq
  exact (fieldValue_heq z₀ z₁ p _ f r).trans
    (dependentValue_heq z₀ z₁ p q (extendHom (basePathFamily z₀ z₁) f p) r)

theorem dependentToField_fieldToDependent {x : Γ.Elements} (p : (basePathFamily z₀ z₁).obj x)
    (q : (fields z₀ z₁).obj (extendObj (basePathFamily z₀ z₁) x p)) :
    dependentToField z₀ z₁ p (fieldToDependent z₀ z₁ p q) = q := by
  apply Subtype.ext
  apply PiElement.ext
  intro y h r
  apply eq_of_heq
  refine (dependentValue_heq z₀ z₁ p _ h r).trans
    ((fieldValue_heq z₀ z₁ p q ((projection (basePathFamily z₀ z₁)).mapElements.map h) r).trans ?_)
  exact pi_value_heq q.val
    (congrArg (extendObj (basePathFamily z₀ z₁) _) (restricted_base z₀ z₁ p h))
    (extendHom (basePathFamily z₀ z₁) ((projection (basePathFamily z₀ z₁)).mapElements.map h) p) h HEq.rfl HEq.rfl

noncomputable def fieldEquiv {x : Γ.Elements} (p : (basePathFamily z₀ z₁).obj x) :
    (fields z₀ z₁).obj (extendObj (basePathFamily z₀ z₁) x p) ≃ SigmaPaths.DependentPath z₀ z₁ p where
  toFun := fieldToDependent z₀ z₁ p
  invFun := dependentToField z₀ z₁ p
  left_inv := dependentToField_fieldToDependent z₀ z₁ p
  right_inv := fieldToDependent_dependentToField z₀ z₁ p

noncomputable def componentsEquiv (x : Γ.Elements) :
    (sigma (basePathFamily z₀ z₁) (fields z₀ z₁)).obj x ≃ (SigmaPaths.components z₀ z₁).obj x :=
  Equiv.sigmaCongrRight (fieldEquiv z₀ z₁)

noncomputable def decomposition :
    sigma (basePathFamily z₀ z₁) (fields z₀ z₁) ≅ SigmaPaths.components z₀ z₁ :=
  NatIso.ofComponents (fun x => (componentsEquiv z₀ z₁ x).toIso) (by
    intro x y f
    apply ConcreteCategory.hom_ext
    intro q
    apply Sigma.ext
    · rfl
    · apply heq_of_eq
      apply SigmaPaths.DependentPath.ext
      intro w g r
      apply eq_of_heq
      exact (fieldValue_heq z₀ z₁ ((basePathFamily z₀ z₁).map f q.1)
        ((fields z₀ z₁).map (extendHom (basePathFamily z₀ z₁) f q.1) q.2) g r).trans
        ((pi_value_heq q.2.val
          (congrArg (extendObj (basePathFamily z₀ z₁) w)
            (ConcreteCategory.congr_hom ((basePathFamily z₀ z₁).map_comp f g) q.1).symm)
          (extendHom (basePathFamily z₀ z₁) f q.1 ≫ extendHom (basePathFamily z₀ z₁) g ((basePathFamily z₀ z₁).map f q.1))
          (extendHom (basePathFamily z₀ z₁) (f ≫ g) q.1) HEq.rfl HEq.rfl).trans
            (fieldValue_heq z₀ z₁ q.1 q.2 (f ≫ g) r).symm))

noncomputable def wholeIso : SigmaPaths.whole z₀ z₁ ≅ sigma (basePathFamily z₀ z₁) (fields z₀ z₁) :=
  SigmaPaths.decomposition z₀ z₁ ≪≫ (decomposition z₀ z₁).symm

theorem wholeIso_inv_fields (x : Γ.Elements) (q : (sigma (basePathFamily z₀ z₁) (fields z₀ z₁)).obj x) :
    SigmaPaths.second z₀ z₁ ((wholeIso z₀ z₁).inv.app x q) =
      fieldToDependent z₀ z₁ q.1 q.2 := rfl

end StructuredPaths

namespace TotalRecovery
variable {Γ : Context.{u}} {A B : Family Γ} (f : A ⟶ B) (E : HomotopyEquivalence f)
noncomputable def inverse : B ⟶ A := IntervalTransport.mapOfSection
  (genericFiberFst f (𝟙 _) E.fibers.center)
noncomputable def rightInverse : Term (homogeneousPath (reindex B (projection B))
    (Term.map (Functor.whiskerLeft (projection B).mapElements f)
      (Term.map (Functor.whiskerLeft (projection B).mapElements (inverse f E)) (generic B)))
    (generic B)) := genericFiberPath f (𝟙 _) E.fibers.center
noncomputable def leftInverse (F : Filling A) (hF : F.Lawful) :=
  E.chosenLeftInverse F hF (inverse f E) (rightInverse f E)
end TotalRecovery

namespace UaStructured
open SmallUniverse
variable {Γ : Context.{u+1}} {S : Family (total (SmallUniverse.family Γ))}
  (z₀ z₁ : Term (sigma (SmallUniverse.family Γ) S))

abbrev code₀ := code (sigmaFst z₀)
abbrev code₁ := code (sigmaFst z₁)
noncomputable def carrierMap := NativeUnivalence.equivToPath (code₀ z₀) (code₁ z₁)
noncomputable def equivalences : Family Γ :=
  DependentTotalEquivalence.source (carrierMap z₀ z₁) (StructuredPaths.fields z₀ z₁)
noncomputable def map : equivalences z₀ z₁ ⟶ SigmaPaths.whole z₀ z₁ :=
  DependentTotalEquivalence.map (carrierMap z₀ z₁) (StructuredPaths.fields z₀ z₁) ≫
    (StructuredPaths.wholeIso z₀ z₁).inv

noncomputable def equivalence (FS : Filling S) (hFS : FS.Lawful) :
    HomotopyEquivalence (map z₀ z₁) := by
  let FE := EquivalenceFamilies.equivFilling (NativeDecode.filling (code₀ z₀))
    (NativeDecode.filling_lawful _) (NativeDecode.filling (code₁ z₁)) (NativeDecode.filling_lawful _)
  have hFE := EquivalenceFamilies.equivFilling_lawful (NativeDecode.filling (code₀ z₀))
    (NativeDecode.filling_lawful _) (NativeDecode.filling (code₁ z₁)) (NativeDecode.filling_lawful _)
  let E := DependentTotalEquivalence.equivalence (carrierMap z₀ z₁) (StructuredPaths.fields z₀ z₁)
    (NativeUnivalence.uaEquivalence (code₀ z₀) (code₁ z₁)) FE hFE
    (NativeUnivalence.pathsFilling (code₀ z₀) (code₁ z₁)) (NativeUnivalence.pathsFilling_lawful _ _)
    (StructuredPaths.fieldsFilling z₀ z₁ FS hFS) (StructuredPaths.fieldsFilling_lawful z₀ z₁ FS hFS)
  exact E.conjugateIso (Iso.refl _) (StructuredPaths.wholeIso z₀ z₁).symm

/-- The carrier path is the model's selected ua of the retained equivalence. -/
theorem map_carrier (x : Γ.Elements) (q : (equivalences z₀ z₁).obj x) :
    SigmaPaths.first z₀ z₁ ((map z₀ z₁).app x q) = (carrierMap z₀ z₁).app x q.1 := rfl

/-- The dependent field path is retained in full, not merely at its endpoints. -/
theorem map_fields (x : Γ.Elements) (q : (equivalences z₀ z₁).obj x) :
    SigmaPaths.second z₀ z₁ ((map z₀ z₁).app x q) =
      StructuredPaths.fieldToDependent z₀ z₁ ((carrierMap z₀ z₁).app x q.1) q.2 :=
  StructuredPaths.wholeIso_inv_fields z₀ z₁ x
    ((DependentTotalEquivalence.map (carrierMap z₀ z₁) (StructuredPaths.fields z₀ z₁)).app x q)

noncomputable def filling (FS : Filling S) (hFS : FS.Lawful) : Filling (equivalences z₀ z₁) :=
  sigmaFilling
    (EquivalenceFamilies.equivFilling (NativeDecode.filling (code₀ z₀))
      (NativeDecode.filling_lawful _) (NativeDecode.filling (code₁ z₁)) (NativeDecode.filling_lawful _))
    (EquivalenceFamilies.equivFilling_lawful _ _ _ _)
    ((StructuredPaths.fieldsFilling z₀ z₁ FS hFS).reindex
      (DependentTotalEquivalence.baseMap (carrierMap z₀ z₁)))

theorem filling_lawful (FS : Filling S) (hFS : FS.Lawful) : (filling z₀ z₁ FS hFS).Lawful :=
  sigmaFilling_lawful _ _ _ ((StructuredPaths.fieldsFilling_lawful z₀ z₁ FS hFS).reindex _)

variable (FS : Filling S) (hFS : FS.Lawful)
noncomputable def inverse := TotalRecovery.inverse (map z₀ z₁) (equivalence z₀ z₁ FS hFS)
/-- Rebuilding retains every original structured path, including its interior. -/
noncomputable def rightInverse := TotalRecovery.rightInverse (map z₀ z₁) (equivalence z₀ z₁ FS hFS)
/-- Classifying again retains the complete carrier-equivalence and field-path witness. -/
noncomputable def leftInverse := TotalRecovery.leftInverse (map z₀ z₁) (equivalence z₀ z₁ FS hFS)
  (filling z₀ z₁ FS hFS) (filling_lawful z₀ z₁ FS hFS)

end UaStructured

namespace IdentitySystem
variable {Γ : Context.{u}} (A : Family Γ) (a : Term A)

abbrev paths : Family (total A) :=
  homogeneousPath (reindex A (projection A)) (Term.reindex a (projection A)) (generic A)

abbrev base : total (paths A a) ⟶ Γ := projection (paths A a) ≫ projection A

def genericPath : Term (homogeneousPath (reindex A (base A a))
    (Term.reindex a (base A a)) (Term.reindex (generic A) (projection (paths A a)))) :=
  Term.map (pathReindexIso (reindex (reindex A (projection A)) (projection (interval (total A))))
    (Term.reindex a (projection A)) (generic A) (projection (paths A a))).hom (generic (paths A a))

def evaluation : total (interval (total (paths A a))) ⟶ total A :=
  pair (projection (interval (total (paths A a))) ≫ base A a) (pathApp (genericPath A a))

theorem evaluation_zero : endpointSub (total (paths A a)) false ≫ evaluation A a =
    base A a ≫ pair (𝟙 Γ) a := by
  ext I z
  exact congrArg (Sigma.mk _) (congrArg (fun t => t.val ((total (paths A a)).elementsMk I z))
    (pathApp_zero (genericPath A a)))

theorem evaluation_one : endpointSub (total (paths A a)) true ≫ evaluation A a =
    projection (paths A a) := by
  ext I z
  exact congrArg (Sigma.mk _) (congrArg (fun t => t.val ((total (paths A a)).elementsMk I z))
    (pathApp_one (genericPath A a)))

variable (R : Family (total A)) (r : Term (reindex R (pair (𝟙 Γ) a))) (FR : Filling R)

def cap : Term (reindex R (endpointSub (total (paths A a)) false ≫ evaluation A a)) :=
  Term.convert (congrArg (reindex R) (evaluation_zero A a).symm) (Term.reindex r (base A a))

def line : Term (reindex R (evaluation A a)) :=
  FR.fill (evaluation A a) (Cofibration.bot _)
    (OpenBox.empty _ (cap A a R r))

def map : paths A a ⟶ R := IntervalTransport.mapOfSection
  (Term.convert (congrArg (reindex R) (evaluation_one A a))
    (Term.reindex (line A a R r FR) (endpointSub _ true)))

noncomputable def equivalence (FA : Filling A) (hFA : FA.Lawful)
    (hFR : FR.Lawful) (c : HomotopyContractible (sigma A R)) : HomotopyEquivalence (map A a R r FR) :=
  HomotopyEquivalence.ofContractibleTotals (map A a R r FR) FA hFA
    (pathFilling ((FA.reindex (projection A)).reindex (projection (interval (total A))))
      ((hFA.reindex _).reindex _) _ _)
    (pathFilling_lawful ((FA.reindex (projection A)).reindex (projection (interval (total A))))
      ((hFA.reindex _).reindex _) _ _)
    FR hFR (NativePathSingleton.contractible a) c

variable (FA : Filling A) (hFA : FA.Lawful) (hFR : FR.Lawful)
  (c : HomotopyContractible (sigma A R))

/-- The reconstructed path is selected from the complete native homotopy fiber. -/
noncomputable def inverse : R ⟶ paths A a := IntervalTransport.mapOfSection
  (genericFiberFst (map A a R r FR) (𝟙 (total R))
    (equivalence A a R r FR FA hFA hFR c).fibers.center)

/-- Reclassifying a reconstructed path retains the full independent relation witness. -/
noncomputable def rightInverse : Term (homogeneousPath (reindex R (projection R))
    (Term.map (Functor.whiskerLeft (projection R).mapElements (map A a R r FR))
      (Term.map (Functor.whiskerLeft (projection R).mapElements
        (inverse A a R r FR FA hFA hFR c)) (generic R))) (generic R)) :=
  genericFiberPath (map A a R r FR) (𝟙 (total R))
    (equivalence A a R r FR FA hFA hFR c).fibers.center

/-- Reconstruction retains an arbitrary original path, including its interior. -/
noncomputable def leftInverse :=
  (equivalence A a R r FR FA hFA hFR c).chosenLeftInverse
    (pathFilling ((FA.reindex (projection A)).reindex (projection (interval (total A))))
      ((hFA.reindex _).reindex _) _ _)
    (pathFilling_lawful ((FA.reindex (projection A)).reindex (projection (interval (total A))))
      ((hFA.reindex _).reindex _) _ _)
    (inverse A a R r FR FA hFA hFR c) (rightInverse A a R r FR FA hFA hFR c)

end IdentitySystem

end StructuredIdentity
end SquareKit.Cubical.Presheaf
