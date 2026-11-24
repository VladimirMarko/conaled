import SquareKit.Internal.Cubical.PropositionExtension
import SquareKit.StructureIdentity.Laws
import SquareKit.Internal.Cubical.NativeStructurePreservation
import SquareKit.Internal.Cubical.HomotopyLevels

/-! Native formulas use paths for equality. The `holds` constructor decodes
the existing discrete host-proposition field, with its own lawful proof family. -/
set_option autoImplicit false
set_option warningAsError true
namespace SquareKit.Cubical.Presheaf.StructureIdentity.Native
open CategoryTheory SquareKit.StructureIdentity
universe u
variable {Γ : Context.{u+1}} {A : Family Γ}

def expression {D C E : Description.{u}} (s : Term (family D A)) (c : Term (family C A)) :
    Expression D C E → Term (family E A)
  | .data => s
  | .var => c
  | .fixed a => ⟨fun _ => ⟨a⟩, fun _ => rfl⟩
  | .pair a b => sigmaIntro (expression s c a) (expression s c b)
  | .first a => sigmaFst (expression s c a)
  | .second a => sigmaSnd (expression s c a)
  | .apply f a => applyTerm (expression s c f) (expression s c a)

def holdsFamily {P : Type u} [PropositionCarrier P] (p : Term (constantFamily Γ (ULift.{u+1} P))) : Family Γ :=
  discreteFamily p (fun q => ULift.{u+1} (PLift (PropositionCarrier.decode q.down)))

def holdsFilling {P : Type u} [PropositionCarrier P] (p : Term (constantFamily Γ (ULift.{u+1} P))) : Filling (holdsFamily p) :=
  discreteFilling p (fun q => ULift.{u+1} (PLift (PropositionCarrier.decode q.down)))

theorem holdsFilling_lawful {P : Type u} [PropositionCarrier P] (p : Term (constantFamily Γ (ULift.{u+1} P))) :
    (holdsFilling p).Lawful := discreteFilling_lawful p _

def holdsIsProp {P : Type u} [PropositionCarrier P] (p : Term (constantFamily Γ (ULift.{u+1} P))) :
    Term (HomotopyLevels.isProp (holdsFamily p)) :=
  HomotopyLevels.ofSubsingleton _ (fun x =>
    (show Subsingleton (ULift.{u+1} (PLift (PropositionCarrier.decode (p.val x).down))) from inferInstance))

def holdsPresentation {P : Type u} [PropositionCarrier P] (p : Term (constantFamily Γ (ULift.{u+1} P))) :
    SmallUniverse.SmallPresentation.Data (holdsFamily p) where
  fiber x := ULift.{u} (PLift (PropositionCarrier.decode (p.val x).down))
  equiv _ := Equiv.ulift.trans Equiv.ulift.symm

def lawFamily {D C : Description.{u}} (p : Formula D C) {Γ : Context.{u+1}} {A : Family Γ}
    (s : Term (family D A)) (c : Term (family C A)) : Family Γ :=
  match p with
  | .truth => constantFamily Γ (ULift.{u+1} PUnit.{u+1})
  | .equal (E := E) a b => homogeneousPath (family E A) (expression s c a) (expression s c b)
  | @Formula.holds _ _ _P hp a =>
    letI := hp
    holdsFamily (expression s c a)
  | .and p q =>
    let P := lawFamily p s c
    sigma P (reindex (lawFamily q s c) (projection P))
  | .implies p q =>
    let P := lawFamily p s c
    pi P (reindex (lawFamily q s c) (projection P))
  | .all E p =>
    let π := projection (family E A)
    pi (family E A) (lawFamily p (reindexTerm D s π)
      (sigmaIntro (reindexTerm C c π)
        (Term.map (reindexIso E A π).hom (generic (family E A)))))

/-- Descriptions built over a native set remain sets, including function fields. -/
noncomputable def familyIsSet (D : Description.{u}) {Γ : Context.{u+1}} {A : Family Γ}
    (sA : Term (HomotopyLevels.isSet A)) (FA : Filling A) (hFA : FA.Lawful) :
    Term (HomotopyLevels.isSet (family D A)) :=
  match D with
  | .carrier => sA
  | .fixed S => HomotopyLevels.constantIsSet (ULift.{u+1} S)
  | .product D E =>
    let d := filling D FA hFA
    let e := filling E FA hFA
    HomotopyLevels.productIsSet (familyIsSet D sA FA hFA) (familyIsSet E sA FA hFA)
      d.1 d.2 e.1 e.2
  | .function D E =>
    let π := projection (family D A)
    let d := filling D FA hFA
    let e := filling E FA hFA
    HomotopyLevels.piIsSet (HomotopyLevels.reindexSet (familyIsSet E sA FA hFA) π)
      d.1 d.2 (e.1.reindex π) (e.2.reindex π)

noncomputable def lawFilling {D C : Description.{u}} (p : Formula D C)
    {Γ : Context.{u+1}} {A : Family Γ} (s : Term (family D A)) (c : Term (family C A))
    (FA : Filling A) (hFA : FA.Lawful) :
    {F : Filling (lawFamily p s c) // F.Lawful} :=
  match p with
  | .truth => filling (.fixed PUnit.{u+1}) FA hFA
  | .equal (E := E) a b =>
    let F := filling E FA hFA
    ⟨pathFilling (F.1.reindex (projection (interval Γ))) (F.2.reindex _)
      (expression s c a) (expression s c b), pathFilling_lawful _ (F.2.reindex _) _ _⟩
  | @Formula.holds _ _ _P hp a =>
    letI := hp
    ⟨holdsFilling (expression s c a), holdsFilling_lawful _⟩
  | .and p q =>
    let d := lawFilling p s c FA hFA
    let e := lawFilling q s c FA hFA
    ⟨sigmaFilling d.1 d.2 (e.1.reindex (projection _)),
      sigmaFilling_lawful d.1 d.2 _ (e.2.reindex _)⟩
  | .implies p q =>
    let d := lawFilling p s c FA hFA
    let e := lawFilling q s c FA hFA
    ⟨piFilling d.1 d.2 (e.1.reindex (projection _)),
      piFilling_lawful d.1 d.2 _ (e.2.reindex _)⟩
  | .all E p =>
    let π := projection (family E A)
    let d := filling E FA hFA
    let e := lawFilling p (reindexTerm D s π)
      (sigmaIntro (reindexTerm C c π)
        (Term.map (reindexIso E A π).hom (generic (family E A))))
      (FA.reindex π) (hFA.reindex π)
    ⟨piFilling d.1 d.2 e.1, piFilling_lawful d.1 d.2 e.1 e.2⟩

noncomputable def lawPresentation {D C : Description.{u}} (p : Formula D C)
    {Γ : Context.{u+1}} {A : Family Γ} (s : Term (family D A)) (c : Term (family C A))
    (PA : SmallUniverse.SmallPresentation.Data A) :
    SmallUniverse.SmallPresentation.Data (lawFamily p s c) :=
  match p with
  | .truth => presentation (.fixed PUnit.{u+1}) PA
  | .equal (E := E) a b => SmallUniverse.SmallPresentation.Data.path _
      (smallReindex (presentation E PA) (projection (interval Γ)))
      (expression s c a) (expression s c b)
  | @Formula.holds _ _ _P hp a =>
    letI := hp
    holdsPresentation (expression s c a)
  | .and p q =>
    let d := lawPresentation p s c PA
    let e := lawPresentation q s c PA
    d.sigma (smallReindex e _)
  | .implies p q =>
    let d := lawPresentation p s c PA
    let e := lawPresentation q s c PA
    d.pi (smallReindex e _)
  | .all E p =>
    let π := projection (family E A)
    (presentation E PA).pi (lawPresentation p (reindexTerm D s π)
      (sigmaIntro (reindexTerm C c π)
        (Term.map (reindexIso E A π).hom (generic (family E A)))) (smallReindex PA π))

/-- Laws are native propositions when their carrier is a native set. Equality
uses that sethood witness; only the explicitly discrete `holds` case uses host proofs. -/
noncomputable def lawIsProp {D C : Description.{u}} (p : Formula D C)
    {Γ : Context.{u+1}} {A : Family Γ} (s : Term (family D A)) (c : Term (family C A))
    (sA : Term (HomotopyLevels.isSet A)) (FA : Filling A) (hFA : FA.Lawful) :
    Term (HomotopyLevels.isProp (lawFamily p s c)) :=
  match p with
  | .truth => HomotopyLevels.ofSubsingleton _ (fun _ =>
      (show Subsingleton (ULift.{u+1} PUnit.{u+1}) from inferInstance))
  | .equal (E := E) a b =>
    HomotopyLevels.pathIsPropAt (familyIsSet E sA FA hFA) (expression s c a) (expression s c b)
  | @Formula.holds _ _ _P hp a =>
    letI := hp
    holdsIsProp (expression s c a)
  | .and p q =>
    let d := lawFilling p s c FA hFA
    let e := lawFilling q s c FA hFA
    HomotopyLevels.productIsProp (lawIsProp p s c sA FA hFA) (lawIsProp q s c sA FA hFA)
      d.1 d.2 e.1 e.2
  | .implies p q =>
    let π := projection (lawFamily p s c)
    let d := lawFilling p s c FA hFA
    let e := lawFilling q s c FA hFA
    HomotopyLevels.piIsProp (HomotopyLevels.reindexProp (lawIsProp q s c sA FA hFA) π)
      d.1 d.2 (e.1.reindex π) (e.2.reindex π)
  | .all E p =>
    let π := projection (family E A)
    let d := filling E FA hFA
    let s' := reindexTerm D s π
    let c' := sigmaIntro (reindexTerm C c π)
      (Term.map (reindexIso E A π).hom (generic (family E A)))
    let e := lawFilling p s' c' (FA.reindex π) (hFA.reindex π)
    HomotopyLevels.piIsProp
      (lawIsProp p s' c' (HomotopyLevels.reindexSet sA π) (FA.reindex π) (hFA.reindex π))
      d.1 d.2 e.1 e.2

noncomputable def classifyLaw {D C : Description.{u}} (p : Formula D C)
    (a : Γ ⟶ smallFamilyCodes.{u})
    (s : Term (family D (SmallUniverse.liftedDecode a)))
    (c : Term (family C (SmallUniverse.liftedDecode a))) :
    SmallUniverse.LargeConstructors.Result (lawFamily p s c) :=
  let F := lawFilling p s c (SmallUniverse.NativeDecode.filling a)
    (SmallUniverse.NativeDecode.filling_lawful a)
  SmallUniverse.LargeConstructors.construct
    (lawPresentation p s c (SmallUniverse.decodePresentation a)) F.1 F.2

def unitContext : Term (family (.fixed PUnit.{u+1}) A) := ⟨fun _ => ⟨PUnit.unit⟩, fun _ => rfl⟩

/-- A law-bearing structure retains the native law witness as its second field. -/
def modelsFamily (T : Specification.{u}) (A : Family Γ) : Family Γ :=
  let S := family T.description A
  let π := projection S
  sigma S (lawFamily T.law (Term.map (reindexIso T.description A π).hom (generic S)) unitContext)

noncomputable def modelsFilling (T : Specification.{u}) (FA : Filling A) (hFA : FA.Lawful) :
    {F : Filling (modelsFamily T A) // F.Lawful} :=
  let S := family T.description A
  let π := projection S
  let d := filling T.description FA hFA
  let p := lawFilling T.law (Term.map (reindexIso T.description A π).hom (generic S))
    unitContext (FA.reindex π) (hFA.reindex π)
  ⟨sigmaFilling d.1 d.2 p.1, sigmaFilling_lawful d.1 d.2 p.1 p.2⟩

noncomputable def modelsPresentation (T : Specification.{u})
    (PA : SmallUniverse.SmallPresentation.Data A) :
    SmallUniverse.SmallPresentation.Data (modelsFamily T A) :=
  let S := family T.description A
  let π := projection S
  (presentation T.description PA).sigma
    (lawPresentation T.law (Term.map (reindexIso T.description A π).hom (generic S))
      unitContext (smallReindex PA π))

noncomputable def classifyModels (T : Specification.{u}) (a : Γ ⟶ smallFamilyCodes.{u}) :
    SmallUniverse.LargeConstructors.Result (modelsFamily T (SmallUniverse.liftedDecode a)) :=
  let F := modelsFilling T (SmallUniverse.NativeDecode.filling a)
    (SmallUniverse.NativeDecode.filling_lawful a)
  SmallUniverse.LargeConstructors.construct
    (modelsPresentation T (SmallUniverse.decodePresentation a)) F.1 F.2

variable {Δ : Context.{u+1}}

theorem applyTerm_reindex (D E : Description.{u})
    (f : Term (family (.function D E) A)) (a : Term (family D A)) (σ : Δ ⟶ Γ) :
    reindexTerm E (applyTerm f a) σ =
      applyTerm (reindexTerm (.function D E) f σ) (reindexTerm D a σ) := by
  apply Term.ext
  intro x
  let y := σ.mapElements.obj x
  exact congrArg (fun b => (reindexIso E A σ).hom.app x ((f.val y).val (𝟙 y) b))
    ((reindexIso D A σ).hom_inv_id_app_apply x (a.val y)).symm

theorem expression_reindex {D C E : Description.{u}}
    (s : Term (family D A)) (c : Term (family C A)) (a : Expression D C E) (σ : Δ ⟶ Γ) :
    reindexTerm E (expression s c a) σ =
      expression (reindexTerm D s σ) (reindexTerm C c σ) a := by
  induction a with
  | data => rfl
  | var => rfl
  | fixed a => rfl
  | @pair E F a b ha hb =>
    change (sigmaIntro (reindexTerm E (expression s c a) σ)
      (reindexTerm F (expression s c b) σ) : Term (family (.product E F) (reindex A σ))) = _
    rw [ha, hb]
    rfl
  | first a ha =>
    change sigmaFst (reindexTerm _ (expression s c a) σ) = _
    rw [ha]
    rfl
  | second a ha =>
    change sigmaSnd (reindexTerm _ (expression s c a) σ) = _
    rw [ha]
    rfl
  | apply f a hf ha =>
    change reindexTerm _ (applyTerm (expression s c f) (expression s c a)) σ = _
    rw [applyTerm_reindex, hf, ha]
    rfl
noncomputable def lawReindexIso {D C : Description.{u}} (p : Formula D C)
    {Γ Δ : Context.{u+1}} {A : Family Γ} (s : Term (family D A)) (c : Term (family C A))
    (σ : Δ ⟶ Γ) : reindex (lawFamily p s c) σ ≅
      lawFamily p (reindexTerm D s σ) (reindexTerm C c σ) :=
  match p with
  | .truth => Iso.refl _
  | .equal (E := E) a b =>
    EquivalenceFamilies.homogeneousReindexIso (family E A) (expression s c a)
      (expression s c b) σ ≪≫
    pathCongr (reindexIso E A σ) (Term.reindex (expression s c a) σ)
      (Term.reindex (expression s c b) σ) ≪≫
    eqToIso (congrArg₂ (homogeneousPath (family E (reindex A σ)))
      (expression_reindex s c a σ) (expression_reindex s c b σ))
  | @Formula.holds _ _ _P hp a =>
    letI := hp
    eqToIso (congrArg holdsFamily (expression_reindex s c a σ))
  | .and p q => productCongr (lawReindexIso p s c σ) (lawReindexIso q s c σ)
  | .implies p q =>
    piReindexIso (lawFamily p s c) (reindex (lawFamily q s c) (projection _)) σ ≪≫
      functionCongr (lawReindexIso p s c σ) (lawReindexIso q s c σ)
  | .all E p => by
    let X := family E A
    let X' := family E (reindex A σ)
    let π := projection X
    let π' := projection X'
    let ρ := liftSub X σ
    let e := reindexIso E A σ
    let κ := PiDomain.baseMap e.hom
    let s0 := reindexTerm D s π
    let a0 := Term.map (reindexIso E A π).hom (generic X)
    let c0 : Term (family (.product C E) (reindex A π)) := sigmaIntro (reindexTerm C c π) a0
    let s1 := reindexTerm D (reindexTerm D s σ) π'
    let a1 := Term.map (reindexIso E (reindex A σ) π').hom (generic X')
    let c1 : Term (family (.product C E) (reindex (reindex A σ) π')) := sigmaIntro (reindexTerm C (reindexTerm C c σ) π') a1
    let j0 := lawReindexIso p s0 c0 ρ
    let j1 := lawReindexIso p s1 c1 κ
    have hs : reindexTerm D s0 ρ = reindexTerm D s1 κ := by
      dsimp only [s0,s1]
      rw [reindexTerm_comp, reindexTerm_comp]
      exact (reindexTerm_comp D s σ (κ ≫ π')).symm
    have hf : reindexTerm C (reindexTerm C c π) ρ =
        reindexTerm C (reindexTerm C (reindexTerm C c σ) π') κ := by
      rw [reindexTerm_comp, reindexTerm_comp]
      exact (reindexTerm_comp C c σ (κ ≫ π')).symm
    have ha : reindexTerm E a0 ρ = reindexTerm E a1 κ := by
      dsimp only [a0,a1]
      rw [reindexIso_comp_map, reindexIso_comp_map]
      apply Term.ext
      intro x
      exact (congrArg (fun m => m.app x x.val.2) (reindexIso_comp E A σ (κ ≫ π'))).symm
    have hc : reindexTerm (.product C E) c0 ρ = reindexTerm (.product C E) c1 κ :=
      by
      apply Term.ext
      intro x
      exact congrArg₂ (fun (c : (family C (reindex A (ρ ≫ π))).obj x)
        (a : (family E (reindex A (ρ ≫ π))).obj x) =>
          (⟨c,a⟩ : (family (.product C E) (reindex A (ρ ≫ π))).obj x))
        (congrArg (fun t => t.val x) hf) (congrArg (fun t => t.val x) ha)
    let P := lawFamily p s1 c1
    let j := j0 ≪≫ eqToIso (congrArg₂ (lawFamily p) hs hc) ≪≫ j1.symm
    exact piReindexIso X (lawFamily p s0 c0) σ ≪≫
      EquivalenceFamilies.piSecondIso (reindex X σ) j ≪≫ PiDomain.congr e P


def objectLaws (T : Specification.{u}) (Γ : Context.{u+1}) : Family (total (objects T.description Γ)) :=
  lawFamily T.law (objectStructure T.description Γ) unitContext

/-- Sethood and the law are retained native fields over each raw structured object. -/
def objectConditions (T : Specification.{u}) (Γ : Context.{u+1}) :
    Family (total (objects T.description Γ)) :=
  let S := HomotopyLevels.isSet (objectCarrier T.description Γ)
  sigma S (reindex (objectLaws T Γ) (projection S))

noncomputable def objectLawsFilling (T : Specification.{u}) (Γ : Context.{u+1}) :
    {F : Filling (objectLaws T Γ) // F.Lawful} :=
  let a := objectCarrierCode T.description Γ
  lawFilling T.law (objectStructure T.description Γ) unitContext
    (SmallUniverse.NativeDecode.filling a) (SmallUniverse.NativeDecode.filling_lawful a)

noncomputable def objectConditionsFilling (T : Specification.{u}) (Γ : Context.{u+1}) :
    {F : Filling (objectConditions T Γ) // F.Lawful} :=
  let a := objectCarrierCode T.description Γ
  let F := SmallUniverse.NativeDecode.filling a
  let hF := SmallUniverse.NativeDecode.filling_lawful a
  let S := HomotopyLevels.isSetFilling F hF
  let hS := HomotopyLevels.isSetFilling_lawful F hF
  let L := objectLawsFilling T Γ
  ⟨sigmaFilling S hS (L.1.reindex (projection _)),
    sigmaFilling_lawful S hS _ (L.2.reindex _)⟩

noncomputable def objectConditionsPresentation (T : Specification.{u}) (Γ : Context.{u+1}) :
    SmallUniverse.SmallPresentation.Data (objectConditions T Γ) :=
  let a := objectCarrierCode T.description Γ
  let P := SmallUniverse.decodePresentation a
  (HomotopyLevels.isSetPresentation P).sigma
    (smallReindex (lawPresentation T.law (objectStructure T.description Γ) unitContext P) _)

noncomputable def classifyObjectConditions (T : Specification.{u}) (Γ : Context.{u+1}) :
    SmallUniverse.LargeConstructors.Result (objectConditions T Γ) :=
  let F := objectConditionsFilling T Γ
  SmallUniverse.LargeConstructors.construct (objectConditionsPresentation T Γ) F.1 F.2

/-- The total family of all small native set carriers with structure and laws. -/
def modelObjects (T : Specification.{u}) (Γ : Context.{u+1}) : Family Γ :=
  sigma (objects T.description Γ) (objectConditions T Γ)

noncomputable def modelObjectsFilling (T : Specification.{u}) (Γ : Context.{u+1}) :
    {F : Filling (modelObjects T Γ) // F.Lawful} :=
  let O := objectsFilling T.description Γ
  let C := objectConditionsFilling T Γ
  ⟨sigmaFilling O.1 O.2 C.1, sigmaFilling_lawful O.1 O.2 C.1 C.2⟩

noncomputable def objectConditionsIsProp (T : Specification.{u}) (Γ : Context.{u+1}) :
    Term (HomotopyLevels.isProp (objectConditions T Γ)) := by
  apply lam
  apply lam
  let O := objects T.description Γ
  let A := objectCarrier T.description Γ
  let C := objectConditions T Γ
  let σ := projection (reindex C (projection C)) ≫ projection C
  let a := Term.reindex (generic C) (projection (reindex C (projection C)))
  let b := generic (reindex C (projection C))
  let code := objectCarrierCode T.description Γ
  let F := SmallUniverse.NativeDecode.filling code
  let hF := SmallUniverse.NativeDecode.filling_lawful code
  let aSet := sigmaFst (A := reindex (HomotopyLevels.isSet A) σ)
    (B := reindex (reindex (objectLaws T Γ) σ) (projection _)) a
  let sA := HomotopyLevels.reindexSetTerm A σ aSet
  let ps := HomotopyLevels.reindexProp (HomotopyLevels.isSetIsProp F hF) σ
  let pl := HomotopyLevels.mapProp
    (lawReindexIso T.law (objectStructure T.description Γ) unitContext σ).symm
    (lawIsProp T.law (reindexTerm T.description (objectStructure T.description Γ) σ)
      (reindexTerm (.fixed PUnit.{u+1}) unitContext σ) sA (F.reindex σ) (hF.reindex σ))
  let L := objectLawsFilling T Γ
  let p := HomotopyLevels.productIsProp ps pl
    ((HomotopyLevels.isSetFilling F hF).reindex σ)
    ((HomotopyLevels.isSetFilling_lawful F hF).reindex σ)
    (L.1.reindex σ) (L.2.reindex σ)
  exact HomotopyLevels.path p a b


private noncomputable def unreindexSetTerm (A : Family Γ) (σ : Δ ⟶ Γ)
    (s : Term (HomotopyLevels.isSet (reindex A σ))) :
    Term (reindex (HomotopyLevels.isSet A) σ) := by
  let τ := liftSub A σ
  let υ := liftSub (reindex A (projection A)) τ
  let q := Term.map (HomotopyLevels.isPropReindexIso (EquivalenceFamilies.contractionPaths A) υ).inv
    (HomotopyLevels.mapProp (HomotopyLevels.contractionPathsReindexIso A σ).symm (app (app s)))
  let s₁ := Term.map (piReindexIso (reindex A (projection A))
    (HomotopyLevels.isProp (EquivalenceFamilies.contractionPaths A)) τ).inv (lam q)
  exact Term.map (piReindexIso A
    (pi (reindex A (projection A)) (HomotopyLevels.isProp (EquivalenceFamilies.contractionPaths A))) σ).inv
    (lam s₁)

noncomputable def modelObject (T : Specification.{u}) (a : Γ ⟶ smallFamilyCodes.{u})
    (s : Term (family T.description (SmallUniverse.liftedDecode a)))
    (sA : Term (HomotopyLevels.isSet (SmallUniverse.liftedDecode a)))
    (p : Term (lawFamily T.law s unitContext)) : Term (modelObjects T Γ) := by
  let o := objectOf T.description a s
  let σ := pair (A := objects T.description Γ) (𝟙 Γ) o
  let hs := unreindexSetTerm (objectCarrier T.description Γ) σ sA
  have hp : Term (lawFamily T.law
      (reindexTerm T.description (objectStructure T.description Γ) σ)
      (reindexTerm (.fixed PUnit.{u+1}) unitContext σ)) := by
    change Term (lawFamily T.law
      (reindexTerm T.description (objectStructure T.description Γ) (pair (𝟙 Γ) (objectOf T.description a s)))
      unitContext)
    rw [objectStructure_at]
    exact p
  let hl := Term.map (lawReindexIso T.law (objectStructure T.description Γ) unitContext σ).inv hp
  let hc : Term (reindex (objectConditions T Γ) σ) :=
    sigmaIntro (B := reindex (reindex (objectLaws T Γ) σ) (projection _)) hs hl
  exact sigmaIntro o hc

noncomputable def modelPathProjectionEquivalence (T : Specification.{u})
    (z w : Term (modelObjects T Γ)) :
    HomotopyEquivalence (HomotopyLevels.pathMap (PropositionExtension.first (objectConditions T Γ)) z w) :=
  let O := objectsFilling T.description Γ
  let C := objectConditionsFilling T Γ
  PropositionExtension.pathEquivalence (objectConditions T Γ) z w (objectConditionsIsProp T Γ)
    O.1 O.2 C.1 C.2

end SquareKit.Cubical.Presheaf.StructureIdentity.Native
