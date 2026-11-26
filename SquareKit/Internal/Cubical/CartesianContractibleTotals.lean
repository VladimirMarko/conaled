import SquareKit.Internal.Cubical.CartesianEquivalenceComposition
import SquareKit.Internal.Cubical.CartesianRelativeExtension
set_option autoImplicit false
set_option warningAsError true
namespace SquareKit.Cubical.Cartesian
open CategoryTheory Glue
universe u
namespace ContractibleTotals

def restrictedSquare {Γ : Context.{u}} (φ : Subcontext Γ) :
    restrictContext ((φ.reindex (projection (interval Γ))).reindex
      (projection (interval (total (interval Γ))))) ⟶
      total (interval (total (interval (restrictContext φ)))) where
  app _ := TypeCat.ofHom (fun z => ⟨⟨⟨z.val.1.1,z.property⟩,z.val.1.2⟩,z.val.2⟩)
  naturality _ _ _ := rfl

noncomputable def verticalSquare {Γ Δ : Context.{u}} {X : Family Γ} {B : Family (total X)}
    (F : Filling B) (hF : F.Lawful) (σ : Δ ⟶ total X)
    {a b : Term (reindex B σ)} (p : Term (homogeneousPath (reindex B σ) a b)) :
    Term (reindex (sigma X B) (NativeSquare.squareBase Δ ≫ σ ≫ projection X)) :=
  sigmaIntro (B := reindex B (liftSub X (NativeSquare.squareBase Δ ≫ σ ≫ projection X)))
    (Term.reindex (generic X) (NativeSquare.squareBase Δ ≫ σ))
    (WeakConnection.squareTerm (F.reindex σ) (hF.reindex σ) p)

theorem verticalSquare_bottom {Γ Δ : Context.{u}} {X : Family Γ} {B : Family (total X)}
    (F : Filling B) (hF : F.Lawful) (σ : Δ ⟶ total X)
    {a b : Term (reindex B σ)} (p : Term (homogeneousPath (reindex B σ) a b)) :
    Term.reindex (verticalSquare F hF σ p) (endpointSub (total (interval Δ)) false) =
      Term.reindex (sigmaIntro (B := reindex B (liftSub X (σ ≫ projection X)))
        (Term.reindex (generic X) σ) a) (projection (interval Δ)) :=
  congrArg (sigmaIntro (B := reindex B (liftSub X (projection (interval Δ) ≫ σ ≫ projection X)))
    (Term.reindex (generic X) (projection (interval Δ) ≫ σ)))
    (WeakConnection.bottom (F.reindex σ) (hF.reindex σ) p)

theorem verticalSquare_top {Γ Δ : Context.{u}} {X : Family Γ} {B : Family (total X)}
    (F : Filling B) (hF : F.Lawful) (σ : Δ ⟶ total X)
    {a b : Term (reindex B σ)} (p : Term (homogeneousPath (reindex B σ) a b)) :
    Term.reindex (verticalSquare F hF σ p) (endpointSub (total (interval Δ)) true) =
      pathApp (verticalPath σ p) :=
  congrArg (sigmaIntro (B := reindex B (liftSub X (projection (interval Δ) ≫ σ ≫ projection X)))
    (Term.reindex (generic X) (projection (interval Δ) ≫ σ)))
    (WeakConnection.top (F.reindex σ) (hF.reindex σ) p)

theorem verticalSquare_left {Γ Δ : Context.{u}} {X : Family Γ} {B : Family (total X)}
    (F : Filling B) (hF : F.Lawful) (σ : Δ ⟶ total X)
    {a b : Term (reindex B σ)} (p : Term (homogeneousPath (reindex B σ) a b)) :
    Term.reindex (verticalSquare F hF σ p) (intervalSub (endpointSub Δ false)) =
      Term.reindex (sigmaIntro (B := reindex B (liftSub X (σ ≫ projection X)))
        (Term.reindex (generic X) σ) a) (projection (interval Δ)) :=
  congrArg (sigmaIntro (B := reindex B (liftSub X (projection (interval Δ) ≫ σ ≫ projection X)))
    (Term.reindex (generic X) (projection (interval Δ) ≫ σ)))
    (WeakConnection.left (F.reindex σ) (hF.reindex σ) p)

theorem verticalSquare_right {Γ Δ : Context.{u}} {X : Family Γ} {B : Family (total X)}
    (F : Filling B) (hF : F.Lawful) (σ : Δ ⟶ total X)
    {a b : Term (reindex B σ)} (p : Term (homogeneousPath (reindex B σ) a b)) :
    Term.reindex (verticalSquare F hF σ p) (intervalSub (endpointSub Δ true)) =
      pathApp (verticalPath σ p) :=
  congrArg (sigmaIntro (B := reindex B (liftSub X (projection (interval Δ) ≫ σ ≫ projection X)))
    (Term.reindex (generic X) (projection (interval Δ) ≫ σ)))
    (WeakConnection.right (F.reindex σ) (hF.reindex σ) p)

variable {Γ Δ : Context.{u}} {X : Family Γ} {A B : Family (total X)}
  (f : A ⟶ B) (σ : Δ ⟶ total B)

abbrev baseSub : Δ ⟶ Γ := σ ≫ projection B ≫ projection X
abbrev fiber : Family Δ :=
  reindex (Homotopy.fiber (Functor.whiskerLeft (projection B).mapElements f) (generic B)) σ

def basePoint : Term (reindex X (baseSub σ)) :=
  Term.reindex (generic X) (σ ≫ projection B)

def target : Term (reindex (sigma X B) (baseSub σ)) :=
  sigmaIntro (B := reindex B (liftSub X (baseSub σ))) (basePoint σ)
    (Term.reindex (generic B) σ)

variable {φ : Subcontext Δ} (s : PartialSection (fiber f σ) φ)

def partialSource : PartialSection (reindex (sigma X A) (baseSub σ)) φ :=
  PartialSection.ofRestricted
    (sigmaIntro (B := reindex A (liftSub X (restrictInclusion φ ≫ baseSub σ)))
      (Term.reindex (basePoint σ) (restrictInclusion φ))
      (genericFiberFst f (restrictInclusion φ ≫ σ) s.toRestricted))

noncomputable def source (c : Contractible (sigma X A))
    (F : Filling (sigma X A)) : Term (reindex (sigma X A) (baseSub σ)) :=
  (c.reindex (baseSub σ)).extend (F.reindex (baseSub σ)) (partialSource f σ s)

theorem source_boundary (c : Contractible (sigma X A))
    (F : Filling (sigma X A)) (hF : F.Lawful) (x : Δ.Elements) (hx : φ.Holds x) :
    (source f σ s c F).val x = (partialSource f σ s).val x hx :=
  (c.reindex (baseSub σ)).extend_boundary (F.reindex (baseSub σ)) (hF.reindex _) _ x hx

theorem source_restricted (c : Contractible (sigma X A))
    (F : Filling (sigma X A)) (hF : F.Lawful) :
    Term.reindex (source f σ s c F) (restrictInclusion φ) = (partialSource f σ s).toRestricted := by
  apply Term.ext
  intro x
  exact source_boundary f σ s c F hF ((restrictInclusion φ).mapElements.obj x) x.val.property


def image (a : Term (reindex (sigma X A) (baseSub σ))) :
    Term (reindex (sigma X B) (baseSub σ)) :=
  Term.map (Functor.whiskerLeft (baseSub σ).mapElements (sigmaSecondMap X f)) a

noncomputable def restrictedPath (c : Contractible (sigma X A))
    (F : Filling (sigma X A)) (hF : F.Lawful) :
    Term (homogeneousPath (reindex (sigma X B) (restrictInclusion φ ≫ baseSub σ))
      (Term.reindex (image f σ (source f σ s c F)) (restrictInclusion φ))
      (Term.reindex (target σ) (restrictInclusion φ))) := by
  let ι := restrictInclusion φ
  let p := verticalPath (ι ≫ σ ≫ projection B)
    (genericFiberPath f (ι ≫ σ) s.toRestricted)
  exact pathLam (pathApp p)
    (by
      have hz := pathApp_zero p
      change Term.reindex (pathApp p) (endpointSub (restrictContext φ) false) =
        Term.map (Functor.whiskerLeft (ι ≫ baseSub σ).mapElements (sigmaSecondMap X f))
          (partialSource f σ s).toRestricted at hz
      rw [← source_restricted f σ s c F hF] at hz
      exact hz)
    (pathApp_one p)

noncomputable def partialPath (c : Contractible (sigma X A))
    (F : Filling (sigma X A)) (hF : F.Lawful) :
    PartialSection (homogeneousPath (reindex (sigma X B) (baseSub σ))
      (image f σ (source f σ s c F)) (target σ)) φ :=
  PartialSection.ofRestricted (Term.map
    (pathReindexIso (reindex (sigma X B) (projection (interval Δ) ≫ baseSub σ))
      (image f σ (source f σ s c F)) (target σ) (restrictInclusion φ)).inv
    (restrictedPath f σ s c F hF))

noncomputable def totalPath (cA : Contractible (sigma X A))
    (FA : Filling (sigma X A)) (hFA : FA.Lawful)
    (cB : Contractible (sigma X B)) (FB : Filling (sigma X B))
    (hFB : FB.Lawful) :
    Term (homogeneousPath (reindex (sigma X B) (baseSub σ))
      (image f σ (source f σ s cA FA)) (target σ)) :=
  EquivalenceFamilies.ContractiblePaths.extend (cB.reindex (baseSub σ))
    (FB.reindex (baseSub σ)) (hFB.reindex _) (partialPath f σ s cA FA hFA)


theorem totalPath_boundary (cA : Contractible (sigma X A))
    (FA : Filling (sigma X A)) (hFA : FA.Lawful)
    (cB : Contractible (sigma X B)) (FB : Filling (sigma X B))
    (hFB : FB.Lawful) (x : Δ.Elements) (hx : φ.Holds x) :
    (totalPath f σ s cA FA hFA cB FB hFB).val x =
      (partialPath f σ s cA FA hFA).val x hx :=
  EquivalenceFamilies.ContractiblePaths.extend_boundary (cB.reindex (baseSub σ))
    (FB.reindex (baseSub σ)) (hFB.reindex _) (partialPath f σ s cA FA hFA) x hx

theorem partialPath_body (cA : Contractible (sigma X A))
    (FA : Filling (sigma X A)) (hFA : FA.Lawful)
    (x : (total (interval Δ)).Elements) (hx : (φ.reindex (projection (interval Δ))).Holds x) :
    (partialPath f σ s cA FA hFA).pathApp.val x hx =
      (pathApp (verticalPath (restrictInclusion φ ≫ σ ≫ projection B)
        (genericFiberPath f (restrictInclusion φ ≫ σ) s.toRestricted))).val
        ((restrictedInterval φ).mapElements.obj
          ((restrictContext (φ.reindex (projection (interval Δ)))).elementsMk x.obj ⟨x.val,hx⟩)) := by
  let i := pathReindexIso (reindex (sigma X B) (projection (interval Δ) ≫ baseSub σ))
    (image f σ (source f σ s cA FA)) (target σ) (restrictInclusion φ)
  have h := Term.map_iso_roundtrip i.symm (restrictedPath f σ s cA FA hFA)
  let z := (restrictedInterval φ).mapElements.obj
    ((restrictContext (φ.reindex (projection (interval Δ)))).elementsMk x.obj ⟨x.val,hx⟩)
  exact congrArg (fun t : Term (homogeneousPath
      (reindex (sigma X B) (restrictInclusion φ ≫ baseSub σ))
      (Term.reindex (image f σ (source f σ s cA FA)) (restrictInclusion φ))
      (Term.reindex (target σ) (restrictInclusion φ))) => (pathApp t).val z) h

theorem partialPath_base (cA : Contractible (sigma X A))
    (FA : Filling (sigma X A)) (hFA : FA.Lawful)
    (x : (total (interval Δ)).Elements) (hx : (φ.reindex (projection (interval Δ))).Holds x) :
    ((partialPath f σ s cA FA hFA).pathApp.val x hx).1 =
      (basePoint σ).val ((projection (interval Δ)).mapElements.obj x) := by
  let i := pathReindexIso (reindex (sigma X B) (projection (interval Δ) ≫ baseSub σ))
    (image f σ (source f σ s cA FA)) (target σ) (restrictInclusion φ)
  have h := Term.map_iso_roundtrip i.symm (restrictedPath f σ s cA FA hFA)
  let z := (restrictedInterval φ).mapElements.obj
    ((restrictContext (φ.reindex (projection (interval Δ)))).elementsMk x.obj ⟨x.val,hx⟩)
  exact congrArg (fun t : Term (homogeneousPath
      (reindex (sigma X B) (restrictInclusion φ ≫ baseSub σ))
      (Term.reindex (image f σ (source f σ s cA FA)) (restrictInclusion φ))
      (Term.reindex (target σ) (restrictInclusion φ))) => ((pathApp t).val z).1) h

noncomputable def sourceBox (cA : Contractible (sigma X A))
    (FA : Filling (sigma X A)) (hFA : FA.Lawful) :
    OpenBox (reindex (sigma X A) (projection (interval Δ) ≫ baseSub σ)) φ (endpoint Δ false) where
  tube := (partialSource f σ s).reindex (projection (interval Δ))
  base := source f σ s cA FA
  boundary x hx := (source_boundary f σ s cA FA hFA x hx).symm

noncomputable def baseLine (cA : Contractible (sigma X A))
    (FA : Filling (sigma X A)) (hFA : FA.Lawful)
    (cB : Contractible (sigma X B)) (FB : Filling (sigma X B))
    (hFB : FB.Lawful) : Term (reindex X (projection (interval Δ) ≫ baseSub σ)) :=
  sigmaFst (B := reindex B (liftSub X (projection (interval Δ) ≫ baseSub σ)))
    (pathApp (totalPath f σ s cA FA hFA cB FB hFB))

theorem baseLine_fills (cA : Contractible (sigma X A))
    (FA : Filling (sigma X A)) (hFA : FA.Lawful)
    (cB : Contractible (sigma X B)) (FB : Filling (sigma X B))
    (hFB : FB.Lawful) :
    (OpenBox.sigmaFst (B := reindex A (liftSub X (projection (interval Δ) ≫ baseSub σ)))
      (sourceBox f σ s cA FA hFA)).Fills (baseLine f σ s cA FA hFA cB FB hFB) := by
  constructor
  · exact congrArg (sigmaFst (B := reindex B (liftSub X (baseSub σ))))
      (pathApp_zero (totalPath f σ s cA FA hFA cB FB hFB))
  · intro x hx
    have h := totalPath_boundary f σ s cA FA hFA cB FB hFB
      ((projection (interval Δ)).mapElements.obj x) hx
    have h' := congrArg (fun p => (p.val.val (𝟙 _) x.val.2).1) h
    exact h'.trans (partialPath_base f σ s cA FA hFA x hx)

noncomputable def sourceLine (cA : Contractible (sigma X A))
    (FA : Filling (sigma X A)) (hFA : FA.Lawful)
    (cB : Contractible (sigma X B)) (FB : Filling (sigma X B))
    (hFB : FB.Lawful) (GA : Filling A) :
    Term (reindex (sigma X A) (projection (interval Δ) ≫ baseSub σ)) :=
  fillOver GA (projection (interval Δ) ≫ baseSub σ) (sourceBox f σ s cA FA hFA)
    (baseLine f σ s cA FA hFA cB FB hFB) (baseLine_fills f σ s cA FA hFA cB FB hFB)


theorem sourceLine_fills (cA : Contractible (sigma X A))
    (FA : Filling (sigma X A)) (hFA : FA.Lawful)
    (cB : Contractible (sigma X B)) (FB : Filling (sigma X B))
    (hFB : FB.Lawful) (GA : Filling A) (hGA : GA.Lawful) :
    (sourceBox f σ s cA FA hFA).Fills (sourceLine f σ s cA FA hFA cB FB hFB GA) :=
  fillOver_fills GA hGA (projection (interval Δ) ≫ baseSub σ) _ _
    (baseLine_fills f σ s cA FA hFA cB FB hFB)

theorem sourceLine_fst (cA : Contractible (sigma X A))
    (FA : Filling (sigma X A)) (hFA : FA.Lawful)
    (cB : Contractible (sigma X B)) (FB : Filling (sigma X B))
    (hFB : FB.Lawful) (GA : Filling A) :
    sigmaFst (B := reindex A (liftSub X (projection (interval Δ) ≫ baseSub σ)))
      (sourceLine f σ s cA FA hFA cB FB hFB GA) = baseLine f σ s cA FA hFA cB FB hFB := rfl


variable (K : Filling B) (hK : K.Lawful)
variable (cA : Contractible (sigma X A))
  (FA : Filling (sigma X A)) (hFA : FA.Lawful)
  (cB : Contractible (sigma X B)) (FB : Filling (sigma X B))
  (hFB : FB.Lawful) (GA : Filling A)

noncomputable def imageLine :
    Term (reindex (sigma X B) (projection (interval Δ) ≫ baseSub σ)) :=
  Term.map (Functor.whiskerLeft (projection (interval Δ) ≫ baseSub σ).mapElements
    (sigmaSecondMap X f)) (sourceLine f σ s cA FA hFA cB FB hFB GA)

abbrev rectangleFamily := reindex (sigma X B)
  (projection (interval (total (interval Δ))) ≫ projection (interval Δ) ≫ baseSub σ)

abbrev sideFace (Δ : Context.{u}) := (intervalFace Δ false).join (intervalFace Δ true)

noncomputable def rectangleSides : PartialSection (rectangleFamily (X := X) σ)
    ((sideFace Δ).reindex (projection (interval (total (interval Δ))))) :=
  (endpointBoundary (rectangleFamily (X := X) σ)
    (imageLine f σ s cA FA hFA cB FB hFB GA)
    (pathApp (totalPath f σ s cA FA hFA cB FB hFB))).reindex (swapIntervals Δ)


noncomputable def rectangleOld : PartialSection (rectangleFamily (X := X) σ)
    ((φ.reindex (projection (interval Δ))).reindex (projection (interval (total (interval Δ))))) :=
  PartialSection.ofRestricted (Term.reindex
    (verticalSquare K hK (restrictInclusion φ ≫ σ ≫ projection B)
      (genericFiberPath f (restrictInclusion φ ≫ σ) s.toRestricted)) (restrictedSquare φ))


include hFA in
theorem rectangleOld_zero (x : (total (interval Δ)).Elements)
    (hx : (φ.reindex (projection (interval Δ))).Holds x) :
    (rectangleOld f σ s K hK).val
      ((endpointSub (total (interval Δ)) false).mapElements.obj x) hx =
      (image f σ (source f σ s cA FA)).val ((projection (interval Δ)).mapElements.obj x) := by
  let y := (projection (interval Δ)).mapElements.obj x
  let y' := (restrictContext φ).elementsMk y.obj ⟨y.val,hx⟩
  let z := extendObj (interval (restrictContext φ)) y' x.val.2
  have h := congrArg (fun t => t.val z)
    (verticalSquare_bottom K hK (restrictInclusion φ ≫ σ ≫ projection B)
      (genericFiberPath f (restrictInclusion φ ≫ σ) s.toRestricted))
  exact h.trans (congrArg ((sigmaSecondMap X f).app ((baseSub σ).mapElements.obj y))
    (source_boundary f σ s cA FA hFA y hx)).symm

include hFA in
theorem rectangleOld_left (x : (total (interval Δ)).Elements)
    (hx : (φ.reindex (projection (interval Δ))).Holds x) :
    (rectangleOld f σ s K hK).val
      ((intervalSub (endpointSub Δ false)).mapElements.obj x) hx =
      (image f σ (source f σ s cA FA)).val ((projection (interval Δ)).mapElements.obj x) := by
  let y := (projection (interval Δ)).mapElements.obj x
  let y' := (restrictContext φ).elementsMk y.obj ⟨y.val,hx⟩
  let z := extendObj (interval (restrictContext φ)) y' x.val.2
  have h := congrArg (fun t => t.val z)
    (verticalSquare_left K hK (restrictInclusion φ ≫ σ ≫ projection B)
      (genericFiberPath f (restrictInclusion φ ≫ σ) s.toRestricted))
  exact h.trans (congrArg ((sigmaSecondMap X f).app ((baseSub σ).mapElements.obj y))
    (source_boundary f σ s cA FA hFA y hx)).symm

theorem rectangleOld_right (x : (total (interval Δ)).Elements)
    (hx : (φ.reindex (projection (interval Δ))).Holds x) :
    (rectangleOld f σ s K hK).val
      ((intervalSub (endpointSub Δ true)).mapElements.obj x) hx =
      (partialPath f σ s cA FA hFA).pathApp.val x hx := by
  let y := (projection (interval Δ)).mapElements.obj x
  let y' := (restrictContext φ).elementsMk y.obj ⟨y.val,hx⟩
  let z := extendObj (interval (restrictContext φ)) y' x.val.2
  have h := congrArg (fun t => t.val z)
    (verticalSquare_right K hK (restrictInclusion φ ≫ σ ≫ projection B)
      (genericFiberPath f (restrictInclusion φ ≫ σ) s.toRestricted))
  exact h.trans (partialPath_body f σ s cA FA hFA x hx).symm

theorem rectangleOld_top (x : (total (interval Δ)).Elements)
    (hx : (φ.reindex (projection (interval Δ))).Holds x) :
    (rectangleOld f σ s K hK).val
      ((endpointSub (total (interval Δ)) true).mapElements.obj x) hx =
      (partialPath f σ s cA FA hFA).pathApp.val x hx := by
  let y := (projection (interval Δ)).mapElements.obj x
  let y' := (restrictContext φ).elementsMk y.obj ⟨y.val,hx⟩
  let z := extendObj (interval (restrictContext φ)) y' x.val.2
  have h := congrArg (fun t => t.val z)
    (verticalSquare_top K hK (restrictInclusion φ ≫ σ ≫ projection B)
      (genericFiberPath f (restrictInclusion φ ≫ σ) s.toRestricted))
  exact h.trans (partialPath_body f σ s cA FA hFA x hx).symm

theorem rectangleOld_base (x : (total (interval (total (interval Δ)))).Elements)
    (hx : ((φ.reindex (projection (interval Δ))).reindex (projection (interval (total (interval Δ))))).Holds x) :
    ((rectangleOld f σ s K hK).val x hx).1 =
      (basePoint σ).val ((NativeSquare.squareBase Δ).mapElements.obj x) := rfl

theorem imageLine_boundary (hGA : GA.Lawful) (x : (total (interval Δ)).Elements)
    (hx : (φ.reindex (projection (interval Δ))).Holds x) :
    (imageLine f σ s cA FA hFA cB FB hFB GA).val x =
      (image f σ (source f σ s cA FA)).val ((projection (interval Δ)).mapElements.obj x) := by
  have h := (sourceLine_fills f σ s cA FA hFA cB FB hFB GA hGA).2 x hx
  have h' := source_boundary f σ s cA FA hFA
    ((projection (interval Δ)).mapElements.obj x) hx
  exact congrArg ((sigmaSecondMap X f).app ((baseSub σ).mapElements.obj
    ((projection (interval Δ)).mapElements.obj x))) (h.trans h'.symm)

theorem totalPath_line_boundary (x : (total (interval Δ)).Elements)
    (hx : (φ.reindex (projection (interval Δ))).Holds x) :
    (pathApp (totalPath f σ s cA FA hFA cB FB hFB)).val x =
      (partialPath f σ s cA FA hFA).pathApp.val x hx :=
  congrArg (fun p => p.val.val (𝟙 _) x.val.2)
    (totalPath_boundary f σ s cA FA hFA cB FB hFB
      ((projection (interval Δ)).mapElements.obj x) hx)

theorem rectangleSides_left (x : (total (interval Δ)).Elements)
    (hx : ((sideFace Δ).reindex (projection (interval (total (interval Δ))))).Holds
      ((liftSub (interval (total (interval Δ))) (endpointSub Δ false)).mapElements.obj x)) :
    (rectangleSides f σ s cA FA hFA cB FB hFB GA).val
      ((liftSub (interval (total (interval Δ))) (endpointSub Δ false)).mapElements.obj x) hx =
      (imageLine f σ s cA FA hFA cB FB hFB GA).val x := by
  let z := (endpointSub (total (interval Δ)) false).mapElements.obj x
  have hz : (intervalFace (total (interval Δ)) false).Holds z :=
    (intervalFace_iff false z).mpr rfl
  exact (endpointBoundary_zero (rectangleFamily (X := X) σ)
    (imageLine f σ s cA FA hFA cB FB hFB GA)
    (pathApp (totalPath f σ s cA FA hFA cB FB hFB)) z hx hz).trans
    (eq_of_heq (endpointSection_val (rectangleFamily (X := X) σ) false
      (imageLine f σ s cA FA hFA cB FB hFB GA) z hz))

theorem rectangleSides_right (x : (total (interval Δ)).Elements)
    (hx : ((sideFace Δ).reindex (projection (interval (total (interval Δ))))).Holds
      ((liftSub (interval (total (interval Δ))) (endpointSub Δ true)).mapElements.obj x)) :
    (rectangleSides f σ s cA FA hFA cB FB hFB GA).val
      ((liftSub (interval (total (interval Δ))) (endpointSub Δ true)).mapElements.obj x) hx =
      (pathApp (totalPath f σ s cA FA hFA cB FB hFB)).val x := by
  let z := (endpointSub (total (interval Δ)) true).mapElements.obj x
  have hz : (intervalFace (total (interval Δ)) true).Holds z :=
    (intervalFace_iff true z).mpr rfl
  exact (endpointBoundary_one (rectangleFamily (X := X) σ)
    (imageLine f σ s cA FA hFA cB FB hFB GA)
    (pathApp (totalPath f σ s cA FA hFA cB FB hFB)) z hx hz).trans
    (eq_of_heq (endpointSection_val (rectangleFamily (X := X) σ) true
      (pathApp (totalPath f σ s cA FA hFA cB FB hFB)) z hz))

theorem rectangle_compatible (hGA : GA.Lawful) :
    (rectangleOld f σ s K hK).Compatible
      (rectangleSides f σ s cA FA hFA cB FB hFB GA) := by
  intro z hz hs
  rcases z with @⟨I,⟨⟨γ,j⟩,i⟩⟩
  rcases (Subcontext.full_join (intervalFace Δ false) (intervalFace Δ true)
    ((total (interval Δ)).elementsMk I ⟨γ,j⟩)).mp hs with hj | hj
  · have he := (intervalFace_iff false
      ((total (interval Δ)).elementsMk I ⟨γ,j⟩)).mp hj
    change j = (endpoint Δ false).val (Δ.elementsMk I γ) at he
    subst j
    let x := (total (interval Δ)).elementsMk I ⟨γ,i⟩
    exact (rectangleOld_left f σ s K hK cA FA hFA x hz).trans
      ((imageLine_boundary f σ s cA FA hFA cB FB hFB GA hGA x hz).symm.trans
        (rectangleSides_left f σ s cA FA hFA cB FB hFB GA x hs).symm)
  · have he := (intervalFace_iff true
      ((total (interval Δ)).elementsMk I ⟨γ,j⟩)).mp hj
    change j = (endpoint Δ true).val (Δ.elementsMk I γ) at he
    subst j
    let x := (total (interval Δ)).elementsMk I ⟨γ,i⟩
    exact (rectangleOld_right f σ s K hK cA FA hFA x hz).trans
      ((totalPath_line_boundary f σ s cA FA hFA cB FB hFB x hz).symm.trans
        (rectangleSides_right f σ s cA FA hFA cB FB hFB GA x hs).symm)


theorem imageLine_zero (hGA : GA.Lawful) :
    Term.reindex (imageLine f σ s cA FA hFA cB FB hFB GA) (endpointSub Δ false) =
      image f σ (source f σ s cA FA) :=
  congrArg (Term.map (Functor.whiskerLeft (baseSub σ).mapElements (sigmaSecondMap X f)))
    (sourceLine_fills f σ s cA FA hFA cB FB hFB GA hGA).1

theorem rectangleSides_zero (hGA : GA.Lawful) (x : (total (interval Δ)).Elements)
    (hx : (sideFace Δ).Holds x) :
    (rectangleSides f σ s cA FA hFA cB FB hFB GA).val
      ((endpointSub (total (interval Δ)) false).mapElements.obj x) hx =
      (image f σ (source f σ s cA FA)).val ((projection (interval Δ)).mapElements.obj x) := by
  rcases x with @⟨I,⟨γ,j⟩⟩
  rcases (Subcontext.full_join _ _ _).mp hx with hj | hj
  · have he := (intervalFace_iff false
      ((total (interval Δ)).elementsMk I ⟨γ,j⟩)).mp hj
    change j = (endpoint Δ false).val (Δ.elementsMk I γ) at he
    subst j
    let x := (endpointSub Δ false).mapElements.obj (Δ.elementsMk I γ)
    exact (rectangleSides_left f σ s cA FA hFA cB FB hFB GA x hx).trans
      (congrArg (fun t => t.val (Δ.elementsMk I γ))
        (imageLine_zero f σ s cA FA hFA cB FB hFB GA hGA))
  · have he := (intervalFace_iff true
      ((total (interval Δ)).elementsMk I ⟨γ,j⟩)).mp hj
    change j = (endpoint Δ true).val (Δ.elementsMk I γ) at he
    subst j
    let x := (endpointSub Δ false).mapElements.obj (Δ.elementsMk I γ)
    exact (rectangleSides_right f σ s cA FA hFA cB FB hFB GA x hx).trans
      (congrArg (fun t => t.val (Δ.elementsMk I γ))
        (pathApp_zero (totalPath f σ s cA FA hFA cB FB hFB)))

abbrev rectangleFace (φ : Subcontext Δ) :=
  (φ.reindex (projection (interval Δ))).join (sideFace Δ)

noncomputable def rectangleTube (hGA : GA.Lawful) :
    PartialSection (rectangleFamily (X := X) σ)
      ((rectangleFace φ).reindex (projection (interval (total (interval Δ))))) :=
  (rectangleOld f σ s K hK).glue
    (rectangleSides f σ s cA FA hFA cB FB hFB GA)
    (rectangle_compatible f σ s K hK cA FA hFA cB FB hFB GA hGA)

noncomputable def rectangleBox (hGA : GA.Lawful) :
    OpenBox (rectangleFamily (X := X) σ) (rectangleFace φ) (endpoint (total (interval Δ)) false) where
  tube := rectangleTube f σ s K hK cA FA hFA cB FB hFB GA hGA
  base := Term.reindex (image f σ (source f σ s cA FA)) (projection (interval Δ))
  boundary x hx := by
    rcases (Subcontext.full_join _ _ x).mp hx with h | h
    · exact (glueValue_left (rectangleOld f σ s K hK)
        (rectangleSides f σ s cA FA hFA cB FB hFB GA)
        ((endpointSub (total (interval Δ)) false).mapElements.obj x) hx h).trans
        (rectangleOld_zero f σ s K hK cA FA hFA x h)
    · exact (glueValue_right (rectangleOld f σ s K hK)
        (rectangleSides f σ s cA FA hFA cB FB hFB GA)
        (rectangle_compatible f σ s K hK cA FA hFA cB FB hFB GA hGA)
        ((endpointSub (total (interval Δ)) false).mapElements.obj x) hx h).trans
        (rectangleSides_zero f σ s cA FA hFA cB FB hFB GA hGA x h)


noncomputable def rectangleBase : Term (reindex X
    (projection (interval (total (interval Δ))) ≫ projection (interval Δ) ≫ baseSub σ)) :=
  Term.reindex (baseLine f σ s cA FA hFA cB FB hFB)
    (swapIntervals Δ ≫ projection (interval (total (interval Δ))))

theorem rectangleSides_base (z : (total (interval (total (interval Δ)))).Elements)
    (hz : ((sideFace Δ).reindex (projection (interval (total (interval Δ))))).Holds z) :
    ((rectangleSides f σ s cA FA hFA cB FB hFB GA).val z hz).1 =
      (rectangleBase f σ s cA FA hFA cB FB hFB).val z := by
  rcases z with @⟨I,⟨⟨γ,j⟩,i⟩⟩
  rcases (Subcontext.full_join (intervalFace Δ false) (intervalFace Δ true)
    ((total (interval Δ)).elementsMk I ⟨γ,j⟩)).mp hz with hj | hj
  · have he := (intervalFace_iff false
      ((total (interval Δ)).elementsMk I ⟨γ,j⟩)).mp hj
    change j = (endpoint Δ false).val (Δ.elementsMk I γ) at he
    subst j
    have h := congrArg (fun z : (sigma X B).obj
        ((baseSub σ).mapElements.obj (Δ.elementsMk I γ)) => z.1)
      (rectangleSides_left f σ s cA FA hFA cB FB hFB GA
        ((total (interval Δ)).elementsMk I ⟨γ,i⟩) hz)
    exact h
  · have he := (intervalFace_iff true
      ((total (interval Δ)).elementsMk I ⟨γ,j⟩)).mp hj
    change j = (endpoint Δ true).val (Δ.elementsMk I γ) at he
    subst j
    exact congrArg Sigma.fst (rectangleSides_right f σ s cA FA hFA cB FB hFB GA
      ((total (interval Δ)).elementsMk I ⟨γ,i⟩) hz)

theorem rectangleBase_fills (hGA : GA.Lawful) :
    (OpenBox.sigmaFst (B := reindex B (liftSub X
      (projection (interval (total (interval Δ))) ≫ projection (interval Δ) ≫ baseSub σ)))
      (rectangleBox f σ s K hK cA FA hFA cB FB hFB GA hGA)).Fills
      (rectangleBase f σ s cA FA hFA cB FB hFB) := by
  constructor
  · exact congrArg (fun t => Term.reindex t (projection (interval Δ)))
      (baseLine_fills f σ s cA FA hFA cB FB hFB).1
  · intro z hz
    rcases (Subcontext.full_join (φ.reindex (projection (interval Δ))) (sideFace Δ)
      ((projection (interval (total (interval Δ)))).mapElements.obj z)).mp hz with h | h
    · have hg := glueValue_left (rectangleOld f σ s K hK)
        (rectangleSides f σ s cA FA hFA cB FB hFB GA) z hz h
      have hb := (baseLine_fills f σ s cA FA hFA cB FB hFB).2
        ((swapIntervals Δ ≫ projection (interval (total (interval Δ)))).mapElements.obj z) h
      have hp := rectangleOld_base f σ s K hK z h
      exact (hb.trans hp.symm).trans (congrArg Sigma.fst hg).symm
    · have hg := glueValue_right (rectangleOld f σ s K hK)
        (rectangleSides f σ s cA FA hFA cB FB hFB GA)
        (rectangle_compatible f σ s K hK cA FA hFA cB FB hFB GA hGA) z hz h
      exact (rectangleSides_base f σ s cA FA hFA cB FB hFB GA z h).symm.trans
        (congrArg Sigma.fst hg).symm

noncomputable def rectangle (hGA : GA.Lawful) (GB : Filling B) :
    Term (rectangleFamily (X := X) σ) :=
  fillOver GB
    (projection (interval (total (interval Δ))) ≫ projection (interval Δ) ≫ baseSub σ)
    (rectangleBox f σ s K hK cA FA hFA cB FB hFB GA hGA)
    (rectangleBase f σ s cA FA hFA cB FB hFB)
    (rectangleBase_fills f σ s K hK cA FA hFA cB FB hFB GA hGA)

theorem rectangle_fills (hGA : GA.Lawful) (GB : Filling B) (hGB : GB.Lawful) :
    (rectangleBox f σ s K hK cA FA hFA cB FB hFB GA hGA).Fills
      (rectangle f σ s K hK cA FA hFA cB FB hFB GA hGA GB) :=
  fillOver_fills GB hGB
    (projection (interval (total (interval Δ))) ≫ projection (interval Δ) ≫ baseSub σ)
    _ _ (rectangleBase_fills f σ s K hK cA FA hFA cB FB hFB GA hGA)

theorem rectangle_fst (hGA : GA.Lawful) (GB : Filling B) :
    sigmaFst (B := reindex B (liftSub X
      (projection (interval (total (interval Δ))) ≫ projection (interval Δ) ≫ baseSub σ)))
      (rectangle f σ s K hK cA FA hFA cB FB hFB GA hGA GB) =
      rectangleBase f σ s cA FA hFA cB FB hFB := rfl


variable (hGA : GA.Lawful) (GB : Filling B) (hGB : GB.Lawful)

include hGB in
theorem rectangle_left :
    Term.reindex (rectangle f σ s K hK cA FA hFA cB FB hFB GA hGA GB)
      (liftSub (interval (total (interval Δ))) (endpointSub Δ false)) =
      imageLine f σ s cA FA hFA cB FB hFB GA := by
  apply Term.ext
  intro x
  let z := (liftSub (interval (total (interval Δ))) (endpointSub Δ false)).mapElements.obj x
  have hz : (intervalFace Δ false).Holds
      ((projection (interval (total (interval Δ)))).mapElements.obj z) :=
    (intervalFace_iff false _).mpr rfl
  have hs := (Subcontext.full_join (intervalFace Δ false) (intervalFace Δ true) _).mpr (Or.inl hz)
  have hf := (Subcontext.full_join (φ.reindex (projection (interval Δ))) (sideFace Δ) _).mpr (Or.inr hs)
  exact ((rectangle_fills f σ s K hK cA FA hFA cB FB hFB GA hGA GB hGB).2 z hf).trans
    ((glueValue_right (rectangleOld f σ s K hK)
      (rectangleSides f σ s cA FA hFA cB FB hFB GA)
      (rectangle_compatible f σ s K hK cA FA hFA cB FB hFB GA hGA) z hf hs).trans
      (rectangleSides_left f σ s cA FA hFA cB FB hFB GA x hs))

include hGB in
theorem rectangle_right :
    Term.reindex (rectangle f σ s K hK cA FA hFA cB FB hFB GA hGA GB)
      (liftSub (interval (total (interval Δ))) (endpointSub Δ true)) =
      pathApp (totalPath f σ s cA FA hFA cB FB hFB) := by
  apply Term.ext
  intro x
  let z := (liftSub (interval (total (interval Δ))) (endpointSub Δ true)).mapElements.obj x
  have hz : (intervalFace Δ true).Holds
      ((projection (interval (total (interval Δ)))).mapElements.obj z) :=
    (intervalFace_iff true _).mpr rfl
  have hs := (Subcontext.full_join (intervalFace Δ false) (intervalFace Δ true) _).mpr (Or.inr hz)
  have hf := (Subcontext.full_join (φ.reindex (projection (interval Δ))) (sideFace Δ) _).mpr (Or.inr hs)
  exact ((rectangle_fills f σ s K hK cA FA hFA cB FB hFB GA hGA GB hGB).2 z hf).trans
    ((glueValue_right (rectangleOld f σ s K hK)
      (rectangleSides f σ s cA FA hFA cB FB hFB GA)
      (rectangle_compatible f σ s K hK cA FA hFA cB FB hFB GA hGA) z hf hs).trans
      (rectangleSides_right f σ s cA FA hFA cB FB hFB GA x hs))

include hGB in
theorem rectangle_old (z : (total (interval (total (interval Δ)))).Elements)
    (hz : ((φ.reindex (projection (interval Δ))).reindex
      (projection (interval (total (interval Δ))))).Holds z) :
    (rectangle f σ s K hK cA FA hFA cB FB hFB GA hGA GB).val z =
      (rectangleOld f σ s K hK).val z hz := by
  have hf := (Subcontext.full_join (φ.reindex (projection (interval Δ))) (sideFace Δ)
    ((projection (interval (total (interval Δ)))).mapElements.obj z)).mpr (Or.inl hz)
  exact ((rectangle_fills f σ s K hK cA FA hFA cB FB hFB GA hGA GB hGB).2 z hf).trans
    (glueValue_left (rectangleOld f σ s K hK)
      (rectangleSides f σ s cA FA hFA cB FB hFB GA) z hf hz)

noncomputable def sourceEndpoint : Term (reindex (sigma X A) (baseSub σ)) :=
  Term.reindex (sourceLine f σ s cA FA hFA cB FB hFB GA) (endpointSub Δ true)

theorem sourceEndpoint_base :
    basePoint σ = sigmaFst (B := reindex A (liftSub X (baseSub σ)))
      (sourceEndpoint f σ s cA FA hFA cB FB hFB GA) := by
  exact (congrArg (sigmaFst (B := reindex B (liftSub X (baseSub σ))))
    (pathApp_one (totalPath f σ s cA FA hFA cB FB hFB))).symm

noncomputable def endpointA : Term (reindex A (σ ≫ projection B)) :=
  Term.sigmaSndOver (B := reindex A (liftSub X (baseSub σ)))
    (sourceEndpoint f σ s cA FA hFA cB FB hFB GA) (basePoint σ)
    (sourceEndpoint_base f σ s cA FA hFA cB FB hFB GA)

noncomputable def endpointEdge : Term (reindex (sigma X B) (projection (interval Δ) ≫ baseSub σ)) :=
  Term.reindex (rectangle f σ s K hK cA FA hFA cB FB hFB GA hGA GB)
    (endpointSub (total (interval Δ)) true)

theorem endpointEdge_base :
    Term.reindex (basePoint σ) (projection (interval Δ)) =
      sigmaFst (B := reindex B (liftSub X (projection (interval Δ) ≫ baseSub σ)))
        (endpointEdge f σ s K hK cA FA hFA cB FB hFB GA hGA GB) :=
  congrArg (fun t => Term.reindex t (projection (interval Δ)))
    (congrArg (sigmaFst (B := reindex B (liftSub X (baseSub σ))))
      (pathApp_one (totalPath f σ s cA FA hFA cB FB hFB))).symm

noncomputable def endpointBody : Term (reindex B (projection (interval Δ) ≫ σ ≫ projection B)) :=
  Term.sigmaSndOver (B := reindex B (liftSub X (projection (interval Δ) ≫ baseSub σ)))
    (endpointEdge f σ s K hK cA FA hFA cB FB hFB GA hGA GB)
    (Term.reindex (basePoint σ) (projection (interval Δ)))
    (endpointEdge_base f σ s K hK cA FA hFA cB FB hFB GA hGA GB)


private theorem family_hom_app_heq {Ξ : Context.{u}} {D E : Family Ξ} (g : D ⟶ E)
    {x y : Ξ.Elements} (h : x = y) {a : D.obj x} {b : D.obj y} (hab : HEq a b) :
    HEq (g.app x a) (g.app y b) := by
  cases h
  cases hab
  rfl

include hGB in
theorem endpointEdge_zero :
    Term.reindex (endpointEdge f σ s K hK cA FA hFA cB FB hFB GA hGA GB) (endpointSub Δ false) =
      image f σ (sourceEndpoint f σ s cA FA hFA cB FB hFB GA) :=
  congrArg (fun t => Term.reindex t (endpointSub Δ true))
    (rectangle_left f σ s K hK cA FA hFA cB FB hFB GA hGA GB hGB)

include hGB in
theorem endpointEdge_one :
    Term.reindex (endpointEdge f σ s K hK cA FA hFA cB FB hFB GA hGA GB) (endpointSub Δ true) = target σ :=
  (congrArg (fun t => Term.reindex t (endpointSub Δ true))
    (rectangle_right f σ s K hK cA FA hFA cB FB hFB GA hGA GB hGB)).trans
      (pathApp_one (totalPath f σ s cA FA hFA cB FB hFB))

include hGB in
theorem endpointBody_zero :
    Term.reindex (endpointBody f σ s K hK cA FA hFA cB FB hFB GA hGA GB) (endpointSub Δ false) =
      Term.map (Functor.whiskerLeft (σ ≫ projection B).mapElements f)
        (endpointA f σ s cA FA hFA cB FB hFB GA) := by
  apply Term.ext
  intro x
  have hb := congrArg (fun t => t.val x) (sourceEndpoint_base f σ s cA FA hFA cB FB hFB GA)
  have ha := Term.sigmaSndOver_val (B := reindex A (liftSub X (baseSub σ)))
    (sourceEndpoint f σ s cA FA hFA cB FB hFB GA) (basePoint σ)
    (sourceEndpoint_base f σ s cA FA hFA cB FB hFB GA) x
  have hm := family_hom_app_heq f (congrArg (extendObj X ((baseSub σ).mapElements.obj x)) hb) ha
  have he := (Sigma.mk.inj (congrArg (fun t => t.val x)
    (endpointEdge_zero f σ s K hK cA FA hFA cB FB hFB GA hGA GB hGB))).2
  exact eq_of_heq ((Term.sigmaSndOver_val
    (B := reindex B (liftSub X (projection (interval Δ) ≫ baseSub σ)))
    (endpointEdge f σ s K hK cA FA hFA cB FB hFB GA hGA GB)
    (Term.reindex (basePoint σ) (projection (interval Δ)))
    (endpointEdge_base f σ s K hK cA FA hFA cB FB hFB GA hGA GB)
    ((endpointSub Δ false).mapElements.obj x)).trans (he.trans hm.symm))

include hGB in
theorem endpointBody_one :
    Term.reindex (endpointBody f σ s K hK cA FA hFA cB FB hFB GA hGA GB) (endpointSub Δ true) =
      Term.reindex (generic B) σ := by
  apply Term.ext
  intro x
  have he := (Sigma.mk.inj (congrArg (fun t => t.val x)
    (endpointEdge_one f σ s K hK cA FA hFA cB FB hFB GA hGA GB hGB))).2
  exact eq_of_heq ((Term.sigmaSndOver_val
    (B := reindex B (liftSub X (projection (interval Δ) ≫ baseSub σ)))
    (endpointEdge f σ s K hK cA FA hFA cB FB hFB GA hGA GB)
    (Term.reindex (basePoint σ) (projection (interval Δ)))
    (endpointEdge_base f σ s K hK cA FA hFA cB FB hFB GA hGA GB)
    ((endpointSub Δ true).mapElements.obj x)).trans he)

noncomputable def endpointPath : Term (homogeneousPath (reindex B (σ ≫ projection B))
    (Term.map (Functor.whiskerLeft (σ ≫ projection B).mapElements f)
      (endpointA f σ s cA FA hFA cB FB hFB GA)) (Term.reindex (generic B) σ)) :=
  pathLam (endpointBody f σ s K hK cA FA hFA cB FB hFB GA hGA GB)
    (endpointBody_zero f σ s K hK cA FA hFA cB FB hFB GA hGA GB hGB)
    (endpointBody_one f σ s K hK cA FA hFA cB FB hFB GA hGA GB hGB)

noncomputable def extend : Term (fiber f σ) :=
  genericFiberIntro f σ (endpointA f σ s cA FA hFA cB FB hFB GA)
    (endpointPath f σ s K hK cA FA hFA cB FB hFB GA hGA GB hGB)


include hGA in
theorem endpointA_on_face :
    Term.reindex (endpointA f σ s cA FA hFA cB FB hFB GA) (restrictInclusion φ) =
      genericFiberFst f (restrictInclusion φ ≫ σ) s.toRestricted := by
  apply Term.ext
  intro x
  let y := (restrictInclusion φ).mapElements.obj x
  have he := (sourceLine_fills f σ s cA FA hFA cB FB hFB GA hGA).2
    ((endpointSub Δ true).mapElements.obj y) x.val.property
  have ha := Term.sigmaSndOver_val (B := reindex A (liftSub X (baseSub σ)))
    (sourceEndpoint f σ s cA FA hFA cB FB hFB GA) (basePoint σ)
    (sourceEndpoint_base f σ s cA FA hFA cB FB hFB GA) y
  exact eq_of_heq (ha.trans (Sigma.mk.inj he).2)

include hGB in
theorem endpointEdge_on_face (x : (total (interval Δ)).Elements)
    (hx : (φ.reindex (projection (interval Δ))).Holds x) :
    (endpointEdge f σ s K hK cA FA hFA cB FB hFB GA hGA GB).val x =
      (partialPath f σ s cA FA hFA).pathApp.val x hx := by
  have h := rectangle_old f σ s K hK cA FA hFA cB FB hFB GA hGA GB hGB
    ((endpointSub (total (interval Δ)) true).mapElements.obj x) hx
  exact h.trans (rectangleOld_top f σ s K hK cA FA hFA x hx)


theorem endpointPath_on_face :
    pathApp (homogeneousReindex (endpointPath f σ s K hK cA FA hFA cB FB hFB GA hGA GB hGB)
      (restrictInclusion φ)) =
      pathApp (genericFiberPath f (restrictInclusion φ ≫ σ) s.toRestricted) := by
  apply Term.ext
  intro x
  let y := (liftSub (interval Δ) (restrictInclusion φ)).mapElements.obj x
  have hy : (φ.reindex (projection (interval Δ))).Holds y := x.val.1.property
  have he := endpointEdge_on_face f σ s K hK cA FA hFA cB FB hFB GA hGA GB hGB y hy
  have hp := partialPath_body f σ s cA FA hFA y hy
  have hb := Term.sigmaSndOver_val
    (B := reindex B (liftSub X (projection (interval Δ) ≫ baseSub σ)))
    (endpointEdge f σ s K hK cA FA hFA cB FB hFB GA hGA GB)
    (Term.reindex (basePoint σ) (projection (interval Δ)))
    (endpointEdge_base f σ s K hK cA FA hFA cB FB hFB GA hGA GB) y
  exact eq_of_heq (hb.trans (Sigma.mk.inj (he.trans hp)).2)

theorem extend_on_face :
    Term.reindex (extend f σ s K hK cA FA hFA cB FB hFB GA hGA GB hGB) (restrictInclusion φ) =
      s.toRestricted :=
  (genericFiberIntro_reindex f σ (endpointA f σ s cA FA hFA cB FB hFB GA)
    (endpointPath f σ s K hK cA FA hFA cB FB hFB GA hGA GB hGB) (restrictInclusion φ)).trans
    ((genericFiberIntro_congr f (restrictInclusion φ ≫ σ) _ _
      (endpointA_on_face f σ s cA FA hFA cB FB hFB GA hGA) _ _
      (pathTerm_hext _ _ (endpointPath_on_face f σ s K hK cA FA hFA cB FB hFB GA hGA GB hGB))).trans
      (genericFiberIntro_eta f (restrictInclusion φ ≫ σ) s.toRestricted))

theorem extend_boundary (x : Δ.Elements) (hx : φ.Holds x) :
    (extend f σ s K hK cA FA hFA cB FB hFB GA hGA GB hGB).val x = s.val x hx :=
  congrArg (fun t => t.val ((restrictContext φ).elementsMk x.obj ⟨x.val,hx⟩))
    (extend_on_face f σ s K hK cA FA hFA cB FB hFB GA hGA GB hGB)


end ContractibleTotals
/-- A map over a common base between contractible total spaces is a native
fiberwise homotopy equivalence. Its fiber contractions retain prescribed paths. -/
noncomputable def HomotopyEquivalence.ofContractibleTotals {Γ : Context.{u}}
    {X : Family Γ} {A B : Family (total X)} (f : A ⟶ B)
    (FX : Filling X) (hFX : FX.Lawful) (FA : Filling A) (hFA : FA.Lawful)
    (FB : Filling B) (hFB : FB.Lawful)
    (cA : Contractible (sigma X A)) (cB : Contractible (sigma X B)) :
    HomotopyEquivalence f where
  fibers := Contractible.ofExtensions
    (fun σ _ s => ContractibleTotals.extend f σ s FB hFB cA
      (sigmaFilling FX hFX FA) (sigmaFilling_lawful FX hFX FA hFA) cB
      (sigmaFilling FX hFX FB) (sigmaFilling_lawful FX hFX FB hFB) FA hFA FB hFB)
    (fun σ _ s x hx => ContractibleTotals.extend_boundary f σ s FB hFB cA
      (sigmaFilling FX hFX FA) (sigmaFilling_lawful FX hFX FA hFA) cB
      (sigmaFilling FX hFX FB) (sigmaFilling_lawful FX hFX FB hFB) FA hFA FB hFB x hx)

end SquareKit.Cubical.Cartesian
