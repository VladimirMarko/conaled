import SquareKit.Internal.Cubical.UniverseCodePaths
import SquareKit.Internal.Cubical.BackwardFilling

/-! Small decoding on represented charts in the larger universe context.
These adapters retain selected chart fillers; universe filling is constructed
separately from Glue and is not assumed by this interface. -/
set_option autoImplicit false
set_option warningAsError true
namespace SquareKit.Cubical.Presheaf.SmallUniverse
open CategoryTheory
universe u


/-- The larger base does not raise the decoded fibers. -/
def decode {Γ : Context.{u+1}} (a : Γ ⟶ smallFamilyCodes.{u}) : Γ.Elements ⥤ Type u :=
  a.mapElements ⋙ universalDecode

/-- A small represented chart reaches any element of a larger context. -/
def chart {Γ : Context.{u+1}} (x : Γ.Elements) :
    raisedContext (representable.{u} x.obj.unop) ⟶ Γ where
  app J := TypeCat.ofHom (fun f => Γ.map f.down.down.op x.val)
  naturality J K f := by
    apply ConcreteCategory.hom_ext
    intro g
    exact ConcreteCategory.congr_hom (Γ.map_comp g.down.down.op f) x.val

/-- Chart filling is the constructed small-family decode operation from #419. -/
def chartFamily {Γ : Context.{u+1}} (a : Γ ⟶ smallFamilyCodes.{u}) (x : Γ.Elements) :
    LocalFamily (representable.{u} x.obj.unop) :=
  decodedLocalFamily (chart x ≫ a)

theorem chart_substitution {Γ Δ : Context.{u+1}} (σ : Δ ⟶ Γ) (x : Δ.Elements) :
    chart (σ.mapElements.obj x) = chart x ≫ σ := by
  ext I f
  exact (σ.naturality_apply f.down.down.op x.val).symm

theorem chart_restrict {Γ : Context.{u+1}} {x y : Γ.Elements} (f : x ⟶ y) :
    raisedSub (representableMap.{u} f.hom.unop) ≫ chart x = chart y := by
  ext I g
  change Γ.map (g.down.down ≫ f.hom.unop).op x.val = Γ.map g.down.down.op y.val
  exact (ConcreteCategory.congr_hom (Γ.map_comp f.hom g.down.down.op) x.val).trans
    (congrArg (fun z => Γ.map g.down.down.op z) f.map_val)

theorem chartFamily_substitution {Γ Δ : Context.{u+1}}
    (a : Γ ⟶ smallFamilyCodes.{u}) (σ : Δ ⟶ Γ) (x : Δ.Elements) :
    chartFamily (σ ≫ a) x = chartFamily a (σ.mapElements.obj x) := by
  unfold chartFamily
  rw [chart_substitution]
  rfl

/-- Restriction preserves the complete local family, including its chosen filler. -/
theorem chartFamily_restrict {Γ : Context.{u+1}} (a : Γ ⟶ smallFamilyCodes.{u})
    {x y : Γ.Elements} (f : x ⟶ y) :
    (chartFamily a x).reindex (representableMap.{u} f.hom.unop) = chartFamily a y := by
  unfold chartFamily
  rw [← decodedLocalFamily_reindex]
  exact congrArg decodedLocalFamily (by rw [← Category.assoc, chart_restrict])

end SquareKit.Cubical.Presheaf.SmallUniverse

namespace SquareKit.Cubical.Presheaf.IntervalTransport
open CategoryTheory
universe u

variable {Γ Δ : Context.{u}} {A : Family (total (interval Γ))}

def forward (F : Filling A) (σ : Δ ⟶ Γ)
    (a : Term (reindex A (endpointSub Δ false ≫ liftSub (interval Γ) σ))) :
    Term (reindex A (liftSub (interval Γ) σ)) :=
  F.fill (liftSub (interval Γ) σ) (Cofibration.bot Δ) (OpenBox.empty _ a)

theorem forward_zero (F : Filling A) (hF : F.Lawful) (σ : Δ ⟶ Γ)
    (a : Term (reindex A (endpointSub Δ false ≫ liftSub (interval Γ) σ))) :
    (forward F σ a).reindex (endpointSub Δ false) = a :=
  (hF.fills (liftSub (interval Γ) σ) (Cofibration.bot Δ) (OpenBox.empty _ a)).1

theorem forward_reindex (F : Filling A) (hF : F.Lawful) (σ : Δ ⟶ Γ)
    (a : Term (reindex A (endpointSub Δ false ≫ liftSub (interval Γ) σ)))
    {Θ : Context.{u}} (τ : Θ ⟶ Δ) :
    forward F (τ ≫ σ) (a.reindex τ) = (forward F σ a).reindex (liftSub (interval Δ) τ) :=
  hF.uniform (liftSub (interval Γ) σ) (Cofibration.bot Δ) (OpenBox.empty _ a) τ

/-- A term over a display gives the corresponding map between two fibers. -/
def mapOfSection {Ξ : Context.{u}} {B C : Family Ξ} (t : Term (reindex C (projection B))) : B ⟶ C where
  app x := TypeCat.ofHom (fun b => t.val (extendObj B x b))
  naturality x y f := by
    apply ConcreteCategory.hom_ext
    intro b
    exact (t.property (extendHom B f b)).symm

def map (F : Filling A) : reindex A (endpointSub Γ false) ⟶ reindex A (endpointSub Γ true) :=
  mapOfSection ((forward F (projection (reindex A (endpointSub Γ false)))
    (generic (reindex A (endpointSub Γ false)))).reindex
      (endpointSub (total (reindex A (endpointSub Γ false))) true))

theorem map_section (F : Filling A) (hF : F.Lawful)
    (a : Term (reindex A (endpointSub Γ false))) :
    Term.map (map F) a = (forward F (𝟙 Γ) a).reindex (endpointSub Γ true) := by
  have h := forward_reindex F hF (projection (reindex A (endpointSub Γ false)))
    (generic (reindex A (endpointSub Γ false))) (pair (𝟙 Γ) a)
  exact (congrArg (fun t => t.reindex (endpointSub Γ true)) h).symm



theorem map_reindex (F : Filling A) (hF : F.Lawful) (σ : Δ ⟶ Γ) :
    map (F.reindex (liftSub (interval Γ) σ)) = Functor.whiskerLeft σ.mapElements (map F) := by
  let B := reindex A (endpointSub Γ false)
  have h := forward_reindex F hF (projection B) (generic B) (liftSub B σ)
  ext x a
  exact congrArg (fun t => t.val
    ((endpointSub (total (reindex B σ)) true).mapElements.obj (extendObj (reindex B σ) x a))) h

private theorem nativePath_inverse_reindex {Ξ Ω Θ : Context.{u}}
    (B : Family (total (interval Ξ)))
    (a₀ : Term (reindex B (endpointSub Ξ false))) (a₁ : Term (reindex B (endpointSub Ξ true)))
    (σ : Ω ⟶ Ξ) (τ : Θ ⟶ Ω)
    (p : Term (path (reindex B (liftSub (interval Ξ) σ)) (a₀.reindex σ) (a₁.reindex σ))) :
    Term.map (pathReindex B a₀ a₁ (τ ≫ σ))
      ((Term.map (pathReindexIso B a₀ a₁ σ).inv p).reindex τ) =
    Term.map (pathReindex (reindex B (liftSub (interval Ξ) σ)) (a₀.reindex σ) (a₁.reindex σ) τ)
      (p.reindex τ) := by
  have h := (Iso.eq_inv_comp (Functor.isoWhiskerLeft τ.mapElements (pathReindexIso B a₀ a₁ σ))).mpr
    (pathReindex_comp B a₀ a₁ σ τ).symm
  exact congrArg (fun η => Term.map η (p.reindex τ)) h.symm

section EndpointLift
variable (F : Filling A) (hF : F.Lawful)
  (a : Term (reindex A (endpointSub Γ false))) (b : Term (reindex A (endpointSub Γ true)))
  (q : Term (homogeneousPath (reindex A (endpointSub Γ true)) (Term.map (map F) a) b))

abbrev endpointBody := reindex A (liftSub (interval Γ) (projection (interval Γ)))

def endpointInitial : Term (reindex
    (path (endpointBody (A := A)) (a.reindex (projection (interval Γ))) (pathApp q))
    (endpointSub Γ false)) :=
  Term.map (pathReindexIso (endpointBody (A := A)) (a.reindex (projection (interval Γ)))
    (pathApp q) (endpointSub Γ false)).inv
    (pathLam (forward F (𝟙 Γ) a) (forward_zero F hF (𝟙 Γ) a)
      ((map_section F hF a).symm.trans (pathApp_zero q).symm))

noncomputable def endpointLift : Term
    (path (endpointBody (A := A)) (a.reindex (projection (interval Γ))) (pathApp q)) :=
  (pathFilling (F.reindex (liftSub (interval Γ) (projection (interval Γ)))) (hF.reindex _)
    (a.reindex (projection (interval Γ))) (pathApp q)).fill (𝟙 _) (Cofibration.bot Γ)
      (OpenBox.empty _ (endpointInitial F hF a b q))

noncomputable def endpointSquare : Term (reindex A (projection (interval (total (interval Γ))))) :=
  (pathApp (endpointLift F hF a b q)).reindex (swapIntervals Γ)

theorem endpointSquare_left :
    (endpointSquare F hF a b q).reindex (liftSub (interval (total (interval Γ))) (endpointSub Γ false)) =
      a.reindex (projection (interval Γ)) := pathApp_zero (endpointLift F hF a b q)

theorem endpointSquare_right :
    (endpointSquare F hF a b q).reindex (liftSub (interval (total (interval Γ))) (endpointSub Γ true)) =
      pathApp q := pathApp_one (endpointLift F hF a b q)

theorem endpointSquare_base :
    (endpointSquare F hF a b q).reindex (endpointSub (total (interval Γ)) false) = forward F (𝟙 Γ) a := by
  let i := pathReindexIso (endpointBody (A := A)) (a.reindex (projection (interval Γ)))
    (pathApp q) (endpointSub Γ false)
  have hz := (pathFilling_fills (F.reindex (liftSub (interval Γ) (projection (interval Γ))))
    (hF.reindex _) (a.reindex (projection (interval Γ))) (pathApp q) (𝟙 _) (Cofibration.bot Γ)
      (OpenBox.empty _ (endpointInitial F hF a b q))).1
  exact (congrArg (fun t => pathApp (Term.map i.hom t)) hz).trans
    (congrArg pathApp (Term.map_iso_roundtrip i.symm
      (pathLam (forward F (𝟙 Γ) a) (forward_zero F hF (𝟙 Γ) a)
        ((map_section F hF a).symm.trans (pathApp_zero q).symm))))


noncomputable def adjustedPath : Term A :=
  (endpointSquare F hF a b q).reindex (endpointSub (total (interval Γ)) true)

theorem adjustedPath_zero : (adjustedPath F hF a b q).reindex (endpointSub Γ false) = a :=
  congrArg (fun t => t.reindex (endpointSub Γ true)) (endpointSquare_left F hF a b q)

theorem adjustedPath_one : (adjustedPath F hF a b q).reindex (endpointSub Γ true) = b :=
  (congrArg (fun t => t.reindex (endpointSub Γ true)) (endpointSquare_right F hF a b q)).trans
    (pathApp_one q)


def endpointPathReindex {Θ : Context.{u}} (σ : Θ ⟶ Γ) : Term (homogeneousPath
    (reindex (reindex A (endpointSub Γ true)) σ)
    (Term.map (map (F.reindex (liftSub (interval Γ) σ))) (a.reindex σ)) (b.reindex σ)) :=
  pathLam ((pathApp q).reindex (liftSub (interval Γ) σ))
    ((congrArg (fun t => t.reindex σ) (pathApp_zero q)).trans
      (congrArg (fun g => Term.map g (a.reindex σ)) (map_reindex F hF σ)).symm)
    (congrArg (fun t => t.reindex σ) (pathApp_one q))

theorem endpointInitial_reindex {Θ : Context.{u}} (σ : Θ ⟶ Γ) :
    endpointInitial (F.reindex (liftSub (interval Γ) σ)) (hF.reindex _) (a.reindex σ) (b.reindex σ)
      (endpointPathReindex F hF a b q σ) =
    Term.map (Functor.whiskerLeft (endpointSub Θ false).mapElements
      (pathReindexIso (endpointBody (A := A)) (a.reindex (projection (interval Γ)))
        (pathApp q) (liftSub (interval Γ) σ)).hom)
      ((endpointInitial F hF a b q).reindex σ) := by
  let L := liftSub (interval Γ) σ
  let q' := endpointPathReindex F hF a b q σ
  let i := pathReindexIso (endpointBody (A := reindex A L))
    ((a.reindex σ).reindex (projection (interval Θ))) (pathApp q') (endpointSub Θ false)
  apply Term.map_injective_of_iso i
  apply pathApp_injective
  have hl := Term.map_iso_roundtrip i.symm
    (pathLam (forward (F.reindex L) (𝟙 Θ) (a.reindex σ))
      (forward_zero (F.reindex L) (hF.reindex _) (𝟙 Θ) (a.reindex σ))
      ((map_section (F.reindex L) (hF.reindex _) (a.reindex σ)).symm.trans (pathApp_zero q').symm))
  have hr := nativePath_inverse_reindex (endpointBody (A := A)) (a.reindex (projection (interval Γ)))
    (pathApp q) (endpointSub Γ false) σ
    (pathLam (forward F (𝟙 Γ) a) (forward_zero F hF (𝟙 Γ) a)
      ((map_section F hF a).symm.trans (pathApp_zero q).symm))
  exact (congrArg pathApp hl).trans
    ((forward_reindex F hF (𝟙 Γ) a σ).trans (congrArg pathApp hr).symm)


theorem endpointLift_reindex {Θ : Context.{u}} (σ : Θ ⟶ Γ) :
    endpointLift (F.reindex (liftSub (interval Γ) σ)) (hF.reindex _) (a.reindex σ) (b.reindex σ)
      (endpointPathReindex F hF a b q σ) =
    Term.map (pathReindexIso (endpointBody (A := A)) (a.reindex (projection (interval Γ)))
      (pathApp q) (liftSub (interval Γ) σ)).hom
      ((endpointLift F hF a b q).reindex (liftSub (interval Γ) σ)) := by
  let L := liftSub (interval Γ) σ
  let q' := endpointPathReindex F hF a b q σ
  let i := pathReindexIso (endpointBody (A := A)) (a.reindex (projection (interval Γ))) (pathApp q) L
  let K := pathFilling (F.reindex (liftSub (interval Γ) (projection (interval Γ)))) (hF.reindex _)
    (a.reindex (projection (interval Γ))) (pathApp q)
  let K' := pathFilling ((F.reindex L).reindex (liftSub (interval Θ) (projection (interval Θ))))
    ((hF.reindex L).reindex _) ((a.reindex σ).reindex (projection (interval Θ))) (pathApp q')
  let c := OpenBox.empty _ (endpointInitial F hF a b q)
  let c' := OpenBox.empty _ (endpointInitial (F.reindex L) (hF.reindex _) (a.reindex σ) (b.reindex σ) q')
  have hc : c' = (c.reindex σ).map i.hom := by
    apply OpenBox.ext
    · apply PartialSection.ext
      intro x hx
      exact (Bool.false_ne_true hx).elim
    · exact endpointInitial_reindex F hF a b q σ
  have hp := pathFilling_reindex_family
    (F.reindex (liftSub (interval Γ) (projection (interval Γ)))) (hF.reindex _)
    (a.reindex (projection (interval Γ))) (pathApp q) L (𝟙 _) (Cofibration.bot Θ) (c.reindex σ)
  have hu := pathFilling_uniform
    (F.reindex (liftSub (interval Γ) (projection (interval Γ)))) (hF.reindex _)
    (a.reindex (projection (interval Γ))) (pathApp q) (𝟙 _) (Cofibration.bot Γ) c σ
  exact (congrArg (K'.fill (𝟙 _) (Cofibration.bot Θ)) hc).trans
    (hp.trans (congrArg (Term.map i.hom) hu))

theorem endpointSquare_reindex {Θ : Context.{u}} (σ : Θ ⟶ Γ) :
    endpointSquare (F.reindex (liftSub (interval Γ) σ)) (hF.reindex _) (a.reindex σ) (b.reindex σ)
      (endpointPathReindex F hF a b q σ) =
    (endpointSquare F hF a b q).reindex
      (liftSub (interval (total (interval Γ))) (liftSub (interval Γ) σ)) :=
  congrArg (fun t => (pathApp t).reindex (swapIntervals Θ)) (endpointLift_reindex F hF a b q σ)

theorem adjustedPath_reindex {Θ : Context.{u}} (σ : Θ ⟶ Γ) :
    adjustedPath (F.reindex (liftSub (interval Γ) σ)) (hF.reindex _) (a.reindex σ) (b.reindex σ)
      (endpointPathReindex F hF a b q σ) =
    (adjustedPath F hF a b q).reindex (liftSub (interval Γ) σ) :=
  congrArg (fun t => t.reindex (endpointSub (total (interval Θ)) true)) (endpointSquare_reindex F hF a b q σ)

end EndpointLift


section RelativeBackward
variable (F : Filling A) (hF : F.Lawful) (φ : Cofibration Γ)
  (t : PartialSection A (φ.reindex (projection (interval Γ))))
  (b : Term (reindex A (endpointSub Γ true)))
  (hb : ∀ (x : Γ.Elements) (hx : φ.full x),
    t.val ((endpointSub Γ true).mapElements.obj x) hx = b.val x)

def backwardBox : OpenBox (reindex A (reverseInterval Γ)) φ where
  tube := t.reindex (reverseInterval Γ)
  base := b.convert (congrArg (fun σ => reindex A σ) (reverseInterval_endpoint Γ false).symm)
  boundary x hx := by
    have he := congrArg (fun σ : Γ ⟶ total (interval Γ) => σ.mapElements.obj x)
      (reverseInterval_endpoint Γ false)
    exact eq_of_heq ((t.val_heq he hx hx).trans ((heq_of_eq (hb x hx)).trans
      (Term.convert_val_heq _ b x).symm))

def backwardRelative : Term A :=
  ((F.fill (reverseInterval Γ) φ (backwardBox φ t b hb)).reindex (reverseInterval Γ)).convert
    (congrArg (fun σ => reindex A σ) (reverseInterval_twice Γ))

include hF in
theorem backwardRelative_one : (backwardRelative F φ t b hb).reindex (endpointSub Γ true) = b := by
  apply Term.ext
  intro x
  let s := F.fill (reverseInterval Γ) φ (backwardBox φ t b hb)
  have he := congrArg (fun σ : Γ ⟶ total (interval Γ) => σ.mapElements.obj x)
    (reverseInterval_endpoint Γ true)
  have hv : HEq (s.val ((reverseInterval Γ).mapElements.obj ((endpointSub Γ true).mapElements.obj x)))
      (s.val ((endpointSub Γ false).mapElements.obj x)) := by
    have hv' : ∀ {y z}, y = z → HEq (s.val y) (s.val z) := by
      intro y z h
      cases h
      rfl
    exact hv' he
  exact eq_of_heq ((Term.convert_val_heq _ _ _).trans
    (hv.trans ((heq_of_eq (congrArg (fun z => z.val x)
      (hF.fills (reverseInterval Γ) φ (backwardBox φ t b hb)).1)).trans
        (Term.convert_val_heq _ b x))))

include hF in
theorem backwardRelative_boundary (x : (total (interval Γ)).Elements)
    (hx : (φ.reindex (projection (interval Γ))).full x) :
    (backwardRelative F φ t b hb).val x = t.val x hx := by
  have he := congrArg (fun σ : total (interval Γ) ⟶ total (interval Γ) => σ.mapElements.obj x)
    (reverseInterval_twice Γ)
  exact eq_of_heq ((Term.convert_val_heq _ _ _).trans
    ((heq_of_eq ((hF.fills (reverseInterval Γ) φ (backwardBox φ t b hb)).2
      ((reverseInterval Γ).mapElements.obj x) hx)).trans (t.val_heq he hx hx)))


include hF in
theorem backwardRelative_reindex {Θ : Context.{u}} (σ : Θ ⟶ Γ) :
    backwardRelative (F.reindex (liftSub (interval Γ) σ)) (φ.reindex σ)
      (t.reindex (liftSub (interval Γ) σ)) (b.reindex σ)
      (fun x hx => hb (σ.mapElements.obj x) hx) =
    (backwardRelative F φ t b hb).reindex (liftSub (interval Γ) σ) := by
  let L := liftSub (interval Γ) σ
  let c := backwardBox φ t b hb
  let c' := backwardBox (φ.reindex σ) (t.reindex L) (b.reindex σ)
    (fun x hx => hb (σ.mapElements.obj x) hx)
  have e : reverseInterval Θ ≫ L = L ≫ reverseInterval Γ := reverseInterval_natural σ
  have hc : HEq c' (c.reindex σ) := by
    apply OpenBox.hext (congrArg (fun p => reindex A p) e)
    · intro x hx
      exact t.val_heq (congrArg (fun p : total (interval Θ) ⟶ total (interval Γ) => p.mapElements.obj x) e) hx hx
    · intro x
      exact (Term.convert_val_heq _ _ _).trans (Term.convert_val_heq _ b (σ.mapElements.obj x)).symm
  have hf := (F.fill_heq e hc).trans (heq_of_eq (hF.uniform (reverseInterval Γ) φ c σ))
  apply Term.ext
  intro x
  apply eq_of_heq
  unfold backwardRelative
  apply (Term.convert_val_heq _ _ _).trans
  apply HEq.trans _ (Term.convert_val_heq _ _ _).symm
  apply (Term.val_heq_of_heq (congrArg (fun p => reindex A p) e) hf
    (x := (reverseInterval Θ).mapElements.obj x) rfl).trans
  exact Term.val_heq_of_heq rfl (HEq.rfl (a := F.fill _ _ c))
    (congrArg (fun p : total (interval Θ) ⟶ total (interval Γ) => p.mapElements.obj x) (reverseInterval_natural σ))


theorem backwardRelative_congr
    (t' : PartialSection A (φ.reindex (projection (interval Γ))))
    (hb' : ∀ (x : Γ.Elements) (hx : φ.full x),
      t'.val ((endpointSub Γ true).mapElements.obj x) hx = b.val x) (ht : t = t') :
    backwardRelative F φ t b hb = backwardRelative F φ t' b hb' := by
  cases ht
  rfl

end RelativeBackward



namespace FiberExtension
variable (F : Filling A) (hF : F.Lawful)
  (f : reindex A (endpointSub Γ false) ⟶ reindex A (endpointSub Γ true)) (hf : f = map F)
  (ρ : Δ ⟶ total (reindex A (endpointSub Γ true))) {φ : Cofibration Δ}
  (z : PartialSection (reindex
    (homotopyFiber (Functor.whiskerLeft (projection (reindex A (endpointSub Γ true))).mapElements f)
      (generic (reindex A (endpointSub Γ true)))) ρ) φ)

abbrev base := ρ ≫ projection (reindex A (endpointSub Γ true))
abbrev localBase := restrictInclusion φ ≫ base ρ

def localSource := genericFiberFst f (restrictInclusion φ ≫ ρ) z.toRestricted

def localTarget := (generic (reindex A (endpointSub Γ true))).reindex (restrictInclusion φ ≫ ρ)

def localPath : Term (homogeneousPath
    (reindex (reindex A (endpointSub Γ true)) (localBase (φ := φ) ρ))
    (Term.map (map (F.reindex (liftSub (interval Γ) (localBase (φ := φ) ρ)))) (localSource f ρ z))
    (localTarget (φ := φ) ρ)) :=
  pathLam (pathApp (genericFiberPath f (restrictInclusion φ ≫ ρ) z.toRestricted))
    ((pathApp_zero (genericFiberPath f (restrictInclusion φ ≫ ρ) z.toRestricted)).trans
      (congrArg (fun g => Term.map g (localSource f ρ z))
        ((congrArg (Functor.whiskerLeft (localBase (φ := φ) ρ).mapElements) hf).trans
          (map_reindex F hF (localBase (φ := φ) ρ)).symm)))
    (pathApp_one (genericFiberPath f (restrictInclusion φ ≫ ρ) z.toRestricted))

noncomputable def localSquare := endpointSquare
  (F.reindex (liftSub (interval Γ) (localBase (φ := φ) ρ))) (hF.reindex _)
  (localSource f ρ z) (localTarget (φ := φ) ρ) (localPath F hF f hf ρ z)

noncomputable def localAdjusted := adjustedPath
  (F.reindex (liftSub (interval Γ) (localBase (φ := φ) ρ))) (hF.reindex _)
  (localSource f ρ z) (localTarget (φ := φ) ρ) (localPath F hF f hf ρ z)

noncomputable def partialAdjusted : PartialSection (reindex A (liftSub (interval Γ) (base ρ)))
    (φ.reindex (projection (interval Δ))) :=
  PartialSection.ofRestricted ((localAdjusted F hF f hf ρ z).reindex (restrictedInterval φ))


theorem localAdjusted_zero :
    (localAdjusted F hF f hf ρ z).reindex (endpointSub (restrictContext φ) false) = localSource f ρ z :=
  adjustedPath_zero (F.reindex (liftSub (interval Γ) (localBase (φ := φ) ρ))) (hF.reindex _)
    (localSource f ρ z) (localTarget (φ := φ) ρ) (localPath F hF f hf ρ z)

theorem localAdjusted_one :
    (localAdjusted F hF f hf ρ z).reindex (endpointSub (restrictContext φ) true) = localTarget (φ := φ) ρ :=
  adjustedPath_one (F.reindex (liftSub (interval Γ) (localBase (φ := φ) ρ))) (hF.reindex _)
    (localSource f ρ z) (localTarget (φ := φ) ρ) (localPath F hF f hf ρ z)

theorem partialAdjusted_zero (x : Δ.Elements) (hx : φ.full x) :
    (partialAdjusted F hF f hf ρ z).val ((endpointSub Δ false).mapElements.obj x) hx = (z.val x hx).1 :=
  congrArg (fun t => t.val (Glue.faceObj φ x hx)) (localAdjusted_zero F hF f hf ρ z)

theorem partialAdjusted_one (x : Δ.Elements) (hx : φ.full x) :
    (partialAdjusted F hF f hf ρ z).val ((endpointSub Δ true).mapElements.obj x) hx =
      ((generic (reindex A (endpointSub Γ true))).reindex ρ).val x :=
  congrArg (fun t => t.val (Glue.faceObj φ x hx)) (localAdjusted_one F hF f hf ρ z)

noncomputable def fullPath := backwardRelative (F.reindex (liftSub (interval Γ) (base ρ))) φ
  (partialAdjusted F hF f hf ρ z) ((generic (reindex A (endpointSub Γ true))).reindex ρ)
  (partialAdjusted_one F hF f hf ρ z)

theorem fullPath_one : (fullPath F hF f hf ρ z).reindex (endpointSub Δ true) =
    (generic (reindex A (endpointSub Γ true))).reindex ρ :=
  backwardRelative_one (F.reindex (liftSub (interval Γ) (base ρ))) (hF.reindex _) φ
    (partialAdjusted F hF f hf ρ z) ((generic (reindex A (endpointSub Γ true))).reindex ρ)
    (partialAdjusted_one F hF f hf ρ z)

noncomputable def fullSource := (fullPath F hF f hf ρ z).reindex (endpointSub Δ false)

theorem fullSource_boundary (x : Δ.Elements) (hx : φ.full x) :
    (fullSource F hF f hf ρ z).val x = (z.val x hx).1 :=
  (backwardRelative_boundary (F.reindex (liftSub (interval Γ) (base ρ))) (hF.reindex _) φ
    (partialAdjusted F hF f hf ρ z) ((generic (reindex A (endpointSub Γ true))).reindex ρ)
    (partialAdjusted_one F hF f hf ρ z) ((endpointSub Δ false).mapElements.obj x) hx).trans
      (partialAdjusted_zero F hF f hf ρ z x hx)

theorem fullSource_on_face : (fullSource F hF f hf ρ z).reindex (restrictInclusion φ) = localSource f ρ z := by
  apply Term.ext
  intro x
  exact fullSource_boundary F hF f hf ρ z ((restrictInclusion φ).mapElements.obj x) x.val.property

noncomputable def fullForward := forward (F.reindex (liftSub (interval Γ) (base ρ))) (𝟙 Δ)
  (fullSource F hF f hf ρ z)

theorem fullForward_on_face :
    (fullForward F hF f hf ρ z).reindex (liftSub (interval Δ) (restrictInclusion φ)) =
    forward (F.reindex (liftSub (interval Γ) (localBase (φ := φ) ρ))) (𝟙 _) (localSource f ρ z) :=
  (forward_reindex (F.reindex (liftSub (interval Γ) (base ρ))) (hF.reindex _) (𝟙 Δ)
    (fullSource F hF f hf ρ z) (restrictInclusion φ)).symm.trans
      (congrArg (forward (F.reindex (liftSub (interval Γ) (base ρ))) (restrictInclusion φ))
        (fullSource_on_face F hF f hf ρ z))

theorem fullPath_on_face :
    (fullPath F hF f hf ρ z).reindex (liftSub (interval Δ) (restrictInclusion φ)) = localAdjusted F hF f hf ρ z := by
  apply Term.ext
  intro x
  exact backwardRelative_boundary (F.reindex (liftSub (interval Γ) (base ρ))) (hF.reindex _) φ
    (partialAdjusted F hF f hf ρ z) ((generic (reindex A (endpointSub Γ true))).reindex ρ)
    (partialAdjusted_one F hF f hf ρ z) ((liftSub (interval Δ) (restrictInclusion φ)).mapElements.obj x) x.val.1.property


noncomputable def localComparison := pathLam (localSquare F hF f hf ρ z)
  ((endpointSquare_base (F.reindex (liftSub (interval Γ) (localBase (φ := φ) ρ))) (hF.reindex _)
    (localSource f ρ z) (localTarget (φ := φ) ρ) (localPath F hF f hf ρ z)).trans
      (fullForward_on_face F hF f hf ρ z).symm)
  (fullPath_on_face F hF f hf ρ z).symm

abbrev comparisonBody := reindex (reindex A (liftSub (interval Γ) (base ρ)))
  (projection (interval (total (interval Δ))))

noncomputable def partialComparison : PartialSection
    (homogeneousPath (reindex A (liftSub (interval Γ) (base ρ))) (fullForward F hF f hf ρ z) (fullPath F hF f hf ρ z))
    (φ.reindex (projection (interval Δ))) :=
  PartialSection.ofRestricted
    (Term.map (pathReindexIso (comparisonBody ρ) (fullForward F hF f hf ρ z) (fullPath F hF f hf ρ z)
      (restrictInclusion (φ.reindex (projection (interval Δ))))).inv
      (homogeneousReindex (localComparison F hF f hf ρ z) (restrictedInterval φ)))

noncomputable def comparisonInitial : Term (reindex
    (homogeneousPath (reindex A (liftSub (interval Γ) (base ρ))) (fullForward F hF f hf ρ z) (fullPath F hF f hf ρ z))
    (endpointSub Δ false)) :=
  Term.map (pathReindexIso (comparisonBody ρ) (fullForward F hF f hf ρ z) (fullPath F hF f hf ρ z)
    (endpointSub Δ false)).inv
    (pathLam ((fullSource F hF f hf ρ z).reindex (projection (interval Δ)))
      (forward_zero (F.reindex (liftSub (interval Γ) (base ρ))) (hF.reindex _) (𝟙 Δ)
        (fullSource F hF f hf ρ z)).symm rfl)


theorem comparison_initial_restricted :
    ((partialComparison F hF f hf ρ z).reindex (endpointSub Δ false)).toRestricted =
      (comparisonInitial F hF f hf ρ z).reindex (restrictInclusion φ) := by
  let χ := φ.reindex (projection (interval Δ))
  let i := pathReindexIso (comparisonBody ρ) (fullForward F hF f hf ρ z) (fullPath F hF f hf ρ z)
    (restrictInclusion φ ≫ endpointSub Δ false)
  apply Term.map_injective_of_iso i
  apply pathApp_injective
  have hl := nativePath_inverse_reindex (comparisonBody ρ) (fullForward F hF f hf ρ z) (fullPath F hF f hf ρ z)
    (restrictInclusion χ) (restrictSubstitution χ (endpointSub Δ false))
      (homogeneousReindex (localComparison F hF f hf ρ z) (restrictedInterval φ))
  have hr := nativePath_inverse_reindex (comparisonBody ρ) (fullForward F hF f hf ρ z) (fullPath F hF f hf ρ z)
    (endpointSub Δ false) (restrictInclusion φ)
    (pathLam ((fullSource F hF f hf ρ z).reindex (projection (interval Δ)))
      (forward_zero (F.reindex (liftSub (interval Γ) (base ρ))) (hF.reindex _) (𝟙 Δ)
        (fullSource F hF f hf ρ z)).symm rfl)
  exact (congrArg pathApp hl).trans
    ((endpointSquare_left (F.reindex (liftSub (interval Γ) (localBase (φ := φ) ρ))) (hF.reindex _)
      (localSource f ρ z) (localTarget (φ := φ) ρ) (localPath F hF f hf ρ z)).trans
        ((congrArg (fun t => t.reindex (projection (interval (restrictContext φ))))
          (fullSource_on_face F hF f hf ρ z)).symm.trans (congrArg pathApp hr).symm))

noncomputable def comparisonBox : OpenBox
    (homogeneousPath (reindex A (liftSub (interval Γ) (base ρ))) (fullForward F hF f hf ρ z) (fullPath F hF f hf ρ z)) φ where
  tube := partialComparison F hF f hf ρ z
  base := comparisonInitial F hF f hf ρ z
  boundary x hx := congrArg (fun t => t.val (Glue.faceObj φ x hx)) (comparison_initial_restricted F hF f hf ρ z)


noncomputable def comparisonFilling := pathFilling
  (F.reindex (projection (interval (total (interval Δ))) ≫ liftSub (interval Γ) (base ρ)))
  (hF.reindex _) (fullForward F hF f hf ρ z) (fullPath F hF f hf ρ z)

noncomputable def comparisonFilled := (comparisonFilling F hF f hf ρ z).fill (𝟙 _) φ (comparisonBox F hF f hf ρ z)

noncomputable def finalNativePath := Term.map
  (pathReindexIso (comparisonBody ρ) (fullForward F hF f hf ρ z) (fullPath F hF f hf ρ z) (endpointSub Δ true)).hom
  ((comparisonFilled F hF f hf ρ z).reindex (endpointSub Δ true))

noncomputable def finalPath : Term (homogeneousPath
    (reindex (reindex A (endpointSub Γ true)) (base ρ))
    (Term.map (Functor.whiskerLeft (base ρ).mapElements f) (fullSource F hF f hf ρ z))
    ((generic (reindex A (endpointSub Γ true))).reindex ρ)) :=
  pathLam (pathApp (finalNativePath F hF f hf ρ z))
    ((pathApp_zero (finalNativePath F hF f hf ρ z)).trans
      ((map_section (F.reindex (liftSub (interval Γ) (base ρ))) (hF.reindex _)
        (fullSource F hF f hf ρ z)).symm.trans
          (congrArg (fun g => Term.map g (fullSource F hF f hf ρ z))
            ((map_reindex F hF (base ρ)).trans
              (congrArg (Functor.whiskerLeft (base ρ).mapElements) hf).symm))))
    ((pathApp_one (finalNativePath F hF f hf ρ z)).trans (fullPath_one F hF f hf ρ z))

noncomputable def extend := genericFiberIntro f ρ (fullSource F hF f hf ρ z) (finalPath F hF f hf ρ z)

theorem comparisonFilled_on_face :
    (comparisonFilled F hF f hf ρ z).reindex (restrictInclusion (φ.reindex (projection (interval Δ)))) =
      (partialComparison F hF f hf ρ z).toRestricted := by
  apply Term.ext
  intro x
  exact ((pathFilling_lawful
    (F.reindex (projection (interval (total (interval Δ))) ≫ liftSub (interval Γ) (base ρ)))
    (hF.reindex _) (fullForward F hF f hf ρ z) (fullPath F hF f hf ρ z)).fills (𝟙 _) φ
      (comparisonBox F hF f hf ρ z)).2
        ((restrictInclusion (φ.reindex (projection (interval Δ)))).mapElements.obj x) x.val.property


theorem finalPathApp_on_face :
    pathApp (homogeneousReindex (finalPath F hF f hf ρ z) (restrictInclusion φ)) =
      pathApp (genericFiberPath f (restrictInclusion φ ≫ ρ) z.toRestricted) := by
  let χ := φ.reindex (projection (interval Δ))
  let τ := restrictSubstitution χ (endpointSub Δ true)
  let i := pathReindex (comparisonBody ρ) (fullForward F hF f hf ρ z) (fullPath F hF f hf ρ z)
    (restrictInclusion φ ≫ endpointSub Δ true)
  have hb := congrArg (fun t => Term.map i (t.reindex τ)) (comparisonFilled_on_face F hF f hf ρ z)
  have hi := nativePath_inverse_reindex (comparisonBody ρ) (fullForward F hF f hf ρ z) (fullPath F hF f hf ρ z)
    (restrictInclusion χ) τ (homogeneousReindex (localComparison F hF f hf ρ z) (restrictedInterval φ))
  exact (congrArg pathApp hb).trans ((congrArg pathApp hi).trans
    (endpointSquare_right (F.reindex (liftSub (interval Γ) (localBase (φ := φ) ρ))) (hF.reindex _)
      (localSource f ρ z) (localTarget (φ := φ) ρ) (localPath F hF f hf ρ z)))

theorem extend_on_face : (extend F hF f hf ρ z).reindex (restrictInclusion φ) = z.toRestricted :=
  (genericFiberIntro_reindex f ρ (fullSource F hF f hf ρ z) (finalPath F hF f hf ρ z)
    (restrictInclusion φ)).symm.trans
    ((genericFiberIntro_congr f (restrictInclusion φ ≫ ρ) _ _ (fullSource_on_face F hF f hf ρ z)
      _ _ (pathTerm_hext _ _ (finalPathApp_on_face F hF f hf ρ z))).trans
        (genericFiberIntro_eta f (restrictInclusion φ ≫ ρ) z.toRestricted))

theorem extend_boundary (x : Δ.Elements) (hx : φ.full x) :
    (extend F hF f hf ρ z).val x = z.val x hx :=
  congrArg (fun t => t.val (Glue.faceObj φ x hx)) (extend_on_face F hF f hf ρ z)


theorem localPath_reindex {Θ : Context.{u}} (τ : Θ ⟶ Δ) :
    localPath F hF f hf (τ ≫ ρ) (z.reindex τ) =
    endpointPathReindex (F.reindex (liftSub (interval Γ) (localBase (φ := φ) ρ))) (hF.reindex _)
      (localSource f ρ z) (localTarget (φ := φ) ρ) (localPath F hF f hf ρ z) (restrictSubstitution φ τ) := by
  apply pathApp_injective
  rfl

theorem localSquare_reindex {Θ : Context.{u}} (τ : Θ ⟶ Δ) :
    localSquare F hF f hf (τ ≫ ρ) (z.reindex τ) =
    (localSquare F hF f hf ρ z).reindex
      (liftSub (interval (total (interval (restrictContext φ))))
        (liftSub (interval (restrictContext φ)) (restrictSubstitution φ τ))) :=
  (congrArg (endpointSquare
    (F.reindex (liftSub (interval Γ) (localBase (φ := φ.reindex τ) (τ ≫ ρ))))
    (hF.reindex _) (localSource f (τ ≫ ρ) (z.reindex τ)) (localTarget (φ := φ.reindex τ) (τ ≫ ρ)))
      (localPath_reindex F hF f hf ρ z τ)).trans
    (endpointSquare_reindex (F.reindex (liftSub (interval Γ) (localBase (φ := φ) ρ))) (hF.reindex _)
      (localSource f ρ z) (localTarget (φ := φ) ρ) (localPath F hF f hf ρ z) (restrictSubstitution φ τ))

theorem localAdjusted_reindex {Θ : Context.{u}} (τ : Θ ⟶ Δ) :
    localAdjusted F hF f hf (τ ≫ ρ) (z.reindex τ) =
    (localAdjusted F hF f hf ρ z).reindex (liftSub (interval (restrictContext φ)) (restrictSubstitution φ τ)) :=
  congrArg (fun t => t.reindex (endpointSub (total (interval (restrictContext (φ.reindex τ)))) true))
    (localSquare_reindex F hF f hf ρ z τ)

theorem partialAdjusted_reindex {Θ : Context.{u}} (τ : Θ ⟶ Δ) :
    partialAdjusted F hF f hf (τ ≫ ρ) (z.reindex τ) =
    (partialAdjusted F hF f hf ρ z).reindex (liftSub (interval Δ) τ) := by
  apply PartialSection.ext
  intro x hx
  exact congrArg (fun t => t.val
    ((total (interval (restrictContext (φ.reindex τ)))).elementsMk x.obj ⟨⟨x.val.1,hx⟩,x.val.2⟩))
    (localAdjusted_reindex F hF f hf ρ z τ)

theorem fullPath_reindex {Θ : Context.{u}} (τ : Θ ⟶ Δ) :
    fullPath F hF f hf (τ ≫ ρ) (z.reindex τ) = (fullPath F hF f hf ρ z).reindex (liftSub (interval Δ) τ) :=
  (backwardRelative_congr (F.reindex (liftSub (interval Γ) (base (τ ≫ ρ)))) (φ.reindex τ)
    (partialAdjusted F hF f hf (τ ≫ ρ) (z.reindex τ)) ((generic (reindex A (endpointSub Γ true))).reindex (τ ≫ ρ))
    (partialAdjusted_one F hF f hf (τ ≫ ρ) (z.reindex τ))
    ((partialAdjusted F hF f hf ρ z).reindex (liftSub (interval Δ) τ))
    (fun x hx => partialAdjusted_one F hF f hf ρ z (τ.mapElements.obj x) hx)
    (partialAdjusted_reindex F hF f hf ρ z τ)).trans
    (backwardRelative_reindex (F.reindex (liftSub (interval Γ) (base ρ))) (hF.reindex _) φ
      (partialAdjusted F hF f hf ρ z) ((generic (reindex A (endpointSub Γ true))).reindex ρ)
      (partialAdjusted_one F hF f hf ρ z) τ)

theorem fullSource_reindex {Θ : Context.{u}} (τ : Θ ⟶ Δ) :
    fullSource F hF f hf (τ ≫ ρ) (z.reindex τ) = (fullSource F hF f hf ρ z).reindex τ :=
  congrArg (fun t => t.reindex (endpointSub Θ false)) (fullPath_reindex F hF f hf ρ z τ)

theorem fullForward_reindex {Θ : Context.{u}} (τ : Θ ⟶ Δ) :
    fullForward F hF f hf (τ ≫ ρ) (z.reindex τ) = (fullForward F hF f hf ρ z).reindex (liftSub (interval Δ) τ) :=
  (congrArg (forward (F.reindex (liftSub (interval Γ) (base (τ ≫ ρ)))) (𝟙 Θ))
    (fullSource_reindex F hF f hf ρ z τ)).trans
      (forward_reindex (F.reindex (liftSub (interval Γ) (base ρ))) (hF.reindex _) (𝟙 Δ)
        (fullSource F hF f hf ρ z) τ)


theorem partialComparison_body (x : (total (interval (total (interval Δ)))).Elements)
    (hx : (φ.reindex (projection (interval (total (interval Δ))) ≫ projection (interval Δ))).full x) :
    (partialComparison F hF f hf ρ z).pathApp.val x hx =
      (localSquare F hF f hf ρ z).val
        ((total (interval (total (interval (restrictContext φ))))).elementsMk x.obj
          ⟨⟨⟨x.val.1.1,hx⟩,x.val.1.2⟩,x.val.2⟩) := by
  let χ := φ.reindex (projection (interval Δ))
  let i := pathReindexIso (comparisonBody ρ) (fullForward F hF f hf ρ z) (fullPath F hF f hf ρ z)
    (restrictInclusion χ)
  have he := Term.map_iso_roundtrip i.symm
    (homogeneousReindex (localComparison F hF f hf ρ z) (restrictedInterval φ))
  exact congrArg (fun p => (pathApp p).val
    ((total (interval (restrictContext χ))).elementsMk x.obj ⟨⟨x.val.1,hx⟩,x.val.2⟩)) he

theorem partialComparison_body_reindex {Θ : Context.{u}} (τ : Θ ⟶ Δ) :
    (partialComparison F hF f hf (τ ≫ ρ) (z.reindex τ)).pathApp =
    (partialComparison F hF f hf ρ z).pathApp.reindex
      (liftSub (interval (total (interval Δ))) (liftSub (interval Δ) τ)) := by
  apply PartialSection.ext
  intro x hx
  exact (partialComparison_body F hF f hf (τ ≫ ρ) (z.reindex τ) x hx).trans
    ((congrArg (fun t => t.val
      ((total (interval (total (interval (restrictContext (φ.reindex τ)))))).elementsMk x.obj
        ⟨⟨⟨x.val.1.1,hx⟩,x.val.1.2⟩,x.val.2⟩)) (localSquare_reindex F hF f hf ρ z τ)).trans
      (partialComparison_body F hF f hf ρ z
        ((liftSub (interval (total (interval Δ))) (liftSub (interval Δ) τ)).mapElements.obj x) hx).symm)

theorem partialComparison_boundary_reindex {Θ : Context.{u}} (τ : Θ ⟶ Δ) :
    (partialComparison F hF f hf (τ ≫ ρ) (z.reindex τ)).pathBoundary =
    (partialComparison F hF f hf ρ z).pathBoundary.reindex
      (liftSub (interval (total (interval Δ))) (liftSub (interval Δ) τ)) := by
  let s := partialComparison F hF f hf ρ z
  let σ := liftSub (interval Δ) τ
  have hb : endpointBoundary (comparisonBody (τ ≫ ρ))
      (fullForward F hF f hf (τ ≫ ρ) (z.reindex τ)) (fullPath F hF f hf (τ ≫ ρ) (z.reindex τ)) =
      (endpointBoundary (comparisonBody ρ) (fullForward F hF f hf ρ z) (fullPath F hF f hf ρ z)).reindex
        (liftSub (interval (total (interval Δ))) σ) :=
    (congrArg₂ (endpointBoundary (comparisonBody (τ ≫ ρ)))
      (fullForward_reindex F hF f hf ρ z τ) (fullPath_reindex F hF f hf ρ z τ)).trans
        (endpointBoundary_reindex (comparisonBody ρ) (fullForward F hF f hf ρ z) (fullPath F hF f hf ρ z) σ).symm
  exact (PartialSection.glue_congr (partialComparison_body_reindex F hF f hf ρ z τ) hb
    (partialComparison F hF f hf (τ ≫ ρ) (z.reindex τ)).pathApp_boundary_compatible
    (s.pathApp_boundary_compatible.reindex (liftSub (interval (total (interval Δ))) σ))).trans
      (PartialSection.glue_reindex s.pathApp _ s.pathApp_boundary_compatible
        (liftSub (interval (total (interval Δ))) σ)).symm

noncomputable def comparisonBodyBox := pathFillingBox (𝟙 _) φ (comparisonBox F hF f hf ρ z)

theorem comparisonBodyBox_base : (comparisonBodyBox F hF f hf ρ z).base =
    (fullSource F hF f hf ρ z).reindex (projection (interval Δ)) :=
  congrArg pathApp (Term.map_iso_roundtrip
    (pathReindexIso (comparisonBody ρ) (fullForward F hF f hf ρ z) (fullPath F hF f hf ρ z)
      (endpointSub Δ false)).symm _)

theorem comparisonBodyBox_reindex {Θ : Context.{u}} (τ : Θ ⟶ Δ) :
    comparisonBodyBox F hF f hf (τ ≫ ρ) (z.reindex τ) =
    (comparisonBodyBox F hF f hf ρ z).reindex (liftSub (interval Δ) τ) := by
  apply OpenBox.ext
  · exact congrArg (fun s => s.reindex (swapIntervals Θ))
      (partialComparison_boundary_reindex F hF f hf ρ z τ)
  · exact (comparisonBodyBox_base F hF f hf (τ ≫ ρ) (z.reindex τ)).trans
      ((congrArg (fun t => t.reindex (projection (interval Θ))) (fullSource_reindex F hF f hf ρ z τ)).trans
        (congrArg (fun t => t.reindex (liftSub (interval Δ) τ)) (comparisonBodyBox_base F hF f hf ρ z)).symm)

noncomputable def comparisonBodyFilled := F.fill
  (pathFillingContext (𝟙 (total (interval Δ))) ≫
    projection (interval (total (interval Δ))) ≫ liftSub (interval Γ) (base ρ))
  (pathBoundaryFace φ) (comparisonBodyBox F hF f hf ρ z)

theorem comparisonBodyFilled_reindex {Θ : Context.{u}} (τ : Θ ⟶ Δ) :
    comparisonBodyFilled F hF f hf (τ ≫ ρ) (z.reindex τ) =
    (comparisonBodyFilled F hF f hf ρ z).reindex
      (liftSub (interval (total (interval Δ))) (liftSub (interval Δ) τ)) :=
  (congrArg (F.fill
    (pathFillingContext (𝟙 (total (interval Θ))) ≫
      projection (interval (total (interval Θ))) ≫ liftSub (interval Γ) (base (τ ≫ ρ)))
    (pathBoundaryFace (φ.reindex τ))) (comparisonBodyBox_reindex F hF f hf ρ z τ)).trans
    (hF.uniform
      (pathFillingContext (𝟙 (total (interval Δ))) ≫
        projection (interval (total (interval Δ))) ≫ liftSub (interval Γ) (base ρ))
      (pathBoundaryFace φ) (comparisonBodyBox F hF f hf ρ z) (liftSub (interval Δ) τ))

theorem comparisonFilled_body : pathApp (comparisonFilled F hF f hf ρ z) =
    (comparisonBodyFilled F hF f hf ρ z).reindex (swapIntervals Δ) :=
  congrArg pathApp (pathFillingResult_normalize (𝟙 _) φ (comparisonBox F hF f hf ρ z)
    (comparisonBodyFilled F hF f hf ρ z) (hF.fills _ _ _))

theorem comparisonFilled_body_reindex {Θ : Context.{u}} (τ : Θ ⟶ Δ) :
    pathApp (comparisonFilled F hF f hf (τ ≫ ρ) (z.reindex τ)) =
    (pathApp (comparisonFilled F hF f hf ρ z)).reindex
      (liftSub (interval (total (interval Δ))) (liftSub (interval Δ) τ)) :=
  (comparisonFilled_body F hF f hf (τ ≫ ρ) (z.reindex τ)).trans
    ((congrArg (fun t => t.reindex (swapIntervals Θ))
      (comparisonBodyFilled_reindex F hF f hf ρ z τ)).trans
      (congrArg (fun t => t.reindex
        (liftSub (interval (total (interval Δ))) (liftSub (interval Δ) τ)))
        (comparisonFilled_body F hF f hf ρ z)).symm)

theorem finalPath_body_reindex {Θ : Context.{u}} (τ : Θ ⟶ Δ) :
    pathApp (finalPath F hF f hf (τ ≫ ρ) (z.reindex τ)) =
    (pathApp (finalPath F hF f hf ρ z)).reindex (liftSub (interval Δ) τ) :=
  congrArg (fun t => t.reindex (liftSub (interval (total (interval Θ))) (endpointSub Θ true)))
    (comparisonFilled_body_reindex F hF f hf ρ z τ)

theorem extend_reindex {Θ : Context.{u}} (τ : Θ ⟶ Δ) :
    extend F hF f hf (τ ≫ ρ) (z.reindex τ) = (extend F hF f hf ρ z).reindex τ :=
  (genericFiberIntro_congr f (τ ≫ ρ) _ _ (fullSource_reindex F hF f hf ρ z τ)
    _ _ (pathTerm_hext _ _ (finalPath_body_reindex F hF f hf ρ z τ))).trans
    (genericFiberIntro_reindex f ρ (fullSource F hF f hf ρ z) (finalPath F hF f hf ρ z) τ)

end FiberExtension


private theorem fiberIntro_input {Γ Ξ Δ : Context.{u}} {C D : Family Γ}
    (f : C ⟶ D) (σ : Ξ ⟶ Γ) (ρ : Δ ⟶ total (reindex D σ))
    (a : Term (reindex C (ρ ≫ liftSub D σ ≫ projection D)))
    (p : Term (homogeneousPath (reindex D (ρ ≫ liftSub D σ ≫ projection D))
      (Term.map (Functor.whiskerLeft (ρ ≫ liftSub D σ ≫ projection D).mapElements f) a)
      ((generic D).reindex (ρ ≫ liftSub D σ)))) :
    genericFiberIntro (Functor.whiskerLeft σ.mapElements f) ρ a p =
      Term.map (Functor.whiskerLeft ρ.mapElements (genericFiberReindexIso f σ).hom)
        (genericFiberIntro f (ρ ≫ liftSub D σ) a p) := by
  let q := Term.map (Functor.whiskerLeft ρ.mapElements (genericFiberReindexIso f σ).hom)
    (genericFiberIntro f (ρ ≫ liftSub D σ) a p)
  have hp : genericFiberPath (Functor.whiskerLeft σ.mapElements f) ρ q = p :=
    (genericFiberPath_input_reindex f σ ρ (genericFiberIntro f (ρ ≫ liftSub D σ) a p)).trans
      (Term.map_iso_roundtrip (genericFiberPathIso f (ρ ≫ liftSub D σ) a).symm p)
  exact (congrArg (genericFiberIntro (Functor.whiskerLeft σ.mapElements f) ρ a) hp).symm.trans
    (genericFiberIntro_eta (Functor.whiskerLeft σ.mapElements f) ρ q)


section SourceInput
variable {Ξ : Context.{u}} (F : Filling A) (hF : F.Lawful)
  (f : reindex A (endpointSub Γ false) ⟶ reindex A (endpointSub Γ true)) (hf : f = map F)
  (σ : Ξ ⟶ Γ)
  (ρ : Δ ⟶ total (reindex (reindex A (endpointSub Γ true)) σ)) {φ : Cofibration Δ}
  (z : PartialSection (reindex
    (homotopyFiber (Functor.whiskerLeft (projection (reindex A (endpointSub Γ true))).mapElements f)
      (generic (reindex A (endpointSub Γ true)))) (ρ ≫ liftSub (reindex A (endpointSub Γ true)) σ)) φ)

theorem FiberExtension.fullPath_input_reindex :
    fullPath (F.reindex (liftSub (interval Γ) σ)) (hF.reindex _)
      (Functor.whiskerLeft σ.mapElements f)
      ((congrArg (Functor.whiskerLeft σ.mapElements) hf).trans (map_reindex F hF σ).symm)
      ρ (z.map (Functor.whiskerLeft ρ.mapElements (genericFiberReindexIso f σ).hom)) =
    fullPath F hF f hf (ρ ≫ liftSub (reindex A (endpointSub Γ true)) σ) z := by
  rfl


theorem FiberExtension.comparisonBodyBox_input_reindex :
    comparisonBodyBox (F.reindex (liftSub (interval Γ) σ)) (hF.reindex _)
      (Functor.whiskerLeft σ.mapElements f)
      ((congrArg (Functor.whiskerLeft σ.mapElements) hf).trans (map_reindex F hF σ).symm)
      ρ (z.map (Functor.whiskerLeft ρ.mapElements (genericFiberReindexIso f σ).hom)) =
    comparisonBodyBox F hF f hf (ρ ≫ liftSub (reindex A (endpointSub Γ true)) σ) z := by
  rfl


theorem FiberExtension.finalPath_body_input_reindex :
    pathApp (finalPath (F.reindex (liftSub (interval Γ) σ)) (hF.reindex _)
      (Functor.whiskerLeft σ.mapElements f)
      ((congrArg (Functor.whiskerLeft σ.mapElements) hf).trans (map_reindex F hF σ).symm)
      ρ (z.map (Functor.whiskerLeft ρ.mapElements (genericFiberReindexIso f σ).hom))) =
    pathApp (finalPath F hF f hf (ρ ≫ liftSub (reindex A (endpointSub Γ true)) σ) z) := by
  let F' := F.reindex (liftSub (interval Γ) σ)
  let f' := Functor.whiskerLeft σ.mapElements f
  let hf' := (congrArg (Functor.whiskerLeft σ.mapElements) hf).trans (map_reindex F hF σ).symm
  let z' := z.map (Functor.whiskerLeft ρ.mapElements (genericFiberReindexIso f σ).hom)
  let ρ' := ρ ≫ liftSub (reindex A (endpointSub Γ true)) σ
  have ht : comparisonBodyFilled F' (hF.reindex _) f' hf' ρ z' =
      comparisonBodyFilled F hF f hf ρ' z :=
    congrArg (F.fill (pathFillingContext (𝟙 (total (interval Δ))) ≫
      projection (interval (total (interval Δ))) ≫ liftSub (interval Γ) (base ρ'))
      (pathBoundaryFace φ)) (comparisonBodyBox_input_reindex F hF f hf σ ρ z)
  have hp := (comparisonFilled_body F' (hF.reindex _) f' hf' ρ z').trans
    ((congrArg (fun t => t.reindex (swapIntervals Δ)) ht).trans
      (comparisonFilled_body F hF f hf ρ' z).symm)
  exact congrArg (fun t => t.reindex
    (liftSub (interval (total (interval Δ))) (endpointSub Δ true))) hp

theorem FiberExtension.extend_input_reindex :
    extend (F.reindex (liftSub (interval Γ) σ)) (hF.reindex _)
      (Functor.whiskerLeft σ.mapElements f)
      ((congrArg (Functor.whiskerLeft σ.mapElements) hf).trans (map_reindex F hF σ).symm)
      ρ (z.map (Functor.whiskerLeft ρ.mapElements (genericFiberReindexIso f σ).hom)) =
    Term.map (Functor.whiskerLeft ρ.mapElements (genericFiberReindexIso f σ).hom)
      (extend F hF f hf (ρ ≫ liftSub (reindex A (endpointSub Γ true)) σ) z) := by
  have hs := congrArg (fun t => t.reindex (endpointSub Δ false))
    (fullPath_input_reindex F hF f hf σ ρ z)
  exact (genericFiberIntro_congr (Functor.whiskerLeft σ.mapElements f) ρ _ _ hs
    _ _ (pathTerm_hext _ _ (finalPath_body_input_reindex F hF f hf σ ρ z))).trans
    (fiberIntro_input f σ ρ (fullSource F hF f hf (ρ ≫ liftSub (reindex A (endpointSub Γ true)) σ) z)
      (finalPath F hF f hf (ρ ≫ liftSub (reindex A (endpointSub Γ true)) σ) z))

end SourceInput


/-- The chosen transport-fiber construction with an explicit presentation of the same map. -/
noncomputable def equivalenceOf (F : Filling A) (hF : F.Lawful)
    (f : reindex A (endpointSub Γ false) ⟶ reindex A (endpointSub Γ true)) (hf : f = map F) :
    HomotopyEquivalence f where
  fibers := HomotopyContractible.ofExtensions
    (fun ρ _ z => FiberExtension.extend F hF f hf ρ z)
    (fun ρ _ z x hx => FiberExtension.extend_boundary F hF f hf ρ z x hx)

theorem equivalenceOf_reindex {Ξ : Context.{u}} (F : Filling A) (hF : F.Lawful)
    (f : reindex A (endpointSub Γ false) ⟶ reindex A (endpointSub Γ true)) (hf : f = map F)
    (σ : Ξ ⟶ Γ) :
    (equivalenceOf F hF f hf).reindex σ =
      equivalenceOf (F.reindex (liftSub (interval Γ) σ)) (hF.reindex _)
        (Functor.whiskerLeft σ.mapElements f)
        ((congrArg (Functor.whiskerLeft σ.mapElements) hf).trans (map_reindex F hF σ).symm) := by
  apply congrArg HomotopyEquivalence.mk
  let τ := liftSub (reindex A (endpointSub Γ true)) σ
  let E := fun {Δ : Context.{u}} (ρ : Δ ⟶ total (reindex A (endpointSub Γ true)))
    (φ : Cofibration Δ) (z : PartialSection _ φ) => FiberExtension.extend F hF f hf ρ z
  let hb := fun {Δ : Context.{u}} (ρ : Δ ⟶ total (reindex A (endpointSub Γ true)))
    (φ : Cofibration Δ) (z : PartialSection _ φ) x hx => FiberExtension.extend_boundary F hF f hf ρ z x hx
  let hu := fun {Δ Θ : Context.{u}} (ρ : Δ ⟶ total (reindex A (endpointSub Γ true)))
    (φ : Cofibration Δ) (z : PartialSection _ φ) (ν : Θ ⟶ Δ) => FiberExtension.extend_reindex F hF f hf ρ z ν
  exact (congrArg (fun c => c.transport (genericFiberReindexIso f σ))
    (HomotopyContractible.ofExtensions_reindex E hb hu τ)).trans
      (HomotopyContractible.ofExtensions_iso
        (fun ρ φ z => E (ρ ≫ τ) φ z) (fun ρ φ z x hx => hb (ρ ≫ τ) φ z x hx)
        (fun ρ φ z ν => hu (ρ ≫ τ) φ z ν)
        _ _ (genericFiberReindexIso f σ)
        (fun ρ _ z => (FiberExtension.extend_input_reindex F hF f hf σ ρ z).symm))

/-- The actual chosen interval transport has contractible native homotopy fibers. -/
noncomputable def equivalence (F : Filling A) (hF : F.Lawful) : HomotopyEquivalence (map F) where
  fibers := HomotopyContractible.ofExtensions
    (fun ρ _ z => FiberExtension.extend F hF (map F) rfl ρ z)
    (fun ρ _ z x hx => FiberExtension.extend_boundary F hF (map F) rfl ρ z x hx)

/-- Changing the presentation of the map does not replace the chosen fiber contraction. -/
theorem equivalenceOf_heq (F : Filling A) (hF : F.Lawful)
    (f : reindex A (endpointSub Γ false) ⟶ reindex A (endpointSub Γ true)) (hf : f = map F) :
    HEq (equivalenceOf F hF f hf) (equivalence F hF) := by
  subst f
  rfl

theorem equivalence_reindex {Ξ : Context.{u}} (F : Filling A) (hF : F.Lawful)
    (σ : Ξ ⟶ Γ) :
    HEq ((equivalence F hF).reindex σ)
      (equivalence (F.reindex (liftSub (interval Γ) σ)) (hF.reindex _)) :=
  (heq_of_eq (equivalenceOf_reindex F hF (map F) rfl σ)).trans
    (equivalenceOf_heq _ _ _ _)

end SquareKit.Cubical.Presheaf.IntervalTransport
