import SquareKit.Internal.Cubical.NativePathComposition
import SquareKit.Internal.Cubical.UnivalenceTransport

set_option autoImplicit false
set_option warningAsError true
namespace SquareKit.Cubical.Presheaf.NativeTransportComposition
open CategoryTheory
universe u

section SectionComparison
variable {Γ : Context.{u}} {A : Family (total (interval Γ))}
  (F : Filling A) (hF : F.Lawful) (z : Term A)

private noncomputable def sectionsInitial (v w : Term A)
    (h : v.reindex (endpointSub Γ false) = w.reindex (endpointSub Γ false)) :
    Term (reindex (homogeneousPath A v w) (endpointSub Γ false)) :=
  Term.map (pathReindexIso (reindex A (projection (interval (total (interval Γ)))))
    v w (endpointSub Γ false)).inv
    (pathLam ((v.reindex (endpointSub Γ false)).reindex (projection (interval Γ))) rfl h)

private noncomputable def sectionsFilling (v w : Term A) :=
  pathFilling (F.reindex (projection (interval (total (interval Γ))))) (hF.reindex _) v w

private noncomputable def sectionsFilled (v w : Term A)
    (h : v.reindex (endpointSub Γ false) = w.reindex (endpointSub Γ false)) :=
  IntervalTransport.forward (sectionsFilling F hF v w) (𝟙 Γ) (sectionsInitial v w h)

private theorem sectionsInitial_reindex {Δ : Context.{u}} (v w : Term A)
    (h : v.reindex (endpointSub Γ false) = w.reindex (endpointSub Γ false)) (σ : Δ ⟶ Γ) :
    Term.map (Functor.whiskerLeft (endpointSub Δ false).mapElements
      (pathReindexIso (reindex A (projection (interval (total (interval Γ))))) v w
        (liftSub (interval Γ) σ)).hom) ((sectionsInitial v w h).reindex σ) =
      sectionsInitial (v.reindex (liftSub (interval Γ) σ))
        (w.reindex (liftSub (interval Γ) σ)) (congrArg (fun t => t.reindex σ) h) := by
  apply Term.map_injective_of_iso (pathReindexIso _ _ _ (endpointSub Δ false))
  apply pathApp_injective
  have hz := Term.map_iso_roundtrip
    (pathReindexIso (reindex A (projection (interval (total (interval Γ))))) v w
      (endpointSub Γ false)).symm
    (pathLam ((v.reindex (endpointSub Γ false)).reindex (projection (interval Γ))) rfl h)
  exact (congrArg (fun t => (pathApp t).reindex (liftSub (interval Γ) σ)) hz).trans
    (congrArg pathApp (Term.map_iso_roundtrip
      (pathReindexIso (reindex (reindex A (liftSub (interval Γ) σ))
        (projection (interval (total (interval Δ)))))
        (v.reindex (liftSub (interval Γ) σ)) (w.reindex (liftSub (interval Γ) σ))
        (endpointSub Δ false)).symm
      (pathLam (((v.reindex (liftSub (interval Γ) σ)).reindex (endpointSub Δ false)).reindex
        (projection (interval Δ))) rfl (congrArg (fun t => t.reindex σ) h)))).symm

private theorem sectionsFilled_reindex {Δ : Context.{u}} (v w : Term A)
    (h : v.reindex (endpointSub Γ false) = w.reindex (endpointSub Γ false)) (σ : Δ ⟶ Γ) :
    Term.map (pathReindexIso (reindex A (projection (interval (total (interval Γ))))) v w
      (liftSub (interval Γ) σ)).hom
      ((sectionsFilled F hF v w h).reindex (liftSub (interval Γ) σ)) =
    sectionsFilled (F.reindex (liftSub (interval Γ) σ)) (hF.reindex _)
      (v.reindex (liftSub (interval Γ) σ)) (w.reindex (liftSub (interval Γ) σ))
      (congrArg (fun t => t.reindex σ) h) := by
  let L := liftSub (interval Γ) σ
  let e := pathReindexIso (reindex A (projection (interval (total (interval Γ))))) v w L
  let K := sectionsFilling F hF v w
  let t := sectionsInitial v w h
  have hk := pathFilling_reindex_iso
    (F.reindex (projection (interval (total (interval Γ))))) (hF.reindex _) v w L
  have hi := sectionsInitial_reindex v w h σ
  have hs := congrArg (fun H => IntervalTransport.forward H (𝟙 Δ)
    (sectionsInitial (v.reindex L) (w.reindex L) (congrArg (fun t => t.reindex σ) h))) hk.symm
  have ht := congrArg (IntervalTransport.forward ((K.reindex L).transport e) (𝟙 Δ)) hi.symm
  have hu := IntervalTransport.forward_transport_map (K.reindex L) e (t.reindex σ)
  have hn := IntervalTransport.forward_reindex K
    (pathFilling_lawful (F.reindex (projection (interval (total (interval Γ)))))
      (hF.reindex _) v w) (𝟙 Γ) t σ
  exact (hs.trans (ht.trans (hu.trans (congrArg (Term.map e.hom) hn)))).symm

private noncomputable def sectionFilled := sectionsFilled F hF
  (IntervalTransport.forward F (𝟙 Γ) (z.reindex (endpointSub Γ false))) z
  (IntervalTransport.forward_zero F hF (𝟙 Γ) (z.reindex (endpointSub Γ false)))

/-- Any actual dependent section compares its endpoint with the chosen transport
of its start. The comparison is a native path, with no regularity assumption. -/
noncomputable def sectionComparison : Term (homogeneousPath (reindex A (endpointSub Γ true))
    (Term.map (IntervalTransport.map F) (z.reindex (endpointSub Γ false)))
    (z.reindex (endpointSub Γ true))) := by
  let q := Term.map (pathReindexIso (reindex A (projection (interval (total (interval Γ)))))
    (IntervalTransport.forward F (𝟙 Γ) (z.reindex (endpointSub Γ false))) z
    (endpointSub Γ true)).hom ((sectionFilled F hF z).reindex (endpointSub Γ true))
  exact pathLam (pathApp q)
    ((pathApp_zero q).trans (IntervalTransport.map_section F hF (z.reindex (endpointSub Γ false))).symm)
    (pathApp_one q)

private theorem sectionsFilled_body_congr (v v' w : Term A) (e : v = v')
    (h : v.reindex (endpointSub Γ false) = w.reindex (endpointSub Γ false))
    (h' : v'.reindex (endpointSub Γ false) = w.reindex (endpointSub Γ false)) :
    pathApp (sectionsFilled F hF v w h) = pathApp (sectionsFilled F hF v' w h') := by
  cases e
  rfl

/-- The full native comparison body commutes with context substitution. -/
theorem sectionComparison_body_reindex {Δ : Context.{u}} (σ : Δ ⟶ Γ) :
    pathApp (sectionComparison (F.reindex (liftSub (interval Γ) σ)) (hF.reindex _)
      (z.reindex (liftSub (interval Γ) σ))) =
    (pathApp (sectionComparison F hF z)).reindex (liftSub (interval Γ) σ) := by
  let v := IntervalTransport.forward F (𝟙 Γ) (z.reindex (endpointSub Γ false))
  let h := IntervalTransport.forward_zero F hF (𝟙 Γ) (z.reindex (endpointSub Γ false))
  let L := liftSub (interval Γ) σ
  have hn := congrArg pathApp (sectionsFilled_reindex F hF v z h σ)
  have hv := IntervalTransport.forward_reindex F hF (𝟙 Γ) (z.reindex (endpointSub Γ false)) σ
  have he := sectionsFilled_body_congr (F.reindex L) (hF.reindex _)
    (IntervalTransport.forward (F.reindex L) (𝟙 Δ)
      ((z.reindex L).reindex (endpointSub Δ false))) (v.reindex L) (z.reindex L) hv
    (IntervalTransport.forward_zero (F.reindex L) (hF.reindex _) (𝟙 Δ)
      ((z.reindex L).reindex (endpointSub Δ false))) (congrArg (fun t => t.reindex σ) h)
  exact congrArg (fun t => t.reindex
    (liftSub (interval (total (interval Δ))) (endpointSub Δ true))) (he.trans hn.symm)

/-- Constant-path transport is homotopic to the identity, even for a filler
which does not satisfy a judgmental regularity rule. -/
noncomputable def identityComparison {B : Family Γ} (G : Filling B) (hG : G.Lawful)
    (x : Term B) : Term (homogeneousPath B
      (Term.map (IntervalTransport.map (G.reindex (projection (interval Γ)))) x) x) :=
  sectionComparison (G.reindex (projection (interval Γ))) (hG.reindex _)
    (x.reindex (projection (interval Γ)))

end SectionComparison
private theorem convert_map {Ξ : Context.{u}} {C D : Family Ξ} (h : C = D) (t : Term C) :
    t.convert h = Term.map (eqToHom h) t := by
  cases h
  rfl

section Along
variable {Γ : Context.{u}} {A : Family Γ} (B : Family (total A))
  {a b : Term A} (p : Term (homogeneousPath A a b))

def fiber (a : Term A) : Family Γ := reindex B (pair (𝟙 Γ) a)
def lineMap : total (interval Γ) ⟶ total A := pair (projection (interval Γ)) (pathApp p)
def line : Family (total (interval Γ)) := reindex B (lineMap p)

theorem line_zero : reindex (line B p) (endpointSub Γ false) = fiber B a :=
  congrArg (fun t => fiber B t) (pathApp_zero p)
theorem line_one : reindex (line B p) (endpointSub Γ true) = fiber B b :=
  congrArg (fun t => fiber B t) (pathApp_one p)

def along (G : Filling B) : fiber B a ⟶ fiber B b :=
  IntervalTransport.mapTo (G.reindex (lineMap p)) (fiber B a) (fiber B b)
    (line_zero B p) (line_one B p)

def alongSection (G : Filling B) (x : Term (fiber B a)) : Term (line B p) :=
  IntervalTransport.forward (G.reindex (lineMap p)) (𝟙 Γ)
    (x.convert (line_zero B p).symm)

theorem alongSection_zero (G : Filling B) (hG : G.Lawful) (x : Term (fiber B a)) :
    (alongSection B p G x).reindex (endpointSub Γ false) = x.convert (line_zero B p).symm :=
  IntervalTransport.forward_zero (G.reindex (lineMap p)) (hG.reindex _) (𝟙 Γ) _

theorem alongSection_one (G : Filling B) (hG : G.Lawful) (x : Term (fiber B a)) :
    ((alongSection B p G x).reindex (endpointSub Γ true)).convert (line_one B p) =
      Term.map (along B p G) x := by
  have h := IntervalTransport.map_section (G.reindex (lineMap p)) (hG.reindex _)
    (x.convert (line_zero B p).symm)
  calc
    _ = Term.map (eqToHom (line_one B p))
        ((alongSection B p G x).reindex (endpointSub Γ true)) := convert_map _ _
    _ = Term.map (eqToHom (line_one B p))
        (Term.map (IntervalTransport.map (G.reindex (lineMap p)))
          (x.convert (line_zero B p).symm)) := congrArg (Term.map (eqToHom (line_one B p))) h.symm
    _ = _ := congrArg (fun t => Term.map (eqToHom (line_one B p))
        (Term.map (IntervalTransport.map (G.reindex (lineMap p))) t)) (convert_map _ x)

/-- A dependent line with specified endpoints compares the selected transport
with its actual endpoint; endpoint casts retain the original selected filler. -/
noncomputable def alongComparison (G : Filling B) (hG : G.Lawful)
    (x : Term (fiber B a)) (y : Term (fiber B b)) (z : Term (line B p))
    (hz₀ : z.reindex (endpointSub Γ false) = x.convert (line_zero B p).symm)
    (hz₁ : (z.reindex (endpointSub Γ true)).convert (line_one B p) = y) :
    Term (homogeneousPath (fiber B b) (Term.map (along B p G) x) y) := by
  let c := homogeneousPathMap (eqToHom (line_one B p))
    (sectionComparison (G.reindex (lineMap p)) (hG.reindex _) z)
  refine pathLam (pathApp c) ((pathApp_zero c).trans ?_) ((pathApp_one c).trans ?_)
  · change Term.map (eqToHom (line_one B p))
      (Term.map (IntervalTransport.map (G.reindex (lineMap p)))
        (z.reindex (endpointSub Γ false))) = _
    rw [hz₀, convert_map]
    rfl
  · exact (convert_map (line_one B p) _).symm.trans hz₁

private theorem reindex_heq {Ξ Ω : Context.{u}} {C : Family Ξ}
    (t : Term C) {σ τ : Ω ⟶ Ξ} (h : σ = τ) : HEq (t.reindex σ) (t.reindex τ) := by
  cases h
  rfl

/-- Reversing the actual chosen forward lift supplies the dependent line for
one inverse law; no independent inverse transport is substituted. -/
def reverseSection (G : Filling B) (x : Term (fiber B a)) :
    Term (line B (homogeneousReverse p)) :=
  (alongSection B p G x).reindex (reverseInterval Γ)

theorem reverseSection_zero (G : Filling B) (hG : G.Lawful) (x : Term (fiber B a)) :
    (reverseSection B p G x).reindex (endpointSub Γ false) =
      (Term.map (along B p G) x).convert (line_zero B (homogeneousReverse p)).symm := by
  apply eq_of_heq
  exact (reindex_heq (alongSection B p G x) (reverseInterval_endpoint Γ false)).trans
    ((Term.convert_heq (line_one B p) _).symm.trans
      ((heq_of_eq (alongSection_one B p G hG x)).trans (Term.convert_heq _ _).symm))

theorem reverseSection_one (G : Filling B) (hG : G.Lawful) (x : Term (fiber B a)) :
    ((reverseSection B p G x).reindex (endpointSub Γ true)).convert
      (line_one B (homogeneousReverse p)) = x := by
  apply eq_of_heq
  exact (Term.convert_heq _ _).trans
    ((reindex_heq (alongSection B p G x) (reverseInterval_endpoint Γ true)).trans
      ((heq_of_eq (alongSection_zero B p G hG x)).trans (Term.convert_heq _ _)))

noncomputable def reverseLeftComparison (G : Filling B) (hG : G.Lawful)
    (x : Term (fiber B a)) : Term (homogeneousPath (fiber B a)
      (Term.map (along B (homogeneousReverse p) G) (Term.map (along B p G) x)) x) :=
  alongComparison B (homogeneousReverse p) G hG (Term.map (along B p G) x) x
    (reverseSection B p G x) (reverseSection_zero B p G hG x) (reverseSection_one B p G hG x)

private theorem reverse_twice : homogeneousReverse (homogeneousReverse p) = p := by
  apply pathApp_injective
  exact eq_of_heq (reindex_heq (pathApp p) (reverseInterval_twice Γ))

/-- The other inverse law uses the chosen lift in the reversed family. -/
noncomputable def reverseRightComparison (G : Filling B) (hG : G.Lawful)
    (y : Term (fiber B b)) : Term (homogeneousPath (fiber B b)
      (Term.map (along B p G) (Term.map (along B (homogeneousReverse p) G) y)) y) := by
  let c := reverseLeftComparison B (homogeneousReverse p) G hG y
  exact pathLam (pathApp c)
    ((pathApp_zero c).trans (congrArg (fun r => Term.map (along B r G)
      (Term.map (along B (homogeneousReverse p) G) y)) (reverse_twice p)))
    (pathApp_one c)

/-- Reflexivity transport has a native identity comparison for every fiber. -/
noncomputable def alongIdentityComparison (G : Filling B) (hG : G.Lawful)
    (a : Term A) (x : Term (fiber B a)) : Term (homogeneousPath (fiber B a)
      (Term.map (along B (homogeneousRefl a) G) x) x) :=
  identityComparison (G.reindex (pair (𝟙 Γ) a)) (hG.reindex _) x

/-- Context substitution preserves the selected dependent transport map. -/
theorem along_reindex {Δ : Context.{u}} (G : Filling B) (hG : G.Lawful) (σ : Δ ⟶ Γ) :
    Functor.whiskerLeft σ.mapElements (along B p G) =
      along (reindex B (liftSub A σ)) (homogeneousReindex p σ)
        (G.reindex (liftSub A σ)) :=
  IntervalTransport.mapTo_reindex (G.reindex (lineMap p)) (hG.reindex _)
    (fiber B a) (fiber B b) (line_zero B p) (line_one B p) σ

/-- The actual chosen lift, not just its endpoint transport, is preserved. -/
theorem alongSection_reindex {Δ : Context.{u}} (G : Filling B) (hG : G.Lawful)
    (x : Term (fiber B a)) (σ : Δ ⟶ Γ) :
    alongSection (reindex B (liftSub A σ)) (homogeneousReindex p σ)
      (G.reindex (liftSub A σ)) (x.reindex σ) =
      (alongSection B p G x).reindex (liftSub (interval Γ) σ) := by
  have hc := Term.convert_reindex (line_zero B p).symm x σ
  have hf := IntervalTransport.forward_reindex (G.reindex (lineMap p)) (hG.reindex _)
    (𝟙 Γ) (x.convert (line_zero B p).symm) σ
  exact (congrArg (IntervalTransport.forward
    ((G.reindex (liftSub A σ)).reindex (lineMap (homogeneousReindex p σ))) (𝟙 Δ)) hc.symm).trans hf

private theorem whisker_eqToHom {Ξ Ω : Context.{u}} {C D : Family Ξ}
    (h : C = D) (σ : Ω ⟶ Ξ) :
    Functor.whiskerLeft σ.mapElements (eqToHom h) =
      eqToHom (congrArg (fun T => reindex T σ) h) := by
  cases h
  rfl

/-- Exact naturality of the native comparison body; the two endpoint proofs
may be any proofs of the stated substituted equations. -/
theorem alongComparison_body_reindex {Δ : Context.{u}} (G : Filling B) (hG : G.Lawful)
    (x : Term (fiber B a)) (y : Term (fiber B b)) (z : Term (line B p))
    (hz₀ : z.reindex (endpointSub Γ false) = x.convert (line_zero B p).symm)
    (hz₁ : (z.reindex (endpointSub Γ true)).convert (line_one B p) = y)
    (σ : Δ ⟶ Γ)
    (h₀ : (z.reindex (liftSub (interval Γ) σ)).reindex (endpointSub Δ false) =
      (x.reindex σ).convert (line_zero (reindex B (liftSub A σ)) (homogeneousReindex p σ)).symm)
    (h₁ : ((z.reindex (liftSub (interval Γ) σ)).reindex (endpointSub Δ true)).convert
      (line_one (reindex B (liftSub A σ)) (homogeneousReindex p σ)) = y.reindex σ) :
    pathApp (alongComparison (reindex B (liftSub A σ)) (homogeneousReindex p σ)
      (G.reindex (liftSub A σ)) (hG.reindex _) (x.reindex σ) (y.reindex σ)
      (z.reindex (liftSub (interval Γ) σ)) h₀ h₁) =
      (pathApp (alongComparison B p G hG x y z hz₀ hz₁)).reindex (liftSub (interval Γ) σ) := by
  have hn := sectionComparison_body_reindex (G.reindex (lineMap p)) (hG.reindex _) z σ
  have he := whisker_eqToHom (line_one B p) σ
  change Term.map (Functor.whiskerLeft (projection (interval Δ)).mapElements (eqToHom _))
    (pathApp (sectionComparison _ _ _)) = _
  exact (congrArg (Term.map (Functor.whiskerLeft (projection (interval Δ)).mapElements
    (eqToHom (line_one (reindex B (liftSub A σ)) (homogeneousReindex p σ))))) hn).trans
    (congrArg (fun (f : reindex (reindex (line B p) (endpointSub Γ true)) σ ⟶
        reindex (fiber B b) σ) => Term.map (Functor.whiskerLeft (projection (interval Δ)).mapElements f)
      ((pathApp (sectionComparison (G.reindex (lineMap p)) (hG.reindex _) z)).reindex
        (liftSub (interval Γ) σ))) he.symm)

/-- Naturality with explicitly identified substituted path and dependent section.
Endpoint terms may have different presentations; their boundary equations
identify the same selected comparison body. -/
theorem alongComparison_body_natural {Δ : Context.{u}} (G : Filling B) (hG : G.Lawful)
    (x : Term (fiber B a)) (y : Term (fiber B b)) (z : Term (line B p))
    (hz₀ : z.reindex (endpointSub Γ false) = x.convert (line_zero B p).symm)
    (hz₁ : (z.reindex (endpointSub Γ true)).convert (line_one B p) = y)
    (σ : Δ ⟶ Γ)
    (p' : Term (homogeneousPath (reindex A σ) (a.reindex σ) (b.reindex σ)))
    (ep : p' = homogeneousReindex p σ)
    (x' : Term (fiber (reindex B (liftSub A σ)) (a.reindex σ)))
    (y' : Term (fiber (reindex B (liftSub A σ)) (b.reindex σ)))
    (z' : Term (line (reindex B (liftSub A σ)) p'))
    (ez : HEq z' (z.reindex (liftSub (interval Γ) σ)))
    (h₀ : z'.reindex (endpointSub Δ false) =
      x'.convert (line_zero (reindex B (liftSub A σ)) p').symm)
    (h₁ : (z'.reindex (endpointSub Δ true)).convert
      (line_one (reindex B (liftSub A σ)) p') = y') :
    pathApp (alongComparison (reindex B (liftSub A σ)) p'
      (G.reindex (liftSub A σ)) (hG.reindex _) x' y' z' h₀ h₁) =
      (pathApp (alongComparison B p G hG x y z hz₀ hz₁)).reindex (liftSub (interval Γ) σ) := by
  cases ep
  have hez := eq_of_heq ez
  subst z'
  have hn := sectionComparison_body_reindex (G.reindex (lineMap p)) (hG.reindex _) z σ
  have he := whisker_eqToHom (line_one B p) σ
  exact (congrArg (Term.map (Functor.whiskerLeft (projection (interval Δ)).mapElements
    (eqToHom (line_one (reindex B (liftSub A σ)) (homogeneousReindex p σ))))) hn).trans
    (congrArg (fun (f : reindex (reindex (line B p) (endpointSub Γ true)) σ ⟶
        reindex (fiber B b) σ) => Term.map (Functor.whiskerLeft (projection (interval Δ)).mapElements f)
      ((pathApp (sectionComparison (G.reindex (lineMap p)) (hG.reindex _) z)).reindex
        (liftSub (interval Γ) σ))) he.symm)

theorem reverseLeftComparison_body_reindex {Δ : Context.{u}} (G : Filling B) (hG : G.Lawful)
    (x : Term (fiber B a)) (σ : Δ ⟶ Γ) :
    pathApp (reverseLeftComparison (reindex B (liftSub A σ)) (homogeneousReindex p σ)
      (G.reindex (liftSub A σ)) (hG.reindex _) (x.reindex σ)) =
    (pathApp (reverseLeftComparison B p G hG x)).reindex (liftSub (interval Γ) σ) :=
  alongComparison_body_natural B (homogeneousReverse p) G hG (Term.map (along B p G) x) x
    (reverseSection B p G x) (reverseSection_zero B p G hG x) (reverseSection_one B p G hG x) σ
    (homogeneousReverse (homogeneousReindex p σ)) rfl _ _ _
    (heq_of_eq (congrArg (fun t => t.reindex (reverseInterval Δ)) (alongSection_reindex B p G hG x σ)))
    (reverseSection_zero (reindex B (liftSub A σ)) (homogeneousReindex p σ)
      (G.reindex (liftSub A σ)) (hG.reindex _) (x.reindex σ))
    (reverseSection_one (reindex B (liftSub A σ)) (homogeneousReindex p σ)
      (G.reindex (liftSub A σ)) (hG.reindex _) (x.reindex σ))

private theorem reverseRightComparison_body (G : Filling B) (hG : G.Lawful)
    (y : Term (fiber B b)) : pathApp (reverseRightComparison B p G hG y) =
      pathApp (reverseLeftComparison B (homogeneousReverse p) G hG y) := rfl

theorem reverseRightComparison_body_reindex {Δ : Context.{u}} (G : Filling B) (hG : G.Lawful)
    (y : Term (fiber B b)) (σ : Δ ⟶ Γ) :
    pathApp (reverseRightComparison (reindex B (liftSub A σ)) (homogeneousReindex p σ)
      (G.reindex (liftSub A σ)) (hG.reindex _) (y.reindex σ)) =
    (pathApp (reverseRightComparison B p G hG y)).reindex (liftSub (interval Γ) σ) := by
  exact (reverseRightComparison_body (reindex B (liftSub A σ)) (homogeneousReindex p σ)
    (G.reindex (liftSub A σ)) (hG.reindex _) (y.reindex σ)).trans
    ((reverseLeftComparison_body_reindex B (homogeneousReverse p) G hG y σ).trans
      (congrArg (fun t => t.reindex (liftSub (interval Γ) σ))
        (reverseRightComparison_body B p G hG y)).symm)

theorem alongIdentityComparison_body_reindex {Δ : Context.{u}} (G : Filling B) (hG : G.Lawful)
    (a : Term A) (x : Term (fiber B a)) (σ : Δ ⟶ Γ) :
    pathApp (alongIdentityComparison (reindex B (liftSub A σ)) (G.reindex (liftSub A σ))
      (hG.reindex _) (a.reindex σ) (x.reindex σ)) =
    (pathApp (alongIdentityComparison B G hG a x)).reindex (liftSub (interval Γ) σ) :=
  sectionComparison_body_reindex ((G.reindex (pair (𝟙 Γ) a)).reindex (projection (interval Γ)))
    ((hG.reindex _).reindex _) (x.reindex (projection (interval Γ))) σ

end Along

section SquareComparison
variable {Γ : Context.{u}}
  {B : Family (total (interval (total (interval Γ))))}
  (F : Filling B) (hF : F.Lawful)
  (l : Term (reindex B (endpointSub (total (interval Γ)) false)))
  (r : Term (reindex B (endpointSub (total (interval Γ)) true)))
  (p : Term (reindex (path B l r) (endpointSub Γ false)))

/-- Lift an actual dependent bottom path through a square while preserving its
specified left and right sections. -/
noncomputable def squareLift : Term (path B l r) :=
  (pathFilling F hF l r).fill (𝟙 _) (Cofibration.bot Γ) (OpenBox.empty _ p)

/-- The upper dependent path produced by the square filler. -/
noncomputable def squareTop : Term (path
    (reindex B (liftSub (interval (total (interval Γ))) (endpointSub Γ true)))
    (l.reindex (endpointSub Γ true)) (r.reindex (endpointSub Γ true))) :=
  Term.map (pathReindex B l r (endpointSub Γ true))
    ((squareLift F hF l r p).reindex (endpointSub Γ true))

/-- Chosen transport across the upper edge agrees by a native path with the
right endpoint obtained by lifting the supplied bottom path. -/
noncomputable def squareComparison : Term (homogeneousPath
    (reindex (reindex B (liftSub (interval (total (interval Γ))) (endpointSub Γ true)))
      (endpointSub Γ true))
    (Term.map (IntervalTransport.map
      (F.reindex (liftSub (interval (total (interval Γ))) (endpointSub Γ true))))
      (l.reindex (endpointSub Γ true)))
    (r.reindex (endpointSub Γ true))) := by
  let q := squareTop F hF l r p
  let c := sectionComparison
    (F.reindex (liftSub (interval (total (interval Γ))) (endpointSub Γ true)))
    (hF.reindex _) (pathApp q)
  exact pathLam (pathApp c)
    ((pathApp_zero c).trans (congrArg (Term.map (IntervalTransport.map
      (F.reindex (liftSub (interval (total (interval Γ))) (endpointSub Γ true)))))
      (pathApp_zero q)))
    ((pathApp_one c).trans (pathApp_one q))

def squareInitialReindex {Δ : Context.{u}} (σ : Δ ⟶ Γ) :=
  Term.map (Functor.whiskerLeft (endpointSub Δ false).mapElements
    (pathReindexIso B l r (liftSub (interval Γ) σ)).hom) (p.reindex σ)

/-- Reindexing preserves the entire selected dependent square lift. -/
theorem squareLift_reindex {Δ : Context.{u}} (σ : Δ ⟶ Γ) :
    Term.map (pathReindexIso B l r (liftSub (interval Γ) σ)).hom
      ((squareLift F hF l r p).reindex (liftSub (interval Γ) σ)) =
    squareLift (F.reindex (liftSub (interval (total (interval Γ))) (liftSub (interval Γ) σ)))
      (hF.reindex _) (l.reindex (liftSub (interval Γ) σ)) (r.reindex (liftSub (interval Γ) σ))
      (squareInitialReindex l r p σ) := by
  let L := liftSub (interval Γ) σ
  let e := pathReindexIso B l r L
  let K := pathFilling F hF l r
  have hk := pathFilling_reindex_iso F hF l r L
  have hs := congrArg (fun H => IntervalTransport.forward H (𝟙 Δ)
    (squareInitialReindex l r p σ)) hk.symm
  have hu := IntervalTransport.forward_transport_map (K.reindex L) e (p.reindex σ)
  have hn := IntervalTransport.forward_reindex K (pathFilling_lawful F hF l r) (𝟙 Γ) p σ
  exact (hs.trans (hu.trans (congrArg (Term.map e.hom) hn))).symm

theorem squareTop_body_reindex {Δ : Context.{u}} (σ : Δ ⟶ Γ) :
    pathApp (squareTop
      (F.reindex (liftSub (interval (total (interval Γ))) (liftSub (interval Γ) σ)))
      (hF.reindex _) (l.reindex (liftSub (interval Γ) σ)) (r.reindex (liftSub (interval Γ) σ))
      (squareInitialReindex l r p σ)) =
      (pathApp (squareTop F hF l r p)).reindex (liftSub (interval Γ) σ) :=
  congrArg (fun t => (pathApp t).reindex
    (liftSub (interval (total (interval Δ))) (endpointSub Δ true)))
    (squareLift_reindex F hF l r p σ).symm

noncomputable def squareTopOfSection
    (z : Term (reindex B (liftSub (interval (total (interval Γ))) (endpointSub Γ false))))
    (h₀ : z.reindex (endpointSub Γ false) = l.reindex (endpointSub Γ false))
    (h₁ : z.reindex (endpointSub Γ true) = r.reindex (endpointSub Γ false)) :=
  squareTop F hF l r (Term.map (pathReindexIso B l r (endpointSub Γ false)).inv
    (pathLam z h₀ h₁))

private theorem squareInitialOfSection_reindex {Δ : Context.{u}}
    (z : Term (reindex B (liftSub (interval (total (interval Γ))) (endpointSub Γ false))))
    (h₀ : z.reindex (endpointSub Γ false) = l.reindex (endpointSub Γ false))
    (h₁ : z.reindex (endpointSub Γ true) = r.reindex (endpointSub Γ false)) (σ : Δ ⟶ Γ) :
    squareInitialReindex l r
      (Term.map (pathReindexIso B l r (endpointSub Γ false)).inv (pathLam z h₀ h₁)) σ =
    Term.map (pathReindexIso
      (reindex B (liftSub (interval (total (interval Γ))) (liftSub (interval Γ) σ)))
      (l.reindex (liftSub (interval Γ) σ)) (r.reindex (liftSub (interval Γ) σ))
      (endpointSub Δ false)).inv
      (pathLam (z.reindex (liftSub (interval Γ) σ))
        (congrArg (fun t => t.reindex σ) h₀) (congrArg (fun t => t.reindex σ) h₁)) := by
  apply Term.map_injective_of_iso (pathReindexIso _ _ _ (endpointSub Δ false))
  apply pathApp_injective
  have h := Term.map_iso_roundtrip (pathReindexIso B l r (endpointSub Γ false)).symm
    (pathLam z h₀ h₁)
  exact (congrArg (fun t => (pathApp t).reindex (liftSub (interval Γ) σ)) h).trans
    (congrArg pathApp (Term.map_iso_roundtrip
      (pathReindexIso
        (reindex B (liftSub (interval (total (interval Γ))) (liftSub (interval Γ) σ)))
        (l.reindex (liftSub (interval Γ) σ)) (r.reindex (liftSub (interval Γ) σ))
        (endpointSub Δ false)).symm
      (pathLam (z.reindex (liftSub (interval Γ) σ))
        (congrArg (fun t => t.reindex σ) h₀) (congrArg (fun t => t.reindex σ) h₁)))).symm

theorem squareTopOfSection_body_reindex {Δ : Context.{u}}
    (z : Term (reindex B (liftSub (interval (total (interval Γ))) (endpointSub Γ false))))
    (h₀ : z.reindex (endpointSub Γ false) = l.reindex (endpointSub Γ false))
    (h₁ : z.reindex (endpointSub Γ true) = r.reindex (endpointSub Γ false)) (σ : Δ ⟶ Γ) :
    pathApp (squareTopOfSection
      (F.reindex (liftSub (interval (total (interval Γ))) (liftSub (interval Γ) σ)))
      (hF.reindex _) (l.reindex (liftSub (interval Γ) σ)) (r.reindex (liftSub (interval Γ) σ))
      (z.reindex (liftSub (interval Γ) σ))
      (congrArg (fun t => t.reindex σ) h₀) (congrArg (fun t => t.reindex σ) h₁)) =
    (pathApp (squareTopOfSection F hF l r z h₀ h₁)).reindex (liftSub (interval Γ) σ) :=
  (congrArg (fun t => pathApp (squareTop
    (F.reindex (liftSub (interval (total (interval Γ))) (liftSub (interval Γ) σ)))
      (hF.reindex _) (l.reindex (liftSub (interval Γ) σ)) (r.reindex (liftSub (interval Γ) σ)) t))
    (squareInitialOfSection_reindex l r z h₀ h₁ σ).symm).trans
    (squareTop_body_reindex F hF l r _ σ)

private theorem squareTopOfSection_body_heq
    (z : Term (reindex B (liftSub (interval (total (interval Γ))) (endpointSub Γ false))))
    (h₀ : z.reindex (endpointSub Γ false) = l.reindex (endpointSub Γ false))
    (h₁ : z.reindex (endpointSub Γ true) = r.reindex (endpointSub Γ false))
    {B' : Family (total (interval (total (interval Γ))))}
    (F' : Filling B') (hF' : F'.Lawful)
    (l' : Term (reindex B' (endpointSub (total (interval Γ)) false)))
    (r' : Term (reindex B' (endpointSub (total (interval Γ)) true)))
    (z' : Term (reindex B' (liftSub (interval (total (interval Γ))) (endpointSub Γ false))))
    (h₀' : z'.reindex (endpointSub Γ false) = l'.reindex (endpointSub Γ false))
    (h₁' : z'.reindex (endpointSub Γ true) = r'.reindex (endpointSub Γ false))
    (eB : B = B') (eF : HEq F F') (el : HEq l l') (er : HEq r r') (ez : HEq z z') :
    HEq (pathApp (squareTopOfSection F hF l r z h₀ h₁))
      (pathApp (squareTopOfSection F' hF' l' r' z' h₀' h₁')) := by
  cases eB
  cases eq_of_heq eF
  cases eq_of_heq el
  cases eq_of_heq er
  cases eq_of_heq ez
  rfl

end SquareComparison
section Concatenation
variable {Γ : Context.{u}} {A : Family Γ} (F : Filling A) (hF : F.Lawful)
  (B : Family (total A)) (G : Filling B) (hG : G.Lawful)
  {a b c : Term A} (p : Term (homogeneousPath A a b)) (q : Term (homogeneousPath A b c))

noncomputable def squareMap : total (interval (total (interval Γ))) ⟶ total A :=
  pair (projection (interval (total (interval Γ))) ≫ projection (interval Γ))
    (NativeConcat.square F hF p q)

noncomputable abbrev squareFamily := reindex B (squareMap F hF p q)

theorem squareFamily_left :
    reindex (squareFamily F hF B p q) (endpointSub (total (interval Γ)) false) =
      reindex (fiber B a) (projection (interval Γ)) :=
  congrArg (fun t => reindex B (pair (projection (interval Γ)) t))
    (NativeConcat.square_left F hF p q)

theorem squareFamily_right :
    reindex (squareFamily F hF B p q) (endpointSub (total (interval Γ)) true) = line B q :=
  congrArg (fun t => reindex B (pair (projection (interval Γ)) t))
    (NativeConcat.square_right F hF p q)

theorem squareFamily_zero :
    reindex (squareFamily F hF B p q)
      (liftSub (interval (total (interval Γ))) (endpointSub Γ false)) = line B p :=
  congrArg (fun t => reindex B (pair (projection (interval Γ)) t))
    (NativeConcat.square_zero F hF p q)

theorem squareFamily_one :
    reindex (squareFamily F hF B p q)
      (liftSub (interval (total (interval Γ))) (endpointSub Γ true)) =
      line B (homogeneousConcat F hF p q) :=
  congrArg (fun t => reindex B (pair (projection (interval Γ)) t))
    (NativeConcat.square_one F hF p q)

private theorem convert_reindex_heq {Ξ Ω : Context.{u}} {C D : Family Ξ}
    (h : C = D) (t : Term C) (σ : Ω ⟶ Ξ) : HEq ((t.convert h).reindex σ) (t.reindex σ) := by
  cases h
  rfl

noncomputable def concatLeft (x : Term (fiber B a)) :=
  (x.reindex (projection (interval Γ))).convert (squareFamily_left F hF B p q).symm

noncomputable def concatRight (x : Term (fiber B a)) :=
  (alongSection B q G (Term.map (along B p G) x)).convert (squareFamily_right F hF B p q).symm

noncomputable def concatBottomSection (x : Term (fiber B a)) :=
  (alongSection B p G x).convert (squareFamily_zero F hF B p q).symm

include hG in
theorem concatBottom_zero (x : Term (fiber B a)) :
    (concatBottomSection F hF B G p q x).reindex (endpointSub Γ false) =
      (concatLeft F hF B p q x).reindex (endpointSub Γ false) := by
  apply eq_of_heq
  exact (convert_reindex_heq _ _ _).trans
    ((heq_of_eq (alongSection_zero B p G hG x)).trans
      ((Term.convert_heq _ _).trans
        (convert_reindex_heq (squareFamily_left F hF B p q).symm
          (x.reindex (projection (interval Γ))) (endpointSub Γ false)).symm))

include hG in
theorem concatBottom_one (x : Term (fiber B a)) :
    (concatBottomSection F hF B G p q x).reindex (endpointSub Γ true) =
      (concatRight F hF B G p q x).reindex (endpointSub Γ false) := by
  apply eq_of_heq
  exact (convert_reindex_heq _ _ _).trans
    ((Term.convert_heq (line_one B p) _).symm.trans
      ((heq_of_eq (alongSection_one B p G hG x)).trans
        ((Term.convert_heq _ _).symm.trans
          ((heq_of_eq (alongSection_zero B q G hG (Term.map (along B p G) x))).symm.trans
            (convert_reindex_heq _ _ _).symm))))

noncomputable def concatBottom (x : Term (fiber B a)) : Term (reindex
    (path (squareFamily F hF B p q) (concatLeft F hF B p q x) (concatRight F hF B G p q x))
    (endpointSub Γ false)) :=
  Term.map (pathReindexIso (squareFamily F hF B p q)
    (concatLeft F hF B p q x) (concatRight F hF B G p q x) (endpointSub Γ false)).inv
    (pathLam (concatBottomSection F hF B G p q x)
      (concatBottom_zero F hF B G hG p q x) (concatBottom_one F hF B G hG p q x))

noncomputable def concatTopSection (x : Term (fiber B a)) :
    Term (line B (homogeneousConcat F hF p q)) :=
  (pathApp (squareTop (G.reindex (squareMap F hF p q)) (hG.reindex _)
    (concatLeft F hF B p q x) (concatRight F hF B G p q x)
    (concatBottom F hF B G hG p q x))).convert (squareFamily_one F hF B p q)

include hG in
theorem concatTop_zero (x : Term (fiber B a)) :
    (concatTopSection F hF B G hG p q x).reindex (endpointSub Γ false) =
      x.convert (line_zero B (homogeneousConcat F hF p q)).symm := by
  apply eq_of_heq
  exact (convert_reindex_heq _ _ _).trans
    ((heq_of_eq (pathApp_zero (squareTop (G.reindex (squareMap F hF p q)) (hG.reindex _)
      (concatLeft F hF B p q x) (concatRight F hF B G p q x)
      (concatBottom F hF B G hG p q x)))).trans
      ((convert_reindex_heq (squareFamily_left F hF B p q).symm
        (x.reindex (projection (interval Γ))) (endpointSub Γ true)).trans
        (Term.convert_heq _ x).symm))

include hG in
theorem concatTop_one (x : Term (fiber B a)) :
    ((concatTopSection F hF B G hG p q x).reindex (endpointSub Γ true)).convert
      (line_one B (homogeneousConcat F hF p q)) =
      Term.map (along B q G) (Term.map (along B p G) x) := by
  apply eq_of_heq
  exact (Term.convert_heq _ _).trans ((convert_reindex_heq _ _ _).trans
    ((heq_of_eq (pathApp_one (squareTop (G.reindex (squareMap F hF p q)) (hG.reindex _)
      (concatLeft F hF B p q x) (concatRight F hF B G p q x)
      (concatBottom F hF B G hG p q x)))).trans
      ((convert_reindex_heq (squareFamily_right F hF B p q).symm
        (alongSection B q G (Term.map (along B p G) x)) (endpointSub Γ true)).trans
        ((Term.convert_heq (line_one B q) _).symm.trans
          (heq_of_eq (alongSection_one B q G hG (Term.map (along B p G) x)))))))

/-- Transport along the constructed native concatenation is homotopic to
sequential transport, for an arbitrary lawful dependent family. -/
noncomputable def concatComparison (x : Term (fiber B a)) :
    Term (homogeneousPath (fiber B c)
      (Term.map (along B (homogeneousConcat F hF p q) G) x)
      (Term.map (along B q G) (Term.map (along B p G) x))) :=
  alongComparison B (homogeneousConcat F hF p q) G hG x
    (Term.map (along B q G) (Term.map (along B p G) x))
    (concatTopSection F hF B G hG p q x)
    (concatTop_zero F hF B G hG p q x) (concatTop_one F hF B G hG p q x)

section Substitution
variable {Δ : Context.{u}} (σ : Δ ⟶ Γ)

theorem squareMap_reindex :
    liftSub (interval (total (interval Γ))) (liftSub (interval Γ) σ) ≫ squareMap F hF p q =
      squareMap (F.reindex σ) (hF.reindex _) (homogeneousReindex p σ) (homogeneousReindex q σ) ≫
        liftSub A σ :=
  congrArg (fun t => pair (projection (interval (total (interval Δ))) ≫
    projection (interval Δ) ≫ σ) t)
    (congrArg pathApp (NativeConcat.squarePath_reindex F hF p q σ))

private theorem filling_reindex_heq {Ξ Ω : Context.{u}} {C : Family Ξ}
    (H : Filling C) {s t : Ω ⟶ Ξ} (h : s = t) : HEq (H.reindex s) (H.reindex t) := by
  cases h
  rfl

private theorem concatLeft_reindex (x : Term (fiber B a)) : HEq
    (concatLeft (F.reindex σ) (hF.reindex _) (reindex B (liftSub A σ))
      (homogeneousReindex p σ) (homogeneousReindex q σ) (x.reindex σ))
    ((concatLeft F hF B p q x).reindex (liftSub (interval Γ) σ)) :=
  (Term.convert_heq _ _).trans
    (convert_reindex_heq (squareFamily_left F hF B p q).symm
      (x.reindex (projection (interval Γ))) (liftSub (interval Γ) σ)).symm

include hG in
private theorem concatRight_reindex (x : Term (fiber B a)) : HEq
    (concatRight (F.reindex σ) (hF.reindex _) (reindex B (liftSub A σ)) (G.reindex (liftSub A σ))
      (homogeneousReindex p σ) (homogeneousReindex q σ) (x.reindex σ))
    ((concatRight F hF B G p q x).reindex (liftSub (interval Γ) σ)) := by
  have ha := congrArg (fun f => Term.map f (x.reindex σ)) (along_reindex B p G hG σ)
  have hs := alongSection_reindex B q G hG (Term.map (along B p G) x) σ
  have ht := congrArg (alongSection (reindex B (liftSub A σ)) (homogeneousReindex q σ)
    (G.reindex (liftSub A σ))) ha.symm
  exact (Term.convert_heq _ _).trans ((heq_of_eq (ht.trans hs)).trans
    (convert_reindex_heq _ _ _).symm)

include hG in
private theorem concatBottomSection_reindex (x : Term (fiber B a)) : HEq
    (concatBottomSection (F.reindex σ) (hF.reindex _) (reindex B (liftSub A σ))
      (G.reindex (liftSub A σ)) (homogeneousReindex p σ) (homogeneousReindex q σ) (x.reindex σ))
    ((concatBottomSection F hF B G p q x).reindex (liftSub (interval Γ) σ)) :=
  (Term.convert_heq _ _).trans ((heq_of_eq (alongSection_reindex B p G hG x σ)).trans
    (convert_reindex_heq _ _ _).symm)

/-- The selected dependent top section is retained, including the chosen base
square and dependent square filling. Heterogeneous equality only accounts for
the exact path-concatenation substitution equation. -/
theorem concatTopSection_reindex (x : Term (fiber B a)) : HEq
    (concatTopSection (F.reindex σ) (hF.reindex _) (reindex B (liftSub A σ))
      (G.reindex (liftSub A σ)) (hG.reindex _) (homogeneousReindex p σ)
      (homogeneousReindex q σ) (x.reindex σ))
    ((concatTopSection F hF B G hG p q x).reindex (liftSub (interval Γ) σ)) := by
  let L := liftSub (interval Γ) σ
  let LL := liftSub (interval (total (interval Γ))) L
  let S := squareMap F hF p q
  let S' := squareMap (F.reindex σ) (hF.reindex _) (homogeneousReindex p σ) (homogeneousReindex q σ)
  let l := concatLeft F hF B p q x
  let r := concatRight F hF B G p q x
  let z := concatBottomSection F hF B G p q x
  let l' := concatLeft (F.reindex σ) (hF.reindex _) (reindex B (liftSub A σ))
    (homogeneousReindex p σ) (homogeneousReindex q σ) (x.reindex σ)
  let r' := concatRight (F.reindex σ) (hF.reindex _) (reindex B (liftSub A σ))
    (G.reindex (liftSub A σ)) (homogeneousReindex p σ) (homogeneousReindex q σ) (x.reindex σ)
  let z' := concatBottomSection (F.reindex σ) (hF.reindex _) (reindex B (liftSub A σ))
    (G.reindex (liftSub A σ)) (homogeneousReindex p σ) (homogeneousReindex q σ) (x.reindex σ)
  have h₀ := concatBottom_zero F hF B G hG p q x
  have h₁ := concatBottom_one F hF B G hG p q x
  have h₀' := concatBottom_zero (F.reindex σ) (hF.reindex _) (reindex B (liftSub A σ))
    (G.reindex (liftSub A σ)) (hG.reindex _) (homogeneousReindex p σ) (homogeneousReindex q σ) (x.reindex σ)
  have h₁' := concatBottom_one (F.reindex σ) (hF.reindex _) (reindex B (liftSub A σ))
    (G.reindex (liftSub A σ)) (hG.reindex _) (homogeneousReindex p σ) (homogeneousReindex q σ) (x.reindex σ)
  have hs := squareMap_reindex F hF p q σ
  have hn := squareTopOfSection_body_reindex (G.reindex S) (hG.reindex _) l r z h₀ h₁ σ
  have hc := squareTopOfSection_body_heq
    ((G.reindex (liftSub A σ)).reindex S') ((hG.reindex _).reindex _) l' r' z' h₀' h₁'
    ((G.reindex S).reindex LL) ((hG.reindex _).reindex _)
    (l.reindex L) (r.reindex L) (z.reindex L)
    (congrArg (fun t => t.reindex σ) h₀) (congrArg (fun t => t.reindex σ) h₁)
    (congrArg (fun t => reindex B t) hs.symm) (filling_reindex_heq G hs.symm)
    (concatLeft_reindex F hF B p q σ x) (concatRight_reindex F hF B G hG p q σ x)
    (concatBottomSection_reindex F hF B G hG p q σ x)
  exact (Term.convert_heq _ _).trans (hc.trans
    ((heq_of_eq hn).trans (convert_reindex_heq _ _ _).symm))

/-- Context substitution preserves the chosen native concatenation comparison. -/
theorem concatComparison_body_reindex (x : Term (fiber B a)) :
    pathApp (concatComparison (F.reindex σ) (hF.reindex _) (reindex B (liftSub A σ))
      (G.reindex (liftSub A σ)) (hG.reindex _) (homogeneousReindex p σ)
      (homogeneousReindex q σ) (x.reindex σ)) =
    (pathApp (concatComparison F hF B G hG p q x)).reindex (liftSub (interval Γ) σ) :=
  alongComparison_body_natural B (homogeneousConcat F hF p q) G hG x
    (Term.map (along B q G) (Term.map (along B p G) x)) (concatTopSection F hF B G hG p q x)
    (concatTop_zero F hF B G hG p q x) (concatTop_one F hF B G hG p q x) σ
    (homogeneousConcat (F.reindex σ) (hF.reindex _) (homogeneousReindex p σ) (homogeneousReindex q σ))
    (homogeneousConcat_reindex F hF p q σ).symm _ _ _
    (concatTopSection_reindex F hF B G hG p q σ x)
    (concatTop_zero (F.reindex σ) (hF.reindex _) (reindex B (liftSub A σ)) (G.reindex (liftSub A σ))
      (hG.reindex _) (homogeneousReindex p σ) (homogeneousReindex q σ) (x.reindex σ))
    (concatTop_one (F.reindex σ) (hF.reindex _) (reindex B (liftSub A σ)) (G.reindex (liftSub A σ))
      (hG.reindex _) (homogeneousReindex p σ) (homogeneousReindex q σ) (x.reindex σ))

end Substitution
end Concatenation
end SquareKit.Cubical.Presheaf.NativeTransportComposition
