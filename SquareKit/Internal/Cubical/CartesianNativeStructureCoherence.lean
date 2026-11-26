import SquareKit.Internal.Cubical.CartesianNativeStructureUaComparison
import SquareKit.Internal.Cubical.CartesianNativeStructureRecovery
import SquareKit.Internal.Cubical.CartesianEquivalenceComposition
import SquareKit.Internal.Cubical.CartesianTransportConcatenation

/-! Independently supplied equivalences of pointed endomorphisms. Composition
and inversion use native map homotopies before comparison with structure paths. -/
set_option autoImplicit false
set_option warningAsError true
namespace SquareKit.Cubical.Cartesian.StructureIdentity.Coherence
open CategoryTheory SquareKit.StructureIdentity Glue
open Native
universe u
variable {Γ : Context.{u+1}}

abbrev MapPath {A B : Family Γ} (f g : A ⟶ B) :=
  Term (homogeneousPath (EquivalenceFamilies.maps A B)
    (EquivalenceFamilies.encodeMap f) (EquivalenceFamilies.encodeMap g))

noncomputable def mapsFilling {A B : Family Γ}
    (FA : Filling A) (hFA : FA.Lawful) (FB : Filling B) : Filling (EquivalenceFamilies.maps A B) :=
  piFilling FA hFA (FB.reindex (projection A))
theorem mapsFilling_lawful {A B : Family Γ}
    (FA : Filling A) (hFA : FA.Lawful) (FB : Filling B) (hFB : FB.Lawful) :
    (mapsFilling FA hFA FB).Lawful := piFilling_lawful FA hFA _ (hFB.reindex _)

namespace MapPath
variable {A B C D : Family Γ} {f g : A ⟶ B}

def whisker (p : MapPath f g) (l : C ⟶ A) (r : B ⟶ D) :
    MapPath (l ≫ f ≫ r) (l ≫ g ≫ r) :=
  homogeneousPathMap (functionMap l r) p

noncomputable def trans {h : A ⟶ B} (p : MapPath f g) (q : MapPath g h)
    (FA : Filling A) (hFA : FA.Lawful) (FB : Filling B) (hFB : FB.Lawful) :
    MapPath f h :=
  homogeneousConcat (mapsFilling FA hFA FB)
    (mapsFilling_lawful FA hFA FB hFB) p q

def pointwise (p : MapPath f g) :
    Term (homogeneousPath (reindex B (projection A))
      (Term.map (Functor.whiskerLeft (projection A).mapElements f) (generic A))
      (Term.map (Functor.whiskerLeft (projection A).mapElements g) (generic A))) :=
  app (Term.map (FunctionPaths.decomposition (EquivalenceFamilies.encodeMap f)
    (EquivalenceFamilies.encodeMap g)).hom p)

def evaluate (p : MapPath f g) (a : Term A) :
    Term (homogeneousPath B (Term.map f a) (Term.map g a)) := by
  let q := Term.reindex (app (Term.map (FunctionPaths.decomposition
    (EquivalenceFamilies.encodeMap f) (EquivalenceFamilies.encodeMap g)).hom p))
      (pair (𝟙 Γ) a)
  exact Term.map (EquivalenceFamilies.homogeneousReindexIso _ _ _ (pair (𝟙 Γ) a)).hom q
noncomputable def horizontal {C : Family Γ} {f' : A ⟶ B} {k k' : B ⟶ C}
    (p : MapPath f f') (q : MapPath k k')
    (FA : Filling A) (hFA : FA.Lawful) (FC : Filling C) (hFC : FC.Lawful) :
    MapPath (f ≫ k) (f' ≫ k') :=
  MapPath.trans (MapPath.whisker p (𝟙 A) k) (MapPath.whisker q f' (𝟙 C)) FA hFA FC hFC

def precompose {C : Family Γ} (p : MapPath f g) (l : C ⟶ A) :
    MapPath (l ≫ f) (l ≫ g) := MapPath.whisker p l (𝟙 B)

end MapPath

abbrev description : Description.{u} := .product .carrier (.function .carrier .carrier)

structure PointedEndomorphism (A : Family Γ) where
  point : Term A
  step : A ⟶ A

def PointedEndomorphism.fields {A : Family Γ} (s : PointedEndomorphism A) :
    Term (family description A) :=
  sigmaIntro s.point (EquivalenceFamilies.encodeMap s.step)

/-- The entire selected contractible-fiber witness is an input, alongside the
point path and the homotopy of complete endomorphisms. -/
structure Equivalence {A B : Family Γ} (s : PointedEndomorphism A) (t : PointedEndomorphism B) where
  map : A ⟶ B
  witness : HomotopyEquivalence map
  point : Term (homogeneousPath B (Term.map map s.point) t.point)
  step : MapPath (s.step ≫ map) (map ≫ t.step)


namespace Selected
variable {A B : Family Γ} {f : A ⟶ B}
def right (E : HomotopyEquivalence f) :
    Term (homogeneousPath (reindex B (projection B))
      (Term.map (Functor.whiskerLeft (projection B).mapElements f)
        (Term.map (Functor.whiskerLeft (projection B).mapElements E.selectedInverse) (generic B)))
      (generic B)) := genericFiberPath f (𝟙 (total B)) E.fibers.center

def left (E : HomotopyEquivalence f) :
    Term (homogeneousPath (reindex A (projection A))
      (Term.map (Functor.whiskerLeft (projection A).mapElements E.selectedInverse)
        (Term.map (Functor.whiskerLeft (projection A).mapElements f) (generic A)))
      (generic A)) := by
  let τ := pair (projection A) (Term.map (Functor.whiskerLeft (projection A).mapElements f) (generic A))
  let z := genericFiberIntro f τ (generic A)
    (homogeneousRefl (Term.map (Functor.whiskerLeft (projection A).mapElements f) (generic A)))
  exact homogeneousPathMap
    (PropositionExtension.first
      (reindex (genericFiberPathFamily f) (liftSub (reindex A (projection B)) τ)))
    ((E.fibers.reindex τ).pathTo z)
def rightComparison (E : HomotopyEquivalence f) (g : B ⟶ A)
    (H : Term (homogeneousPath (reindex B (projection B))
      (Term.map (Functor.whiskerLeft (projection B).mapElements (g ≫ f)) (generic B))
      (generic B))) :
    Term (homogeneousPath (reindex A (projection B))
      (Term.map (Functor.whiskerLeft (projection B).mapElements E.selectedInverse) (generic B))
      (Term.map (Functor.whiskerLeft (projection B).mapElements g) (generic B))) :=
  homogeneousPathMap (PropositionExtension.first (genericFiberPathFamily f))
    (E.fibers.pathTo (genericFiberIntro f (𝟙 (total B))
      (Term.map (Functor.whiskerLeft (projection B).mapElements g) (generic B)) H))

theorem inverse_ofIso (e : A ≅ B) (F : Filling B) (hF : F.Lawful) :
    (HomotopyEquivalence.ofIso e F hF).selectedInverse = e.inv := by
  ext x a
  rfl

end Selected

namespace Equivalence
variable {A B C : Family Γ} {s : PointedEndomorphism A}
  {t : PointedEndomorphism B} {v : PointedEndomorphism C}

/-- A separately supplied composite witness is retained without replacing its
inverse or contractions with a strict carrier isomorphism. -/
noncomputable def compWith (e : Equivalence s t) (d : Equivalence t v)
    (w : HomotopyEquivalence (e.map ≫ d.map))
    (FA : Filling A) (hFA : FA.Lawful) (FC : Filling C) (hFC : FC.Lawful) :
    Equivalence s v where
  map := e.map ≫ d.map
  witness := w
  point := homogeneousConcat FC hFC (homogeneousPathMap d.map e.point) d.point
  step := MapPath.trans (MapPath.whisker e.step (𝟙 A) d.map)
    (MapPath.whisker d.step e.map (𝟙 C)) FA hFA FC hFC

noncomputable def comp (e : Equivalence s t) (d : Equivalence t v)
    (FA : Filling A) (hFA : FA.Lawful) (FB : Filling B) (hFB : FB.Lawful)
    (FC : Filling C) (hFC : FC.Lawful) : Equivalence s v :=
  e.compWith d (e.witness.comp d.witness FA hFA FB hFB FC hFC) FA hFA FC hFC

noncomputable def inverseWith (e : Equivalence s t)
    (w : HomotopyEquivalence e.witness.selectedInverse)
    (FA : Filling A) (hFA : FA.Lawful) (FB : Filling B) (hFB : FB.Lawful) :
    Equivalence t s := by
  let g := e.witness.selectedInverse
  let L : MapPath (e.map ≫ g) (𝟙 A) :=
    EquivalencePaths.mapPath _ _ (Selected.left e.witness)
  let R : MapPath (g ≫ e.map) (𝟙 B) :=
    EquivalencePaths.mapPath _ _ (Selected.right e.witness)
  let p := MapPath.trans
    (homogeneousReverse (mapsFilling FB hFB FA)
      (mapsFilling_lawful FB hFB FA hFA) (MapPath.whisker L (g ≫ s.step) (𝟙 A)))
    (MapPath.whisker e.step g g) FB hFB FA hFA
  let q := MapPath.trans p (MapPath.whisker R (𝟙 B) (t.step ≫ g)) FB hFB FA hFA
  exact {
    map := g
    witness := w
    point := homogeneousConcat FA hFA
      (homogeneousReverse FA hFA (homogeneousPathMap g e.point)) (MapPath.evaluate L s.point)
    step := homogeneousReverse (mapsFilling FB hFB FA)
      (mapsFilling_lawful FB hFB FA hFA) q }

/-- The independent point and function homotopies inhabit the existing
recursive preservation interface, with the original witness-selected inverse. -/
noncomputable def preservation (e : Equivalence s t) :
    Term (preserves description e.map e.witness.selectedInverse s.fields t.fields) :=
  sigmaIntro e.point (Term.map (FunctionPaths.decomposition
    (EquivalenceFamilies.encodeMap (s.step ≫ e.map))
    (EquivalenceFamilies.encodeMap (e.map ≫ t.step))).hom e.step)

noncomputable def native (e : Equivalence s t) :
    Term (Native.equivalences description s.fields t.fields) :=
  sigmaIntro (EquivalenceFamilies.equivSections A B ⟨e.map, e.witness⟩)
    (Term.map (suppliedEquivalenceFiberIso description e.map e.witness s.fields t.fields).inv
      e.preservation)

example (e : Equivalence s t) : sigmaFst e.native =
    EquivalenceFamilies.equivSections A B ⟨e.map, e.witness⟩ := rfl

end Equivalence
/-- Reflect a path through a genuine native equivalence, using the inverse
selected from that same witness and retaining both endpoint homotopies. -/
noncomputable def reflectPath {A B : Family Γ} (f : A ⟶ B) (E : HomotopyEquivalence f)
    (FA : Filling A) (hFA : FA.Lawful) (x y : Term A)
    (p : Term (homogeneousPath B (Term.map f x) (Term.map f y))) :
    Term (homogeneousPath A x y) := by
  let L : MapPath (f ≫ E.selectedInverse) (𝟙 A) :=
    EquivalencePaths.mapPath _ _ (Selected.left E)
  exact homogeneousConcat FA hFA
    (homogeneousReverse FA hFA (MapPath.evaluate L x))
    (homogeneousConcat FA hFA (homogeneousPathMap E.selectedInverse p) (MapPath.evaluate L y))

section WholeComparison
open StructuredIdentity.UaComparison SmallUniverse
variable (D : Description.{u}) (a b : Γ ⟶ smallFamilyCodes.{u})
  (s : Term (family D (SmallUniverse.liftedDecode a)))
  (t : Term (family D (SmallUniverse.liftedDecode b)))
  (sB : Term (HomotopyLevels.isSet (SmallUniverse.liftedDecode b)))

/-- A homotopy of complete carrier equivalences lifts through proposition-valued
preservation. Native sethood is explicit; no discrete presentation is required. -/
noncomputable def equivalencePath (q r : Term (Native.equivalences D s t))
    (h : Term (homogeneousPath
      (EquivalenceFamilies.equiv (SmallUniverse.liftedDecode a) (SmallUniverse.liftedDecode b))
      (sigmaFst q) (sigmaFst r))) :
    Term (homogeneousPath (Native.equivalences D s t) q r) := by
  let FA := NativeDecode.filling a
  let FB := NativeDecode.filling b
  let hFA := NativeDecode.filling_lawful a
  let hFB := NativeDecode.filling_lawful b
  let P := equivalenceFieldsFilling D s t FA hFA FB hFB
  exact Term.map (PropositionExtension.pathInverse (equivalenceFields D s t) q r
    (equivalenceFieldsIsProp D s t sB FA hFA FB hFB)
    (EquivalenceFamilies.equivFilling FA hFA FB hFB)
    (EquivalenceFamilies.equivFilling_lawful FA hFA FB hFB) P.1 P.2) h

noncomputable def uaEquivalencePath (q r : Term (Native.equivalences D s t))
    (h : Term (homogeneousPath (SmallUniverse.NativeUnivalence.paths a b)
      (Term.map (SmallUniverse.NativeUnivalence.equivToPath a b) (sigmaFst q))
      (Term.map (SmallUniverse.NativeUnivalence.equivToPath a b) (sigmaFst r)))) :
    Term (homogeneousPath (Native.equivalences D s t) q r) := by
  let F := EquivalenceFamilies.equivFilling (NativeDecode.filling a) (NativeDecode.filling_lawful a)
    (NativeDecode.filling b) (NativeDecode.filling_lawful b)
  let hF := EquivalenceFamilies.equivFilling_lawful (NativeDecode.filling a) (NativeDecode.filling_lawful a)
    (NativeDecode.filling b) (NativeDecode.filling_lawful b)
  exact equivalencePath D a b s t sB q r
    (reflectPath (SmallUniverse.NativeUnivalence.equivToPath a b)
      (SmallUniverse.NativeUnivalence.uaEquivalence a b) F hF (sigmaFst q) (sigmaFst r) h)
def carrierProjection :=
  HomotopyLevels.pathMap (SIP.Exchange.first (SIP.objectFields D))
    (objectOf D a s) (objectOf D b t)

theorem carrier_explicit (q : Term (Native.equivalences D s t)) :
    Term.map (carrierProjection D a b s t) (Term.map (explicitMap D a s b t) q) =
      Term.map (SmallUniverse.NativeUnivalence.equivToPath a b) (sigmaFst q) := by
  apply Term.ext
  intro x
  exact explicitMap_carrier D a s b t x (q.val x)

set_option maxHeartbeats 400000 in
/-- Carrier-path comparison determines a whole structure-path comparison when
the target is a native set. The proof retains the supplied whole paths through
the selected correspondence's recovery homotopies. -/
noncomputable def wholeComparison
    (p q : Term (homogeneousPath (objects D Γ) (objectOf D a s) (objectOf D b t)))
    (h : Term (homogeneousPath (SmallUniverse.NativeUnivalence.paths a b)
      (Term.map (carrierProjection D a b s t) p)
      (Term.map (carrierProjection D a b s t) q))) :
    Term (homogeneousPath
      (homogeneousPath (objects D Γ) (objectOf D a s) (objectOf D b t)) p q) := by
  let ep := Term.map (explicitInverse D a s b t) p
  let eq := Term.map (explicitInverse D a s b t) q
  let rp := explicitRightInverseAt D a s b t p
  let rq := explicitRightInverseAt D a s b t q
  let cp := homogeneousPathMap (carrierProjection D a b s t) rp
  let cq := homogeneousPathMap (carrierProjection D a b s t) rq
  let cp' := pathLam (pathApp cp)
    ((pathApp_zero cp).trans (carrier_explicit D a b s t ep)) (pathApp_one cp)
  let cq' := pathLam (pathApp cq)
    ((pathApp_zero cq).trans (carrier_explicit D a b s t eq)) (pathApp_one cq)
  let H := homogeneousConcat (SmallUniverse.NativeUnivalence.pathsFilling a b)
    (SmallUniverse.NativeUnivalence.pathsFilling_lawful a b) cp'
    (homogeneousConcat (SmallUniverse.NativeUnivalence.pathsFilling a b)
      (SmallUniverse.NativeUnivalence.pathsFilling_lawful a b) h (homogeneousReverse (SmallUniverse.NativeUnivalence.pathsFilling a b)
        (SmallUniverse.NativeUnivalence.pathsFilling_lawful a b) cq'))
  let K := homogeneousPathMap (explicitMap D a s b t)
    (uaEquivalencePath D a b s t sB ep eq H)
  let O := objectsFilling D Γ
  let F := pathFilling (O.1.reindex (projection (interval Γ))) (O.2.reindex _)
    (objectOf D a s) (objectOf D b t)
  let hF := pathFilling_lawful (O.1.reindex (projection (interval Γ))) (O.2.reindex _)
    (objectOf D a s) (objectOf D b t)
  exact homogeneousConcat F hF (homogeneousReverse F hF rp) (homogeneousConcat F hF K rq)
end WholeComparison

end SquareKit.Cubical.Cartesian.StructureIdentity.Coherence

namespace SquareKit.Cubical.Cartesian.StructureIdentity.Coherence.SigmaFillingPaths
open CategoryTheory
universe u
variable {Γ : Context.{u}} {A : Family Γ} {B : Family (total A)}
  (F : Filling A) (hF : F.Lawful) (G : Filling B) (hG : G.Lawful)

private abbrev first := PropositionExtension.first B
private abbrev lineMap := Functor.whiskerLeft (projection (interval Γ)).mapElements (first (B := B))

theorem square_first (ε : Bool) (l r base : Term (intervalCoefficient (sigma A B)))
    (h₀ : Term.reindex base (endpointSub Γ false) = Term.reindex l (endpointSub Γ ε))
    (h₁ : Term.reindex base (endpointSub Γ true) = Term.reindex r (endpointSub Γ ε)) :
    Term.map (Functor.whiskerLeft (NativeSquare.squareBase Γ).mapElements (first (B := B)))
      (NativeSquare.fill (sigmaFilling F hF G) ε l r base h₀ h₁) =
    NativeSquare.fill F ε (Term.map lineMap l) (Term.map lineMap r) (Term.map lineMap base)
      (congrArg (Term.map (first (B := B))) h₀) (congrArg (Term.map (first (B := B))) h₁) := by
  have hb : OpenBox.sigmaFst (B := reindex B (liftSub A (NativeSquare.squareBase Γ)))
      (NativeSquare.box ε l r base h₀ h₁) =
      NativeSquare.box ε (Term.map lineMap l) (Term.map lineMap r) (Term.map lineMap base)
        (congrArg (Term.map (first (B := B))) h₀) (congrArg (Term.map (first (B := B))) h₁) := by
    apply OpenBox.ext
    · apply PartialSection.ext
      intro a ha
      dsimp [OpenBox.sigmaFst, PartialSection.sigmaFst, NativeSquare.box, NativeSquare.tube]
      split <;> rfl
    · rfl
  exact congrArg (F.fill (NativeSquare.squareBase Γ) (NativeSquare.sides Γ)
    (endpoint (total (interval Γ)) ε)) hb

theorem concat_first {x y z : Term (sigma A B)}
    (p : Term (homogeneousPath (sigma A B) x y))
    (q : Term (homogeneousPath (sigma A B) y z)) :
    homogeneousPathMap (first (B := B))
      (homogeneousConcat (sigmaFilling F hF G) (sigmaFilling_lawful F hF G hG) p q) =
    homogeneousConcat F hF (homogeneousPathMap (first (B := B)) p)
      (homogeneousPathMap (first (B := B)) q) := by
  apply pathApp_injective
  have h := congrArg (fun t => NativeSquare.slice t true)
    (square_first F hF G false (Term.reindex x (projection (interval Γ)))
      (pathApp q) (pathApp p) (pathApp_zero p) ((pathApp_one p).trans (pathApp_zero q).symm))
  exact h
theorem reverse_first {x y : Term (sigma A B)}
    (p : Term (homogeneousPath (sigma A B) x y)) :
    homogeneousPathMap (first (B := B))
      (homogeneousReverse (sigmaFilling F hF G) (sigmaFilling_lawful F hF G hG) p) =
    homogeneousReverse F hF (homogeneousPathMap (first (B := B)) p) := by
  apply pathApp_injective
  exact congrArg (fun t => NativeSquare.slice t false)
    (square_first F hF G true (Term.reindex y (projection (interval Γ)))
      (pathApp p) (Term.reindex y (projection (interval Γ))) rfl (pathApp_one p).symm)
end SquareKit.Cubical.Cartesian.StructureIdentity.Coherence.SigmaFillingPaths

namespace SquareKit.Cubical.Cartesian.StructureIdentity.Coherence
open CategoryTheory SquareKit.StructureIdentity Native SmallUniverse StructuredIdentity.UaComparison
universe u
variable {Γ : Context.{u+1}}
theorem reverse_reindex {Ξ Ψ : Context.{u}} {A : Family Ξ}
    (F : Filling A) (hF : F.Lawful) {a b : Term A}
    (p : Term (homogeneousPath A a b)) (σ : Ψ ⟶ Ξ) :
    homogeneousReindex (homogeneousReverse F hF p) σ =
      homogeneousReverse (F.reindex σ) (hF.reindex σ) (homogeneousReindex p σ) := by
  apply pathApp_injective
  exact (congrArg (fun t => Term.reindex t (endpointSub (total (interval Ψ)) false))
    (NativeSquare.fill_reindex F hF true (Term.reindex b (projection (interval Ξ)))
      (pathApp p) (Term.reindex b (projection (interval Ξ))) rfl (pathApp_one p).symm σ)).symm

namespace Coded
noncomputable def reverseTransportComparison {a b : Γ ⟶ smallFamilyCodes.{u}}
    (F : Filling (SmallUniverse.family Γ)) (hF : F.Lawful)
    (p : Term (NativeUnivalence.paths a b)) (x : Term (liftedDecode b)) :
    Term (homogeneousPath (liftedDecode b)
      (Term.map (NativeUnivalence.pathToMap p)
        (Term.map (NativeUnivalence.pathToMap (homogeneousReverse
          F hF p)) x)) x) := by
  let l := Term.reindex (SmallUniverse.term b) (projection (interval Γ))
  let z := NativeSquare.fill F true l (pathApp p) l rfl (pathApp_one p).symm
  let S := SmallUniverse.code z
  let r := homogeneousReverse F hF p
  have hb : endpointSub (total (interval Γ)) false ≫ S = SmallUniverse.codeOfPath r := rfl
  have hl : intervalSub (endpointSub Γ false) ≫ S = projection (interval Γ) ≫ b :=
    congrArg SmallUniverse.code (NativeSquare.fill_left F hF true l (pathApp p) l rfl (pathApp_one p).symm)
  have hr : intervalSub (endpointSub Γ true) ≫ S = SmallUniverse.codeOfPath p :=
    congrArg SmallUniverse.code (NativeSquare.fill_right F hF true l (pathApp p) l rfl (pathApp_one p).symm)
  have ht : SmallUniverse.CodeTransportSquare.top S =
      SmallUniverse.codeOfPath (homogeneousRefl (SmallUniverse.term b)) :=
    congrArg SmallUniverse.code (NativeSquare.fill_source F hF true l (pathApp p) l rfl (pathApp_one p).symm)
  let H := SmallUniverse.CodeTransportSquare.comparisonPaths S r p
    (homogeneousRefl (SmallUniverse.term b)) hb hl hr ht x
  let G := NativeDecode.filling b
  let hG := NativeDecode.filling_lawful b
  exact homogeneousConcat G hG (homogeneousReverse G hG H)
    (homogeneousReverse G hG (NativeUnivalence.reflexiveTransportPath b x))

noncomputable def uaMapPath (a b : Γ ⟶ smallFamilyCodes.{u})
    (f : liftedDecode a ⟶ liftedDecode b) (E : HomotopyEquivalence f) :
    MapPath f (NativeUnivalence.pathToMap (NativeUnivalence.ua a b f E)) :=
  EquivalencePaths.mapPath _ _ (NativeUnivalence.uaMapHomotopy a b f E)

noncomputable def sequentialMapPath (a b c : Γ ⟶ smallFamilyCodes.{u})
    (f : liftedDecode a ⟶ liftedDecode b) (E : HomotopyEquivalence f)
    (g : liftedDecode b ⟶ liftedDecode c) (D : HomotopyEquivalence g) :
    MapPath (f ≫ g) (NativeUnivalence.pathToMap (NativeUnivalence.ua a b f E) ≫
      NativeUnivalence.pathToMap (NativeUnivalence.ua b c g D)) :=
  MapPath.horizontal (uaMapPath a b f E) (uaMapPath b c g D)
    (NativeDecode.filling a) (NativeDecode.filling_lawful a)
    (NativeDecode.filling c) (NativeDecode.filling_lawful c)

noncomputable def concatMapPath (a b c : Γ ⟶ smallFamilyCodes.{u})
    (p : Term (NativeUnivalence.paths a b)) (q : Term (NativeUnivalence.paths b c)) :
    MapPath (NativeUnivalence.pathToMap (homogeneousConcat
      (SmallUniverse.filling Γ) (SmallUniverse.filling_lawful Γ) p q))
      (NativeUnivalence.pathToMap p ≫ NativeUnivalence.pathToMap q) :=
  EquivalencePaths.mapPath _ _ (NativeUnivalence.concatMapHomotopy
    (SmallUniverse.filling Γ) (SmallUniverse.filling_lawful Γ) p q)

noncomputable def compositeMapPath (a b c : Γ ⟶ smallFamilyCodes.{u})
    (f : liftedDecode a ⟶ liftedDecode b) (E : HomotopyEquivalence f)
    (g : liftedDecode b ⟶ liftedDecode c) (D : HomotopyEquivalence g) :
    MapPath (f ≫ g) (NativeUnivalence.pathToMap (homogeneousConcat
      (SmallUniverse.filling Γ) (SmallUniverse.filling_lawful Γ)
      (NativeUnivalence.ua a b f E) (NativeUnivalence.ua b c g D))) :=
  MapPath.trans (sequentialMapPath a b c f E g D)
    (homogeneousReverse (mapsFilling (NativeDecode.filling a) (NativeDecode.filling_lawful a)
      (NativeDecode.filling c))
      (mapsFilling_lawful (NativeDecode.filling a) (NativeDecode.filling_lawful a)
        (NativeDecode.filling c) (NativeDecode.filling_lawful c))
      (concatMapPath a b c (NativeUnivalence.ua a b f E) (NativeUnivalence.ua b c g D)))
    (NativeDecode.filling a) (NativeDecode.filling_lawful a)
    (NativeDecode.filling c) (NativeDecode.filling_lawful c)

noncomputable def uaCompositeOfWitness (a b c : Γ ⟶ smallFamilyCodes.{u})
    (f : liftedDecode a ⟶ liftedDecode b) (E : HomotopyEquivalence f)
    (g : liftedDecode b ⟶ liftedDecode c) (D : HomotopyEquivalence g)
    (W : HomotopyEquivalence (f ≫ g)) :
    Term (homogeneousPath (NativeUnivalence.paths a c) (NativeUnivalence.ua a c (f ≫ g) W)
      (homogeneousConcat (SmallUniverse.filling Γ) (SmallUniverse.filling_lawful Γ)
        (NativeUnivalence.ua a b f E) (NativeUnivalence.ua b c g D))) :=
  NativeUnivalence.uaOfTransportHomotopy a c (f ≫ g) W _
    (MapPath.pointwise (compositeMapPath a b c f E g D))

variable {a b c : Γ ⟶ smallFamilyCodes.{u}}
  {s : PointedEndomorphism (liftedDecode a)} {t : PointedEndomorphism (liftedDecode b)}
  {v : PointedEndomorphism (liftedDecode c)}

noncomputable def path (e : Equivalence s t) :
    Term (homogeneousPath (objects description Γ)
      (objectOf description a s.fields) (objectOf description b t.fields)) :=
  Term.map (explicitMap description a s.fields b t.fields) e.native

theorem carrier_path (e : Equivalence s t) :
    Term.map (carrierProjection description a b s.fields t.fields) (path e) =
      NativeUnivalence.ua a b e.map e.witness :=
  (carrier_explicit description a b s.fields t.fields e.native).trans
    (NativeUnivalence.equivToPath_beta e.map e.witness)

theorem pathMap_eq {A B : Family Γ} (f : A ⟶ B) {x y : Term A}
    (p : Term (homogeneousPath A x y)) :
    Term.map (HomotopyLevels.pathMap f x y) p = homogeneousPathMap f p := by
  apply pathApp_injective
  exact (pathApp_lam (Term.map (Functor.whiskerLeft
    (projection (interval Γ)).mapElements f) (pathApp p))
    (congrArg (Term.map f) (pathApp_zero p))
    (congrArg (Term.map f) (pathApp_one p))).symm

theorem carrier_concat
    (p : Term (homogeneousPath (objects description Γ)
      (objectOf description a s.fields) (objectOf description b t.fields)))
    (q : Term (homogeneousPath (objects description Γ)
      (objectOf description b t.fields) (objectOf description c v.fields))) :
    Term.map (carrierProjection description a c s.fields v.fields)
      (homogeneousConcat (objectsFilling description Γ).1 (objectsFilling description Γ).2 p q) =
    homogeneousConcat (SmallUniverse.filling Γ) (SmallUniverse.filling_lawful Γ)
      (Term.map (carrierProjection description a b s.fields t.fields) p)
      (Term.map (carrierProjection description b c t.fields v.fields) q) := by
  have h := SigmaFillingPaths.concat_first (SmallUniverse.filling Γ) (SmallUniverse.filling_lawful Γ)
    (Native.filling description (NativeDecode.filling (SmallUniverse.code (generic (SmallUniverse.family Γ))))
      (NativeDecode.filling_lawful _)).1
    (Native.filling description (NativeDecode.filling (SmallUniverse.code (generic (SmallUniverse.family Γ))))
      (NativeDecode.filling_lawful _)).2 p q
  exact (pathMap_eq _ _).trans (h.trans
    (congrArg₂ (homogeneousConcat (SmallUniverse.filling Γ) (SmallUniverse.filling_lawful Γ))
      (pathMap_eq _ p).symm (pathMap_eq _ q).symm))

/-- The supplied complete composite witness and independent point/function
composition agree with concatenation of the actual selected whole paths. -/
noncomputable def composition (e : Equivalence s t) (d : Equivalence t v)
    (w : HomotopyEquivalence (e.map ≫ d.map))
    (sC : Term (HomotopyLevels.isSet (liftedDecode c))) :
    Term (homogeneousPath
      (homogeneousPath (objects description Γ) (objectOf description a s.fields) (objectOf description c v.fields))
      (path (e.compWith d w (NativeDecode.filling a) (NativeDecode.filling_lawful a)
        (NativeDecode.filling c) (NativeDecode.filling_lawful c)))
      (homogeneousConcat (objectsFilling description Γ).1 (objectsFilling description Γ).2 (path e) (path d))) := by
  let ed := e.compWith d w (NativeDecode.filling a) (NativeDecode.filling_lawful a)
    (NativeDecode.filling c) (NativeDecode.filling_lawful c)
  let H := uaCompositeOfWitness a b c e.map e.witness d.map d.witness w
  have h₀ := carrier_path ed
  have h₁ := (carrier_concat (path e) (path d)).trans
    (congrArg₂ (homogeneousConcat (SmallUniverse.filling Γ) (SmallUniverse.filling_lawful Γ))
      (carrier_path e) (carrier_path d))
  exact wholeComparison description a c s.fields v.fields sC _ _
    (pathLam (pathApp H) ((pathApp_zero H).trans h₀.symm) ((pathApp_one H).trans h₁.symm))

noncomputable def reverseMapRight {a b : Γ ⟶ smallFamilyCodes.{u}}
    (F : Filling (SmallUniverse.family Γ)) (hF : F.Lawful)
    (p : Term (NativeUnivalence.paths a b)) :
    MapPath (NativeUnivalence.pathToMap (homogeneousReverse
      F hF p) ≫ NativeUnivalence.pathToMap p) (𝟙 _) := by
  let σ := projection (liftedDecode b)
  let r := homogeneousReverse F hF p
  let P := reverseTransportComparison (F.reindex σ) (hF.reindex σ)
    (NativeUnivalence.reindexPath p σ) (generic (liftedDecode b))
  have hr : NativeUnivalence.reindexPath r σ =
      homogeneousReverse (F.reindex σ) (hF.reindex σ) (NativeUnivalence.reindexPath p σ) :=
    reverse_reindex F hF p σ
  have hm := (NativeUnivalence.pathToMap_reindex r σ).trans (congrArg NativeUnivalence.pathToMap hr)
  have hp := NativeUnivalence.pathToMap_reindex p σ
  let g' := NativeUnivalence.pathToMap (homogeneousReverse (F.reindex σ) (hF.reindex σ)
    (NativeUnivalence.reindexPath p σ))
  have hL := (congrArg (fun f => Term.map f (Term.map g' (generic (liftedDecode b)))) hp.symm).trans
    (congrArg (Term.map (Functor.whiskerLeft σ.mapElements (NativeUnivalence.pathToMap p)))
      (congrArg (fun f => Term.map f (generic (liftedDecode b))) hm.symm))
  let Q : Term (homogeneousPath (reindex (liftedDecode b) σ)
      (Term.map (Functor.whiskerLeft σ.mapElements
        (NativeUnivalence.pathToMap r ≫ NativeUnivalence.pathToMap p)) (generic (liftedDecode b)))
      (generic (liftedDecode b))) := pathLam (pathApp P) ((pathApp_zero P).trans hL) (pathApp_one P)
  exact EquivalencePaths.mapPath (NativeUnivalence.pathToMap r ≫ NativeUnivalence.pathToMap p)
    (𝟙 (liftedDecode b)) Q

noncomputable def inverseOfRightComparison
    (f : liftedDecode a ⟶ liftedDecode b) (E : HomotopyEquivalence f)
    (w : HomotopyEquivalence E.selectedInverse)
    (q : Term (NativeUnivalence.paths b a))
    (R : MapPath (NativeUnivalence.pathToMap q ≫ f) (𝟙 (liftedDecode b))) :
    Term (homogeneousPath (NativeUnivalence.paths b a)
      (NativeUnivalence.ua b a E.selectedInverse w) q) :=
  NativeUnivalence.uaOfTransportHomotopy b a E.selectedInverse w q
    (Selected.rightComparison E (NativeUnivalence.pathToMap q) (MapPath.pointwise R))

noncomputable def reverseRightWithMap
    (F : Filling (SmallUniverse.family Γ)) (hF : F.Lawful)
    (p : Term (NativeUnivalence.paths a b))
    (f : liftedDecode a ⟶ liftedDecode b)
    (H : MapPath f (NativeUnivalence.pathToMap p)) :
    MapPath (NativeUnivalence.pathToMap (homogeneousReverse F hF p) ≫ f) (𝟙 (liftedDecode b)) :=
  MapPath.trans (MapPath.precompose H (NativeUnivalence.pathToMap (homogeneousReverse F hF p)))
    (reverseMapRight F hF p)
    (NativeDecode.filling b) (NativeDecode.filling_lawful b)
    (NativeDecode.filling b) (NativeDecode.filling_lawful b)

noncomputable def inverseCarrierComparison (F : Filling (SmallUniverse.family Γ)) (hF : F.Lawful)
    (e : Equivalence s t)
    (w : HomotopyEquivalence e.witness.selectedInverse) :
    Term (homogeneousPath (NativeUnivalence.paths b a)
      (NativeUnivalence.ua b a e.witness.selectedInverse w)
      (homogeneousReverse F hF
        (NativeUnivalence.ua a b e.map e.witness))) :=
  inverseOfRightComparison e.map e.witness w _
    (reverseRightWithMap F hF (NativeUnivalence.ua a b e.map e.witness) e.map
      (uaMapPath a b e.map e.witness))

theorem carrier_reverse
    (p : Term (homogeneousPath (objects description Γ)
      (objectOf description a s.fields) (objectOf description b t.fields))) :
    Term.map (carrierProjection description b a t.fields s.fields)
      (homogeneousReverse (objectsFilling description Γ).1 (objectsFilling description Γ).2 p) =
    homogeneousReverse (SmallUniverse.filling Γ) (SmallUniverse.filling_lawful Γ)
      (Term.map (carrierProjection description a b s.fields t.fields) p) := by
  have h := SigmaFillingPaths.reverse_first (SmallUniverse.filling Γ) (SmallUniverse.filling_lawful Γ)
    (Native.filling description (NativeDecode.filling (SmallUniverse.code (generic (SmallUniverse.family Γ))))
      (NativeDecode.filling_lawful _)).1
    (Native.filling description (NativeDecode.filling (SmallUniverse.code (generic (SmallUniverse.family Γ))))
      (NativeDecode.filling_lawful _)).2 p
  exact (pathMap_eq _ _).trans (h.trans
    (congrArg (homogeneousReverse (SmallUniverse.filling Γ) (SmallUniverse.filling_lawful Γ))
      (pathMap_eq _ p).symm))

noncomputable def inversion (e : Equivalence s t)
    (w : HomotopyEquivalence e.witness.selectedInverse)
    (sA : Term (HomotopyLevels.isSet (liftedDecode a))) :
    Term (homogeneousPath
      (homogeneousPath (objects description Γ) (objectOf description b t.fields) (objectOf description a s.fields))
      (path (e.inverseWith w (NativeDecode.filling a) (NativeDecode.filling_lawful a)
        (NativeDecode.filling b) (NativeDecode.filling_lawful b)))
      (homogeneousReverse (objectsFilling description Γ).1 (objectsFilling description Γ).2 (path e))) := by
  let ei := e.inverseWith w (NativeDecode.filling a) (NativeDecode.filling_lawful a)
    (NativeDecode.filling b) (NativeDecode.filling_lawful b)
  let H := inverseCarrierComparison (SmallUniverse.filling Γ) (SmallUniverse.filling_lawful Γ) e w
  have h₀ := carrier_path ei
  have h₁ := (carrier_reverse (path e)).trans
    (congrArg (homogeneousReverse (SmallUniverse.filling Γ) (SmallUniverse.filling_lawful Γ)) (carrier_path e))
  exact wholeComparison description b a t.fields s.fields sA _ _
    (pathLam (pathApp H) ((pathApp_zero H).trans h₀.symm) ((pathApp_one H).trans h₁.symm))

end Coded
end SquareKit.Cubical.Cartesian.StructureIdentity.Coherence

namespace SquareKit.Cubical.Cartesian.StructureIdentity.Coherence
open CategoryTheory SquareKit.StructureIdentity Native SmallUniverse
universe u
variable {Γ Δ : Context.{u+1}}

noncomputable def MapPath.reindex {A B : Family Γ} {f g : A ⟶ B}
    (p : MapPath f g) (σ : Δ ⟶ Γ) :
    MapPath (Functor.whiskerLeft σ.mapElements f) (Functor.whiskerLeft σ.mapElements g) :=
  homogeneousPathMap (piReindexIso A (Cartesian.reindex B (projection A)) σ).hom
    (homogeneousReindex p σ)

def PointedEndomorphism.reindex {A : Family Γ} (s : PointedEndomorphism A) (σ : Δ ⟶ Γ) :
    PointedEndomorphism (Cartesian.reindex A σ) where
  point := Term.reindex s.point σ
  step := Functor.whiskerLeft σ.mapElements s.step

noncomputable def Equivalence.reindex {A B : Family Γ} {s : PointedEndomorphism A} {t : PointedEndomorphism B}
    (e : Equivalence s t) (σ : Δ ⟶ Γ) : Equivalence (s.reindex σ) (t.reindex σ) where
  map := Functor.whiskerLeft σ.mapElements e.map
  witness := e.witness.reindex σ
  point := homogeneousReindex e.point σ
  step := MapPath.reindex e.step σ

theorem fields_reindex {A : Family Γ} (s : PointedEndomorphism A) (σ : Δ ⟶ Γ) :
    Native.reindexTerm description s.fields σ = (s.reindex σ).fields := by
  apply Term.ext
  intro x
  rfl

namespace Coded
variable {a b : Γ ⟶ smallFamilyCodes.{u}}
  {s : PointedEndomorphism (liftedDecode a)} {t : PointedEndomorphism (liftedDecode b)}

theorem object_reindex (s : PointedEndomorphism (liftedDecode a)) (σ : Δ ⟶ Γ) :
    Term.map (objectsReindexIso description σ).hom (Term.reindex (objectOf description a s.fields) σ) =
      objectOf description (σ ≫ a) (s.reindex σ).fields :=
  (objectOf_reindex description a s.fields σ).trans
    (congrArg (objectOf description (σ ≫ a)) (fields_reindex s σ))

noncomputable def reindexPath
    (p : Term (homogeneousPath (objects description Γ)
      (objectOf description a s.fields) (objectOf description b t.fields)))
    (σ : Δ ⟶ Γ) :
    Term (homogeneousPath (objects description Δ)
      (objectOf description (σ ≫ a) (s.reindex σ).fields)
      (objectOf description (σ ≫ b) (t.reindex σ).fields)) := by
  let q := homogeneousPathMap (objectsReindexIso description σ).hom (homogeneousReindex p σ)
  exact pathLam (pathApp q) ((pathApp_zero q).trans (object_reindex s σ))
    ((pathApp_one q).trans (object_reindex t σ))

theorem carrier_reindex
    (p : Term (homogeneousPath (objects description Γ)
      (objectOf description a s.fields) (objectOf description b t.fields)))
    (σ : Δ ⟶ Γ) :
    Term.map (carrierProjection description (σ ≫ a) (σ ≫ b) (s.reindex σ).fields (t.reindex σ).fields)
      (reindexPath p σ) =
      homogeneousReindex (Term.map (carrierProjection description a b s.fields t.fields) p) σ := by
  apply pathApp_injective
  apply Term.ext
  intro x
  rfl
/-- The selected complete witness is substituted, and the selected whole path
commutes with substitution up to a native two-path. -/
noncomputable def pathReindex (e : Equivalence s t)
    (sB : Term (HomotopyLevels.isSet (liftedDecode b))) (σ : Δ ⟶ Γ) :
    Term (homogeneousPath
      (homogeneousPath (objects description Δ)
        (objectOf description (σ ≫ a) (s.reindex σ).fields)
        (objectOf description (σ ≫ b) (t.reindex σ).fields))
      (path (e.reindex σ)) (reindexPath (path e) σ)) := by
  let P := carrierProjection description (σ ≫ a) (σ ≫ b) (s.reindex σ).fields (t.reindex σ).fields
  have h₀ := carrier_path (a := σ ≫ a) (b := σ ≫ b) (e.reindex σ)
  have h₁ := (carrier_reindex (path e) σ).trans
    (congrArg (fun p => homogeneousReindex p σ) (carrier_path e))
  have h : Term.map P (path (e.reindex σ)) = Term.map P (reindexPath (path e) σ) :=
    h₀.trans ((NativeUnivalence.ua_reindex a b e.map e.witness σ).symm.trans h₁.symm)
  exact wholeComparison description (σ ≫ a) (σ ≫ b) (s.reindex σ).fields (t.reindex σ).fields
    (HomotopyLevels.reindexSet sB σ) _ _
    (Term.convert (congrArg (homogeneousPath _ (Term.map P (path (e.reindex σ)))) h)
      (homogeneousRefl (Term.map P (path (e.reindex σ)))))

noncomputable def pathReindexWith (e : Equivalence s t)
    (sB : Term (HomotopyLevels.isSet (liftedDecode b))) (σ : Δ ⟶ Γ)
    (d : Equivalence (s.reindex σ) (t.reindex σ))
    (h : (⟨d.map, d.witness⟩ : Σ f : liftedDecode (σ ≫ a) ⟶ liftedDecode (σ ≫ b), HomotopyEquivalence f) =
      ⟨(e.reindex σ).map, (e.reindex σ).witness⟩) :
    Term (homogeneousPath
      (homogeneousPath (objects description Δ)
        (objectOf description (σ ≫ a) (s.reindex σ).fields)
        (objectOf description (σ ≫ b) (t.reindex σ).fields))
      (path d) (reindexPath (path e) σ)) := by
  let P := carrierProjection description (σ ≫ a) (σ ≫ b) (s.reindex σ).fields (t.reindex σ).fields
  have hd := carrier_path (a := σ ≫ a) (b := σ ≫ b) d
  have he := (carrier_reindex (path e) σ).trans
    (congrArg (fun p => homogeneousReindex p σ) (carrier_path e))
  have hu := congrArg
    (fun q : Σ f : liftedDecode (σ ≫ a) ⟶ liftedDecode (σ ≫ b), HomotopyEquivalence f =>
      NativeUnivalence.ua (σ ≫ a) (σ ≫ b) q.1 q.2) h
  have hc : Term.map P (path d) = Term.map P (reindexPath (path e) σ) :=
    hd.trans (hu.trans ((NativeUnivalence.ua_reindex a b e.map e.witness σ).symm.trans he.symm))
  exact wholeComparison description (σ ≫ a) (σ ≫ b) (s.reindex σ).fields (t.reindex σ).fields
    (HomotopyLevels.reindexSet sB σ) _ _
    (Term.convert (congrArg (homogeneousPath _ (Term.map P (path d))) hc)
      (homogeneousRefl (Term.map P (path d))))

/-- Fresh composition after substitution agrees with substituting the original
whole selected path; the complete supplied composite witness is reindexed. -/
noncomputable def compositionReindex {c : Γ ⟶ smallFamilyCodes.{u}}
    {v : PointedEndomorphism (liftedDecode c)}
    (e : Equivalence s t) (d : Equivalence t v)
    (w : HomotopyEquivalence (e.map ≫ d.map))
    (sC : Term (HomotopyLevels.isSet (liftedDecode c))) (σ : Δ ⟶ Γ)
    (FA : Filling (liftedDecode a)) (hFA : FA.Lawful)
    (FC : Filling (liftedDecode c)) (hFC : FC.Lawful)
    (GA : Filling (liftedDecode (σ ≫ a))) (hGA : GA.Lawful)
    (GC : Filling (liftedDecode (σ ≫ c))) (hGC : GC.Lawful) :=
  pathReindexWith (a := a) (b := c) (s := s) (t := v)
    (e.compWith d w FA hFA
      FC hFC) sC σ
    ((e.reindex σ).compWith (d.reindex σ) (w.reindex σ)
      GA hGA
      GC hGC) rfl

noncomputable def inversionReindex (e : Equivalence s t)
    (w : HomotopyEquivalence e.witness.selectedInverse)
    (sA : Term (HomotopyLevels.isSet (liftedDecode a))) (σ : Δ ⟶ Γ)
    (FA : Filling (liftedDecode a)) (hFA : FA.Lawful)
    (FB : Filling (liftedDecode b)) (hFB : FB.Lawful)
    (GA : Filling (liftedDecode (σ ≫ a))) (hGA : GA.Lawful)
    (GB : Filling (liftedDecode (σ ≫ b))) (hGB : GB.Lawful) :=
  pathReindexWith (a := b) (b := a) (s := t) (t := s)
    (e.inverseWith w FA hFA
      FB hFB) sA σ
    ((e.reindex σ).inverseWith (w.reindex σ)
      GA hGA
      GB hGB) rfl

end Coded
end SquareKit.Cubical.Cartesian.StructureIdentity.Coherence
