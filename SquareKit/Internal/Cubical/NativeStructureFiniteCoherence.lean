import SquareKit.Internal.Cubical.NativeStructureSethood
import SquareKit.Internal.Cubical.NativeStructureCoherence
import SquareKit.Internal.Cubical.NativePathWhiskering

/-! Finite coherence retains each supplied composite equivalence witness. -/
set_option autoImplicit false
set_option warningAsError true
namespace SquareKit.Cubical.Presheaf.StructureIdentity.Coherence.Finite
open CategoryTheory Native StructuredIdentity.UaComparison SmallUniverse
universe u

variable {Γ : Context.{u+1}}
  {a b c d : Γ ⟶ smallFamilyCodes.{u}}
  {x : PointedEndomorphism (liftedDecode a)} {y : PointedEndomorphism (liftedDecode b)}
  {z : PointedEndomorphism (liftedDecode c)} {w : PointedEndomorphism (liftedDecode d)}

abbrev Arrow (x : PointedEndomorphism (liftedDecode a))
    (y : PointedEndomorphism (liftedDecode b)) := Equivalence x y
noncomputable def Whole (x : PointedEndomorphism (liftedDecode a))
    (y : PointedEndomorphism (liftedDecode b)) :=
  homogeneousPath (objects description Γ) (objectOf description a x.fields) (objectOf description b y.fields)
abbrev Path (x : PointedEndomorphism (liftedDecode a))
    (y : PointedEndomorphism (liftedDecode b)) := Term (Whole x y)
abbrev Cell (p q : Path x y) := Term (homogeneousPath (Whole x y) p q)

noncomputable def wholeFilling (x : PointedEndomorphism (liftedDecode a)) (y : PointedEndomorphism
  (liftedDecode b)) : Filling (Whole x y) :=
  pathFilling ((objectsFilling description Γ).1.reindex (projection (interval Γ)))
    ((objectsFilling description Γ).2.reindex _) (objectOf description a x.fields) (objectOf description b y.fields)
theorem wholeFilling_lawful (x : PointedEndomorphism (liftedDecode a)) (y : PointedEndomorphism (liftedDecode
  b)) : (wholeFilling x y).Lawful :=
  by
  unfold wholeFilling
  exact pathFilling_lawful ((objectsFilling description Γ).1.reindex (projection (interval Γ)))
    ((objectsFilling description Γ).2.reindex (projection (interval Γ))) (objectOf description a x.fields) (objectOf description b y.fields)

noncomputable abbrev concat (p : Path x y) (q : Path y z) : Path x z :=
  homogeneousConcat (objectsFilling description Γ).1 (objectsFilling description Γ).2 p q
noncomputable def vertical {p q r : Path x y} (H : Cell p q) (K : Cell q r) : Cell p r :=
  homogeneousConcat (wholeFilling x y) (wholeFilling_lawful x y) H K
noncomputable def reverse {p q : Path x y} (H : Cell p q) : Cell q p := homogeneousReverse H
noncomputable def whiskerRight {p p' : Path x y} (H : Cell p p') (q : Path y z) :
    Cell (concat p q) (concat p' q) :=
  NativeWhiskering.right (objectsFilling description Γ).1 (objectsFilling description Γ).2 H q
noncomputable def whiskerLeft (p : Path x y) {q q' : Path y z} (H : Cell q q') :
    Cell (concat p q) (concat p q') :=
  NativeWhiskering.left (objectsFilling description Γ).1 (objectsFilling description Γ).2 p H

noncomputable def compareCells (sY : Term (HomotopyLevels.isSet (liftedDecode b))) {p q : Path x y} (H K : Cell p q) :
    Term (homogeneousPath (homogeneousPath (Whole x y) p q) H K) :=
  wholeThreePath description a b x.fields y.fields sY p q H K

noncomputable abbrev compose (e : Arrow x y) (f : Arrow y z)
    (W : HomotopyEquivalence (e.map ≫ f.map)) : Arrow x z :=
  e.compWith f W (NativeDecode.filling a) (NativeDecode.filling_lawful a)
    (NativeDecode.filling c) (NativeDecode.filling_lawful c)
noncomputable def binary (e : Arrow x y) (f : Arrow y z)
    (W : HomotopyEquivalence (e.map ≫ f.map)) (sZ : Term (HomotopyLevels.isSet (liftedDecode c))) :
    Term (homogeneousPath
      (homogeneousPath (objects description Γ) (objectOf description a x.fields) (objectOf description c z.fields))
      (Coded.path (e.compWith f W (NativeDecode.filling a) (NativeDecode.filling_lawful a)
        (NativeDecode.filling c) (NativeDecode.filling_lawful c)))
      (homogeneousConcat (objectsFilling description Γ).1 (objectsFilling description Γ).2 (Coded.path e) (Coded.path f))) :=
  Coded.composition e f W sZ

def pointwise {A B : Family Γ} {f g : A ⟶ B} (H : MapPath f g) :
    Term (homogeneousPath (reindex B (projection A))
      (Term.map (Functor.whiskerLeft (projection A).mapElements f) (generic A))
      (Term.map (Functor.whiskerLeft (projection A).mapElements g) (generic A))) :=
  app (Term.map (FunctionPaths.decomposition (EquivalenceFamilies.encodeMap f)
    (EquivalenceFamilies.encodeMap g)).hom H)

noncomputable def carrier (p : Path x y) : Term (NativeUnivalence.paths a b) :=
  Term.map (carrierProjection description a b x.fields y.fields) p
noncomputable def transport (p : Path x y) : (liftedDecode a) ⟶ (liftedDecode b) := NativeUnivalence.pathToMap (carrier p)

/-- Recover whole paths from a comparison of transport maps, retaining both full path decodings. -/
noncomputable def compareTransport (sY : Term (HomotopyLevels.isSet (liftedDecode b))) (p q : Path x y)
    (H : MapPath (transport p) (transport q)) : Cell p q := by
  let P := carrier p
  let Q := carrier q
  let f := NativeUnivalence.pathToMap P
  let E := NativeUnivalence.pathToEquivalence P
  let left := NativeUnivalence.uaOfTransportHomotopy a b f E P
    (homogeneousRefl (Term.map (Functor.whiskerLeft (projection (liftedDecode a)).mapElements f) (generic (liftedDecode a))))
  let right := NativeUnivalence.uaOfTransportHomotopy a b f E Q (pointwise H)
  exact wholeComparison description a b x.fields y.fields sY p q
    (homogeneousConcat (NativeUnivalence.pathsFilling a b)
      (NativeUnivalence.pathsFilling_lawful a b) (homogeneousReverse left) right)

/-- A map homotopy compares the two complete supplied structured equivalences. -/
noncomputable def compareArrows (sY : Term (HomotopyLevels.isSet (liftedDecode b))) (e f : Arrow x y) (H : MapPath e.map f.map) :
    Cell (Coded.path e) (Coded.path f) :=
  homogeneousPathMap (explicitMap description a x.fields b y.fields)
    (equivalencePath description a b x.fields y.fields sY e.native f.native
      (EquivalencePaths.ofHomotopy e.map f.map (pointwise H)
        (NativeDecode.filling a) (NativeDecode.filling_lawful a) (NativeDecode.filling b)
          (NativeDecode.filling_lawful b) e.witness f.witness))

noncomputable def concatMapPath (a b c : Γ ⟶ smallFamilyCodes.{u})
    (p : Term (NativeUnivalence.paths a b)) (q : Term (NativeUnivalence.paths b c)) :
    MapPath (NativeUnivalence.pathToMap (homogeneousConcat (SmallUniverse.filling Γ)
      (SmallUniverse.filling_lawful Γ) p q))
      (NativeUnivalence.pathToMap p ≫ NativeUnivalence.pathToMap q) := by
  let π := projection (liftedDecode a)
  let P : Term (NativeUnivalence.paths (π ≫ a) (π ≫ b)) := homogeneousReindex p π
  let Q : Term (NativeUnivalence.paths (π ≫ b) (π ≫ c)) := homogeneousReindex q π
  let H := NativeUnivalence.concatTransportComparison (π ≫ a) (π ≫ b) (π ≫ c) P Q
    (generic (liftedDecode a))
  have ht : NativeUnivalence.pathToMap (a := π ≫ a) (b := π ≫ c) (homogeneousConcat (SmallUniverse.filling (total (liftedDecode a)))
      (SmallUniverse.filling_lawful _) P Q) =
      Functor.whiskerLeft π.mapElements (NativeUnivalence.pathToMap
        (homogeneousConcat (SmallUniverse.filling Γ) (SmallUniverse.filling_lawful Γ) p q)) :=
    (congrArg NativeUnivalence.pathToMap (homogeneousConcat_reindex
      (SmallUniverse.filling Γ) (SmallUniverse.filling_lawful Γ) p q π).symm).trans
      (NativeUnivalence.pathToMap_reindex _ π).symm
  have hL := congrArg (fun m => Term.map m (generic (liftedDecode a))) ht
  have hR := (congrArg (fun m => Term.map m
    (Term.map (NativeUnivalence.pathToMap P) (generic (liftedDecode a))))
      (NativeUnivalence.pathToMap_reindex q π).symm).trans
    (congrArg (Term.map (Functor.whiskerLeft π.mapElements (NativeUnivalence.pathToMap q)))
      (congrArg (fun m => Term.map m (generic (liftedDecode a)))
        (NativeUnivalence.pathToMap_reindex p π).symm))
  exact EquivalencePaths.mapPath _ _
    (pathLam (pathApp H) ((pathApp_zero H).trans hL) ((pathApp_one H).trans hR))

theorem carrier_concat (p : Path x y) (q : Path y z) : carrier (concat p q) =
    homogeneousConcat (SmallUniverse.filling Γ) (SmallUniverse.filling_lawful Γ) (carrier p) (carrier q) :=
  Coded.carrier_concat p q

noncomputable def mapConcat (p : Path x y) (q : Path y z) :
    MapPath (transport (concat p q)) (transport p ≫ transport q) := by
  unfold transport
  rw [carrier_concat]
  exact concatMapPath a b c (carrier p) (carrier q)

noncomputable def mapTrans {f g h : (liftedDecode a) ⟶ (liftedDecode b)}
    (H : MapPath f g) (K : MapPath g h) : MapPath f h :=
  MapPath.trans H K (NativeDecode.filling a) (NativeDecode.filling_lawful a) (NativeDecode.filling b) (NativeDecode.filling_lawful b)
noncomputable def mapReverse {f g : (liftedDecode a) ⟶ (liftedDecode b)} (H : MapPath f g) : MapPath g f :=
  homogeneousReverse H

/-- The whole-path associator is derived from transport composition and Coded.path recovery. -/
noncomputable def associator (sW : Term (HomotopyLevels.isSet (liftedDecode d))) (p : Path x y) (q : Path y z) (r : Path z w) :
    Cell (concat (concat p q) r) (concat p (concat q r)) := by
  have HL : MapPath (transport (concat p q) ≫ transport r)
      (transport p ≫ transport q ≫ transport r) := by
    simpa only [Category.id_comp, Category.assoc] using
      MapPath.whisker (mapConcat p q) (𝟙 (liftedDecode a)) (transport r)
  have HR : MapPath (transport p ≫ transport (concat q r))
      (transport p ≫ transport q ≫ transport r) := by
    simpa only [Category.comp_id] using
      MapPath.whisker (mapConcat q r) (transport p) (𝟙 (liftedDecode d))
  let L := mapTrans (a := a) (b := d) (mapConcat (concat p q) r) HL
  let R := mapTrans (a := a) (b := d) (mapConcat p (concat q r)) HR
  exact compareTransport sW _ _ (mapTrans (a := a) (b := d) L (mapReverse (a := a) (b := d) R))

noncomputable def refl (x : PointedEndomorphism (liftedDecode a)) : Path x x := homogeneousRefl (objectOf description a x.fields)

def mapPathOfEq {A B : Family Γ} {f g : A ⟶ B} (h : f = g) : MapPath f g :=
  h ▸ homogeneousRefl (EquivalenceFamilies.encodeMap f)

noncomputable def mapIdentity (x : PointedEndomorphism (liftedDecode a)) : MapPath (transport (refl x)) (𝟙 (liftedDecode a)) := by
  let σ := projection (liftedDecode a)
  let p := homogeneousRefl (SmallUniverse.term a)
  let h := NativeUnivalence.reflexiveTransportComparison (σ ≫ a) (generic (liftedDecode a))
  have hm := NativeUnivalence.pathToMap_reindex p σ
  exact EquivalencePaths.mapPath _ _ (pathLam (pathApp h)
    ((pathApp_zero h).trans (congrArg (fun k => Term.map k (generic (liftedDecode a))) hm.symm))
    (pathApp_one h))

noncomputable def leftUnitor (sY : Term (HomotopyLevels.isSet (liftedDecode b))) (p : Path x y) : Cell (concat (refl x) p) p := by
  have H : MapPath (transport (refl x) ≫ transport p) (transport p) := by
    simpa only [Category.id_comp] using MapPath.whisker (mapIdentity x) (𝟙 (liftedDecode a)) (transport p)
  exact compareTransport sY _ _ (mapTrans (a := a) (b := b) (mapConcat (refl x) p) H)

noncomputable def rightUnitor (sY : Term (HomotopyLevels.isSet (liftedDecode b))) (p : Path x y) : Cell (concat p (refl y)) p := by
  have H : MapPath (transport p ≫ transport (refl y)) (transport p) := by
    simpa only [Category.comp_id] using MapPath.whisker (mapIdentity y) (transport p) (𝟙 (liftedDecode b))
  exact compareTransport sY _ _ (mapTrans (a := a) (b := b) (mapConcat p (refl y)) H)

noncomputable def triangle (sY : Term (HomotopyLevels.isSet (liftedDecode b))) (sZ : Term
  (HomotopyLevels.isSet (liftedDecode c))) (p : Path x y) (q : Path y z) :=
  compareCells sZ
    (vertical (associator sZ p (refl y) q) (whiskerLeft p (leftUnitor sZ q)))
    (whiskerRight (rightUnitor sY p) q)

noncomputable def pentagon {k : Γ ⟶ smallFamilyCodes.{u}} {v : PointedEndomorphism (liftedDecode k)} (sW :
  Term (HomotopyLevels.isSet (liftedDecode d))) (sV : Term (HomotopyLevels.isSet (liftedDecode k)))
    (p : Path x y) (q : Path y z) (r : Path z w) (t : Path w v) :=
  compareCells sV
    (vertical (vertical (whiskerRight (associator sW p q r) t)
      (associator sV p (concat q r) t)) (whiskerLeft p (associator sV q r t)))
    (vertical (associator sV (concat p q) r t) (associator sV p q (concat r t)))


private noncomputable opaque namedPath (e : Arrow x y) : { p : Path x y // p = Coded.path e } :=
  ⟨Coded.path e, rfl⟩
noncomputable def selected (e : Arrow x y) : Path x y := (namedPath e).val
theorem selected_eq (e : Arrow x y) : selected e = Coded.path e := (namedPath e).property

noncomputable def selectedBinary (e : Arrow x y) (f : Arrow y z)
    (W : HomotopyEquivalence (e.map ≫ f.map)) (sZ : Term (HomotopyLevels.isSet (liftedDecode c))) :
    Cell (selected (e.compWith f W (NativeDecode.filling a) (NativeDecode.filling_lawful a)
      (NativeDecode.filling c) (NativeDecode.filling_lawful c))) (concat (selected e) (selected f)) :=
  Term.convert (congrArg₂ (homogeneousPath (Whole x z)) (selected_eq _).symm
    (congrArg₂ (homogeneousConcat (objectsFilling description Γ).1 (objectsFilling description Γ).2)
      (selected_eq e) (selected_eq f)).symm)
    (Coded.composition e f W sZ)

noncomputable def identity (x : PointedEndomorphism (liftedDecode a)) (W : HomotopyEquivalence (𝟙 (liftedDecode a))) : Arrow x x where
  map := 𝟙 _
  witness := W
  point := homogeneousRefl x.point
  step := mapPathOfEq (by simp only [Category.comp_id, Category.id_comp])

noncomputable def rawSelectedIdentity (sX : Term (HomotopyLevels.isSet (liftedDecode a))) (W : HomotopyEquivalence (𝟙 (liftedDecode a))) :
    Cell (x := x) (y := x) (Coded.path (identity x W)) (refl x) := by
  let H := NativeUnivalence.uaOfTransportHomotopy a a (𝟙 (liftedDecode a)) W
    (homogeneousRefl (SmallUniverse.term a)) (pointwise (mapReverse (a := a) (b := a) (mapIdentity x)))
  exact wholeComparison description a a x.fields x.fields sX _ _
    (pathLam (pathApp H) ((pathApp_zero H).trans (Coded.carrier_path (identity x W)).symm)
      (pathApp_one H))

noncomputable def rawSelectedLeftUnitor (sY : Term (HomotopyLevels.isSet (liftedDecode b))) (e : Arrow x y)
    (W : HomotopyEquivalence (𝟙 (liftedDecode a)))
    (V : HomotopyEquivalence ((𝟙 (liftedDecode a)) ≫ e.map)) :
    Cell (x := x) (y := y) (Coded.path (compose (identity x W) e V)) (Coded.path e) :=
  compareArrows sY _ _ (mapPathOfEq (Category.id_comp e.map))

noncomputable def rawSelectedRightUnitor (sY : Term (HomotopyLevels.isSet (liftedDecode b))) (e : Arrow x y)
    (W : HomotopyEquivalence (𝟙 (liftedDecode b)))
    (V : HomotopyEquivalence (e.map ≫ (𝟙 (liftedDecode b)))) :
    Cell (x := x) (y := y) (Coded.path (compose e (identity y W) V)) (Coded.path e) :=
  compareArrows sY _ _ (mapPathOfEq (Category.comp_id e.map))


noncomputable def selectedIdentity (sX : Term (HomotopyLevels.isSet (liftedDecode a))) (W : HomotopyEquivalence (𝟙 (liftedDecode a))) :
    Cell (selected (identity x W)) (refl x) :=
  Term.convert (congrArg (fun p => homogeneousPath (Whole x x) p (refl x)) (selected_eq _).symm)
    (rawSelectedIdentity sX W)

noncomputable def leftUnitRoute (sX : Term (HomotopyLevels.isSet (liftedDecode a))) (sY : Term
  (HomotopyLevels.isSet (liftedDecode b))) (e : Arrow x y)
    (W : HomotopyEquivalence (𝟙 (liftedDecode a)))
    (V : HomotopyEquivalence ((𝟙 (liftedDecode a)) ≫ e.map)) :
    Cell (selected (compose (identity x W) e V)) (selected e) :=
  vertical (vertical (selectedBinary (identity x W) e V sY)
    (whiskerRight (selectedIdentity sX W) (selected e))) (leftUnitor sY (selected e))

noncomputable def rightUnitRoute (sY : Term (HomotopyLevels.isSet (liftedDecode b))) (e : Arrow x y)
    (W : HomotopyEquivalence (𝟙 (liftedDecode b)))
    (V : HomotopyEquivalence (e.map ≫ (𝟙 (liftedDecode b)))) :
    Cell (selected (compose e (identity y W) V)) (selected e) :=
  vertical (vertical (selectedBinary e (identity y W) V sY)
    (whiskerLeft (selected e) (selectedIdentity sY W))) (rightUnitor sY (selected e))

noncomputable def selectedLeftUnitor (sY : Term (HomotopyLevels.isSet (liftedDecode b))) (e : Arrow x y)
    (W : HomotopyEquivalence (𝟙 (liftedDecode a)))
    (V : HomotopyEquivalence ((𝟙 (liftedDecode a)) ≫ e.map)) :
    Cell (selected (compose (identity x W) e V)) (selected e) :=
  Term.convert (congrArg₂ (homogeneousPath (Whole x y)) (selected_eq _).symm (selected_eq e).symm)
    (rawSelectedLeftUnitor sY e W V)

noncomputable def selectedRightUnitor (sY : Term (HomotopyLevels.isSet (liftedDecode b))) (e : Arrow x y)
    (W : HomotopyEquivalence (𝟙 (liftedDecode b)))
    (V : HomotopyEquivalence (e.map ≫ (𝟙 (liftedDecode b)))) :
    Cell (selected (compose e (identity y W) V)) (selected e) :=
  Term.convert (congrArg₂ (homogeneousPath (Whole x y)) (selected_eq _).symm (selected_eq e).symm)
    (rawSelectedRightUnitor sY e W V)

noncomputable def leftUnitCompatibility (sX : Term (HomotopyLevels.isSet (liftedDecode a))) (sY : Term
  (HomotopyLevels.isSet (liftedDecode b))) (e : Arrow x y)
    (W : HomotopyEquivalence (𝟙 (liftedDecode a)))
    (V : HomotopyEquivalence ((𝟙 (liftedDecode a)) ≫ e.map)) :=
  compareCells sY (selectedLeftUnitor sY e W V) (leftUnitRoute sX sY e W V)

noncomputable def rightUnitCompatibility (sY : Term (HomotopyLevels.isSet (liftedDecode b))) (e : Arrow x y)
    (W : HomotopyEquivalence (𝟙 (liftedDecode b)))
    (V : HomotopyEquivalence (e.map ≫ (𝟙 (liftedDecode b)))) :=
  compareCells sY (selectedRightUnitor sY e W V) (rightUnitRoute sY e W V)
variable {Δ : Context.{u+1}}
noncomputable def reindexPath (p : Path x y) (σ : Δ ⟶ Γ) : Path (a := σ ≫ a) (b := σ ≫ b) (x.reindex σ) (y.reindex σ) :=
  Coded.reindexPath p σ

noncomputable def reindexMap (x : PointedEndomorphism (liftedDecode a)) (y : PointedEndomorphism (liftedDecode b)) (σ : Δ ⟶ Γ) :
    reindex (Whole x y) σ ⟶ Whole (a := σ ≫ a) (b := σ ≫ b) (x.reindex σ) (y.reindex σ) :=
  (EquivalenceFamilies.homogeneousReindexIso (objects description Γ) (objectOf description a x.fields)
    (objectOf description b y.fields) σ).hom ≫
    HomotopyLevels.pathMap (objectsReindexIso description σ).hom
      (Term.reindex (objectOf description a x.fields) σ) (Term.reindex (objectOf description b y.fields) σ) ≫
    eqToHom (congrArg₂ (homogeneousPath (objects description Δ))
      (Coded.object_reindex x σ) (Coded.object_reindex y σ))

theorem changeEndpoints_apply {Ξ : Context.{u+1}} {A : Family Ξ} {p q p' q' : Term A}
    (hp : p = p') (hq : q = q') (H : Term (homogeneousPath A p q)) :
    Term.map (eqToHom (congrArg₂ (homogeneousPath A) hp hq)) H =
      pathLam (pathApp H) ((pathApp_zero H).trans hp) ((pathApp_one H).trans hq) := by
  cases hp
  cases hq
  exact (pathLam_app H).symm

theorem reindexMap_apply (p : Path x y) (σ : Δ ⟶ Γ) :
    Term.map (reindexMap x y σ) (Term.reindex p σ) = reindexPath p σ := by
  let Q := homogeneousPathMap (objectsReindexIso description σ).hom (homogeneousReindex p σ)
  have h : Term.map
      (HomotopyLevels.pathMap (objectsReindexIso description σ).hom
        (Term.reindex (objectOf description a x.fields) σ) (Term.reindex (objectOf description b y.fields) σ))
      (Term.map (EquivalenceFamilies.homogeneousReindexIso (objects description Γ)
        (objectOf description a x.fields) (objectOf description b y.fields) σ).hom (Term.reindex p σ)) = Q := by
    apply pathApp_injective
    apply Term.ext
    intro j
    rfl
  exact (congrArg (Term.map (eqToHom (congrArg₂ (homogeneousPath (objects description Δ))
    (Coded.object_reindex x σ) (Coded.object_reindex y σ)))) h).trans
    (changeEndpoints_apply (Coded.object_reindex x σ) (Coded.object_reindex y σ) Q)

noncomputable def reindexCell {p q : Path x y} (H : Cell p q) (σ : Δ ⟶ Γ) :
    Cell (reindexPath p σ) (reindexPath q σ) :=
  Term.convert (congrArg₂ (homogeneousPath (Whole (a := σ ≫ a) (b := σ ≫ b) (x.reindex σ) (y.reindex σ)))
    (reindexMap_apply p σ) (reindexMap_apply q σ))
    (homogeneousPathMap (reindexMap x y σ) (homogeneousReindex H σ))

theorem selected_carrier (e : Arrow x y) : carrier (selected e) = NativeUnivalence.ua a b e.map e.witness :=
  (congrArg carrier (selected_eq e)).trans (Coded.carrier_path e)

noncomputable def compareSelectedArrows (sY : Term (HomotopyLevels.isSet (liftedDecode b)))
    (e f : Arrow x y) (H : MapPath e.map f.map) : Cell (selected e) (selected f) :=
  Term.convert (congrArg₂ (homogeneousPath (Whole x y)) (selected_eq e).symm (selected_eq f).symm)
    (compareArrows sY e f H)

/-- Compare selected paths without exposing the map-homotopy conversion to callers. -/
noncomputable def compareSelectedMaps (sY : Term (HomotopyLevels.isSet (liftedDecode b)))
    (e f : Arrow x y) (h : e.map = f.map) : Cell (selected e) (selected f) :=
  compareSelectedArrows sY e f (mapPathOfEq h)

noncomputable def selectedReindexWith (e : Arrow x y)
    (sY : Term (HomotopyLevels.isSet (liftedDecode b))) (σ : Δ ⟶ Γ)
    (d : Arrow (a := σ ≫ a) (b := σ ≫ b) (x.reindex σ) (y.reindex σ))
    (h : (⟨d.map, d.witness⟩ : Σ f : liftedDecode (σ ≫ a) ⟶ liftedDecode (σ ≫ b), HomotopyEquivalence f) =
      ⟨(e.reindex σ).map, (e.reindex σ).witness⟩) :
    Cell (selected d) (reindexPath (selected e) σ) :=
  Term.convert (congrArg₂ (homogeneousPath (Whole (a := σ ≫ a) (b := σ ≫ b) (x.reindex σ) (y.reindex σ)))
    (selected_eq d).symm (congrArg (fun p => reindexPath p σ) (selected_eq e)).symm)
    (Coded.pathReindexWith e sY σ d h)

/-- Compare two constructed cells after aligning the actual selected endpoints. -/
noncomputable def reindexComparison (e f : Arrow x y)
    (sY : Term (HomotopyLevels.isSet (liftedDecode b))) (σ : Δ ⟶ Γ)
    (d e' : Arrow (a := σ ≫ a) (b := σ ≫ b) (x.reindex σ) (y.reindex σ))
    (hd : (⟨d.map, d.witness⟩ : Σ f : liftedDecode (σ ≫ a) ⟶ liftedDecode (σ ≫ b), HomotopyEquivalence f) =
      ⟨(e.reindex σ).map, (e.reindex σ).witness⟩)
    (he : (⟨e'.map, e'.witness⟩ : Σ f : liftedDecode (σ ≫ a) ⟶ liftedDecode (σ ≫ b), HomotopyEquivalence f) =
      ⟨(f.reindex σ).map, (f.reindex σ).witness⟩)
    (H : Cell (selected e) (selected f)) (K : Cell (selected d) (selected e')) :=
  compareCells (a := σ ≫ a) (b := σ ≫ b) (HomotopyLevels.reindexSet sY σ)
    (vertical K (selectedReindexWith f sY σ e' he))
    (vertical (selectedReindexWith e sY σ d hd) (reindexCell H σ))

structure TripleWitnesses (e : Arrow x y) (f : Arrow y z) (g : Arrow z w) where
  pairLeft : HomotopyEquivalence (e.map ≫ f.map)
  pairRight : HomotopyEquivalence (f.map ≫ g.map)
  outerLeft : HomotopyEquivalence ((e.map ≫ f.map) ≫ g.map)
  outerRight : HomotopyEquivalence (e.map ≫ (f.map ≫ g.map))

namespace TripleWitnesses
variable (e : Arrow x y) (f : Arrow y z) (g : Arrow z w) (W : TripleWitnesses e f g)

noncomputable def path1 (e : Arrow x y) (f : Arrow y z) (g : Arrow z w) (_W : TripleWitnesses e f g) := selected e
theorem path1_eq (e : Arrow x y) (f : Arrow y z) (g : Arrow z w) (W : TripleWitnesses e f g) : W.path1 e f g = Coded.path e := selected_eq _

noncomputable def path2 (e : Arrow x y) (f : Arrow y z) (g : Arrow z w) (_W : TripleWitnesses e f g) := selected f
theorem path2_eq (e : Arrow x y) (f : Arrow y z) (g : Arrow z w) (W : TripleWitnesses e f g) : W.path2 e f g = Coded.path f := selected_eq _

noncomputable def path3 (e : Arrow x y) (f : Arrow y z) (g : Arrow z w) (_W : TripleWitnesses e f g) := selected g
theorem path3_eq (e : Arrow x y) (f : Arrow y z) (g : Arrow z w) (W : TripleWitnesses e f g) : W.path3 e f g = Coded.path g := selected_eq _

noncomputable def path12 (e : Arrow x y) (f : Arrow y z) (g : Arrow z w) (W : TripleWitnesses e f g) :=
  selected (e.compWith f W.pairLeft (NativeDecode.filling a) (NativeDecode.filling_lawful a)
  (NativeDecode.filling c) (NativeDecode.filling_lawful c))
theorem path12_eq (e : Arrow x y) (f : Arrow y z) (g : Arrow z w) (W : TripleWitnesses e f g) : W.path12 e f g
  = Coded.path (e.compWith f W.pairLeft (NativeDecode.filling a) (NativeDecode.filling_lawful a)
  (NativeDecode.filling c) (NativeDecode.filling_lawful c)) := selected_eq _

noncomputable def path23 (e : Arrow x y) (f : Arrow y z) (g : Arrow z w) (W : TripleWitnesses e f g) :=
  selected (f.compWith g W.pairRight (NativeDecode.filling b) (NativeDecode.filling_lawful b)
  (NativeDecode.filling d) (NativeDecode.filling_lawful d))
theorem path23_eq (e : Arrow x y) (f : Arrow y z) (g : Arrow z w) (W : TripleWitnesses e f g) : W.path23 e f g
  = Coded.path (f.compWith g W.pairRight (NativeDecode.filling b) (NativeDecode.filling_lawful b)
  (NativeDecode.filling d) (NativeDecode.filling_lawful d)) := selected_eq _

noncomputable def pathLeft (e : Arrow x y) (f : Arrow y z) (g : Arrow z w) (W : TripleWitnesses e f g) :=
  selected ((e.compWith f W.pairLeft (NativeDecode.filling a) (NativeDecode.filling_lawful a)
  (NativeDecode.filling c) (NativeDecode.filling_lawful c)).compWith g W.outerLeft (NativeDecode.filling a)
  (NativeDecode.filling_lawful a) (NativeDecode.filling d) (NativeDecode.filling_lawful d))
theorem pathLeft_eq (e : Arrow x y) (f : Arrow y z) (g : Arrow z w) (W : TripleWitnesses e f g) : W.pathLeft e
  f g = Coded.path ((e.compWith f W.pairLeft (NativeDecode.filling a) (NativeDecode.filling_lawful a)
  (NativeDecode.filling c) (NativeDecode.filling_lawful c)).compWith g W.outerLeft (NativeDecode.filling a)
  (NativeDecode.filling_lawful a) (NativeDecode.filling d) (NativeDecode.filling_lawful d)) := selected_eq _

noncomputable def pathRight (e : Arrow x y) (f : Arrow y z) (g : Arrow z w) (W : TripleWitnesses e f g) :=
  selected (e.compWith (f.compWith g W.pairRight (NativeDecode.filling b) (NativeDecode.filling_lawful b)
  (NativeDecode.filling d) (NativeDecode.filling_lawful d)) W.outerRight (NativeDecode.filling a)
  (NativeDecode.filling_lawful a) (NativeDecode.filling d) (NativeDecode.filling_lawful d))
theorem pathRight_eq (e : Arrow x y) (f : Arrow y z) (g : Arrow z w) (W : TripleWitnesses e f g) : W.pathRight
  e f g = Coded.path (e.compWith (f.compWith g W.pairRight (NativeDecode.filling b)
  (NativeDecode.filling_lawful b) (NativeDecode.filling d) (NativeDecode.filling_lawful d)) W.outerRight
  (NativeDecode.filling a) (NativeDecode.filling_lawful a) (NativeDecode.filling d)
  (NativeDecode.filling_lawful d)) := selected_eq _

noncomputable def left : Arrow x w := ((e.compWith f W.pairLeft (NativeDecode.filling a)
  (NativeDecode.filling_lawful a) (NativeDecode.filling c) (NativeDecode.filling_lawful c)).compWith g
  W.outerLeft (NativeDecode.filling a) (NativeDecode.filling_lawful a) (NativeDecode.filling d)
  (NativeDecode.filling_lawful d))
noncomputable def right : Arrow x w := (e.compWith (f.compWith g W.pairRight (NativeDecode.filling b)
  (NativeDecode.filling_lawful b) (NativeDecode.filling d) (NativeDecode.filling_lawful d)) W.outerRight
  (NativeDecode.filling a) (NativeDecode.filling_lawful a) (NativeDecode.filling d)
  (NativeDecode.filling_lawful d))

private noncomputable def rawAssociator (sW : Term (HomotopyLevels.isSet (liftedDecode d))) :=
  compareArrows (a := a) (b := d) (x := x) (y := w) sW ((e.compWith f W.pairLeft (NativeDecode.filling a)
    (NativeDecode.filling_lawful a) (NativeDecode.filling c) (NativeDecode.filling_lawful c)).compWith g
    W.outerLeft (NativeDecode.filling a) (NativeDecode.filling_lawful a) (NativeDecode.filling d)
    (NativeDecode.filling_lawful d)) (e.compWith (f.compWith g W.pairRight (NativeDecode.filling b)
    (NativeDecode.filling_lawful b) (NativeDecode.filling d) (NativeDecode.filling_lawful d)) W.outerRight
    (NativeDecode.filling a) (NativeDecode.filling_lawful a) (NativeDecode.filling d)
    (NativeDecode.filling_lawful d))
    (mapPathOfEq (Category.assoc e.map f.map g.map))

noncomputable def selectedAssociator (sW : Term (HomotopyLevels.isSet (liftedDecode d))) :
    Cell (selected (W.left e f g)) (selected (W.right e f g)) :=
  Term.convert (congrArg₂ (homogeneousPath (Whole x w))
    (W.pathLeft_eq e f g).symm (W.pathRight_eq e f g).symm) (W.rawAssociator e f g sW)

noncomputable def binary12 (sZ : Term (HomotopyLevels.isSet (liftedDecode c))) :
    Cell (W.path12 e f g) (concat (W.path1 e f g) (W.path2 e f g)) :=
  Term.convert (congrArg₂ (homogeneousPath (Whole x z))
    (W.path12_eq e f g).symm
    (congrArg₂ (homogeneousConcat (objectsFilling description Γ).1 (objectsFilling description Γ).2)
      (W.path1_eq e f g) (W.path2_eq e f g)).symm)
    (Coded.composition (a := a) (b := b) (c := c) e f W.pairLeft sZ)

noncomputable def binary23 (sW : Term (HomotopyLevels.isSet (liftedDecode d))) :
    Cell (W.path23 e f g) (concat (W.path2 e f g) (W.path3 e f g)) :=
  Term.convert (congrArg₂ (homogeneousPath (Whole y w))
    (W.path23_eq e f g).symm
    (congrArg₂ (homogeneousConcat (objectsFilling description Γ).1 (objectsFilling description Γ).2)
      (W.path2_eq e f g) (W.path3_eq e f g)).symm)
    (Coded.composition (a := b) (b := c) (c := d) f g W.pairRight sW)

noncomputable def binaryLeft (sW : Term (HomotopyLevels.isSet (liftedDecode d))) :
    Cell (W.pathLeft e f g) (concat (W.path12 e f g) (W.path3 e f g)) :=
  Term.convert (congrArg₂ (homogeneousPath (Whole x w))
    (W.pathLeft_eq e f g).symm
    (congrArg₂ (homogeneousConcat (objectsFilling description Γ).1 (objectsFilling description Γ).2)
      (W.path12_eq e f g) (W.path3_eq e f g)).symm)
    (Coded.composition (a := a) (b := c) (c := d) (e.compWith f W.pairLeft (NativeDecode.filling a)
      (NativeDecode.filling_lawful a) (NativeDecode.filling c) (NativeDecode.filling_lawful c)) g W.outerLeft
      sW)

noncomputable def binaryRight (sW : Term (HomotopyLevels.isSet (liftedDecode d))) :
    Cell (W.pathRight e f g) (concat (W.path1 e f g) (W.path23 e f g)) :=
  Term.convert (congrArg₂ (homogeneousPath (Whole x w))
    (W.pathRight_eq e f g).symm
    (congrArg₂ (homogeneousConcat (objectsFilling description Γ).1 (objectsFilling description Γ).2)
      (W.path1_eq e f g) (W.path23_eq e f g)).symm)
    (Coded.composition (a := a) (b := b) (c := d) e (f.compWith g W.pairRight (NativeDecode.filling b)
      (NativeDecode.filling_lawful b) (NativeDecode.filling d) (NativeDecode.filling_lawful d)) W.outerRight
      sW)

noncomputable def leftNormalization (sZ : Term (HomotopyLevels.isSet (liftedDecode c)))
    (sW : Term (HomotopyLevels.isSet (liftedDecode d))) :=
  vertical (x := x) (y := w) (W.binaryLeft e f g sW)
    (whiskerRight (x := x) (y := z) (z := w) (W.binary12 e f g sZ) (W.path3 e f g))

noncomputable def rightNormalization (sW : Term (HomotopyLevels.isSet (liftedDecode d))) :
    Cell (W.pathRight e f g) (concat (W.path1 e f g) (concat (W.path2 e f g) (W.path3 e f g))) :=
  vertical (x := x) (y := w) (W.binaryRight e f g sW)
    (whiskerLeft (a := a) (b := b) (c := d) (x := x) (y := y) (z := w) (W.path1 e f g) (W.binary23 e f g sW))

noncomputable def compatibility (sZ : Term (HomotopyLevels.isSet (liftedDecode c)))
    (sW : Term (HomotopyLevels.isSet (liftedDecode d))) :=
  compareCells (x := x) (y := w) sW
    (vertical (W.leftNormalization e f g sZ sW)
      (associator sW (W.path1 e f g) (W.path2 e f g) (W.path3 e f g)))
    (vertical (W.selectedAssociator e f g sW) (W.rightNormalization e f g sW))

noncomputable def binaryAssociator (sZ : Term (HomotopyLevels.isSet (liftedDecode c)))
    (sW : Term (HomotopyLevels.isSet (liftedDecode d))) : Cell (selected (W.left e f g)) (selected (W.right e f g)) :=
  vertical (vertical (W.leftNormalization e f g sZ sW)
    (associator sW (W.path1 e f g) (W.path2 e f g) (W.path3 e f g)))
    (reverse (W.rightNormalization e f g sW))

noncomputable def reindex (σ : Δ ⟶ Γ) :
    TripleWitnesses (a := σ ≫ a) (b := σ ≫ b) (c := σ ≫ c) (d := σ ≫ d)
      (e.reindex σ) (f.reindex σ) (g.reindex σ) where
  pairLeft := W.pairLeft.reindex σ
  pairRight := W.pairRight.reindex σ
  outerLeft := W.outerLeft.reindex σ
  outerRight := W.outerRight.reindex σ

/-- Fresh outer preservation data may be supplied independently of the reindexed data. -/
noncomputable def freshAssociator (sW : Term (HomotopyLevels.isSet (liftedDecode d))) (σ : Δ ⟶ Γ)
    (l r : Arrow (a := σ ≫ a) (b := σ ≫ d) (x.reindex σ) (w.reindex σ))
    (hl : (⟨l.map, l.witness⟩ : Σ f : liftedDecode (σ ≫ a) ⟶ liftedDecode (σ ≫ d), HomotopyEquivalence f) =
      ⟨((W.left e f g).reindex σ).map, ((W.left e f g).reindex σ).witness⟩)
    (hr : (⟨r.map, r.witness⟩ : Σ f : liftedDecode (σ ≫ a) ⟶ liftedDecode (σ ≫ d), HomotopyEquivalence f) =
      ⟨((W.right e f g).reindex σ).map, ((W.right e f g).reindex σ).witness⟩) : Cell (selected l) (selected r) :=
  compareSelectedArrows (a := σ ≫ a) (b := σ ≫ d) (HomotopyLevels.reindexSet sW σ) l r
      (mapPathOfEq ((congrArg Sigma.fst hl).trans
        ((Category.assoc (e.reindex σ).map (f.reindex σ).map (g.reindex σ).map).trans
          (congrArg Sigma.fst hr).symm)))

noncomputable def freshAssociatorReindex (sW : Term (HomotopyLevels.isSet (liftedDecode d))) (σ : Δ ⟶ Γ)
    (l r : Arrow (a := σ ≫ a) (b := σ ≫ d) (x.reindex σ) (w.reindex σ))
    (hl : (⟨l.map, l.witness⟩ : Σ f : liftedDecode (σ ≫ a) ⟶ liftedDecode (σ ≫ d), HomotopyEquivalence f) =
      ⟨((W.left e f g).reindex σ).map, ((W.left e f g).reindex σ).witness⟩)
    (hr : (⟨r.map, r.witness⟩ : Σ f : liftedDecode (σ ≫ a) ⟶ liftedDecode (σ ≫ d), HomotopyEquivalence f) =
      ⟨((W.right e f g).reindex σ).map, ((W.right e f g).reindex σ).witness⟩) :=
  reindexComparison (W.left e f g) (W.right e f g) sW σ l r hl hr
    (W.selectedAssociator e f g sW)
    (W.freshAssociator e f g sW σ l r hl hr)

/-- Compare the binary-derived route with a constructed fresh binary route. -/
noncomputable def freshBinaryAssociatorReindex (sZ : Term (HomotopyLevels.isSet (liftedDecode c)))
    (sW : Term (HomotopyLevels.isSet (liftedDecode d))) (σ : Δ ⟶ Γ)
    (l r : Arrow (a := σ ≫ a) (b := σ ≫ d) (x.reindex σ) (w.reindex σ))
    (hl : (⟨l.map, l.witness⟩ : Σ f : liftedDecode (σ ≫ a) ⟶ liftedDecode (σ ≫ d), HomotopyEquivalence f) =
      ⟨((W.left e f g).reindex σ).map, ((W.left e f g).reindex σ).witness⟩)
    (hr : (⟨r.map, r.witness⟩ : Σ f : liftedDecode (σ ≫ a) ⟶ liftedDecode (σ ≫ d), HomotopyEquivalence f) =
      ⟨((W.right e f g).reindex σ).map, ((W.right e f g).reindex σ).witness⟩)
    (K : Cell (selected l) (selected r)) :=
  reindexComparison (W.left e f g) (W.right e f g) sW σ l r hl hr
    (W.binaryAssociator e f g sZ sW) K
end TripleWitnesses

structure FourWitnesses {k : Γ ⟶ smallFamilyCodes.{u}} {v : PointedEndomorphism (liftedDecode k)}
    (e : Arrow x y) (f : Arrow y z) (g : Arrow z w) (h : Arrow w v) where
  pair12 : HomotopyEquivalence (e.map ≫ f.map)
  pair23 : HomotopyEquivalence (f.map ≫ g.map)
  pair34 : HomotopyEquivalence (g.map ≫ h.map)
  triple123L : HomotopyEquivalence ((e.map ≫ f.map) ≫ g.map)
  triple123R : HomotopyEquivalence (e.map ≫ (f.map ≫ g.map))
  triple234L : HomotopyEquivalence ((f.map ≫ g.map) ≫ h.map)
  triple234R : HomotopyEquivalence (f.map ≫ (g.map ≫ h.map))
  outer0 : HomotopyEquivalence (((e.map ≫ f.map) ≫ g.map) ≫ h.map)
  outer1 : HomotopyEquivalence ((e.map ≫ (f.map ≫ g.map)) ≫ h.map)
  outer2 : HomotopyEquivalence (e.map ≫ ((f.map ≫ g.map) ≫ h.map))
  outer3 : HomotopyEquivalence (e.map ≫ (f.map ≫ (g.map ≫ h.map)))
  outer4 : HomotopyEquivalence ((e.map ≫ f.map) ≫ (g.map ≫ h.map))

namespace FourWitnesses
variable {k : Γ ⟶ smallFamilyCodes.{u}} {v : PointedEndomorphism (liftedDecode k)}
  (e : Arrow x y) (f : Arrow y z) (g : Arrow z w) (h : Arrow w v) (W : FourWitnesses e f g h)

noncomputable def p (e : Arrow x y) (f : Arrow y z) (g : Arrow z w) (h : Arrow w v) (_W : FourWitnesses e f g h) := selected e
theorem p_eq (e : Arrow x y) (f : Arrow y z) (g : Arrow z w) (h : Arrow w v) (W : FourWitnesses e f g h) : W.p
  e f g h = Coded.path e := selected_eq _

noncomputable def q (e : Arrow x y) (f : Arrow y z) (g : Arrow z w) (h : Arrow w v) (_W : FourWitnesses e f g h) := selected f
theorem q_eq (e : Arrow x y) (f : Arrow y z) (g : Arrow z w) (h : Arrow w v) (W : FourWitnesses e f g h) : W.q
  e f g h = Coded.path f := selected_eq _

noncomputable def r (e : Arrow x y) (f : Arrow y z) (g : Arrow z w) (h : Arrow w v) (_W : FourWitnesses e f g h) := selected g
theorem r_eq (e : Arrow x y) (f : Arrow y z) (g : Arrow z w) (h : Arrow w v) (W : FourWitnesses e f g h) : W.r
  e f g h = Coded.path g := selected_eq _

noncomputable def t (e : Arrow x y) (f : Arrow y z) (g : Arrow z w) (h : Arrow w v) (_W : FourWitnesses e f g h) := selected h
theorem t_eq (e : Arrow x y) (f : Arrow y z) (g : Arrow z w) (h : Arrow w v) (W : FourWitnesses e f g h) : W.t
  e f g h = Coded.path h := selected_eq _

noncomputable def pq (e : Arrow x y) (f : Arrow y z) (g : Arrow z w) (h : Arrow w v) (W : FourWitnesses e f g
  h) := selected (e.compWith f W.pair12 (NativeDecode.filling a) (NativeDecode.filling_lawful a)
  (NativeDecode.filling c) (NativeDecode.filling_lawful c))
theorem pq_eq (e : Arrow x y) (f : Arrow y z) (g : Arrow z w) (h : Arrow w v) (W : FourWitnesses e f g h) :
  W.pq e f g h = Coded.path (e.compWith f W.pair12 (NativeDecode.filling a) (NativeDecode.filling_lawful a)
  (NativeDecode.filling c) (NativeDecode.filling_lawful c)) := selected_eq _

noncomputable def qr (e : Arrow x y) (f : Arrow y z) (g : Arrow z w) (h : Arrow w v) (W : FourWitnesses e f g
  h) := selected (f.compWith g W.pair23 (NativeDecode.filling b) (NativeDecode.filling_lawful b)
  (NativeDecode.filling d) (NativeDecode.filling_lawful d))
theorem qr_eq (e : Arrow x y) (f : Arrow y z) (g : Arrow z w) (h : Arrow w v) (W : FourWitnesses e f g h) :
  W.qr e f g h = Coded.path (f.compWith g W.pair23 (NativeDecode.filling b) (NativeDecode.filling_lawful b)
  (NativeDecode.filling d) (NativeDecode.filling_lawful d)) := selected_eq _

noncomputable def rt (e : Arrow x y) (f : Arrow y z) (g : Arrow z w) (h : Arrow w v) (W : FourWitnesses e f g
  h) := selected (g.compWith h W.pair34 (NativeDecode.filling c) (NativeDecode.filling_lawful c)
  (NativeDecode.filling k) (NativeDecode.filling_lawful k))
theorem rt_eq (e : Arrow x y) (f : Arrow y z) (g : Arrow z w) (h : Arrow w v) (W : FourWitnesses e f g h) :
  W.rt e f g h = Coded.path (g.compWith h W.pair34 (NativeDecode.filling c) (NativeDecode.filling_lawful c)
  (NativeDecode.filling k) (NativeDecode.filling_lawful k)) := selected_eq _

noncomputable def pqrL (e : Arrow x y) (f : Arrow y z) (g : Arrow z w) (h : Arrow w v) (W : FourWitnesses e f
  g h) := selected ((e.compWith f W.pair12 (NativeDecode.filling a) (NativeDecode.filling_lawful a)
  (NativeDecode.filling c) (NativeDecode.filling_lawful c)).compWith g W.triple123L (NativeDecode.filling a)
  (NativeDecode.filling_lawful a) (NativeDecode.filling d) (NativeDecode.filling_lawful d))
theorem pqrL_eq (e : Arrow x y) (f : Arrow y z) (g : Arrow z w) (h : Arrow w v) (W : FourWitnesses e f g h) :
  W.pqrL e f g h = Coded.path ((e.compWith f W.pair12 (NativeDecode.filling a) (NativeDecode.filling_lawful a)
  (NativeDecode.filling c) (NativeDecode.filling_lawful c)).compWith g W.triple123L (NativeDecode.filling a)
  (NativeDecode.filling_lawful a) (NativeDecode.filling d) (NativeDecode.filling_lawful d)) := selected_eq _

noncomputable def pqrR (e : Arrow x y) (f : Arrow y z) (g : Arrow z w) (h : Arrow w v) (W : FourWitnesses e f
  g h) := selected (e.compWith (f.compWith g W.pair23 (NativeDecode.filling b) (NativeDecode.filling_lawful b)
  (NativeDecode.filling d) (NativeDecode.filling_lawful d)) W.triple123R (NativeDecode.filling a)
  (NativeDecode.filling_lawful a) (NativeDecode.filling d) (NativeDecode.filling_lawful d))
theorem pqrR_eq (e : Arrow x y) (f : Arrow y z) (g : Arrow z w) (h : Arrow w v) (W : FourWitnesses e f g h) :
  W.pqrR e f g h = Coded.path (e.compWith (f.compWith g W.pair23 (NativeDecode.filling b)
  (NativeDecode.filling_lawful b) (NativeDecode.filling d) (NativeDecode.filling_lawful d)) W.triple123R
  (NativeDecode.filling a) (NativeDecode.filling_lawful a) (NativeDecode.filling d)
  (NativeDecode.filling_lawful d)) := selected_eq _

noncomputable def qrtL (e : Arrow x y) (f : Arrow y z) (g : Arrow z w) (h : Arrow w v) (W : FourWitnesses e f
  g h) := selected ((f.compWith g W.pair23 (NativeDecode.filling b) (NativeDecode.filling_lawful b)
  (NativeDecode.filling d) (NativeDecode.filling_lawful d)).compWith h W.triple234L (NativeDecode.filling b)
  (NativeDecode.filling_lawful b) (NativeDecode.filling k) (NativeDecode.filling_lawful k))
theorem qrtL_eq (e : Arrow x y) (f : Arrow y z) (g : Arrow z w) (h : Arrow w v) (W : FourWitnesses e f g h) :
  W.qrtL e f g h = Coded.path ((f.compWith g W.pair23 (NativeDecode.filling b) (NativeDecode.filling_lawful b)
  (NativeDecode.filling d) (NativeDecode.filling_lawful d)).compWith h W.triple234L (NativeDecode.filling b)
  (NativeDecode.filling_lawful b) (NativeDecode.filling k) (NativeDecode.filling_lawful k)) := selected_eq _

noncomputable def qrtR (e : Arrow x y) (f : Arrow y z) (g : Arrow z w) (h : Arrow w v) (W : FourWitnesses e f
  g h) := selected (f.compWith (g.compWith h W.pair34 (NativeDecode.filling c) (NativeDecode.filling_lawful c)
  (NativeDecode.filling k) (NativeDecode.filling_lawful k)) W.triple234R (NativeDecode.filling b)
  (NativeDecode.filling_lawful b) (NativeDecode.filling k) (NativeDecode.filling_lawful k))
theorem qrtR_eq (e : Arrow x y) (f : Arrow y z) (g : Arrow z w) (h : Arrow w v) (W : FourWitnesses e f g h) :
  W.qrtR e f g h = Coded.path (f.compWith (g.compWith h W.pair34 (NativeDecode.filling c)
  (NativeDecode.filling_lawful c) (NativeDecode.filling k) (NativeDecode.filling_lawful k)) W.triple234R
  (NativeDecode.filling b) (NativeDecode.filling_lawful b) (NativeDecode.filling k)
  (NativeDecode.filling_lawful k)) := selected_eq _

noncomputable def v0 (e : Arrow x y) (f : Arrow y z) (g : Arrow z w) (h : Arrow w v) (W : FourWitnesses e f g
  h) := selected (((e.compWith f W.pair12 (NativeDecode.filling a) (NativeDecode.filling_lawful a)
  (NativeDecode.filling c) (NativeDecode.filling_lawful c)).compWith g W.triple123L (NativeDecode.filling a)
  (NativeDecode.filling_lawful a) (NativeDecode.filling d) (NativeDecode.filling_lawful d)).compWith h
  W.outer0 (NativeDecode.filling a) (NativeDecode.filling_lawful a) (NativeDecode.filling k)
  (NativeDecode.filling_lawful k))
theorem v0_eq (e : Arrow x y) (f : Arrow y z) (g : Arrow z w) (h : Arrow w v) (W : FourWitnesses e f g h) :
  W.v0 e f g h = Coded.path (((e.compWith f W.pair12 (NativeDecode.filling a) (NativeDecode.filling_lawful a)
  (NativeDecode.filling c) (NativeDecode.filling_lawful c)).compWith g W.triple123L (NativeDecode.filling a)
  (NativeDecode.filling_lawful a) (NativeDecode.filling d) (NativeDecode.filling_lawful d)).compWith h
  W.outer0 (NativeDecode.filling a) (NativeDecode.filling_lawful a) (NativeDecode.filling k)
  (NativeDecode.filling_lawful k)) := selected_eq _

noncomputable def v1 (e : Arrow x y) (f : Arrow y z) (g : Arrow z w) (h : Arrow w v) (W : FourWitnesses e f g
  h) := selected ((e.compWith (f.compWith g W.pair23 (NativeDecode.filling b) (NativeDecode.filling_lawful b)
  (NativeDecode.filling d) (NativeDecode.filling_lawful d)) W.triple123R (NativeDecode.filling a)
  (NativeDecode.filling_lawful a) (NativeDecode.filling d) (NativeDecode.filling_lawful d)).compWith h
  W.outer1 (NativeDecode.filling a) (NativeDecode.filling_lawful a) (NativeDecode.filling k)
  (NativeDecode.filling_lawful k))
theorem v1_eq (e : Arrow x y) (f : Arrow y z) (g : Arrow z w) (h : Arrow w v) (W : FourWitnesses e f g h) :
  W.v1 e f g h = Coded.path ((e.compWith (f.compWith g W.pair23 (NativeDecode.filling b)
  (NativeDecode.filling_lawful b) (NativeDecode.filling d) (NativeDecode.filling_lawful d)) W.triple123R
  (NativeDecode.filling a) (NativeDecode.filling_lawful a) (NativeDecode.filling d)
  (NativeDecode.filling_lawful d)).compWith h W.outer1 (NativeDecode.filling a) (NativeDecode.filling_lawful
  a) (NativeDecode.filling k) (NativeDecode.filling_lawful k)) := selected_eq _

noncomputable def v2 (e : Arrow x y) (f : Arrow y z) (g : Arrow z w) (h : Arrow w v) (W : FourWitnesses e f g
  h) := selected (e.compWith ((f.compWith g W.pair23 (NativeDecode.filling b) (NativeDecode.filling_lawful b)
  (NativeDecode.filling d) (NativeDecode.filling_lawful d)).compWith h W.triple234L (NativeDecode.filling b)
  (NativeDecode.filling_lawful b) (NativeDecode.filling k) (NativeDecode.filling_lawful k)) W.outer2
  (NativeDecode.filling a) (NativeDecode.filling_lawful a) (NativeDecode.filling k)
  (NativeDecode.filling_lawful k))
theorem v2_eq (e : Arrow x y) (f : Arrow y z) (g : Arrow z w) (h : Arrow w v) (W : FourWitnesses e f g h) :
  W.v2 e f g h = Coded.path (e.compWith ((f.compWith g W.pair23 (NativeDecode.filling b)
  (NativeDecode.filling_lawful b) (NativeDecode.filling d) (NativeDecode.filling_lawful d)).compWith h
  W.triple234L (NativeDecode.filling b) (NativeDecode.filling_lawful b) (NativeDecode.filling k)
  (NativeDecode.filling_lawful k)) W.outer2 (NativeDecode.filling a) (NativeDecode.filling_lawful a)
  (NativeDecode.filling k) (NativeDecode.filling_lawful k)) := selected_eq _

noncomputable def v3 (e : Arrow x y) (f : Arrow y z) (g : Arrow z w) (h : Arrow w v) (W : FourWitnesses e f g
  h) := selected (e.compWith (f.compWith (g.compWith h W.pair34 (NativeDecode.filling c)
  (NativeDecode.filling_lawful c) (NativeDecode.filling k) (NativeDecode.filling_lawful k)) W.triple234R
  (NativeDecode.filling b) (NativeDecode.filling_lawful b) (NativeDecode.filling k)
  (NativeDecode.filling_lawful k)) W.outer3 (NativeDecode.filling a) (NativeDecode.filling_lawful a)
  (NativeDecode.filling k) (NativeDecode.filling_lawful k))
theorem v3_eq (e : Arrow x y) (f : Arrow y z) (g : Arrow z w) (h : Arrow w v) (W : FourWitnesses e f g h) :
  W.v3 e f g h = Coded.path (e.compWith (f.compWith (g.compWith h W.pair34 (NativeDecode.filling c)
  (NativeDecode.filling_lawful c) (NativeDecode.filling k) (NativeDecode.filling_lawful k)) W.triple234R
  (NativeDecode.filling b) (NativeDecode.filling_lawful b) (NativeDecode.filling k)
  (NativeDecode.filling_lawful k)) W.outer3 (NativeDecode.filling a) (NativeDecode.filling_lawful a)
  (NativeDecode.filling k) (NativeDecode.filling_lawful k)) := selected_eq _

noncomputable def v4 (e : Arrow x y) (f : Arrow y z) (g : Arrow z w) (h : Arrow w v) (W : FourWitnesses e f g
  h) := selected ((e.compWith f W.pair12 (NativeDecode.filling a) (NativeDecode.filling_lawful a)
  (NativeDecode.filling c) (NativeDecode.filling_lawful c)).compWith (g.compWith h W.pair34
  (NativeDecode.filling c) (NativeDecode.filling_lawful c) (NativeDecode.filling k)
  (NativeDecode.filling_lawful k)) W.outer4 (NativeDecode.filling a) (NativeDecode.filling_lawful a)
  (NativeDecode.filling k) (NativeDecode.filling_lawful k))
theorem v4_eq (e : Arrow x y) (f : Arrow y z) (g : Arrow z w) (h : Arrow w v) (W : FourWitnesses e f g h) :
  W.v4 e f g h = Coded.path ((e.compWith f W.pair12 (NativeDecode.filling a) (NativeDecode.filling_lawful a)
  (NativeDecode.filling c) (NativeDecode.filling_lawful c)).compWith (g.compWith h W.pair34
  (NativeDecode.filling c) (NativeDecode.filling_lawful c) (NativeDecode.filling k)
  (NativeDecode.filling_lawful k)) W.outer4 (NativeDecode.filling a) (NativeDecode.filling_lawful a)
  (NativeDecode.filling k) (NativeDecode.filling_lawful k)) := selected_eq _

noncomputable def binary_pq (s : Term (HomotopyLevels.isSet (liftedDecode c))) :
    Cell (W.pq e f g h) (concat (W.p e f g h) (W.q e f g h)) :=
  Term.convert (congrArg₂ (homogeneousPath (Whole x z))
    (W.pq_eq e f g h).symm
    (congrArg₂ (homogeneousConcat (objectsFilling description Γ).1 (objectsFilling description Γ).2) (W.p_eq e
      f g h) (W.q_eq e f g h)).symm)
    (Coded.composition (a := a) (b := b) (c := c) e f W.pair12 s)

noncomputable def binary_qr (s : Term (HomotopyLevels.isSet (liftedDecode d))) :
    Cell (W.qr e f g h) (concat (W.q e f g h) (W.r e f g h)) :=
  Term.convert (congrArg₂ (homogeneousPath (Whole y w))
    (W.qr_eq e f g h).symm
    (congrArg₂ (homogeneousConcat (objectsFilling description Γ).1 (objectsFilling description Γ).2) (W.q_eq e
      f g h) (W.r_eq e f g h)).symm)
    (Coded.composition (a := b) (b := c) (c := d) f g W.pair23 s)

noncomputable def binary_rt (s : Term (HomotopyLevels.isSet (liftedDecode k))) :
    Cell (W.rt e f g h) (concat (W.r e f g h) (W.t e f g h)) :=
  Term.convert (congrArg₂ (homogeneousPath (Whole z v))
    (W.rt_eq e f g h).symm
    (congrArg₂ (homogeneousConcat (objectsFilling description Γ).1 (objectsFilling description Γ).2) (W.r_eq e
      f g h) (W.t_eq e f g h)).symm)
    (Coded.composition (a := c) (b := d) (c := k) g h W.pair34 s)

noncomputable def binary_pqrL (s : Term (HomotopyLevels.isSet (liftedDecode d))) :
    Cell (W.pqrL e f g h) (concat (W.pq e f g h) (W.r e f g h)) :=
  Term.convert (congrArg₂ (homogeneousPath (Whole x w))
    (W.pqrL_eq e f g h).symm
    (congrArg₂ (homogeneousConcat (objectsFilling description Γ).1 (objectsFilling description Γ).2) (W.pq_eq
      e f g h) (W.r_eq e f g h)).symm)
    (Coded.composition (a := a) (b := c) (c := d) (e.compWith f W.pair12 (NativeDecode.filling a)
      (NativeDecode.filling_lawful a) (NativeDecode.filling c) (NativeDecode.filling_lawful c)) g W.triple123L
      s)

noncomputable def binary_pqrR (s : Term (HomotopyLevels.isSet (liftedDecode d))) :
    Cell (W.pqrR e f g h) (concat (W.p e f g h) (W.qr e f g h)) :=
  Term.convert (congrArg₂ (homogeneousPath (Whole x w))
    (W.pqrR_eq e f g h).symm
    (congrArg₂ (homogeneousConcat (objectsFilling description Γ).1 (objectsFilling description Γ).2) (W.p_eq e
      f g h) (W.qr_eq e f g h)).symm)
    (Coded.composition (a := a) (b := b) (c := d) e (f.compWith g W.pair23 (NativeDecode.filling b)
      (NativeDecode.filling_lawful b) (NativeDecode.filling d) (NativeDecode.filling_lawful d)) W.triple123R
      s)

noncomputable def binary_qrtL (s : Term (HomotopyLevels.isSet (liftedDecode k))) :
    Cell (W.qrtL e f g h) (concat (W.qr e f g h) (W.t e f g h)) :=
  Term.convert (congrArg₂ (homogeneousPath (Whole y v))
    (W.qrtL_eq e f g h).symm
    (congrArg₂ (homogeneousConcat (objectsFilling description Γ).1 (objectsFilling description Γ).2) (W.qr_eq
      e f g h) (W.t_eq e f g h)).symm)
    (Coded.composition (a := b) (b := d) (c := k) (f.compWith g W.pair23 (NativeDecode.filling b)
      (NativeDecode.filling_lawful b) (NativeDecode.filling d) (NativeDecode.filling_lawful d)) h W.triple234L
      s)

noncomputable def binary_qrtR (s : Term (HomotopyLevels.isSet (liftedDecode k))) :
    Cell (W.qrtR e f g h) (concat (W.q e f g h) (W.rt e f g h)) :=
  Term.convert (congrArg₂ (homogeneousPath (Whole y v))
    (W.qrtR_eq e f g h).symm
    (congrArg₂ (homogeneousConcat (objectsFilling description Γ).1 (objectsFilling description Γ).2) (W.q_eq e
      f g h) (W.rt_eq e f g h)).symm)
    (Coded.composition (a := b) (b := c) (c := k) f (g.compWith h W.pair34 (NativeDecode.filling c)
      (NativeDecode.filling_lawful c) (NativeDecode.filling k) (NativeDecode.filling_lawful k)) W.triple234R
      s)

noncomputable def binary_v0 (s : Term (HomotopyLevels.isSet (liftedDecode k))) :
    Cell (W.v0 e f g h) (concat (W.pqrL e f g h) (W.t e f g h)) :=
  Term.convert (congrArg₂ (homogeneousPath (Whole x v))
    (W.v0_eq e f g h).symm
    (congrArg₂ (homogeneousConcat (objectsFilling description Γ).1 (objectsFilling description Γ).2)
      (W.pqrL_eq e f g h) (W.t_eq e f g h)).symm)
    (Coded.composition (a := a) (b := d) (c := k) ((e.compWith f W.pair12 (NativeDecode.filling a)
      (NativeDecode.filling_lawful a) (NativeDecode.filling c) (NativeDecode.filling_lawful c)).compWith g
      W.triple123L (NativeDecode.filling a) (NativeDecode.filling_lawful a) (NativeDecode.filling d)
      (NativeDecode.filling_lawful d)) h W.outer0 s)

noncomputable def binary_v1 (s : Term (HomotopyLevels.isSet (liftedDecode k))) :
    Cell (W.v1 e f g h) (concat (W.pqrR e f g h) (W.t e f g h)) :=
  Term.convert (congrArg₂ (homogeneousPath (Whole x v))
    (W.v1_eq e f g h).symm
    (congrArg₂ (homogeneousConcat (objectsFilling description Γ).1 (objectsFilling description Γ).2)
      (W.pqrR_eq e f g h) (W.t_eq e f g h)).symm)
    (Coded.composition (a := a) (b := d) (c := k) (e.compWith (f.compWith g W.pair23 (NativeDecode.filling b)
      (NativeDecode.filling_lawful b) (NativeDecode.filling d) (NativeDecode.filling_lawful d)) W.triple123R
      (NativeDecode.filling a) (NativeDecode.filling_lawful a) (NativeDecode.filling d)
      (NativeDecode.filling_lawful d)) h W.outer1 s)

noncomputable def binary_v2 (s : Term (HomotopyLevels.isSet (liftedDecode k))) :
    Cell (W.v2 e f g h) (concat (W.p e f g h) (W.qrtL e f g h)) :=
  Term.convert (congrArg₂ (homogeneousPath (Whole x v))
    (W.v2_eq e f g h).symm
    (congrArg₂ (homogeneousConcat (objectsFilling description Γ).1 (objectsFilling description Γ).2) (W.p_eq e
      f g h) (W.qrtL_eq e f g h)).symm)
    (Coded.composition (a := a) (b := b) (c := k) e ((f.compWith g W.pair23 (NativeDecode.filling b)
      (NativeDecode.filling_lawful b) (NativeDecode.filling d) (NativeDecode.filling_lawful d)).compWith h
      W.triple234L (NativeDecode.filling b) (NativeDecode.filling_lawful b) (NativeDecode.filling k)
      (NativeDecode.filling_lawful k)) W.outer2 s)

noncomputable def binary_v3 (s : Term (HomotopyLevels.isSet (liftedDecode k))) :
    Cell (W.v3 e f g h) (concat (W.p e f g h) (W.qrtR e f g h)) :=
  Term.convert (congrArg₂ (homogeneousPath (Whole x v))
    (W.v3_eq e f g h).symm
    (congrArg₂ (homogeneousConcat (objectsFilling description Γ).1 (objectsFilling description Γ).2) (W.p_eq e
      f g h) (W.qrtR_eq e f g h)).symm)
    (Coded.composition (a := a) (b := b) (c := k) e (f.compWith (g.compWith h W.pair34 (NativeDecode.filling
      c) (NativeDecode.filling_lawful c) (NativeDecode.filling k) (NativeDecode.filling_lawful k))
      W.triple234R (NativeDecode.filling b) (NativeDecode.filling_lawful b) (NativeDecode.filling k)
      (NativeDecode.filling_lawful k)) W.outer3 s)

noncomputable def binary_v4 (s : Term (HomotopyLevels.isSet (liftedDecode k))) :
    Cell (W.v4 e f g h) (concat (W.pq e f g h) (W.rt e f g h)) :=
  Term.convert (congrArg₂ (homogeneousPath (Whole x v))
    (W.v4_eq e f g h).symm
    (congrArg₂ (homogeneousConcat (objectsFilling description Γ).1 (objectsFilling description Γ).2) (W.pq_eq
      e f g h) (W.rt_eq e f g h)).symm)
    (Coded.composition (a := a) (b := c) (c := k) (e.compWith f W.pair12 (NativeDecode.filling a)
      (NativeDecode.filling_lawful a) (NativeDecode.filling c) (NativeDecode.filling_lawful c)) (g.compWith h
      W.pair34 (NativeDecode.filling c) (NativeDecode.filling_lawful c) (NativeDecode.filling k)
      (NativeDecode.filling_lawful k)) W.outer4 s)

noncomputable def normalization0 (sZ : Term (HomotopyLevels.isSet (liftedDecode c))) (sW : Term
  (HomotopyLevels.isSet (liftedDecode d))) (sV : Term (HomotopyLevels.isSet (liftedDecode k))) :
    Cell (W.v0 e f g h) (concat (concat (concat (W.p e f g h) (W.q e f g h)) (W.r e f g h)) (W.t e f g h)) :=
  (vertical (W.binary_v0 e f g h sV) (whiskerRight (vertical (W.binary_pqrL e f g h sW) (whiskerRight
    (W.binary_pq e f g h sZ) (W.r e f g h))) (W.t e f g h)))

noncomputable def normalization1 (sW : Term (HomotopyLevels.isSet (liftedDecode d))) (sV : Term (HomotopyLevels.isSet (liftedDecode k))) :
    Cell (W.v1 e f g h) (concat (concat (W.p e f g h) (concat (W.q e f g h) (W.r e f g h))) (W.t e f g h)) :=
  (vertical (W.binary_v1 e f g h sV) (whiskerRight (vertical (W.binary_pqrR e f g h sW) (whiskerLeft (W.p e f
    g h) (W.binary_qr e f g h sW))) (W.t e f g h)))

noncomputable def normalization2 (sW : Term (HomotopyLevels.isSet (liftedDecode d))) (sV : Term (HomotopyLevels.isSet (liftedDecode k))) :
    Cell (W.v2 e f g h) (concat (W.p e f g h) (concat (concat (W.q e f g h) (W.r e f g h)) (W.t e f g h))) :=
  (vertical (W.binary_v2 e f g h sV) (whiskerLeft (W.p e f g h) (vertical (W.binary_qrtL e f g h sV)
    (whiskerRight (W.binary_qr e f g h sW) (W.t e f g h)))))

noncomputable def normalization3 (sV : Term (HomotopyLevels.isSet (liftedDecode k))) :
    Cell (W.v3 e f g h) (concat (W.p e f g h) (concat (W.q e f g h) (concat (W.r e f g h) (W.t e f g h)))) :=
  (vertical (W.binary_v3 e f g h sV) (whiskerLeft (W.p e f g h) (vertical (W.binary_qrtR e f g h sV)
    (whiskerLeft (W.q e f g h) (W.binary_rt e f g h sV)))))

noncomputable def normalization4 (sZ : Term (HomotopyLevels.isSet (liftedDecode c))) (sV : Term (HomotopyLevels.isSet (liftedDecode k))) :
    Cell (W.v4 e f g h) (concat (concat (W.p e f g h) (W.q e f g h)) (concat (W.r e f g h) (W.t e f g h))) :=
  (vertical (vertical (W.binary_v4 e f g h sV) (whiskerRight (W.binary_pq e f g h sZ) (W.rt e f g h)))
    (whiskerLeft (concat (W.p e f g h) (W.q e f g h)) (W.binary_rt e f g h sV)))


noncomputable def edge01 (sZ : Term (HomotopyLevels.isSet (liftedDecode c))) (sW : Term (HomotopyLevels.isSet
  (liftedDecode d))) (sV : Term (HomotopyLevels.isSet (liftedDecode k))) : Cell (W.v0 e f g h) (W.v1 e f g h)
  :=
  (vertical (vertical (W.normalization0 e f g h sZ sW sV) (whiskerRight (associator sW (W.p e f g h) (W.q e f
    g h) (W.r e f g h)) (W.t e f g h))) (reverse (W.normalization1 e f g h sW sV)))

noncomputable def edge12 (sW : Term (HomotopyLevels.isSet (liftedDecode d))) (sV : Term (HomotopyLevels.isSet
  (liftedDecode k))) : Cell (W.v1 e f g h) (W.v2 e f g h) :=
  (vertical (vertical (W.normalization1 e f g h sW sV) (associator sV (W.p e f g h) (concat (W.q e f g h) (W.r
    e f g h)) (W.t e f g h))) (reverse (W.normalization2 e f g h sW sV)))

noncomputable def edge23 (sW : Term (HomotopyLevels.isSet (liftedDecode d))) (sV : Term (HomotopyLevels.isSet
  (liftedDecode k))) : Cell (W.v2 e f g h) (W.v3 e f g h) :=
  (vertical (vertical (W.normalization2 e f g h sW sV) (whiskerLeft (W.p e f g h) (associator sV (W.q e f g h)
    (W.r e f g h) (W.t e f g h)))) (reverse (W.normalization3 e f g h sV)))

noncomputable def edge04 (sZ : Term (HomotopyLevels.isSet (liftedDecode c))) (sW : Term (HomotopyLevels.isSet
  (liftedDecode d))) (sV : Term (HomotopyLevels.isSet (liftedDecode k))) : Cell (W.v0 e f g h) (W.v4 e f g h)
  :=
  (vertical (vertical (W.normalization0 e f g h sZ sW sV) (associator sV (concat (W.p e f g h) (W.q e f g h))
    (W.r e f g h) (W.t e f g h))) (reverse (W.normalization4 e f g h sZ sV)))

noncomputable def edge43 (sZ : Term (HomotopyLevels.isSet (liftedDecode c))) (sV : Term (HomotopyLevels.isSet
  (liftedDecode k))) : Cell (W.v4 e f g h) (W.v3 e f g h) :=
  (vertical (vertical (W.normalization4 e f g h sZ sV) (associator sV (W.p e f g h) (W.q e f g h) (concat (W.r
    e f g h) (W.t e f g h)))) (reverse (W.normalization3 e f g h sV)))

noncomputable def selectedPentagon (sZ : Term (HomotopyLevels.isSet (liftedDecode c)))
    (sW : Term (HomotopyLevels.isSet (liftedDecode d))) (sV : Term (HomotopyLevels.isSet (liftedDecode k))) :=
  compareCells sV
    (vertical (vertical (W.edge01 e f g h sZ sW sV) (W.edge12 e f g h sW sV))
      (W.edge23 e f g h sW sV))
    (vertical (W.edge04 e f g h sZ sW sV) (W.edge43 e f g h sZ sV))
end FourWitnesses

end SquareKit.Cubical.Presheaf.StructureIdentity.Coherence.Finite
