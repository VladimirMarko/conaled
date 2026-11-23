import SquareKit.SmoothCoordinatePullbacks
import SquareKit.SmoothOpenPullback

/-! Ordinary coordinate maps and their all-stage principal-open pullbacks. -/
noncomputable section
namespace SquareKit.EuclideanOpen.Coordinates
open CategoryTheory CategoryTheory.Limits Opposite SmoothAlgebra SmoothPresentationSite Localization

/-- A tuple of globally smooth operations is an actual ordinary map of full domains. -/
def coordinateMap {m n : ℕ} (g : Fin n → Operation m) : full m ⟶ full n where
  toFun x := ⟨fun i => (g i).val x.val, one_ne_zero⟩
  smooth i := (OpenFunctions.representative_iff _ (g i).val (fun _ => rfl)).mpr
    (g i).property.contDiffOn

theorem coordinateMap_base {m n : ℕ} (g : Fin n → Operation m) (i : Fin n) :
    Localization.pullback (coordinateMap g) (principalBase 1 (generator i)) =
      principalBase 1 (g i) := by
  apply (toOpen_bijective (1 : Free m)).injective
  apply OpenFunctions.ext
  intro x
  rw [Localization.pullback_apply, toOpen_base]
  exact (toOpen_base (1 : Free m) (show Free m from g i) x).symm

theorem coordinateMap_comparison {m n : ℕ} (g : Fin n → Operation m) :
    embedding.map (coordinateMap g) ≫ (fullPowerIso n).hom =
      (fullPowerIso m).hom ≫ SmoothOpenSite.tuple (fun i => SmoothOpenSite.operation (g i)) := by
  ext A a
  funext i
  change smoothMap a.unop (Localization.pullback (coordinateMap g) (principalBase 1 (generator i))) =
    act (g i) (fun j => smoothMap a.unop (principalBase 1 (generator j)))
  rw [coordinateMap_base]
  exact congrArg (fun h : Hom (Free m) (Carrier A.unop.unop) => h (g i))
    (evaluate_unique ((smoothMap a.unop).comp (principalBase 1))).symm

def first (n k : ℕ) : full (n+k) ⟶ full n :=
  coordinateMap (fun i => projection (Fin.castAdd k i))

def last (n k : ℕ) : full (n+k) ⟶ full k :=
  coordinateMap (fun i => projection (Fin.natAdd n i))

def toPoint (n : ℕ) : full n ⟶ full 0 := coordinateMap Fin.elim0

def zero (k : ℕ) : full 0 ⟶ full k := coordinateMap (fun _ => constant 0 0)

def insertZero (n k : ℕ) : full n ⟶ full (n+k) :=
  coordinateMap (Fin.addCases projection (fun _ => constant n 0))

theorem first_comparison (n k : ℕ) :
    embedding.map (first n k) ≫ (fullPowerIso n).hom =
      (fullPowerIso (n+k)).hom ≫ SmoothOpenSite.Coordinates.first n k := by
  rw [first, coordinateMap_comparison]
  congr 1
  ext A x
  funext i
  exact Structure.projection _ _

theorem last_comparison (n k : ℕ) :
    embedding.map (last n k) ≫ (fullPowerIso k).hom =
      (fullPowerIso (n+k)).hom ≫ SmoothOpenSite.Coordinates.last n k := by
  rw [last, coordinateMap_comparison]
  congr 1
  ext A x
  funext i
  exact Structure.projection _ _

theorem toPoint_comparison (n : ℕ) :
    embedding.map (toPoint n) ≫ (fullPowerIso 0).hom =
      (fullPowerIso n).hom ≫ SmoothOpenSite.Coordinates.toPoint n :=
  SmoothOpenSite.Coordinates.point_unique _ _

theorem zero_comparison (k : ℕ) :
    embedding.map (zero k) ≫ (fullPowerIso k).hom =
      (fullPowerIso 0).hom ≫ SmoothOpenSite.Coordinates.zero k :=
  coordinateMap_comparison _

set_option backward.isDefEq.respectTransparency false in
set_option backward.isDefEq.respectTransparency.types false in
theorem insertZero_comparison (n k : ℕ) :
    embedding.map (insertZero n k) ≫ (fullPowerIso (n+k)).hom =
      (fullPowerIso n).hom ≫ SmoothOpenSite.Coordinates.insertZero n k := by
  rw [insertZero, coordinateMap_comparison]
  congr 1
  ext A x
  apply Eq.trans (b := Fin.addCases x (fun _ => 0))
  · funext i
    refine Fin.addCases (fun j => ?_) (fun j => ?_) i
    · change act (Fin.addCases projection (fun _ => constant n 0) (Fin.castAdd k j)) x = _
      simp [Structure.projection]
    · change act (Fin.addCases projection (fun _ => constant n 0) (Fin.natAdd n j)) x = _
      simp [Structure.constant]
  · exact (SmoothOpenSite.Coordinates.insertZero_apply n k A.unop.unop x).symm

theorem product_isPullback (n k : ℕ) :
    IsPullback (embedding.map (first n k)) (embedding.map (last n k))
      (embedding.map (toPoint n)) (embedding.map (toPoint k)) :=
  (SmoothOpenSite.Coordinates.product_isPullback n k).of_iso'
    (fullPowerIso (n+k)) (fullPowerIso n) (fullPowerIso k) (fullPowerIso 0)
    (first_comparison n k).symm (last_comparison n k).symm
    (toPoint_comparison n).symm (toPoint_comparison k).symm

theorem zeroFiber_isPullback (n k : ℕ) :
    IsPullback (embedding.map (insertZero n k)) (embedding.map (toPoint n))
      (embedding.map (last n k)) (embedding.map (zero k)) :=
  (SmoothOpenSite.Coordinates.zeroFiber_isPullback n k).of_iso'
    (fullPowerIso n) (fullPowerIso (n+k)) (fullPowerIso 0) (fullPowerIso k)
    (insertZero_comparison n k).symm (toPoint_comparison n).symm
    (last_comparison n k).symm (zero_comparison k).symm

/-- The coordinate zero fiber inside any ordinary principal ambient open. -/
theorem restricted_zeroFiber_isPullback (n k : ℕ) (q : Free (n+k)) :
    IsPullback (embedding.map (inverseRestriction (insertZero n k) q))
      (embedding.map (subInclusion (full n) (inverseDefining (insertZero n k) q) ≫ toPoint n))
      (embedding.map (subInclusion (full (n+k)) q ≫ last n k)) (embedding.map (zero k)) := by
  simpa only [embedding.map_comp] using
    (inverse_sheaf_pullback (insertZero n k) q).flip.paste_vert (zeroFiber_isPullback n k)

theorem restricted_points (n k : ℕ) (q : Free (n+k)) (x : Points (full n)) :
    (inverseDefining (insertZero n k) q).val x.val ≠ 0 ↔
      q.val (Fin.addCases x.val (fun _ => 0)) ≠ 0 := by
  rw [inverseDefining_iff]
  have he : ((insertZero n k).toFun x).val = Fin.addCases x.val (fun _ => 0) := by
    funext i
    refine Fin.addCases (fun j => ?_) (fun j => ?_) i
    · change (Fin.addCases (motive := fun _ => Operation n) projection (fun _ => constant n 0) (Fin.castAdd k j)).val x.val = _
      simp [SmoothAlgebra.projection]
    · change (Fin.addCases (motive := fun _ => Operation n) projection (fun _ => constant n 0) (Fin.natAdd n j)).val x.val = _
      simp [constant]
  rw [he]

/-- Restriction of any established ordinary square along a principal open in
its upper-right corner. This can be iterated without identifying chosen support functions. -/
theorem restrict_isPullback {P X Y Z : Domain} (fst : P ⟶ X) (snd : P ⟶ Y)
    (f : X ⟶ Z) (g : Y ⟶ Z)
    (h : IsPullback (embedding.map fst) (embedding.map snd) (embedding.map f) (embedding.map g))
    (q : Free X.dimension) :
    IsPullback (embedding.map (inverseRestriction fst q))
      (embedding.map (subInclusion P (inverseDefining fst q) ≫ snd))
      (embedding.map (subInclusion X q ≫ f)) (embedding.map g) := by
  simpa only [embedding.map_comp] using (inverse_sheaf_pullback fst q).flip.paste_vert h

/-- A second principal restriction retains the composite actual projections. -/
theorem twice_restricted_zeroFiber_isPullback (n k : ℕ) (q r : Free (n+k)) :
    IsPullback
      (embedding.map (inverseRestriction (inverseRestriction (insertZero n k) q) r))
      (embedding.map
        (subInclusion (subdomain (full n) (inverseDefining (insertZero n k) q))
            (inverseDefining (inverseRestriction (insertZero n k) q) r) ≫
          (subInclusion (full n) (inverseDefining (insertZero n k) q) ≫ toPoint n)))
      (embedding.map (subInclusion (subdomain (full (n+k)) q) r ≫
        (subInclusion (full (n+k)) q ≫ last n k))) (embedding.map (zero k)) :=
  restrict_isPullback _ _ _ _ (restricted_zeroFiber_isPullback n k q) r

/-- The chosen ordinary inverse image commutes with both actual localization
bases, even though its defining function is selected by smooth support. -/
theorem inverse_localization_square {U V : Domain} (f : U ⟶ V) (q : Free V.dimension) :
    (localizationBase (code V) (element V q) ≫ (subdomainIso V q).hom) ≫
      (show code (subdomain V q) ⟶ code (subdomain U (inverseDefining f q)) from
        Localization.pullback (inverseRestriction f q)) =
      (show code V ⟶ code U from Localization.pullback f) ≫
        (localizationBase (code U) (element U (inverseDefining f q)) ≫
          (subdomainIso U (inverseDefining f q)).hom) := by
  change (localizationBase (code V) (element V q) ≫ toSubdomain V q) ≫ _ =
    _ ≫ (localizationBase (code U) (element U (inverseDefining f q)) ≫
      toSubdomain U (inverseDefining f q))
  rw [toSubdomain_base, toSubdomain_base]
  exact (Localization.pullback_comp (inverseRestriction f q) (subInclusion V q)).symm.trans
    ((congrArg (fun a : Map (subdomain U (inverseDefining f q)) V => Localization.pullback a)
      (inverseRestriction_square f q)).trans
      (Localization.pullback_comp (subInclusion U (inverseDefining f q)) f))

end SquareKit.EuclideanOpen.Coordinates

namespace SquareKit.EuclideanOpen
open CategoryTheory CategoryTheory.Limits SmoothAlgebra

/-- Empty-cover gluing constructs the unique arrow into every sheaf. -/
def emptyDomainIsInitial (U : Domain) (hU : IsEmpty (Points U)) :
    IsInitial (embedding.obj U) := by
  let g : Fin 0 → Free U.dimension := Fin.elim0
  have hc : Covers U g := (empty_cover_iff U g).mpr hU
  have hu (F : Sheaf SmoothOpenSite.topology Type) :
      ∃! b : embedding.obj U ⟶ F, ∀ i : Fin 0,
        embedding.map (subInclusion U (g i)) ≫ b =
          (Fin.elim0 i : embedding.obj (subdomain U (g i)) ⟶ F) :=
    sheaf_exists_unique U g hc F (fun i => Fin.elim0 i) (fun i => Fin.elim0 i)
  exact IsInitial.ofUniqueHom (fun F => (hu F).choose)
    (fun F b => (hu F).choose_spec.2 b (fun i => Fin.elim0 i))

theorem isEmpty_points_subdomain_zero (U : Domain) : IsEmpty (Points (subdomain U 0)) := by
  refine ⟨fun x => ?_⟩
  have h := x.property
  change U.defining.val x.val * (0 : ℝ) ≠ 0 at h
  exact h (mul_zero _)

def zeroSubdomainIsInitial (U : Domain) : IsInitial (embedding.obj (subdomain U 0)) :=
  emptyDomainIsInitial _ (isEmpty_points_subdomain_zero U)

/-- The inverse image of an empty principal open is initial as well. -/
def inverseEmptyIsInitial {U V : Domain} (f : U ⟶ V) (q : Free V.dimension)
    (h : IsEmpty (Points (subdomain V q))) :
    IsInitial (embedding.obj (subdomain U (inverseDefining f q))) :=
  emptyDomainIsInitial _ ⟨fun x => h.false ((inverseRestriction f q).toFun x)⟩


end SquareKit.EuclideanOpen
