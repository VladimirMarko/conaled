import SquareKit.SmoothClutchingScaling

/-! Principal-open refinements of the actual doubled-origin atlas. -/
noncomputable section
open scoped ContDiff
namespace SquareKit.SmoothClutching.Refined
open CategoryTheory CategoryTheory.Limits Opposite EuclideanOpen SmoothOpenSite SmoothAlgebra

def principal (f : freeAlgebra 1) : Domain := ⟨1, f⟩

def inclusionOf {f g : freeAlgebra 1} (h : ∀ x, f.val x ≠ 0 → g.val x ≠ 0) :
    principal f ⟶ principal g where
  toFun x := ⟨x.val, h x.val x.property⟩
  smooth i := (OpenFunctions.representative_iff _ (fun x => x i) (fun _ => rfl)).mpr
    (contDiff_apply ℝ (fun _ : Fin 1 => ℝ) i).contDiffOn

def toLine (f : freeAlgebra 1) : principal f ⟶ line :=
  inclusionOf (fun _ _ => one_ne_zero)

def intersectionLeft (f g : freeAlgebra 1) : principal (f*g) ⟶ principal f :=
  inclusionOf (fun _ h => left_ne_zero_of_mul h)

def intersectionRight (f g : freeAlgebra 1) : principal (f*g) ⟶ principal g :=
  inclusionOf (fun _ h => right_ne_zero_of_mul h)

def locusIso (f g : freeAlgebra 1) (h : ∀ x, f.val x ≠ 0 ↔ g.val x ≠ 0) :
    principal f ≅ principal g where
  hom := inclusionOf (fun x => (h x).mp)
  inv := inclusionOf (fun x => (h x).mpr)
  hom_inv_id := OpenFunctions.Map.ext (fun _ => rfl)
  inv_hom_id := OpenFunctions.Map.ext (fun _ => rfl)

theorem intersection_pullback (f g : freeAlgebra 1) :
    IsPullback (embedding.map (intersectionLeft f g)) (embedding.map (intersectionRight f g))
      (embedding.map (toLine f)) (embedding.map (toLine g)) := by
  let e₁ : EuclideanOpen.overlap line f g ≅ principal (f*g) := locusIso ((1*f)*g) (f*g) (fun x => by simp)
  let e₂ : subdomain line f ≅ principal f := locusIso (1*f) f (fun x => by simp)
  let e₃ : subdomain line g ≅ principal g := locusIso (1*g) g (fun x => by simp)
  apply (overlap_sheaf_pullback line f g).of_iso
    (embedding.mapIso e₁) (embedding.mapIso e₂) (embedding.mapIso e₃) (Iso.refl _)
  all_goals
    simp only [Functor.mapIso_hom, Iso.refl_hom, Category.comp_id]
    first
    | rw [← Functor.map_comp, ← Functor.map_comp]
      exact congrArg embedding.map (OpenFunctions.Map.ext (fun _ => rfl))
    | rw [← Functor.map_comp]
      exact congrArg embedding.map (OpenFunctions.Map.ext (fun _ => rfl))

theorem mixed_origin_pullback : IsPullback (embedding.map (toLine (generator 0)))
    (embedding.map (toLine (generator 0))) left right := by
  let e : punctured ≅ principal (generator 0) :=
    locusIso (1 * generator 0) (generator 0) (fun x => by simp)
  apply SmoothClutching.overlap.of_iso (embedding.mapIso e)
    (Iso.refl _) (Iso.refl _) (Iso.refl _)
  · simp only [Iso.refl_hom, Category.comp_id, Functor.mapIso_hom]
    rw [← Functor.map_comp]
    exact congrArg embedding.map (OpenFunctions.Map.ext (fun _ => rfl))
  · simp only [Iso.refl_hom, Category.comp_id, Functor.mapIso_hom]
    rw [← Functor.map_comp]
    exact congrArg embedding.map (OpenFunctions.Map.ext (fun _ => rfl))
  · simp
  · simp

def mixedLeft (f g : freeAlgebra 1) : principal ((f * generator 0) * g) ⟶ principal f :=
  intersectionLeft (f * generator 0) g ≫ intersectionLeft f (generator 0)

theorem mixed_pullback_of (f g : freeAlgebra 1) (a b : lineSheaf ⟶ base)
    (hab : IsPullback (embedding.map (toLine (generator 0)))
      (embedding.map (toLine (generator 0))) a b) :
    IsPullback (embedding.map (mixedLeft f g))
      (embedding.map (intersectionRight (f * generator 0) g))
      (embedding.map (toLine f) ≫ a) (embedding.map (toLine g) ≫ b) := by
  have h := (intersection_pullback f (generator 0)).paste_vert hab
  have he : intersectionRight f (generator 0) ≫ toLine (generator 0) = toLine (f * generator 0) :=
    OpenFunctions.Map.ext (fun _ => rfl)
  rw [← Functor.map_comp, he] at h
  simpa only [mixedLeft, Functor.map_comp] using
    (intersection_pullback (f * generator 0) g).paste_horiz h

theorem same_origin_pullback (f g : freeAlgebra 1) (j : lineSheaf ⟶ base) [Mono j] :
    IsPullback (embedding.map (intersectionLeft f g)) (embedding.map (intersectionRight f g))
      (embedding.map (toLine f) ≫ j) (embedding.map (toLine g) ≫ j) := by
  have h : IsPullback (embedding.map (toLine g)) (𝟙 _) j (embedding.map (toLine g) ≫ j) :=
    IsPullback.of_vert_isIso_mono ⟨by simp⟩
  simpa only [Category.comp_id] using (intersection_pullback f g).paste_vert h

def product : Bool → Bool → freeAlgebra 1 → freeAlgebra 1 → freeAlgebra 1
  | false, false, f, g => f*g
  | true, true, f, g => f*g
  | _, _, f, g => (f * generator 0) * g

def productLeft (i j : Bool) (f g : freeAlgebra 1) : principal (product i j f g) ⟶ principal f :=
  inclusionOf (by
    intro x hx
    cases i <;> cases j
    · exact left_ne_zero_of_mul hx
    · exact left_ne_zero_of_mul (left_ne_zero_of_mul hx)
    · exact left_ne_zero_of_mul (left_ne_zero_of_mul hx)
    · exact left_ne_zero_of_mul hx)

def productRight (i j : Bool) (f g : freeAlgebra 1) : principal (product i j f g) ⟶ principal g :=
  inclusionOf (by intro x hx; cases i <;> cases j <;> exact right_ne_zero_of_mul hx)

theorem product_pullback (i j : Bool) (f g : freeAlgebra 1) :
    IsPullback (embedding.map (productLeft i j f g)) (embedding.map (productRight i j f g))
      (embedding.map (toLine f) ≫ Represented.chart i)
      (embedding.map (toLine g) ≫ Represented.chart j) := by
  cases i <;> cases j
  · have hl : productLeft false false f g = intersectionLeft f g := OpenFunctions.Map.ext (fun _ => rfl)
    have hr : productRight false false f g = intersectionRight f g := OpenFunctions.Map.ext (fun _ => rfl)
    rw [hl, hr]
    exact same_origin_pullback f g left
  · have hl : productLeft false true f g = mixedLeft f g := OpenFunctions.Map.ext (fun _ => rfl)
    have hr : productRight false true f g = intersectionRight (f * generator 0) g := OpenFunctions.Map.ext (fun _ => rfl)
    rw [hl, hr]
    exact mixed_pullback_of f g left right mixed_origin_pullback
  · have hl : productLeft true false f g = mixedLeft f g := OpenFunctions.Map.ext (fun _ => rfl)
    have hr : productRight true false f g = intersectionRight (f * generator 0) g := OpenFunctions.Map.ext (fun _ => rfl)
    rw [hl, hr]
    exact mixed_pullback_of f g right left mixed_origin_pullback.flip
  · have hl : productLeft true true f g = intersectionLeft f g := OpenFunctions.Map.ext (fun _ => rfl)
    have hr : productRight true true f g = intersectionRight f g := OpenFunctions.Map.ext (fun _ => rfl)
    rw [hl, hr]
    exact same_origin_pullback f g right

theorem principal_covering {K : Type} (f : K → freeAlgebra 1) (hf : Covers line f)
    {V : SmoothPresentationSite.Site} (y : lineSheaf.obj.obj (op V)) :
    SheafCoproductLocal.liftSieve (fun k => embedding.obj (principal (f k)))
      (fun k => embedding.map (toLine (f k))) y ∈ topology V := by
  apply topology.superset_covering _ (topology.pullback_stable y (covering line f hf))
  intro W r hr
  rcases hr with ⟨Z, t, a, ⟨k⟩, he⟩
  let e : subdomain line (f k) ≅ principal (f k) :=
    locusIso (1 * f k) (f k) (fun x => by simp)
  refine ⟨k, t ≫ toSite.map e.hom, ?_⟩
  change (t ≫ toSite.map e.hom) ≫ toSite.map (toLine (f k)) = r ≫ y
  rw [Category.assoc, ← Functor.map_comp]
  have eh : e.hom ≫ toLine (f k) = subInclusion line (f k) :=
    OpenFunctions.Map.ext (fun _ => rfl)
  rw [eh]
  exact he

def refinedChart {K : Type} (f : K → freeAlgebra 1) (i : Bool × K) :
    embedding.obj (principal (f i.2)) ⟶ base :=
  embedding.map (toLine (f i.2)) ≫ Represented.chart i.1

theorem refined_covering {K : Type} (f : K → freeAlgebra 1) (hf : Covers line f)
    (V : SmoothPresentationSite.Site) (x : base.obj.obj (op V)) :
    SheafCoproductLocal.liftSieve (fun i : Bool × K => embedding.obj (principal (f i.2)))
      (refinedChart f) x ∈ topology V := by
  apply topology.transitive (Represented.atlas.covering V x)
  intro W r hr
  obtain ⟨i, y, hy⟩ := hr
  change lineSheaf.obj.obj (op W) at y
  change (Represented.chart i).hom.app (op W) y = base.obj.map r.op x at hy
  apply topology.superset_covering _ (principal_covering f hf y)
  intro Z t ht
  obtain ⟨k, z, hz⟩ := ht
  refine ⟨(i,k), z, ?_⟩
  change (Represented.chart i).hom.app (op Z) ((embedding.map (toLine (f k))).hom.app (op Z) z) =
    base.obj.map (t ≫ r).op x
  rw [hz, NatTrans.naturality_apply, hy]
  exact (ConcreteCategory.congr_hom (base.obj.map_comp r.op t.op) x).symm

def atlas {K : Type} (f : K → freeAlgebra 1) (hf : Covers line f) :
    SmoothRepresentedCover.Atlas base (Bool × K) where
  domain i := principal (f i.2)
  chart := refinedChart f
  covering := refined_covering f hf
  pair i j := principal (product i.1 j.1 (f i.2) (f j.2))
  left i j := productLeft i.1 j.1 (f i.2) (f j.2)
  right i j := productRight i.1 j.1 (f i.2) (f j.2)
  square i j := product_pullback i.1 j.1 (f i.2) (f j.2)
  triple i j k := principal (product i.1 k.1 (product i.1 j.1 (f i.2) (f j.2)) (f k.2))
  firstSecond i j k := productLeft i.1 k.1 (product i.1 j.1 (f i.2) (f j.2)) (f k.2)
  third i j k := productRight i.1 k.1 (product i.1 j.1 (f i.2) (f j.2)) (f k.2)
  tripleSquare i j k := by
    have he : productLeft i.1 j.1 (f i.2) (f j.2) ≫ toLine (f i.2) =
        toLine (product i.1 j.1 (f i.2) (f j.2)) := OpenFunctions.Map.ext (fun _ => rfl)
    change IsPullback _ _ (_ ≫ (embedding.map (toLine _) ≫ _)) _
    rw [← Category.assoc, ← Functor.map_comp, he]
    exact product_pullback i.1 k.1 (product i.1 j.1 (f i.2) (f j.2)) (f k.2)

def refinement {K : Type} (f : K → freeAlgebra 1) (hf : Covers line f) :
    SmoothRepresentedCover.AtlasMap Represented.atlas (atlas f hf) (𝟙 base) where
  index := Prod.fst
  chart i := toLine (f i.2)
  commutes _ := by simp only [Category.comp_id]; rfl

def hole (a : ℝ) : freeAlgebra 1 := generator 0 - algebraMap ℝ (freeAlgebra 1) a

def punctures (a : ℝ) : Bool → freeAlgebra 1
  | false => hole a
  | true => hole (-a)

theorem punctures_cover (a : ℝ) (ha : a ≠ 0) : Covers line (punctures a) := by
  intro x
  by_cases h : x.val 0 = a
  · refine ⟨true, ?_⟩
    change x.val 0 - (-a) ≠ 0
    rw [h]
    intro hz
    apply ha
    linarith
  · exact ⟨false, sub_ne_zero.mpr h⟩

def atlasOne := atlas (punctures 1) (punctures_cover 1 (by norm_num))
def atlasTwo := atlas (punctures 2) (punctures_cover 2 (by norm_num))

def commonFunctions (i : Bool × Bool) : freeAlgebra 1 := punctures 1 i.1 * punctures 2 i.2

theorem common_cover : Covers line commonFunctions := by
  intro x
  obtain ⟨i, hi⟩ := punctures_cover 1 (by norm_num) x
  obtain ⟨j, hj⟩ := punctures_cover 2 (by norm_num) x
  exact ⟨(i,j), mul_ne_zero hi hj⟩

def commonAtlas := atlas commonFunctions common_cover

def commonToOne : SmoothRepresentedCover.AtlasMap atlasOne commonAtlas (𝟙 base) where
  index i := (i.1, i.2.1)
  chart i := intersectionLeft (punctures 1 i.2.1) (punctures 2 i.2.2)
  commutes i := by
    dsimp only [atlasOne, atlasTwo, commonAtlas, atlas, refinedChart, commonFunctions]
    rw [Category.comp_id, ← Category.assoc, ← Functor.map_comp]
    congr 1

def commonToTwo : SmoothRepresentedCover.AtlasMap atlasTwo commonAtlas (𝟙 base) where
  index i := (i.1, i.2.2)
  chart i := intersectionRight (punctures 1 i.2.1) (punctures 2 i.2.2)
  commutes i := by
    dsimp only [atlasOne, atlasTwo, commonAtlas, atlas, refinedChart, commonFunctions]
    rw [Category.comp_id, ← Category.assoc, ← Functor.map_comp]
    congr 1

theorem hole_excludes (a : ℝ) : ¬ (fun _ : Fin 1 => a) ∈ Points (principal (hole a)) := by
  change ¬ a - a ≠ 0
  simp

theorem common_projection_one (i : Bool × (Bool × Bool)) :
    commonToOne.chart i ≫ (refinement (punctures 1) (punctures_cover 1 (by norm_num))).chart (commonToOne.index i) =
      (refinement commonFunctions common_cover).chart i := OpenFunctions.Map.ext (fun _ => rfl)

theorem common_projection_two (i : Bool × (Bool × Bool)) :
    commonToTwo.chart i ≫ (refinement (punctures 2) (punctures_cover 2 (by norm_num))).chart (commonToTwo.index i) =
      (refinement commonFunctions common_cover).chart i := OpenFunctions.Map.ext (fun _ => rfl)

def scaledFunction (r : ℝ) (f : freeAlgebra 1) : freeAlgebra 1 :=
  ⟨fun x => f.val (fun i => r * x i), (show ContDiff ℝ ∞ f.val from f.property).comp
    (contDiff_pi.mpr (fun i => contDiff_const.mul (contDiff_apply ℝ (fun _ : Fin 1 => ℝ) i)))⟩


theorem scaledFunction_one (f : freeAlgebra 1) : scaledFunction 1 f = f := by
  apply Subtype.ext
  funext x
  change f.val (fun i => 1 * x i) = f.val x
  simp only [one_mul]

theorem scaledFunction_comp (r s : ℝ) (f : freeAlgebra 1) :
    scaledFunction r (scaledFunction s f) = scaledFunction (s * r) f := by
  apply Subtype.ext
  funext x
  change f.val (fun i => s * (r * x i)) = f.val (fun i => (s * r) * x i)
  simp only [mul_assoc]

def principalScalingIso (r : ℝ) (hr : r ≠ 0) (f : freeAlgebra 1) :
    principal (scaledFunction r f) ≅ principal f where
  hom := {
    toFun x := ⟨fun i => r * x.val i, x.property⟩
    smooth i := (OpenFunctions.representative_iff _ (fun x => r * x i) (fun _ => rfl)).mpr
      (contDiff_const.mul (contDiff_apply ℝ (fun _ : Fin 1 => ℝ) i)).contDiffOn }
  inv := {
    toFun x := ⟨fun i => r⁻¹ * x.val i, by
      change f.val (fun i => r * (r⁻¹ * x.val i)) ≠ 0
      have hx : f.val x.val ≠ 0 := x.property
      simpa only [← mul_assoc, mul_inv_cancel₀ hr, one_mul] using hx⟩
    smooth i := (OpenFunctions.representative_iff _ (fun x => r⁻¹ * x i) (fun _ => rfl)).mpr
      (contDiff_const.mul (contDiff_apply ℝ (fun _ : Fin 1 => ℝ) i)).contDiffOn }
  hom_inv_id := by
    apply OpenFunctions.Map.ext
    intro x
    apply Subtype.ext
    funext i
    change r⁻¹ * (r * x.val i) = x.val i
    rw [← mul_assoc, inv_mul_cancel₀ hr, one_mul]
  inv_hom_id := by
    apply OpenFunctions.Map.ext
    intro x
    apply Subtype.ext
    funext i
    change r * (r⁻¹ * x.val i) = x.val i
    rw [← mul_assoc, mul_inv_cancel₀ hr, one_mul]

theorem scaling_inclusion (r : ℝ) (hr : r ≠ 0) (f : freeAlgebra 1) :
    (principalScalingIso r hr f).hom ≫ toLine f = toLine (scaledFunction r f) ≫ lineScale r :=
  OpenFunctions.Map.ext (fun _ => rfl)

theorem scaling_pullback (r : ℝ) (hr : r ≠ 0) (f : freeAlgebra 1) :
    IsPullback (embedding.map (principalScalingIso r hr f).hom)
      (embedding.map (toLine (scaledFunction r f)))
      (embedding.map (toLine f)) (embedding.map (lineScale r)) := by
  let : IsIso (embedding.map (lineScale r)) :=
    (embedding.mapIso (lineScalingIso r hr)).isIso_hom
  apply IsPullback.of_horiz_isIso
  exact ⟨by rw [← Functor.map_comp, ← Functor.map_comp, scaling_inclusion]⟩

theorem scaled_cover {K : Type} (f : K → freeAlgebra 1) (hf : Covers line f) (r : ℝ) :
    Covers line (fun k => scaledFunction r (f k)) := by
  intro x
  exact hf ((show EuclideanOpen.Map _ _ from lineScale r) x)

def scaledAtlasMap {K : Type} (f : K → freeAlgebra 1) (hf : Covers line f)
    (r : ℝ) (hr : r ≠ 0) :
    SmoothRepresentedCover.AtlasMap (atlas f hf)
      (atlas (fun k => scaledFunction r (f k)) (scaled_cover f hf r)) (baseScale r hr) where
  index := id
  chart i := (principalScalingIso r hr (f i.2)).hom
  commutes i := by
    dsimp only [atlas, refinedChart, id_eq]
    rw [← Category.assoc, ← Functor.map_comp, scaling_inclusion, Functor.map_comp,
      Category.assoc, Category.assoc]
    congr 1
    cases i.1
    · exact (left_baseScale r hr).symm
    · exact (right_baseScale r hr).symm

theorem scaled_chart_pullback {K : Type} (f : K → freeAlgebra 1) (hf : Covers line f)
    (r : ℝ) (hr : r ≠ 0) (i : Bool × K) :
    IsPullback (embedding.map ((scaledAtlasMap f hf r hr).chart i))
      ((atlas (fun k => scaledFunction r (f k)) (scaled_cover f hf r)).chart i)
      ((atlas f hf).chart i) (baseScale r hr) := by
  let : IsIso (baseScale r hr) := (baseScalingIso r hr).isIso_hom
  let : IsIso (embedding.map ((scaledAtlasMap f hf r hr).chart i)) :=
    (embedding.mapIso (principalScalingIso r hr (f i.2))).isIso_hom
  exact IsPullback.of_horiz_isIso ⟨(scaledAtlasMap f hf r hr).commutes i⟩

end SquareKit.SmoothClutching.Refined
