import SquareKit.Internal.Cubical.CartesianRestriction
import SquareKit.Internal.Cubical.IntervalExtension
import SquareKit.Internal.Cubical.Paths

/-! Relative interval products, evaluated and reconstructed at the generic cube. -/
set_option autoImplicit false
set_option warningAsError true
namespace SquareKit.Cubical.Presheaf
open CategoryTheory
universe u

def freshBase {Γ : Context.{u}} (x : Γ.Elements) : Γ.Elements :=
  Γ.elementsMk (.op (Cube.extend x.obj.unop)) (Γ.map (dropOpp x.obj) x.val)

def freshBaseHom {Γ : Context.{u}} (x : Γ.Elements) : x ⟶ freshBase x :=
  Functor.Elements.homMk (dropOpp x.obj) rfl

/-- Substitute an arbitrary generalized interval argument into the generic cube. -/
def intervalArgument {Γ : Context.{u}} {x y : Γ.Elements} (f : x ⟶ y)
    (r : (interval Γ).obj y) : freshExtension x ⟶ extendObj (interval Γ) y r :=
  Functor.Elements.homMk (Quiver.Hom.op (Cube.pair f.hom.unop r.down)) (by
    change (⟨Γ.map (Quiver.Hom.op (Cube.pair f.hom.unop r.down))
      (Γ.map (dropOpp x.obj) x.val),
      ULift.up (Cube.comp (Cube.pair f.hom.unop r.down) (Cube.fresh x.obj.unop))⟩ :
        (total (interval Γ)).obj y.obj) = ⟨y.val,r⟩
    have hc : dropOpp x.obj ≫ Quiver.Hom.op (Cube.pair f.hom.unop r.down) = f.hom :=
      congrArg Quiver.Hom.op (Cube.pair_drop f.hom.unop r.down)
    rw [← types_comp_apply, ← Γ.map_comp, hc, f.map_val, Cube.pair_fresh]
    cases r
    rfl)

/-- The coefficient is the actual dependent fiber at the fresh generalized point. -/
def intervalEvaluate {Γ : Context.{u}} {B : Family (total (interval Γ))}
    {x : Γ.Elements} (p : PiElement (interval Γ) B x) : B.obj (freshExtension x) :=
  p.val (freshBaseHom x) ⟨Cube.fresh x.obj.unop⟩

theorem intervalArgument_natural {Γ : Context.{u}} {x y z : Γ.Elements}
    (f : x ⟶ y) (g : y ⟶ z) (r : (interval Γ).obj y) :
    intervalArgument f r ≫ extendHom (interval Γ) g r =
      intervalArgument (f ≫ g) ((interval Γ).map g r) := by
  apply Functor.Elements.Hom.ext
  exact congrArg Quiver.Hom.op (Cube.comp_pair g.hom.unop f.hom.unop r.down)

def intervalReconstruct {Γ : Context.{u}} {B : Family (total (interval Γ))}
    {x : Γ.Elements} (v : B.obj (freshExtension x)) : PiElement (interval Γ) B x where
  val f r := B.map (intervalArgument f r) v
  naturality f g r := by
    rw [← types_comp_apply, ← B.map_comp, intervalArgument_natural]

@[simp] theorem intervalEvaluate_reconstruct {Γ : Context.{u}}
    {B : Family (total (interval Γ))} {x : Γ.Elements} (v : B.obj (freshExtension x)) :
    intervalEvaluate (intervalReconstruct v) = v := by
  change B.map (intervalArgument (freshBaseHom x) ⟨Cube.fresh x.obj.unop⟩) v = v
  have h : intervalArgument (freshBaseHom x) ⟨Cube.fresh x.obj.unop⟩ = 𝟙 (freshExtension x) := by
    apply Functor.Elements.Hom.ext
    exact congrArg (@Quiver.Hom.op SquareKit.Cubical.Cube _ _ _) (Cube.pair_eta x.obj.unop)
  rw [h]
  exact congrArg (fun k => k v) (B.map_id (freshExtension x))

@[simp] theorem intervalReconstruct_evaluate {Γ : Context.{u}}
    {B : Family (total (interval Γ))} {x : Γ.Elements} (p : PiElement (interval Γ) B x) :
    intervalReconstruct (intervalEvaluate p) = p := by
  apply PiElement.ext
  intro y f r
  let g : freshBase x ⟶ y := Functor.Elements.homMk
    (Quiver.Hom.op (Cube.pair f.hom.unop r.down)) (by
      have h := (intervalArgument f r).map_val
      exact congrArg Sigma.fst h)
  have hg : freshBaseHom x ≫ g = f := by
    apply Functor.Elements.Hom.ext
    exact congrArg Quiver.Hom.op (Cube.pair_drop f.hom.unop r.down)
  have hr : (interval Γ).map g (ULift.up (Cube.fresh x.obj.unop)) = r := by
    apply ULift.ext
    exact Cube.pair_fresh f.hom.unop r.down
  have naturalityAlong {w z : Γ.Elements} (f' : x ⟶ w) (g' : w ⟶ z)
      (r' : (interval Γ).obj w) (s' : (interval Γ).obj z)
      (he : (interval Γ).map g' r' = s') :
      B.map (extendAlong (interval Γ) g' he) (p.val f' r') = p.val (f' ≫ g') s' := by
    subst s'
    exact p.naturality f' g' r'
  have hn := naturalityAlong (freshBaseHom x) g ⟨Cube.fresh x.obj.unop⟩ r hr
  rw [hg] at hn
  exact hn

/-- This is the interval-specific product equivalence, not a general Pi inverse. -/
def intervalProductEquiv {Γ : Context.{u}} (B : Family (total (interval Γ))) (x : Γ.Elements) :
    PiElement (interval Γ) B x ≃ B.obj (freshExtension x) where
  toFun := intervalEvaluate
  invFun := intervalReconstruct
  left_inv := intervalReconstruct_evaluate
  right_inv := intervalEvaluate_reconstruct

end SquareKit.Cubical.Presheaf

namespace SquareKit.Cubical.Cartesian
open CategoryTheory
universe u

def interval (Γ : Context.{u}) : Family Γ where
  obj x := ULift.{u} (Cube.Hom x.obj.unop ⟨1⟩)
  map f := TypeCat.ofHom (fun r => ⟨Cube.comp f.hom.unop r.down⟩)
  map_id x := by
    apply ConcreteCategory.hom_ext
    intro r
    exact congrArg ULift.up (@Category.id_comp Cube _ x.obj.unop ⟨1⟩ r.down)
  map_comp f g := by
    apply ConcreteCategory.hom_ext
    intro r
    exact congrArg ULift.up (Category.assoc g.hom.unop f.hom.unop r.down)

/-- The interval inclusion changes the represented interval; it is not an iso. -/
def intervalInclusion (Γ : Presheaf.Context.{u}) : interval (restrict Γ) ⟶
    restrictFamily (Presheaf.interval Γ) where
  app x := TypeCat.ofHom (fun r => ⟨inclusion.map r.down⟩)
  naturality x y f := by
    apply ConcreteCategory.hom_ext
    intro r
    exact congrArg ULift.up (inclusion.map_comp f.hom.unop r.down)

/-- The explicit relative-interval pullback functor on dependent generalized points. -/
def intervalElements (Γ : Presheaf.Context.{u}) :
    (total (interval (restrict Γ))).Elements ⥤ (Presheaf.total (Presheaf.interval Γ)).Elements where
  obj z := (Presheaf.total (Presheaf.interval Γ)).elementsMk (inclusion.op.obj z.obj)
    ⟨z.val.1, ⟨inclusion.map z.val.2.down⟩⟩
  map {X Y} f := Functor.Elements.homMk (inclusion.op.map f.hom) (by
    rcases f with ⟨f, h⟩
    have hb := congrArg Sigma.fst h
    have hr := congrArg (fun z : (total (interval (restrict Γ))).obj Y.obj =>
      (show ULift (Cube.Hom Y.obj.unop ⟨1⟩) from z.2).down) h
    apply Sigma.ext
    · exact hb
    · change HEq (ULift.up (SquareKit.Cubical.Cube.comp (inclusion.map f.unop)
        (inclusion.map _))) (ULift.up (inclusion.map _))
      apply heq_of_eq
      apply congrArg ULift.up
      exact (inclusion.map_comp f.unop X.val.2.down).symm.trans (congrArg inclusion.map hr))

  map_id _ := rfl
  map_comp f g := by
    apply Functor.Elements.Hom.ext
    exact inclusion.op.map_comp f.hom g.hom

abbrev relativeFamily {Γ : Presheaf.Context.{u}}
    (B : Presheaf.Family (Presheaf.total (Presheaf.interval Γ))) :
    Family (total (interval (restrict Γ))) := intervalElements Γ ⋙ B

/-- The represented Cartesian interval includes in the restricted source interval context. -/
def intervalContextInclusion (Γ : Presheaf.Context.{u}) :
    total (interval (restrict Γ)) ⟶ restrict (Presheaf.total (Presheaf.interval Γ)) where
  app I := TypeCat.ofHom (fun z => ⟨z.1, ⟨inclusion.map z.2.down⟩⟩)
  naturality I J f := by
    apply ConcreteCategory.hom_ext
    intro z
    let k : (total (interval (restrict Γ))).elementsMk I z ⟶
        (total (interval (restrict Γ))).elementsMk J ((total (interval (restrict Γ))).map f z) :=
      Functor.Elements.homMk f rfl
    exact ((intervalElements Γ).map k).map_val.symm

def relativeTerm {Γ : Presheaf.Context.{u}}
    {B : Presheaf.Family (Presheaf.total (Presheaf.interval Γ))} (s : Presheaf.Term B) :
    Term (relativeFamily B) where
  val x := s.val ((intervalElements Γ).obj x)
  property f := s.property ((intervalElements Γ).map f)

/-- Every De Morgan generalized interval function restricts to Cartesian arguments. -/
def relativePi {Γ : Presheaf.Context.{u}}
    (B : Presheaf.Family (Presheaf.total (Presheaf.interval Γ)))
    (x : (restrict Γ).Elements)
    (p : Presheaf.PiElement (Presheaf.interval Γ) B ((elements Γ).obj x)) :
    PiElement (interval (restrict Γ)) (relativeFamily B) x where
  val f r := p.val ((elements Γ).map f) ⟨inclusion.map r.down⟩
  naturality f g r := by
    have he : (Presheaf.interval Γ).map ((elements Γ).map g)
        (ULift.up (inclusion.map r.down)) =
        ULift.up (inclusion.map (((interval (restrict Γ)).map g r).down)) :=
      congrArg ULift.up (inclusion.map_comp g.hom.unop r.down).symm
    have naturalityAlong {w z : Γ.Elements} (f' : (elements Γ).obj x ⟶ w) (g' : w ⟶ z)
        (r' : (Presheaf.interval Γ).obj w) (s' : (Presheaf.interval Γ).obj z)
        (he' : (Presheaf.interval Γ).map g' r' = s') :
        B.map (Presheaf.extendAlong (Presheaf.interval Γ) g' he') (p.val f' r') =
          p.val (f' ≫ g') s' := by
      subst s'
      exact p.naturality f' g' r'
    have h := naturalityAlong ((elements Γ).map f) ((elements Γ).map g) _ _ he
    rw [← (elements Γ).map_comp] at h
    exact h


abbrev dropOpp (I : Cubeᵒᵖ) : I ⟶ Opposite.op (Cube.extend I.unop) :=
  @Quiver.Hom.op Cube _ _ _ (Cube.drop I.unop)

def freshBase {Γ : Context.{u}} (x : Γ.Elements) : Γ.Elements :=
  Γ.elementsMk (.op (Cube.extend x.obj.unop)) (Γ.map (dropOpp x.obj) x.val)
def freshBaseHom {Γ : Context.{u}} (x : Γ.Elements) : x ⟶ freshBase x :=
  Functor.Elements.homMk (dropOpp x.obj) rfl

def freshExtension {Γ : Context.{u}} (x : Γ.Elements) : (total (interval Γ)).Elements :=
  extendObj (interval Γ) (freshBase x) ⟨Cube.fresh x.obj.unop⟩

def intervalArgument {Γ : Context.{u}} {x y : Γ.Elements} (f : x ⟶ y)
    (r : (interval Γ).obj y) : freshExtension x ⟶ extendObj (interval Γ) y r :=
  Functor.Elements.homMk (Quiver.Hom.op (Cube.pair f.hom.unop r.down)) (by
    change (⟨Γ.map (Quiver.Hom.op (Cube.pair f.hom.unop r.down))
      (Γ.map (dropOpp x.obj) x.val),
      ULift.up (Cube.comp (Cube.pair f.hom.unop r.down) (Cube.fresh x.obj.unop))⟩ :
        (total (interval Γ)).obj y.obj) = ⟨y.val,r⟩
    have hc : dropOpp x.obj ≫ Quiver.Hom.op (Cube.pair f.hom.unop r.down) = f.hom :=
      congrArg Quiver.Hom.op (Cube.pair_drop f.hom.unop r.down)
    rw [← types_comp_apply, ← Γ.map_comp, hc, f.map_val, Cube.pair_fresh]
    cases r
    rfl)

def relativeEvaluate {Γ : Presheaf.Context.{u}}
    {B : Presheaf.Family (Presheaf.total (Presheaf.interval Γ))}
    {x : (restrict Γ).Elements}
    (p : PiElement (interval (restrict Γ)) (relativeFamily B) x) :
    B.obj (Presheaf.freshExtension ((elements Γ).obj x)) :=
  p.val (freshBaseHom x) ⟨Cube.fresh x.obj.unop⟩

def relativeRecover {Γ : Presheaf.Context.{u}}
    {B : Presheaf.Family (Presheaf.total (Presheaf.interval Γ))}
    {x : (restrict Γ).Elements}
    (p : PiElement (interval (restrict Γ)) (relativeFamily B) x) :
    Presheaf.PiElement (Presheaf.interval Γ) B ((elements Γ).obj x) :=
  Presheaf.intervalReconstruct (relativeEvaluate p)

@[simp] theorem relativeRecover_pi {Γ : Presheaf.Context.{u}}
    {B : Presheaf.Family (Presheaf.total (Presheaf.interval Γ))}
    {x : (restrict Γ).Elements}
    (p : Presheaf.PiElement (Presheaf.interval Γ) B ((elements Γ).obj x)) :
    relativeRecover (relativePi B x p) = p :=
  Presheaf.intervalReconstruct_evaluate p

/-- Recovering the source interval function recovers every Cartesian evaluation. -/
@[simp] theorem relativePi_recover {Γ : Presheaf.Context.{u}}
    {B : Presheaf.Family (Presheaf.total (Presheaf.interval Γ))}
    {x : (restrict Γ).Elements}
    (p : PiElement (interval (restrict Γ)) (relativeFamily B) x) :
    relativePi B x (relativeRecover p) = p := by
  apply PiElement.ext
  intro y f r
  let g : freshBase x ⟶ y := Functor.Elements.homMk
    (Quiver.Hom.op (Cube.pair f.hom.unop r.down)) (by
      have h := (intervalArgument f r).map_val
      exact congrArg Sigma.fst h)
  have hg : freshBaseHom x ≫ g = f := by
    apply Functor.Elements.Hom.ext
    exact congrArg Quiver.Hom.op (Cube.pair_drop f.hom.unop r.down)
  have hr : (interval (restrict Γ)).map g (ULift.up (Cube.fresh x.obj.unop)) = r := by
    apply ULift.ext
    exact Cube.pair_fresh f.hom.unop r.down
  have naturalityAlong {w z : (restrict Γ).Elements} (f' : x ⟶ w) (g' : w ⟶ z)
      (r' : (interval (restrict Γ)).obj w) (s' : (interval (restrict Γ)).obj z)
      (he : (interval (restrict Γ)).map g' r' = s') :
      (relativeFamily B).map (extendAlong (interval (restrict Γ)) g' he)
        (p.val f' r') = p.val (f' ≫ g') s' := by
    subst s'
    exact p.naturality f' g' r'
  have hn := naturalityAlong (freshBaseHom x) g ⟨Cube.fresh x.obj.unop⟩ r hr
  rw [hg] at hn
  change B.map ((intervalElements Γ).map (intervalArgument f r))
      (relativeEvaluate p) = p.val f r at hn
  change B.map (Presheaf.intervalArgument ((elements Γ).map f) ⟨inclusion.map r.down⟩)
      (relativeEvaluate p) = p.val f r
  have he : (intervalElements Γ).map (intervalArgument f r) =
      Presheaf.intervalArgument ((elements Γ).map f) ⟨inclusion.map r.down⟩ := by
    apply Functor.Elements.Hom.ext
    exact congrArg Quiver.Hom.op (inclusion_pair f.hom.unop r.down)
  rw [← he]
  exact hn

/-- Relative dependent interval products are isomorphic even for varying coefficients. -/
def relativePiEquiv {Γ : Presheaf.Context.{u}}
    (B : Presheaf.Family (Presheaf.total (Presheaf.interval Γ)))
    (x : (restrict Γ).Elements) :
    Presheaf.PiElement (Presheaf.interval Γ) B ((elements Γ).obj x) ≃
      PiElement (interval (restrict Γ)) (relativeFamily B) x where
  toFun := relativePi B x
  invFun := relativeRecover
  left_inv := relativeRecover_pi
  right_inv := relativePi_recover


abbrev RelativePathElement {Γ : Presheaf.Context.{u}}
    (B : Presheaf.Family (Presheaf.total (Presheaf.interval Γ)))
    (a₀ : Presheaf.Term (Presheaf.reindex B (Presheaf.endpointSub Γ false)))
    (a₁ : Presheaf.Term (Presheaf.reindex B (Presheaf.endpointSub Γ true)))
    (x : (restrict Γ).Elements) :=
  { p : PiElement (interval (restrict Γ)) (relativeFamily B) x // ∀ {y} (f : x ⟶ y),
      p.val f ⟨Cube.endpoint y.obj.unop false⟩ = a₀.val ((elements Γ).obj y) ∧
      p.val f ⟨Cube.endpoint y.obj.unop true⟩ = a₁.val ((elements Γ).obj y) }

def relativePath {Γ : Presheaf.Context.{u}}
    (B : Presheaf.Family (Presheaf.total (Presheaf.interval Γ)))
    (a₀ : Presheaf.Term (Presheaf.reindex B (Presheaf.endpointSub Γ false)))
    (a₁ : Presheaf.Term (Presheaf.reindex B (Presheaf.endpointSub Γ true))) :
    Family (restrict Γ) where
  obj x := RelativePathElement B a₀ a₁ x
  map f := TypeCat.ofHom (fun p => ⟨p.val.restrict f, fun g => p.property (f ≫ g)⟩)
  map_id x := by
    apply ConcreteCategory.hom_ext
    intro p
    apply Subtype.ext
    apply PiElement.ext
    intro y f r
    simp [PiElement.restrict]
  map_comp f g := by
    apply ConcreteCategory.hom_ext
    intro p
    apply Subtype.ext
    apply PiElement.ext
    intro y h r
    simp [PiElement.restrict]

def pathComparison {Γ : Presheaf.Context.{u}}
    (B : Presheaf.Family (Presheaf.total (Presheaf.interval Γ)))
    (a₀ : Presheaf.Term (Presheaf.reindex B (Presheaf.endpointSub Γ false)))
    (a₁ : Presheaf.Term (Presheaf.reindex B (Presheaf.endpointSub Γ true))) :
    restrictFamily (Presheaf.path B a₀ a₁) ⟶ relativePath B a₀ a₁ where
  app x := TypeCat.ofHom (fun p => ⟨relativePi B x p.val,
    fun f => p.property ((elements Γ).map f)⟩)
  naturality x y f := by
    apply ConcreteCategory.hom_ext
    intro p
    apply Subtype.ext
    apply PiElement.ext
    intro z g r
    change p.val.val ((elements Γ).map f ≫ (elements Γ).map g) _ =
      p.val.val ((elements Γ).map (f ≫ g)) _
    rw [(elements Γ).map_comp]

end SquareKit.Cubical.Cartesian

namespace SquareKit.Cubical.Presheaf
open CategoryTheory
universe u

/-- Endpoint laws at the identity imply their laws at every generalized substitution. -/
theorem interval_endpoint_of_identity {Γ : Context.{u}}
    {B : Family (total (interval Γ))} {x : Γ.Elements}
    (p : PiElement (interval Γ) B x) (b : Bool)
    (a : Term (reindex B (endpointSub Γ b)))
    (h : p.val (𝟙 x) ((endpoint Γ b).val x) = a.val x)
    {y : Γ.Elements} (f : x ⟶ y) :
    p.val f ((endpoint Γ b).val y) = a.val y := by
  have he := (endpoint Γ b).property f
  have naturalityAlong (s : (interval Γ).obj y) (hs : (interval Γ).map f ((endpoint Γ b).val x) = s) :
      B.map (extendAlong (interval Γ) f hs) (p.val (𝟙 x) ((endpoint Γ b).val x)) =
        p.val ((𝟙 x) ≫ f) s := by
    subst s
    exact p.naturality (𝟙 x) f _
  have hn := naturalityAlong _ he
  rw [Category.id_comp, h] at hn
  exact hn.symm.trans (a.property f)

end SquareKit.Cubical.Presheaf

namespace SquareKit.Cubical.Cartesian
open CategoryTheory
universe u

def pathRecover {Γ : Presheaf.Context.{u}}
    {B : Presheaf.Family (Presheaf.total (Presheaf.interval Γ))}
    {a₀ : Presheaf.Term (Presheaf.reindex B (Presheaf.endpointSub Γ false))}
    {a₁ : Presheaf.Term (Presheaf.reindex B (Presheaf.endpointSub Γ true))}
    {x : (restrict Γ).Elements} (p : RelativePathElement B a₀ a₁ x) :
    Presheaf.PathElement B a₀ a₁ ((elements Γ).obj x) := by
  refine ⟨relativeRecover p.val, ?_⟩
  intro y f
  have hc := relativePi_recover p.val
  have h₀ := congrArg (fun q => q.val (𝟙 x) ⟨Cube.endpoint x.obj.unop false⟩) hc
  have h₁ := congrArg (fun q => q.val (𝟙 x) ⟨Cube.endpoint x.obj.unop true⟩) hc
  refine ⟨Presheaf.interval_endpoint_of_identity _ false a₀ ?_ f,
    Presheaf.interval_endpoint_of_identity _ true a₁ ?_ f⟩
  · exact h₀.trans (p.property (𝟙 x)).1
  · exact h₁.trans (p.property (𝟙 x)).2

def pathEquiv {Γ : Presheaf.Context.{u}}
    (B : Presheaf.Family (Presheaf.total (Presheaf.interval Γ)))
    (a₀ : Presheaf.Term (Presheaf.reindex B (Presheaf.endpointSub Γ false)))
    (a₁ : Presheaf.Term (Presheaf.reindex B (Presheaf.endpointSub Γ true)))
    (x : (restrict Γ).Elements) :
    Presheaf.PathElement B a₀ a₁ ((elements Γ).obj x) ≃ RelativePathElement B a₀ a₁ x where
  toFun := (pathComparison B a₀ a₁).app x
  invFun := pathRecover
  left_inv p := Subtype.ext (relativeRecover_pi p.val)
  right_inv p := Subtype.ext (relativePi_recover p.val)

/-- The derived relative path comparison is natural in generalized base points. -/
def pathIso {Γ : Presheaf.Context.{u}}
    (B : Presheaf.Family (Presheaf.total (Presheaf.interval Γ)))
    (a₀ : Presheaf.Term (Presheaf.reindex B (Presheaf.endpointSub Γ false)))
    (a₁ : Presheaf.Term (Presheaf.reindex B (Presheaf.endpointSub Γ true))) :
    restrictFamily (Presheaf.path B a₀ a₁) ≅ relativePath B a₀ a₁ :=
  NatIso.ofComponents (fun x => Equiv.toIso (pathEquiv B a₀ a₁ x))
    (fun f => (pathComparison B a₀ a₁).naturality f)

/-- Forgetting a coordinate is a genuine nonidentity base change whenever the base has a point. -/
theorem interval_projection_not_injective (Γ : Context.{u}) (γ : Γ.obj (.op ⟨0⟩)) :
    ¬ Function.Injective ((projection (interval Γ)).app (.op ⟨0⟩)) := by
  intro h
  have e := h (a₁ := ⟨γ, ⟨Cube.endpoint ⟨0⟩ false⟩⟩)
    (a₂ := ⟨γ, ⟨Cube.endpoint ⟨0⟩ true⟩⟩) rfl
  have hdim := congrArg (fun z : (total (interval Γ)).obj (.op ⟨0⟩) => (show Dim 0 from z.2.down 0)) e
  cases hdim
/-- The relative interval retains enough generic cubes to recover the whole source section. -/
theorem relativeTerm_injective {Γ : Presheaf.Context.{u}}
    {B : Presheaf.Family (Presheaf.total (Presheaf.interval Γ))} :
    Function.Injective (relativeTerm (B := B)) := by
  intro s t h
  have hl : Presheaf.lam s = Presheaf.lam t := by
    apply Presheaf.Term.ext
    intro x
    rcases x with @⟨⟨⟨n⟩⟩, γ⟩
    apply (relativePiEquiv B ((restrict Γ).elementsMk (.op ⟨n⟩) γ)).injective
    apply PiElement.ext
    intro y f r
    exact congrArg (fun z => z.val (extendObj (interval (restrict Γ)) y r)) h
  exact congrArg Presheaf.app hl
end SquareKit.Cubical.Cartesian
