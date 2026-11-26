import SquareKit.Internal.Cubical.CartesianGlueFilling
import SquareKit.Internal.Cubical.CartesianUniverseComposition
import SquareKit.Internal.Cubical.CartesianRelativeExtension
import SquareKit.Internal.Cubical.CartesianIntervalTransport

/-! Dimension-dependent universe codes with a chosen lawful filling. Normalized Glue
preserves source and tube codes, and the complete operation commutes with substitution. -/
set_option autoImplicit false
set_option warningAsError true
namespace SquareKit.Cubical.Cartesian.SmallUniverse
open CategoryTheory
universe u

/-- The universe as a family has dimension-dependent code fibers. It is not
assumed to be a constant presheaf, nor is a filling operation assumed here. -/
def family (Γ : Context.{u+1}) : Family Γ where
  obj x := SmallFamilyCode.{u} x.obj.unop
  map f := smallFamilyCodes.map f.hom
  map_id x := smallFamilyCodes.map_id x.obj
  map_comp f g := smallFamilyCodes.map_comp f.hom g.hom

def term {Γ : Context.{u+1}} (a : Γ ⟶ smallFamilyCodes.{u}) : Term (family Γ) where
  val x := a.app x.obj x.val
  property f := (a.naturality_apply f.hom _).symm.trans (congrArg (a.app _) f.map_val)

def code {Γ : Context.{u+1}} (a : Term (family Γ)) : Γ ⟶ smallFamilyCodes.{u} where
  app I := TypeCat.ofHom (fun x => a.val (Γ.elementsMk I x))
  naturality I J f := by
    apply ConcreteCategory.hom_ext
    intro x
    let g : Γ.elementsMk I x ⟶ Γ.elementsMk J (Γ.map f x) :=
      Functor.Elements.homMk f rfl
    exact (a.property g).symm

theorem code_term {Γ : Context.{u+1}} (a : Γ ⟶ smallFamilyCodes.{u}) : code (term a) = a := rfl

theorem term_code {Γ : Context.{u+1}} (a : Term (family Γ)) : term (code a) = a := rfl

theorem family_reindex {Γ Δ : Context.{u+1}} (σ : Δ ⟶ Γ) :
    reindex (family Γ) σ = family Δ := rfl

theorem term_reindex {Γ Δ : Context.{u+1}} (a : Γ ⟶ smallFamilyCodes.{u}) (σ : Δ ⟶ Γ) :
    Term.reindex (term a) σ = term (σ ≫ a) := rfl

/-- A code-valued line with exact endpoints gives a native universe path. -/
def pathOfCode {Γ : Context.{u+1}} (a b : Γ ⟶ smallFamilyCodes.{u})
    (p : total (interval Γ) ⟶ smallFamilyCodes.{u})
    (h₀ : endpointSub Γ false ≫ p = a) (h₁ : endpointSub Γ true ≫ p = b) :
    Term (homogeneousPath (family Γ) (term a) (term b)) :=
  pathLam (term p) (congrArg term h₀) (congrArg term h₁)

/-- Reading a universe path recovers its actual code-valued line. -/
def codeOfPath {Γ : Context.{u+1}} {a b : Γ ⟶ smallFamilyCodes.{u}}
    (p : Term (homogeneousPath (family Γ) (term a) (term b))) :
    total (interval Γ) ⟶ smallFamilyCodes.{u} := code (pathApp p)

theorem codeOfPath_pathOfCode {Γ : Context.{u+1}} (a b : Γ ⟶ smallFamilyCodes.{u})
    (p : total (interval Γ) ⟶ smallFamilyCodes.{u})
    (h₀ : endpointSub Γ false ≫ p = a) (h₁ : endpointSub Γ true ≫ p = b) :
    codeOfPath (pathOfCode a b p h₀ h₁) = p := rfl


theorem codeOfPath_zero {Γ : Context.{u+1}} {a b : Γ ⟶ smallFamilyCodes.{u}}
    (p : Term (homogeneousPath (family Γ) (term a) (term b))) :
    endpointSub Γ false ≫ codeOfPath p = a :=
  congrArg code (pathApp_zero p)

theorem codeOfPath_one {Γ : Context.{u+1}} {a b : Γ ⟶ smallFamilyCodes.{u}}
    (p : Term (homogeneousPath (family Γ) (term a) (term b))) :
    endpointSub Γ true ≫ codeOfPath p = b :=
  congrArg code (pathApp_one p)

theorem pathOfCode_codeOfPath {Γ : Context.{u+1}} {a b : Γ ⟶ smallFamilyCodes.{u}}
    (p : Term (homogeneousPath (family Γ) (term a) (term b))) :
    pathOfCode a b (codeOfPath p) (codeOfPath_zero p) (codeOfPath_one p) = p :=
  pathLam_app p


end SquareKit.Cubical.Cartesian.SmallUniverse

namespace SquareKit.Cubical.Cartesian
open CategoryTheory
universe u
noncomputable section
attribute [local instance] Classical.propDecidable
namespace CodeSystem

/-- Compatibility compares entire codes, including the chosen filling operation. -/
def Compatible {Γ : Context.{u}} {φ ψ : Subcontext Γ}
    (a : raisedContext (restrictContext φ) ⟶ smallFamilyCodes.{u})
    (b : raisedContext (restrictContext ψ) ⟶ smallFamilyCodes.{u}) : Prop :=
  ∀ (x : Γ.Elements) (h : φ.Holds x) (k : ψ.Holds x),
    a.app x.obj ⟨⟨x.val,h⟩⟩ = b.app x.obj ⟨⟨x.val,k⟩⟩

def value {Γ : Context.{u}} {φ ψ : Subcontext Γ}
    (a : raisedContext (restrictContext φ) ⟶ smallFamilyCodes.{u})
    (b : raisedContext (restrictContext ψ) ⟶ smallFamilyCodes.{u})
    (x : Γ.Elements) (p : (φ.join ψ).Holds x) : SmallFamilyCode.{u} x.obj.unop :=
  if h : φ.Holds x then a.app x.obj ⟨⟨x.val,h⟩⟩
  else b.app x.obj ⟨⟨x.val,((Subcontext.full_join φ ψ x).mp p).resolve_left h⟩⟩

theorem value_left {Γ : Context.{u}} {φ ψ : Subcontext Γ}
    (a : raisedContext (restrictContext φ) ⟶ smallFamilyCodes.{u})
    (b : raisedContext (restrictContext ψ) ⟶ smallFamilyCodes.{u})
    (x : Γ.Elements) (p : (φ.join ψ).Holds x) (h : φ.Holds x) :
    value a b x p = a.app x.obj ⟨⟨x.val,h⟩⟩ := by
  exact dite_eq_left h

theorem value_right {Γ : Context.{u}} {φ ψ : Subcontext Γ}
    (a : raisedContext (restrictContext φ) ⟶ smallFamilyCodes.{u})
    (b : raisedContext (restrictContext ψ) ⟶ smallFamilyCodes.{u}) (c : Compatible a b)
    (x : Γ.Elements) (p : (φ.join ψ).Holds x) (h : ψ.Holds x) :
    value a b x p = b.app x.obj ⟨⟨x.val,h⟩⟩ := by
  by_cases k : φ.Holds x
  · exact (value_left a b x p k).trans (c x k h)
  · exact dite_eq_right k

/-- Compatible partial codes assemble on a union of faces. No family or filling
is supplied for the union: both are retained in these actual universe codes. -/
def glue {Γ : Context.{u}} {φ ψ : Subcontext Γ}
    (a : raisedContext (restrictContext φ) ⟶ smallFamilyCodes.{u})
    (b : raisedContext (restrictContext ψ) ⟶ smallFamilyCodes.{u}) (c : Compatible a b) :
    raisedContext (restrictContext (φ.join ψ)) ⟶ smallFamilyCodes.{u} where
  app I := TypeCat.ofHom (fun x => value a b (Γ.elementsMk I x.down.val) x.down.property)
  naturality I J f := by
    apply ConcreteCategory.hom_ext
    intro x
    let z := Γ.elementsMk I x.down.val
    let w := Γ.elementsMk J (Γ.map f x.down.val)
    let g : z ⟶ w := Functor.Elements.homMk f rfl
    change value a b w ((φ.join ψ).natural g x.down.property) =
      smallFamilyCodes.map f (value a b z x.down.property)
    rcases (Subcontext.full_join φ ψ z).mp x.down.property with h | h
    · rw [value_left a b z _ h, value_left a b w _ (φ.natural g h)]
      exact a.naturality_apply f ⟨⟨x.down.val,h⟩⟩
    · rw [value_right a b c z _ h, value_right a b c w _ (ψ.natural g h)]
      exact b.naturality_apply f ⟨⟨x.down.val,h⟩⟩

/-- The left face includes into its union without changing cube coordinates. -/
def includeLeft {Γ : Context.{u}} (φ ψ : Subcontext Γ) :
    restrictContext φ ⟶ restrictContext (φ.join ψ) where
  app _ := TypeCat.ofHom (fun x => ⟨x.val,(Subcontext.full_join φ ψ _).mpr (Or.inl x.property)⟩)
  naturality _ _ _ := rfl

def includeRight {Γ : Context.{u}} (φ ψ : Subcontext Γ) :
    restrictContext ψ ⟶ restrictContext (φ.join ψ) where
  app _ := TypeCat.ofHom (fun x => ⟨x.val,(Subcontext.full_join φ ψ _).mpr (Or.inr x.property)⟩)
  naturality _ _ _ := rfl

theorem glue_left {Γ : Context.{u}} {φ ψ : Subcontext Γ}
    (a : raisedContext (restrictContext φ) ⟶ smallFamilyCodes.{u})
    (b : raisedContext (restrictContext ψ) ⟶ smallFamilyCodes.{u}) (c : Compatible a b) :
    raisedSub (includeLeft φ ψ) ≫ glue a b c = a := by
  ext I x
  exact value_left a b (Γ.elementsMk I x.down.val)
    ((Subcontext.full_join φ ψ _).mpr (Or.inl x.down.property)) x.down.property

theorem glue_right {Γ : Context.{u}} {φ ψ : Subcontext Γ}
    (a : raisedContext (restrictContext φ) ⟶ smallFamilyCodes.{u})
    (b : raisedContext (restrictContext ψ) ⟶ smallFamilyCodes.{u}) (c : Compatible a b) :
    raisedSub (includeRight φ ψ) ≫ glue a b c = b := by
  ext I x
  exact value_right a b c (Γ.elementsMk I x.down.val)
    ((Subcontext.full_join φ ψ _).mpr (Or.inr x.down.property)) x.down.property

theorem Compatible.reindex {Γ Δ : Context.{u}} {φ ψ : Subcontext Γ}
    {a : raisedContext (restrictContext φ) ⟶ smallFamilyCodes.{u}}
    {b : raisedContext (restrictContext ψ) ⟶ smallFamilyCodes.{u}}
    (c : Compatible a b) (σ : Δ ⟶ Γ) :
    Compatible (raisedSub (restrictSubstitution φ σ) ≫ a)
      (raisedSub (restrictSubstitution ψ σ) ≫ b) :=
  fun x h k => c (σ.mapElements.obj x) h k

/-- Substitution preserves the assembled codes, including their selected data. -/
theorem glue_reindex {Γ Δ : Context.{u}} {φ ψ : Subcontext Γ}
    (a : raisedContext (restrictContext φ) ⟶ smallFamilyCodes.{u})
    (b : raisedContext (restrictContext ψ) ⟶ smallFamilyCodes.{u})
    (c : Compatible a b) (σ : Δ ⟶ Γ) :
    raisedSub (restrictSubstitution (φ.join ψ) σ) ≫ glue a b c =
      glue (raisedSub (restrictSubstitution φ σ) ≫ a)
        (raisedSub (restrictSubstitution ψ σ) ≫ b) (c.reindex σ) := by
  ext I x
  rfl

/-- A code at an endpoint is restricted along the projection of its face. -/
def endpointCode {Γ : Context.{u}}
    (a : raisedContext Γ ⟶ smallFamilyCodes.{u}) (b : Bool) :
    raisedContext (restrictContext (intervalFace Γ b)) ⟶ smallFamilyCodes.{u} :=
  raisedSub (restrictInclusion (intervalFace Γ b) ≫ projection (interval Γ)) ≫ a

theorem endpoints_compatible {Γ : Context.{u}}
    (a b : raisedContext Γ ⟶ smallFamilyCodes.{u}) :
    Compatible (endpointCode a false) (endpointCode b true) :=
  fun x h k => (intervalFace_disjoint x h k).elim

/-- This is only a boundary system. It does not supply a path between arbitrary
codes: extension to the whole interval needs the equivalence construction. -/
def boundary {Γ : Context.{u}} (a b : raisedContext Γ ⟶ smallFamilyCodes.{u}) :
    raisedContext (restrictContext ((intervalFace Γ false).join (intervalFace Γ true))) ⟶
      smallFamilyCodes.{u} :=
  glue (endpointCode a false) (endpointCode b true) (endpoints_compatible a b)

def endpointFace (Γ : Context.{u}) (b : Bool) : Γ ⟶ restrictContext (intervalFace Γ b) where
  app I := TypeCat.ofHom (fun x => ⟨(endpointSub Γ b).app I x,
    (intervalFace_iff b _).mpr rfl⟩)
  naturality I J f := by
    apply ConcreteCategory.hom_ext
    intro x
    apply Subtype.ext
    exact (endpointSub Γ b).naturality_apply f x

def boundaryZero (Γ : Context.{u}) :
    Γ ⟶ restrictContext ((intervalFace Γ false).join (intervalFace Γ true)) :=
  endpointFace Γ false ≫ includeLeft _ _

def boundaryOne (Γ : Context.{u}) :
    Γ ⟶ restrictContext ((intervalFace Γ false).join (intervalFace Γ true)) :=
  endpointFace Γ true ≫ includeRight _ _

theorem boundary_zero {Γ : Context.{u}} (a b : raisedContext Γ ⟶ smallFamilyCodes.{u}) :
    raisedSub (boundaryZero Γ) ≫ boundary a b = a := by
  ext I x
  exact value_left (endpointCode a false) (endpointCode b true)
    ((total (interval Γ)).elementsMk I ((endpointSub Γ false).app I x.down))
    ((Subcontext.full_join _ _ _).mpr (Or.inl
      ((intervalFace_iff false _).mpr rfl)))
    ((intervalFace_iff false _).mpr rfl)

theorem boundary_one {Γ : Context.{u}} (a b : raisedContext Γ ⟶ smallFamilyCodes.{u}) :
    raisedSub (boundaryOne Γ) ≫ boundary a b = b := by
  ext I x
  exact value_right (endpointCode a false) (endpointCode b true) (endpoints_compatible a b)
    ((total (interval Γ)).elementsMk I ((endpointSub Γ true).app I x.down))
    ((Subcontext.full_join _ _ _).mpr (Or.inr
      ((intervalFace_iff true _).mpr rfl)))
    ((intervalFace_iff true _).mpr rfl)

/-- Decoding the union recovers the full chosen local family on the left. -/
theorem decoded_glue_left {Γ : Context.{u}} {φ ψ : Subcontext Γ}
    (a : raisedContext (restrictContext φ) ⟶ smallFamilyCodes.{u})
    (b : raisedContext (restrictContext ψ) ⟶ smallFamilyCodes.{u}) (c : Compatible a b) :
    (decodedLocalFamily (glue a b c)).reindex (includeLeft φ ψ) = decodedLocalFamily a :=
  (decodedLocalFamily_reindex _ _).symm.trans (congrArg decodedLocalFamily (glue_left a b c))

theorem decoded_glue_right {Γ : Context.{u}} {φ ψ : Subcontext Γ}
    (a : raisedContext (restrictContext φ) ⟶ smallFamilyCodes.{u})
    (b : raisedContext (restrictContext ψ) ⟶ smallFamilyCodes.{u}) (c : Compatible a b) :
    (decodedLocalFamily (glue a b c)).reindex (includeRight φ ψ) = decodedLocalFamily b :=
  (decodedLocalFamily_reindex _ _).symm.trans (congrArg decodedLocalFamily (glue_right a b c))

namespace Maps
variable {Γ : Context.{u}} {φ ψ : Subcontext Γ}
  {A B : Family (restrictContext (φ.join ψ))}

abbrev original (x : (restrictContext (φ.join ψ)).Elements) : Γ.Elements :=
  (restrictInclusion (φ.join ψ)).mapElements.obj x

def left (x : (restrictContext (φ.join ψ)).Elements) (h : φ.Holds (original x)) :
    (restrictContext φ).Elements :=
  (restrictContext φ).elementsMk x.obj ⟨x.val.val,h⟩

def right (x : (restrictContext (φ.join ψ)).Elements) (h : ψ.Holds (original x)) :
    (restrictContext ψ).Elements :=
  (restrictContext ψ).elementsMk x.obj ⟨x.val.val,h⟩

variable (a : reindex A (includeLeft φ ψ) ⟶ reindex B (includeLeft φ ψ))
  (b : reindex A (includeRight φ ψ) ⟶ reindex B (includeRight φ ψ))

/-- Equality on the overlap is required for maps, independently of code compatibility. -/
def Compatible : Prop :=
  ∀ (x : (restrictContext (φ.join ψ)).Elements)
    (h : φ.Holds (original x)) (k : ψ.Holds (original x)) (z : A.obj x),
    a.app (left x h) z = b.app (right x k) z

def value (x : (restrictContext (φ.join ψ)).Elements) (z : A.obj x) : B.obj x :=
  if h : φ.Holds (original x) then a.app (left x h) z
  else b.app (right x (((Subcontext.full_join φ ψ _).mp x.val.property).resolve_left h)) z

theorem value_left (x : (restrictContext (φ.join ψ)).Elements)
    (h : φ.Holds (original x)) (z : A.obj x) : value a b x z = a.app (left x h) z := by
  exact dite_eq_left h

theorem value_right (c : Compatible a b) (x : (restrictContext (φ.join ψ)).Elements)
    (h : ψ.Holds (original x)) (z : A.obj x) : value a b x z = b.app (right x h) z := by
  by_cases k : φ.Holds (original x)
  · exact (value_left a b x k z).trans (c x k h z)
  · exact dite_eq_right k

/-- Compatible family maps assemble over the actual union context. -/
def glue (c : Compatible a b) : A ⟶ B where
  app x := TypeCat.ofHom (value a b x)
  naturality x y f := by
    apply ConcreteCategory.hom_ext
    intro z
    change value a b y (A.map f z) = B.map f (value a b x z)
    let g := (restrictInclusion (φ.join ψ)).mapElements.map f
    rcases (Subcontext.full_join φ ψ (original x)).mp x.val.property with h | h
    · rw [value_left a b x h z, value_left a b y (φ.natural g h) (A.map f z)]
      let q : left x h ⟶ left y (φ.natural g h) :=
        Functor.Elements.homMk f.hom (Subtype.ext (congrArg (fun z : (restrictContext (φ.join ψ)).obj y.obj => z.val) f.map_val))
      exact ConcreteCategory.congr_hom (a.naturality q) z
    · rw [value_right a b c x h z, value_right a b c y (ψ.natural g h) (A.map f z)]
      let q : right x h ⟶ right y (ψ.natural g h) :=
        Functor.Elements.homMk f.hom (Subtype.ext (congrArg (fun z : (restrictContext (φ.join ψ)).obj y.obj => z.val) f.map_val))
      exact ConcreteCategory.congr_hom (b.naturality q) z

theorem glue_left (c : Compatible a b) :
    Functor.whiskerLeft (includeLeft φ ψ).mapElements (glue a b c) = a := by
  ext x z
  exact value_left a b ((includeLeft φ ψ).mapElements.obj x) x.val.property z

theorem glue_right (c : Compatible a b) :
    Functor.whiskerLeft (includeRight φ ψ).mapElements (glue a b c) = b := by
  ext x z
  exact value_right a b c ((includeRight φ ψ).mapElements.obj x) x.val.property z

end Maps


def sourceCode {Γ : Context.{u}} (a : raisedContext Γ ⟶ smallFamilyCodes.{u})
    (r : Term (interval Γ)) : raisedContext (restrictContext (Glue.sourceFace r)) ⟶ smallFamilyCodes.{u} :=
  raisedSub (restrictInclusion (Glue.sourceFace r) ≫ projection (interval Γ)) ≫ a

def sourceFaceMap {Γ : Context.{u}} (r : Term (interval Γ)) : Γ ⟶ restrictContext (Glue.sourceFace r) where
  app I := TypeCat.ofHom (fun x => ⟨(graph r).app I x,rfl⟩)
  naturality I J f := by
    apply ConcreteCategory.hom_ext
    intro x
    apply Subtype.ext
    exact (graph r).naturality_apply f x

def tubeSource {Γ : Context.{u}} (φ : Subcontext Γ) (r : Term (interval Γ)) :
    restrictContext φ ⟶ restrictContext (φ.reindex (projection (interval Γ))) where
  app I := TypeCat.ofHom (fun x => ⟨(graph r).app I x.val,x.property⟩)
  naturality I J f := by
    apply ConcreteCategory.hom_ext
    intro x
    apply Subtype.ext
    exact (graph r).naturality_apply f x.val

structure Box (Γ : Context.{u}) (φ : Subcontext Γ) (r : Term (interval Γ)) where
  base : raisedContext Γ ⟶ smallFamilyCodes.{u}
  tube : raisedContext (restrictContext (φ.reindex (projection (interval Γ)))) ⟶ smallFamilyCodes.{u}
  boundary : raisedSub (tubeSource φ r) ≫ tube = raisedSub (restrictInclusion φ) ≫ base

namespace Box
variable {Γ : Context.{u}} {φ : Subcontext Γ} {r : Term (interval Γ)} (b : Box Γ φ r)

theorem compatible : Compatible (sourceCode b.base r) b.tube := by
  intro x h k
  rcases x with @⟨I,⟨γ,z⟩⟩
  change z = r.val (Γ.elementsMk I γ) at h
  subst z
  exact (congrArg (fun a => a.app I (ULift.up (⟨γ,k⟩ : (restrictContext φ).obj I))) b.boundary).symm

def face : Subcontext (total (interval Γ)) :=
  (Glue.sourceFace r).join (φ.reindex (projection (interval Γ)))

def partialCode : raisedContext (restrictContext (face (φ := φ) (r := r))) ⟶ smallFamilyCodes.{u} :=
  glue (sourceCode b.base r) b.tube b.compatible

def cap : Γ ⟶ restrictContext (face (φ := φ) (r := r)) :=
  sourceFaceMap r ≫ includeLeft _ _

theorem partial_cap : raisedSub (cap (φ := φ) (r := r)) ≫ b.partialCode = b.base := by
  ext I x
  exact value_left (sourceCode b.base r) b.tube
    ((total (interval Γ)).elementsMk I ((graph r).app I x.down)) (Or.inl rfl) rfl

theorem partial_tube :
    raisedSub (includeRight (Glue.sourceFace r) (φ.reindex (projection (interval Γ)))) ≫ b.partialCode = b.tube :=
  glue_right (sourceCode b.base r) b.tube b.compatible

def constant (φ : Subcontext Γ) (r : Term (interval Γ))
    (a : raisedContext Γ ⟶ smallFamilyCodes.{u}) : Box Γ φ r where
  base := a
  tube := raisedSub (restrictInclusion (φ.reindex (projection (interval Γ))) ≫ projection (interval Γ)) ≫ a
  boundary := rfl

theorem constant_partial (a : raisedContext Γ ⟶ smallFamilyCodes.{u}) :
    (constant φ r a).partialCode =
      raisedSub (restrictInclusion (face (φ := φ) (r := r)) ≫ projection (interval Γ)) ≫ a := by
  ext I x
  let y := (total (interval Γ)).elementsMk I x.down.val
  by_cases h : (Glue.sourceFace r).Holds y
  · exact value_left (sourceCode a r) (constant φ r a).tube y x.down.property h
  · exact value_right (sourceCode a r) (constant φ r a).tube (constant φ r a).compatible
      y x.down.property (x.down.property.resolve_left h)

def reindex {Δ : Context.{u}} (σ : Δ ⟶ Γ) : Box Δ (φ.reindex σ) (Term.reindex r σ) where
  base := raisedSub σ ≫ b.base
  tube := raisedSub (restrictSubstitution (φ.reindex (projection (interval Γ))) (intervalSub σ)) ≫ b.tube
  boundary := congrArg (fun a => raisedSub (restrictSubstitution φ σ) ≫ a) b.boundary

theorem partial_reindex {Δ : Context.{u}} (σ : Δ ⟶ Γ) :
    raisedSub (restrictSubstitution (face (φ := φ) (r := r)) (intervalSub σ)) ≫ b.partialCode = (b.reindex σ).partialCode :=
  CodeSystem.glue_reindex (sourceCode b.base r) b.tube b.compatible (intervalSub σ)

end Box

end CodeSystem
end
end SquareKit.Cubical.Cartesian

namespace SquareKit.Cubical.Cartesian.SmallUniverse
open CategoryTheory
universe u
variable {Γ Θ : Context.{u}} {Δ : Context.{u+1}}

def chartTube (φ : Subcontext Δ) (σ : raisedContext Γ ⟶ Δ) :
    raisedContext (restrictContext ((chartFace φ σ).reindex (projection (interval Γ)))) ⟶
      restrictContext (φ.reindex (projection (interval Δ))) where
  app I := TypeCat.ofHom (fun x => ⟨(chartInterval σ).app I ⟨x.down.val⟩,x.down.property⟩)
  naturality I J f := by
    apply ConcreteCategory.hom_ext
    intro x
    apply Subtype.ext
    exact (chartInterval σ).naturality_apply f ⟨x.down.val⟩

theorem chartFace_reindex (φ : Subcontext Δ) (σ : raisedContext Γ ⟶ Δ) (τ : Θ ⟶ Γ) :
    chartFace φ (raisedSub τ ≫ σ) = (chartFace φ σ).reindex τ := rfl

theorem chartInterval_reindex (σ : raisedContext Γ ⟶ Δ) (τ : Θ ⟶ Γ) :
    chartInterval (raisedSub τ ≫ σ) = raisedSub (intervalSub τ) ≫ chartInterval σ := rfl

theorem chartTube_reindex (φ : Subcontext Δ) (σ : raisedContext Γ ⟶ Δ) (τ : Θ ⟶ Γ) :
    chartTube φ (raisedSub τ ≫ σ) =
      raisedSub (restrictSubstitution ((chartFace φ σ).reindex (projection (interval Γ)))
        (intervalSub τ)) ≫ chartTube φ σ := rfl

variable {φ : Subcontext Δ} {r : Term (interval Δ)}
    (b : OpenBox (family (total (interval Δ))) φ r)

/-- The source graph and its exact code equation survive restriction to a small chart. -/
def chartBox (σ : raisedContext Γ ⟶ Δ) : CodeSystem.Box Γ (chartFace φ σ) (chartSource σ r) where
  base := σ ≫ code b.base
  tube := chartTube φ σ ≫ code b.tube.toRestricted
  boundary := by
    ext I x
    exact b.boundary (Δ.elementsMk I (σ.app I ⟨x.down.val⟩)) x.down.property

theorem chartBox_reindex (σ : raisedContext Γ ⟶ Δ) (τ : Θ ⟶ Γ) :
    chartBox b (raisedSub τ ≫ σ) = (chartBox b σ).reindex τ := rfl

end SquareKit.Cubical.Cartesian.SmallUniverse

namespace SquareKit.Cubical.Cartesian.CodeSystem.Sections
open CategoryTheory
universe u
noncomputable section
local instance : ∀ p : Prop, Decidable p := Classical.propDecidable
variable {Γ : Context.{u}} {φ ψ : Subcontext Γ}
  {A : Family (restrictContext (φ.join ψ))}
  (a : Term (reindex A (includeLeft φ ψ)))
  (b : Term (reindex A (includeRight φ ψ)))

def Compatible : Prop := ∀ (x : (restrictContext (φ.join ψ)).Elements)
    (h : φ.Holds (Maps.original x)) (k : ψ.Holds (Maps.original x)),
    a.val (Maps.left x h) = b.val (Maps.right x k)

def value (x : (restrictContext (φ.join ψ)).Elements) : A.obj x :=
  if h : φ.Holds (Maps.original x) then a.val (Maps.left x h)
  else b.val (Maps.right x (x.val.property.resolve_left h))

theorem value_left (x : (restrictContext (φ.join ψ)).Elements)
    (h : φ.Holds (Maps.original x)) : value a b x = a.val (Maps.left x h) :=
  dite_eq_left h

theorem value_right (c : Compatible a b) (x : (restrictContext (φ.join ψ)).Elements)
    (k : ψ.Holds (Maps.original x)) : value a b x = b.val (Maps.right x k) := by
  by_cases h : φ.Holds (Maps.original x)
  · exact (value_left a b x h).trans (c x h k)
  · exact dite_eq_right h

/-- Compatible sections glue as entire elements of the dependent family. -/
def glue (c : Compatible a b) : Term A where
  val := value a b
  property {x y} f := by
    let g := (restrictInclusion (φ.join ψ)).mapElements.map f
    rcases x.val.property with h | k
    · rw [value_left a b x h, value_left a b y (φ.natural g h)]
      let q : Maps.left x h ⟶ Maps.left y (φ.natural g h) :=
        Functor.Elements.homMk f.hom (Subtype.ext (congrArg (fun z : (restrictContext (φ.join ψ)).obj y.obj => z.val) f.map_val))
      exact a.property q
    · rw [value_right a b c x k, value_right a b c y (ψ.natural g k)]
      let q : Maps.right x k ⟶ Maps.right y (ψ.natural g k) :=
        Functor.Elements.homMk f.hom (Subtype.ext (congrArg (fun z : (restrictContext (φ.join ψ)).obj y.obj => z.val) f.map_val))
      exact b.property q

theorem glue_left (c : Compatible a b) : Term.reindex (glue a b c) (includeLeft φ ψ) = a := by
  apply Term.ext
  intro x
  exact value_left a b ((includeLeft φ ψ).mapElements.obj x) x.val.property

theorem glue_right (c : Compatible a b) : Term.reindex (glue a b c) (includeRight φ ψ) = b := by
  apply Term.ext
  intro x
  exact value_right a b c ((includeRight φ ψ).mapElements.obj x) x.val.property

/-- The left section prescribes a partial section on the right overlap. -/
def overlap : PartialSection (reindex A (includeRight φ ψ))
    (φ.reindex (restrictInclusion ψ)) where
  val x h := a.val ((restrictContext φ).elementsMk x.obj ⟨x.val.val,h⟩)
  natural {x y} f h := by
    let q : (restrictContext φ).elementsMk x.obj ⟨x.val.val,h⟩ ⟶
        (restrictContext φ).elementsMk y.obj ⟨y.val.val,φ.natural ((restrictInclusion ψ).mapElements.map f) h⟩ :=
      Functor.Elements.homMk f.hom (Subtype.ext (congrArg (fun z : (restrictContext ψ).obj y.obj => z.val) f.map_val))
    exact a.property q

variable (c : Contractible (reindex A (includeRight φ ψ)))
  (F : Filling (reindex A (includeRight φ ψ))) (hF : F.Lawful)

/-- Contractibility adjusts the right section to the full prescribed left data. -/
def alignRight : Term (reindex A (includeRight φ ψ)) := c.extend F (overlap a)

include hF in
theorem alignRight_compatible : Compatible a (alignRight a c F) := by
  intro x h k
  exact (c.extend_boundary F hF (overlap a) (Maps.right x k) h).symm

/-- Relative assembly keeps the left section literally, including all record fields. -/
def relativeGlue : Term A := glue a (alignRight a c F) (alignRight_compatible a c F hF)

theorem relativeGlue_left : Term.reindex (relativeGlue a c F hF) (includeLeft φ ψ) = a :=
  glue_left a _ _

theorem relativeGlue_right : Term.reindex (relativeGlue a c F hF) (includeRight φ ψ) =
    alignRight a c F := glue_right a _ _

end
end SquareKit.Cubical.Cartesian.CodeSystem.Sections

namespace SquareKit.Cubical.Cartesian.CodeSystem.IsEquivSections
open CategoryTheory EquivalenceFamilies
universe u
noncomputable section
variable {Γ Δ : Context.{u}} {A B : Family Γ} (f : A ⟶ B)
  (F : Filling A) (hF : F.Lawful) (G : Filling B) (hG : G.Lawful)
  (σ : Δ ⟶ Γ) (e : HomotopyEquivalence (Functor.whiskerLeft σ.mapElements f))
  (φ : Subcontext Δ) (s : PartialSection (reindex (isEquiv f) σ) φ)

abbrev fiber := Homotopy.fiber (Functor.whiskerLeft (projection B).mapElements f) (generic B)

/-- Local equivalence evidence contracts the actual pulled-back generic fiber. -/
def fiberContractible : Contractible (reindex (fiber f) (liftSub B σ)) :=
  Contractible.map
    (Homotopy.fiberReindexIso (Functor.whiskerLeft (projection B).mapElements f)
      (generic B) (liftSub B σ)).symm e.fibers

def body : Term (reindex (contr (fiber f)) (liftSub B σ)) :=
  let i := contrReindexIso (fiber f) (liftSub B σ)
  Term.map i.inv (ContractibilityExtension.extend (fiberContractible f σ e)
    ((genericFiberFilling f F hF G hG).reindex (liftSub B σ))
    ((genericFiberFilling_lawful f F hF G hG).reindex (liftSub B σ))
    (((s.map (piReindex B (contr (fiber f)) σ)).app).map i.hom))

/-- Extend full internal equivalence witnesses using evidence only on this context. -/
def extend : Term (reindex (isEquiv f) σ) :=
  Term.map (piReindexIso B (contr (fiber f)) σ).inv
    (lam (body f F hF G hG σ e φ s))

theorem body_boundary (x : (total (reindex B σ)).Elements)
    (hx : (φ.reindex (projection (reindex B σ))).Holds x) :
    (body f F hF G hG σ e φ s).val x =
      ((s.map (piReindex B (contr (fiber f)) σ)).app).val x hx := by
  let i := contrReindexIso (fiber f) (liftSub B σ)
  exact (congrArg (i.inv.app x)
    (ContractibilityExtension.extend_boundary (fiberContractible f σ e)
      ((genericFiberFilling f F hF G hG).reindex (liftSub B σ))
      ((genericFiberFilling_lawful f F hF G hG).reindex (liftSub B σ))
      (((s.map (piReindex B (contr (fiber f)) σ)).app).map i.hom) x hx)).trans
    (congrArg (fun m => m.app x (((s.map (piReindex B (contr (fiber f)) σ)).app).val x hx)) i.hom_inv_id)

theorem extend_boundary (x : Δ.Elements) (hx : φ.Holds x) :
    (extend f F hF G hG σ e φ s).val x = s.val x hx := by
  let i := piReindexIso B (contr (fiber f)) σ
  let p := s.map i.hom
  have h : (lam (body f F hF G hG σ e φ s)).val x = p.val x hx := by
    apply PiElement.ext
    intro y g v
    have hb := body_boundary f F hF G hG σ e φ s
      (extendObj (reindex B σ) y v) (φ.natural g hx)
    have hp := congrArg (fun k => k.val (𝟙 y) v) (p.natural g hx)
    refine hb.trans ?_
    change (p.val x hx).val (g ≫ 𝟙 y) v =
      (p.val y (φ.natural g hx)).val (𝟙 y) v at hp
    change (p.val y (φ.natural g hx)).val (𝟙 y) v = (p.val x hx).val g v
    simpa only [Category.comp_id] using hp.symm
  exact (congrArg (i.inv.app x) h).trans
    (congrArg (fun m => m.app x (s.val x hx)) i.hom_inv_id)
end
end SquareKit.Cubical.Cartesian.CodeSystem.IsEquivSections

namespace SquareKit.Cubical.Cartesian.CodeSystem.Equivalences
open CategoryTheory EquivalenceFamilies
universe u
noncomputable section
variable {Γ : Context.{u}} {φ ψ : Subcontext Γ}
  {A B : Family (restrictContext (φ.join ψ))} (f : A ⟶ B)
  (F : Filling A) (hF : F.Lawful) (G : Filling B) (hG : G.Lawful)
  (a : HomotopyEquivalence (Functor.whiskerLeft (includeLeft φ ψ).mapElements f))
  (b : HomotopyEquivalence (Functor.whiskerLeft (includeRight φ ψ).mapElements f))

def leftWitness : Term (reindex (isEquiv f) (includeLeft φ ψ)) :=
  isEquivReindexSections f (includeLeft φ ψ) a

/-- The right witness is adjusted on the overlap, rather than equated merely
because its underlying map agrees with the left map. -/
def rightWitness : Term (reindex (isEquiv f) (includeRight φ ψ)) :=
  IsEquivSections.extend f F hF G hG (includeRight φ ψ) b
    (φ.reindex (restrictInclusion ψ)) (Sections.overlap (leftWitness f a))

theorem witnesses_compatible : Sections.Compatible (leftWitness f a)
    (rightWitness f F hF G hG a b) := by
  intro x h k
  exact (IsEquivSections.extend_boundary f F hF G hG (includeRight φ ψ) b
    (φ.reindex (restrictInclusion ψ)) (Sections.overlap (leftWitness f a))
    (Maps.right x k) h).symm

/-- Full contractible-fiber evidence assembles across an arbitrary overlap. -/
def witness : Term (isEquiv f) :=
  Sections.glue (leftWitness f a) (rightWitness f F hF G hG a b)
    (witnesses_compatible f F hF G hG a b)

def glue : HomotopyEquivalence f := decodeIsEquiv (witness f F hF G hG a b)

/-- The prescribed left contraction record is retained in its canonical encoding. -/
theorem glue_left : Term.reindex (encodeIsEquiv (glue f F hF G hG a b))
    (includeLeft φ ψ) = isEquivReindexSections f (includeLeft φ ψ) a := by
  rw [glue, encode_decodeIsEquiv]
  exact Sections.glue_left _ _ _

theorem glue_right : Term.reindex (encodeIsEquiv (glue f F hF G hG a b))
    (includeRight φ ψ) = rightWitness f F hF G hG a b := by
  rw [glue, encode_decodeIsEquiv]
  exact Sections.glue_right _ _ _

/-- Restriction recovers the prescribed native equivalence record, not only its map. -/
theorem glue_reindex_left : (glue f F hF G hG a b).reindex (includeLeft φ ψ) = a := by
  apply (isEquivReindexSections f (includeLeft φ ψ)).injective
  rw [isEquivReindexSections_reindex]
  exact glue_left f F hF G hG a b

end
end SquareKit.Cubical.Cartesian.CodeSystem.Equivalences

namespace SquareKit.Cubical.Cartesian.CodeSystem.Equivalences
open CategoryTheory
universe u
noncomputable def glueMaps {Ω : Context.{u}} {α β : Subcontext Ω}
    (A B : LocalFamily (restrictContext (α.join β)))
    (a : Cartesian.reindex A.family (includeLeft α β) ⟶ Cartesian.reindex B.family (includeLeft α β))
    (b : Cartesian.reindex A.family (includeRight α β) ⟶ Cartesian.reindex B.family (includeRight α β))
    (c : Maps.Compatible a b) (ea : HomotopyEquivalence a) (eb : HomotopyEquivalence b) :
    HomotopyEquivalence (Maps.glue a b c) :=
  glue (Maps.glue a b c) A.toFilling A.toFilling_lawful B.toFilling B.toFilling_lawful
    ((Maps.glue_left a b c).symm ▸ ea) ((Maps.glue_right a b c).symm ▸ eb)

end SquareKit.Cubical.Cartesian.CodeSystem.Equivalences


namespace SquareKit.Cubical.Cartesian.CodeSystem.Box
open CategoryTheory
universe u
variable {Γ : Context.{u}} (φ : Subcontext Γ)

abbrev tubeContext := restrictContext (φ.reindex (projection (interval Γ)))

/-- Forget the tube coordinate while retaining its face membership. -/
def tubeProjection : tubeContext φ ⟶ restrictContext φ where
  app _I := TypeCat.ofHom (fun x => ⟨x.val.1,x.property⟩)
  naturality _I _J _f := rfl

def tubeVariable : Term (interval (tubeContext φ)) :=
  Term.reindex (generic (interval Γ)) (restrictInclusion (φ.reindex (projection (interval Γ))))

def tubeSourceTerm (r : Term (interval Γ)) : Term (interval (tubeContext φ)) :=
  Term.reindex r (restrictInclusion (φ.reindex (projection (interval Γ))) ≫ projection (interval Γ))

/-- Replace the tube coordinate by an independent variable. No connection is used. -/
def tubeEvaluation : total (interval (tubeContext φ)) ⟶ tubeContext φ where
  app _I := TypeCat.ofHom (fun x => ⟨⟨x.1.val.1,x.2⟩,x.1.property⟩)
  naturality _I _J _f := rfl

theorem tubeEvaluation_variable : graph (tubeVariable φ) ≫ tubeEvaluation φ = 𝟙 _ := rfl

theorem tubeEvaluation_source (r : Term (interval Γ)) :
    graph (tubeSourceTerm φ r) ≫ tubeEvaluation φ = tubeProjection φ ≫ tubeSource φ r := rfl


variable {φ} {r : Term (interval Γ)} (b : Box Γ φ r)

def tubeLine : LocalFamily (total (interval (tubeContext φ))) :=
  decodedLocalFamily (raisedSub (tubeEvaluation φ) ≫ b.tube)

theorem tubeLine_variable : (tubeLine b).reindex (graph (tubeVariable φ)) =
    decodedLocalFamily b.tube := by
  rw [tubeLine, ← decodedLocalFamily_reindex]
  rfl

theorem tubeLine_source : (tubeLine b).reindex (graph (tubeSourceTerm φ r)) =
    (decodedLocalFamily b.base).reindex
      (restrictInclusion (φ.reindex (projection (interval Γ))) ≫ projection (interval Γ)) := by
  rw [tubeLine, ← decodedLocalFamily_reindex, ← decodedLocalFamily_reindex]
  apply congrArg decodedLocalFamily
  exact congrArg (fun q => raisedSub (tubeProjection φ) ≫ q) b.boundary

end SquareKit.Cubical.Cartesian.CodeSystem.Box

namespace SquareKit.Cubical.Cartesian.EquivalenceFamilies
open CategoryTheory
universe u
theorem partialSigmaSnd_reindex {Γ Δ : Context.{u}} {A : Family Γ} {B : Family (total A)}
    {φ : Subcontext Γ} (s : PartialSection (sigma A B) φ) (a : Term A)
    (ha : ∀ x h, a.val x = (s.val x h).1) (σ : Δ ⟶ Γ) :
    (s.sigmaSnd a ha).reindex σ =
      (s.reindex σ).sigmaSnd (B := reindex B (liftSub A σ)) (Term.reindex a σ)
        (fun x h => ha (σ.mapElements.obj x) h) := by
  apply PartialSection.ext
  intro x h
  exact eq_of_heq ((PartialSection.sigmaSnd_val s a ha (σ.mapElements.obj x) h).trans
    (PartialSection.sigmaSnd_val (B := reindex B (liftSub A σ)) (s.reindex σ)
      (Term.reindex a σ) (fun x h => ha (σ.mapElements.obj x) h) x h).symm)

theorem partialSigmaSnd_map {Γ : Context.{u}} {A : Family Γ} {B C : Family (total A)}
    {φ : Subcontext Γ} (s : PartialSection (sigma A B) φ) (a : Term A)
    (ha : ∀ x h, a.val x = (s.val x h).1) (i : B ≅ C) :
    (s.map (Homotopy.sigmaSecondIso A i).hom).sigmaSnd a ha =
      (s.sigmaSnd a ha).map (Functor.whiskerLeft (pair (𝟙 Γ) a).mapElements i.hom) := by
  apply PartialSection.ext
  intro x h
  have hs := PartialSection.sigmaSnd_val s a ha x h
  have hm := PartialSection.sigmaSnd_val
    (s.map (Homotopy.sigmaSecondIso A i).hom) a ha x h
  apply eq_of_heq
  refine hm.trans ?_
  have hx : extendObj A x (a.val x) = extendObj A x (s.val x h).1 := congrArg (extendObj A x) (ha x h)
  have helper {x y : (total A).Elements} (he : x = y) {p : B.obj x} {q : B.obj y}
      (hp : HEq p q) : HEq (i.hom.app x p) (i.hom.app y q) := by
    cases he
    cases hp
    rfl
  exact (helper hx hs).symm

namespace ContractiblePaths
variable {Γ Δ : Context.{u}} {A : Family Γ} (c : Contractible A)
  (F : Filling A) (hF : F.Lawful) {a b : Term A} {φ : Subcontext Γ}
  (s : PartialSection (homogeneousPath A a b) φ) (σ : Δ ⟶ Γ)

include hF in
theorem line_reindex : Term.reindex (line c F s) (intervalSub σ) =
    line (c.reindex σ) (F.reindex σ)
      ((s.reindex σ).map (homogeneousReindexIso A a b σ).hom) := by
  exact ((c.reindex (projection (interval Γ))).extend_reindex
    (F.reindex (projection (interval Γ))) (hF.reindex _) s.pathBoundary (intervalSub σ)).symm.trans
    (congrArg (fun p => (c.reindex (projection (interval Δ) ≫ σ)).extend
      (F.reindex (projection (interval Δ) ≫ σ)) p) (s.pathBoundary_reindex σ))

theorem extend_reindex : homogeneousReindex (extend c F hF s) σ =
    extend (c.reindex σ) (F.reindex σ) (hF.reindex _)
      ((s.reindex σ).map (homogeneousReindexIso A a b σ).hom) := by
  apply pathApp_injective
  exact line_reindex c F hF s σ
end ContractiblePaths
namespace ContractibilityExtension
variable {Γ Δ : Context.{u}} {A : Family Γ} (c : Contractible A)
  (F : Filling A) (hF : F.Lawful) {φ : Subcontext Γ}
  (s : PartialSection (contr A) φ) (σ : Δ ⟶ Γ)

def substituted := (s.reindex σ).map (contrReindexIso A σ).hom

include hF in
theorem center_reindex : Term.reindex (center c F s) σ =
    center (c.reindex σ) (F.reindex σ) (substituted s σ) := by
  exact (c.extend_reindex F hF s.sigmaFst σ).symm


def partialAt (a : Term A) (ha : ∀ x h, a.val x = (s.val x h).1) :
    PartialSection (homogeneousPath (reindex A (projection A))
      (Term.reindex a (projection A)) (generic A)) (φ.reindex (projection A)) :=
  ((s.sigmaSnd a ha).map (contractionsAtIso A a).hom).app

theorem partialAt_reindex (a : Term A) (ha : ∀ x h, a.val x = (s.val x h).1) :
    ((partialAt s a ha).reindex (liftSub A σ)).map
      (homogeneousReindexIso (reindex A (projection A)) (Term.reindex a (projection A))
        (generic A) (liftSub A σ)).hom =
    partialAt (substituted s σ) (Term.reindex a σ)
      (fun x h => ha (σ.mapElements.obj x) h) := by
  unfold partialAt substituted
  change _ = (((s.reindex σ).map (contrReindexIso A σ).hom).sigmaSnd
    (Term.reindex a σ) (fun x h => ha (σ.mapElements.obj x) h) |>.map
      (contractionsAtIso (reindex A σ) (Term.reindex a σ)).hom).app
  unfold contrReindexIso
  erw [partialSigmaSnd_map, ← partialSigmaSnd_reindex]
  apply PartialSection.ext
  intro x hx
  apply Subtype.ext
  apply PiElement.ext
  intro y f r
  rfl


noncomputable def witnessAt (a : Term A) (ha : ∀ x h, a.val x = (s.val x h).1) : Contractible A :=
  Contractible.ofContraction a (ContractiblePaths.extend (c.reindex (projection A))
    (F.reindex (projection A)) (hF.reindex _) (partialAt s a ha))

theorem witnessAt_reindex (a : Term A) (ha : ∀ x h, a.val x = (s.val x h).1) :
    (witnessAt c F hF s a ha).reindex σ =
      witnessAt (c.reindex σ) (F.reindex σ) (hF.reindex _) (substituted s σ)
        (Term.reindex a σ) (fun x h => ha (σ.mapElements.obj x) h) := by
  change Contractible.ofContraction (Term.reindex a σ)
    (homogeneousReindex (ContractiblePaths.extend (c.reindex (projection A))
      (F.reindex (projection A)) (hF.reindex _) (partialAt s a ha)) (liftSub A σ)) = _
  rw [ContractiblePaths.extend_reindex, partialAt_reindex]
  rfl

theorem witness_reindex : (witness c F hF s).reindex σ =
    witness (c.reindex σ) (F.reindex σ) (hF.reindex _) (substituted s σ) := by
  change (witnessAt c F hF s (center c F s) (center_boundary c F hF s)).reindex σ = _
  rw [witnessAt_reindex]
  change witnessAt (c.reindex σ) (F.reindex σ) (hF.reindex _) (substituted s σ) _ _ =
    witnessAt (c.reindex σ) (F.reindex σ) (hF.reindex _) (substituted s σ) _ _
  congr 1
  exact center_reindex c F hF s σ

theorem extend_reindex : Term.map (contrReindexIso A σ).hom
    (Term.reindex (extend c F hF s) σ) =
      extend (c.reindex σ) (F.reindex σ) (hF.reindex _) (substituted s σ) :=
  (encodeContr_reindex (witness c F hF s) σ).trans
    (congrArg encodeContr (witness_reindex c F hF s σ))

end ContractibilityExtension
end SquareKit.Cubical.Cartesian.EquivalenceFamilies

namespace SquareKit.Cubical.Cartesian.CodeSystem.IsEquivSections
open CategoryTheory EquivalenceFamilies
universe u
noncomputable section
variable {Γ Δ Θ : Context.{u}} {A B : Family Γ} (f : A ⟶ B)
  (F : Filling A) (hF : F.Lawful) (G : Filling B) (hG : G.Lawful)
  (σ : Δ ⟶ Γ) (e : HomotopyEquivalence (Functor.whiskerLeft σ.mapElements f))
  (φ : Subcontext Δ) (s : PartialSection (reindex (isEquiv f) σ) φ)
  (τ : Θ ⟶ Δ)

def partialPiContr {Γ Δ : Context.{u}} (B : Family Γ) (C : Family (total B))
    (σ : Δ ⟶ Γ) (φ : Subcontext Δ) (s : PartialSection (reindex (pi B (contr C)) σ) φ) :
    PartialSection (contr (reindex C (liftSub B σ))) (φ.reindex (projection (reindex B σ))) :=
  ((s.map (piReindex B (contr C) σ)).app).map (contrReindexIso C (liftSub B σ)).hom

theorem contrReindex_hom_comp {Γ Δ Θ : Context.{u}} (A : Family Γ) (σ : Δ ⟶ Γ) (τ : Θ ⟶ Δ) :
    Functor.whiskerLeft τ.mapElements (contrReindexIso A σ).hom ≫
      (contrReindexIso (reindex A σ) τ).hom = (contrReindexIso A (τ ≫ σ)).hom := by
  ext x z
  rfl

theorem partialPiContr_reindex {Γ Δ Θ : Context.{u}} (B : Family Γ) (C : Family (total B))
    (σ : Δ ⟶ Γ) (φ : Subcontext Δ) (s : PartialSection (reindex (pi B (contr C)) σ) φ)
    (τ : Θ ⟶ Δ) :
    ((partialPiContr B C σ φ s).reindex (liftSub (reindex B σ) τ)).map
      (contrReindexIso (reindex C (liftSub B σ)) (liftSub (reindex B σ) τ)).hom =
    partialPiContr B C (τ ≫ σ) (φ.reindex τ) (s.reindex τ) := by
  apply PartialSection.ext
  intro x hx
  let ρ := liftSub (reindex B σ) τ
  let p := ((s.map (piReindex B (contr C) σ)).app).reindex ρ
  have hi := congrArg (fun m => m.app x (p.val x hx))
    (contrReindex_hom_comp C (liftSub B σ) ρ)
  refine hi.trans ?_
  apply congrArg ((contrReindexIso C (liftSub B (τ ≫ σ))).hom.app x)
  change ((s.map (piReindex B (contr C) σ)).app).val (ρ.mapElements.obj x) hx =
    (((s.reindex τ).map (piReindex B (contr C) (τ ≫ σ))).app).val x hx
  erw [PartialSection.app_val]


def partialBody : PartialSection (contr (reindex (fiber f) (liftSub B σ)))
    (φ.reindex (projection (reindex B σ))) := partialPiContr B (fiber f) σ φ s

theorem partialBody_reindex :
    ((partialBody f σ φ s).reindex (liftSub (reindex B σ) τ)).map
      (contrReindexIso (reindex (fiber f) (liftSub B σ)) (liftSub (reindex B σ) τ)).hom =
    partialBody f (τ ≫ σ) (φ.reindex τ) (s.reindex τ) :=
  partialPiContr_reindex B (fiber f) σ φ s τ

theorem fiberContractible_reindex : (fiberContractible f σ e).reindex (liftSub (reindex B σ) τ) =
    fiberContractible f (τ ≫ σ) (e.reindex τ) := by
  exact (Homotopy.fiberReindexInverse_map
    (Functor.whiskerLeft (projection B).mapElements f) (generic B) (liftSub B σ)
    (liftSub (reindex B σ) τ) e.fibers).symm

theorem extend_reindex : Term.reindex (extend f F hF G hG σ e φ s) τ =
    extend f F hF G hG (τ ≫ σ) (e.reindex τ) (φ.reindex τ) (s.reindex τ) := by
  let H := genericFiberFilling f F hF G hG
  have hH := genericFiberFilling_lawful f F hF G hG
  change Term.reindex (reindexedIsEquivSections f σ
    (ContractibilityExtension.witness (fiberContractible f σ e) (H.reindex (liftSub B σ))
      (hH.reindex _) (partialBody f σ φ s))) τ =
    reindexedIsEquivSections f (τ ≫ σ)
      (ContractibilityExtension.witness (fiberContractible f (τ ≫ σ) (e.reindex τ))
        (H.reindex (liftSub B (τ ≫ σ))) (hH.reindex _) (partialBody f (τ ≫ σ) (φ.reindex τ) (s.reindex τ)))
  rw [reindexedIsEquivSections_comp]
  apply congrArg (reindexedIsEquivSections f (τ ≫ σ))
  rw [ContractibilityExtension.witness_reindex]
  change ContractibilityExtension.witness _ _ _
    (((partialBody f σ φ s).reindex (liftSub (reindex B σ) τ)).map
      (contrReindexIso (reindex (fiber f) (liftSub B σ)) (liftSub (reindex B σ) τ)).hom) = _
  rw [partialBody_reindex, fiberContractible_reindex]
  rfl

end
end SquareKit.Cubical.Cartesian.CodeSystem.IsEquivSections

namespace SquareKit.Cubical.Cartesian.CodeSystem.Box
open CategoryTheory
universe u
noncomputable section
variable {Γ : Context.{u}} {φ : Subcontext Γ} {r : Term (interval Γ)} (b : Box Γ φ r)

def ambientFamily : LocalFamily (total (interval Γ)) :=
  decodedLocalFamily (raisedSub (projection (interval Γ)) ≫ b.base)

def faceFamily : LocalFamily (restrictContext (face (φ := φ) (r := r))) :=
  decodedLocalFamily b.partialCode

variable (f : b.faceFamily.family ⟶ Cartesian.reindex b.ambientFamily.family (restrictInclusion face))
  (E : HomotopyEquivalence f)

/-- An actual equivalence of the complete box face gives its normalized Glue code. -/
def glueFamily : LocalFamily (total (interval Γ)) :=
  LocalFamily.normalizedGlue face b.ambientFamily b.faceFamily f E

def glueCode : raisedContext (total (interval Γ)) ⟶ smallFamilyCodes.{u} :=
  (b.glueFamily f E).code

theorem glueCode_face : raisedSub (restrictInclusion face) ≫ b.glueCode f E = b.partialCode :=
  (LocalFamily.normalizedGlue_code_full face b.ambientFamily b.faceFamily f E).trans
    (code_decode b.partialCode)

theorem glueCode_source : raisedSub (graph r) ≫ b.glueCode f E = b.base :=
  (congrArg (fun q => raisedSub (cap (φ := φ) (r := r)) ≫ q) (b.glueCode_face f E)).trans b.partial_cap

theorem glueCode_tube :
    raisedSub (restrictInclusion (φ.reindex (projection (interval Γ)))) ≫ b.glueCode f E = b.tube :=
  (congrArg (fun q => raisedSub (includeRight (Glue.sourceFace r)
    (φ.reindex (projection (interval Γ)))) ≫ q) (b.glueCode_face f E)).trans b.partial_tube

theorem glueFamily_face : (b.glueFamily f E).reindex (restrictInclusion face) = b.faceFamily :=
  LocalFamily.normalizedGlue_full face b.ambientFamily b.faceFamily f E

end
end SquareKit.Cubical.Cartesian.CodeSystem.Box

namespace SquareKit.Cubical.Cartesian.UniversalTransport
open CategoryTheory
universe u
variable {Γ : Context.{u}}
  (a : raisedContext (total (interval Γ)) ⟶ smallFamilyCodes.{u}) (r s : Term (interval Γ))
theorem smallMap_at_equal_terms (h : r = s) (x : Γ.Elements)
    (v : (decode (raisedSub (graph r) ≫ a)).obj x) :
    HEq ((smallMap a r s).app x v) v := by
  cases h
  rw [smallMap_diagonal]
  rfl

theorem smallMap_at_equal (x : Γ.Elements) (h : r.val x = s.val x)
    (v : (decode (raisedSub (graph r) ≫ a)).obj x) :
    HEq ((smallMap a r s).app x v) v := by
  let φ := Subcontext.intervalEq r s
  let σ := restrictInclusion φ
  let z := (restrictContext φ).elementsMk x.obj ⟨x.val,h⟩
  have hr : Term.reindex r σ = Term.reindex s σ := by
    apply Term.ext
    intro y
    exact y.val.property
  have hd := smallMap_at_equal_terms (raisedSub (intervalSub σ) ≫ a)
    (Term.reindex r σ) (Term.reindex s σ) hr z v
  have hm := congrArg (fun f => f.app z v) (smallMap_reindex a r s σ)
  exact (heq_of_eq hm.symm).trans hd

def mapTo (B C : Family Γ) (hr : decode (raisedSub (graph r) ≫ a) = B)
    (hs : decode (raisedSub (graph s) ≫ a) = C) : B ⟶ C :=
  eqToHom hr.symm ≫ smallMap a r s ≫ eqToHom hs

noncomputable def equivalenceTo (B C : Family Γ) (hr : decode (raisedSub (graph r) ≫ a) = B)
    (hs : decode (raisedSub (graph s) ≫ a) = C) : HomotopyEquivalence (mapTo a r s B C hr hs) := by
  subst B
  subst C
  exact smallEquivalence a r s

theorem mapTo_at_equal (B C : Family Γ) (hr : decode (raisedSub (graph r) ≫ a) = B)
    (hs : decode (raisedSub (graph s) ≫ a) = C) (x : Γ.Elements) (h : r.val x = s.val x)
    (v : B.obj x) : HEq ((mapTo a r s B C hr hs).app x v) v := by
  subst B
  subst C
  exact smallMap_at_equal a r s x h v
end SquareKit.Cubical.Cartesian.UniversalTransport

namespace SquareKit.Cubical.Cartesian.IntervalTransport
open CategoryTheory
universe u
variable {Γ : Context.{u}} {A : Family (total (interval Γ))}
def mapTo (F : Filling A) (r s : Term (interval Γ)) (B C : Family Γ)
    (hr : reindex A (graph r) = B) (hs : reindex A (graph s) = C) : B ⟶ C :=
  eqToHom hr.symm ≫ map F r s ≫ eqToHom hs

noncomputable def equivalenceTo (F : Filling A) (hF : F.Lawful) (r s : Term (interval Γ))
    (B C : Family Γ) (hr : reindex A (graph r) = B) (hs : reindex A (graph s) = C) :
    HomotopyEquivalence (mapTo F r s B C hr hs) := by
  subst B
  subst C
  exact equivalence F hF r s
end SquareKit.Cubical.Cartesian.IntervalTransport

namespace SquareKit.Cubical.Cartesian.CodeSystem.Box
open CategoryTheory
universe u
noncomputable section
variable {Γ : Context.{u}} {φ : Subcontext Γ} {r : Term (interval Γ)} (b : Box Γ φ r)

theorem faceFamily_left : b.faceFamily.reindex (includeLeft (Glue.sourceFace r)
    (φ.reindex (projection (interval Γ)))) =
    b.ambientFamily.reindex (restrictInclusion (Glue.sourceFace r)) := by
  exact (decoded_glue_left (sourceCode b.base r) b.tube b.compatible).trans
    (decodedLocalFamily_reindex (raisedSub (projection (interval Γ)) ≫ b.base)
      (restrictInclusion (Glue.sourceFace r)))

theorem faceFamily_right : b.faceFamily.reindex (includeRight (Glue.sourceFace r)
    (φ.reindex (projection (interval Γ)))) = decodedLocalFamily b.tube :=
  decoded_glue_right (sourceCode b.base r) b.tube b.compatible

abbrev targetFamily : Family (restrictContext (face (φ := φ) (r := r))) :=
  Cartesian.reindex b.ambientFamily.family (restrictInclusion face)

def capMap : Cartesian.reindex b.faceFamily.family (includeLeft (Glue.sourceFace r)
    (φ.reindex (projection (interval Γ)))) ⟶
    Cartesian.reindex b.targetFamily (includeLeft (Glue.sourceFace r) (φ.reindex (projection (interval Γ)))) :=
  eqToHom (congrArg LocalFamily.family b.faceFamily_left)

def tubeMap : Cartesian.reindex b.faceFamily.family (includeRight (Glue.sourceFace r)
    (φ.reindex (projection (interval Γ)))) ⟶
    Cartesian.reindex b.targetFamily (includeRight (Glue.sourceFace r) (φ.reindex (projection (interval Γ)))) :=
  UniversalTransport.mapTo (raisedSub (tubeEvaluation φ) ≫ b.tube) (tubeVariable φ) (tubeSourceTerm φ r) _ _
    ((congrArg LocalFamily.family b.tubeLine_variable).trans
      (congrArg LocalFamily.family b.faceFamily_right).symm)
    (congrArg LocalFamily.family b.tubeLine_source)

def tubeEquivalence : HomotopyEquivalence b.tubeMap :=
  UniversalTransport.equivalenceTo (raisedSub (tubeEvaluation φ) ≫ b.tube)
    (tubeVariable φ) (tubeSourceTerm φ r) _ _ _ _

end
end SquareKit.Cubical.Cartesian.CodeSystem.Box

namespace SquareKit.Cubical.Cartesian.IntervalTransport
open CategoryTheory
universe u
variable {Γ : Context.{u}} {A : Family (total (interval Γ))}
theorem map_at_equal (F : Filling A) (hF : F.Lawful) (r s : Term (interval Γ))
    (x : Γ.Elements) (h : r.val x = s.val x) (a : (reindex A (graph r)).obj x) :
    HEq ((map F r s).app x a) a := by
  let σ := projection (reindex A (graph r))
  let z := extendObj (reindex A (graph r)) x a
  have hb := congrArg (fun t => t.val z) (line_source F hF r σ (generic _))
  change HEq ((line F r σ (generic _)).val
    (extendObj (interval (total (reindex A (graph r)))) z (s.val x))) a
  rw [← h]
  exact heq_of_eq hb
theorem mapTo_at_equal (F : Filling A) (hF : F.Lawful) (r s : Term (interval Γ))
    (B C : Family Γ) (hr : reindex A (graph r) = B) (hs : reindex A (graph s) = C)
    (x : Γ.Elements) (h : r.val x = s.val x) (a : B.obj x) :
    HEq ((mapTo F r s B C hr hs).app x a) a := by
  subst B
  subst C
  exact map_at_equal F hF r s x h a
end SquareKit.Cubical.Cartesian.IntervalTransport

namespace SquareKit.Cubical.Cartesian.CodeSystem.Box
open CategoryTheory
universe u
noncomputable section
variable {Γ : Context.{u}} {φ : Subcontext Γ} {r : Term (interval Γ)} (b : Box Γ φ r)

private theorem eqToHom_value_heq {Δ : Context.{u}} {A B : Family Δ}
    (h : A = B) (x : Δ.Elements) (a : A.obj x) : HEq ((eqToHom h).app x a) a := by
  cases h
  rfl

theorem mapsCompatibleOfDiagonal {Δ : Context.{u}} {α β : Subcontext Δ}
    {A B : Family (restrictContext (α.join β))}
    (hleft : Cartesian.reindex A (includeLeft α β) = Cartesian.reindex B (includeLeft α β))
    (m : Cartesian.reindex A (includeRight α β) ⟶ Cartesian.reindex B (includeRight α β))
    (hm : ∀ (x : (restrictContext (α.join β)).Elements)
      (_h : α.Holds (Maps.original x)) (k : β.Holds (Maps.original x)) (z : A.obj x),
      HEq (m.app (Maps.right x k) z) z) : Maps.Compatible (eqToHom hleft) m := by
  intro x h k z
  have hl := eqToHom_value_heq hleft (Maps.left x h) z
  exact eq_of_heq (hl.trans (hm x h k z).symm)

theorem mapsCompatibleOfCodeDiagonal {Δ : Context.{u}} {α β : Subcontext Δ}
    {A B : Family (restrictContext (α.join β))}
    (hleft : Cartesian.reindex A (includeLeft α β) = Cartesian.reindex B (includeLeft α β))
    (a : raisedContext (total (interval (restrictContext β))) ⟶ smallFamilyCodes.{u})
    (r s : Term (interval (restrictContext β)))
    (hr : decode (raisedSub (graph r) ≫ a) = Cartesian.reindex A (includeRight α β))
    (hs : decode (raisedSub (graph s) ≫ a) = Cartesian.reindex B (includeRight α β))
    (hdiag : ∀ (x : (restrictContext (α.join β)).Elements)
      (_h : α.Holds (Maps.original x)) (k : β.Holds (Maps.original x)),
      r.val (Maps.right x k) = s.val (Maps.right x k)) :
    Maps.Compatible (eqToHom hleft) (UniversalTransport.mapTo a r s _ _ hr hs) :=
  mapsCompatibleOfDiagonal hleft _
    (fun x h k z => UniversalTransport.mapTo_at_equal a r s _ _ hr hs (Maps.right x k) (hdiag x h k) z)

theorem faceMaps_compatible : Maps.Compatible b.capMap b.tubeMap :=
  mapsCompatibleOfCodeDiagonal (A := b.faceFamily.family) (B := b.targetFamily)
    (congrArg LocalFamily.family b.faceFamily_left) (raisedSub (tubeEvaluation φ) ≫ b.tube)
    (tubeVariable φ) (tubeSourceTerm φ r) _ _ (fun _ h _ => h)

def faceMap : b.faceFamily.family ⟶ b.targetFamily :=
  Maps.glue b.capMap b.tubeMap b.faceMaps_compatible

def capEquivalence : HomotopyEquivalence b.capMap :=
  HomotopyEquivalence.ofIso (eqToIso (congrArg LocalFamily.family b.faceFamily_left))
    ((b.ambientFamily.reindex (restrictInclusion (Glue.sourceFace r))).toFilling)
    ((b.ambientFamily.reindex (restrictInclusion (Glue.sourceFace r))).toFilling_lawful)

def faceEquivalence : HomotopyEquivalence b.faceMap :=
  Equivalences.glueMaps b.faceFamily (b.ambientFamily.reindex (restrictInclusion face))
    b.capMap b.tubeMap b.faceMaps_compatible b.capEquivalence b.tubeEquivalence

/-- Fill the small code box with the actual arbitrary-source transport equivalence. -/
def fillCode : raisedContext (total (interval Γ)) ⟶ smallFamilyCodes.{u} :=
  b.glueCode b.faceMap b.faceEquivalence

theorem fillCode_source : raisedSub (graph r) ≫ b.fillCode = b.base :=
  b.glueCode_source b.faceMap b.faceEquivalence

theorem fillCode_tube : raisedSub (restrictInclusion (φ.reindex (projection (interval Γ)))) ≫
    b.fillCode = b.tube := b.glueCode_tube b.faceMap b.faceEquivalence

end
end SquareKit.Cubical.Cartesian.CodeSystem.Box

namespace SquareKit.Cubical.Cartesian.CodeSystem.Sections
open CategoryTheory
universe u
variable {Γ Δ : Context.{u}} {φ ψ : Subcontext Γ}
  {A : Family (restrictContext (φ.join ψ))}
  (a : Term (reindex A (includeLeft φ ψ)))
  (b : Term (reindex A (includeRight φ ψ))) (c : Compatible a b) (σ : Δ ⟶ Γ)

include c in
theorem Compatible.reindex : Compatible (φ := φ.reindex σ) (ψ := ψ.reindex σ)
    (A := reindex A (restrictSubstitution (φ.join ψ) σ))
    (Term.reindex a (restrictSubstitution φ σ))
    (Term.reindex b (restrictSubstitution ψ σ)) := by
  intro x h k
  exact c ((restrictSubstitution (φ.join ψ) σ).mapElements.obj x) h k

theorem glue_reindex : Term.reindex (glue a b c) (restrictSubstitution (φ.join ψ) σ) =
    glue (φ := φ.reindex σ) (ψ := ψ.reindex σ)
      (A := reindex A (restrictSubstitution (φ.join ψ) σ)) (Term.reindex a (restrictSubstitution φ σ))
      (Term.reindex b (restrictSubstitution ψ σ)) (Compatible.reindex a b c σ) := by
  apply Term.ext
  intro x
  let y := (restrictSubstitution (φ.join ψ) σ).mapElements.obj x
  by_cases h : φ.Holds (Maps.original y)
  · exact (value_left a b y h).trans
      (value_left (φ := φ.reindex σ) (ψ := ψ.reindex σ)
        (A := reindex A (restrictSubstitution (φ.join ψ) σ)) (Term.reindex a (restrictSubstitution φ σ))
        (Term.reindex b (restrictSubstitution ψ σ)) x h).symm
  · have k : ψ.Holds (Maps.original y) := y.val.property.resolve_left h
    exact (value_right a b c y k).trans
      (value_right (φ := φ.reindex σ) (ψ := ψ.reindex σ)
        (A := reindex A (restrictSubstitution (φ.join ψ) σ)) (Term.reindex a (restrictSubstitution φ σ))
        (Term.reindex b (restrictSubstitution ψ σ)) (Compatible.reindex a b c σ) x k).symm
end SquareKit.Cubical.Cartesian.CodeSystem.Sections

namespace SquareKit.Cubical.Cartesian.EquivalenceFamilies
open CategoryTheory
universe u
variable {Γ : Context.{u}} {A B : Family Γ} (e : A ≅ B)
  {a b : Term A} {φ : Subcontext Γ}
  (s : PartialSection (homogeneousPath A a b) φ)
theorem pathBoundary_map : (s.map (pathMap e.hom a b)).pathBoundary =
    s.pathBoundary.map (Functor.whiskerLeft (projection (interval Γ)).mapElements e.hom) := by
  apply PartialSection.ext
  intro x hx
  rcases (Subcontext.full_join _ _ x).mp hx with h | h
  · erw [PartialSection.pathBoundary_old (s.map (pathMap e.hom a b)) x hx h]
    change _ = e.hom.app _ (s.pathBoundary.val x hx)
    erw [PartialSection.pathBoundary_old s x hx h]
    rfl
  · rcases (Subcontext.full_join _ _ x).mp h with h | h
    · exact eq_of_heq ((PartialSection.pathBoundary_zero _ x hx h).trans
        (heq_of_eq (congrArg (e.hom.app _) (eq_of_heq (s.pathBoundary_zero x hx h)))).symm)
    · exact eq_of_heq ((PartialSection.pathBoundary_one _ x hx h).trans
        (heq_of_eq (congrArg (e.hom.app _) (eq_of_heq (s.pathBoundary_one x hx h)))).symm)
namespace ContractiblePaths
variable (c : Contractible A) (F : Filling A) (hF : F.Lawful)
theorem line_transport : line (Contractible.map e c) (F.transport e)
    (s.map (pathMap e.hom a b)) =
      Term.map (Functor.whiskerLeft (projection (interval Γ)).mapElements e.hom) (line c F s) := by
  unfold line
  rw [pathBoundary_map]
  exact (c.reindex (projection (interval Γ))).extend_transport
    (Functor.isoWhiskerLeft (projection (interval Γ)).mapElements e)
    (F.reindex (projection (interval Γ))) s.pathBoundary

theorem extend_transport : extend (Contractible.map e c) (F.transport e)
    (Filling.transport_lawful e F hF) (s.map (pathMap e.hom a b)) =
      Term.map (pathMap e.hom a b) (extend c F hF s) := by
  apply pathApp_injective
  exact line_transport e s c F
end ContractiblePaths
noncomputable def contrMap {Γ : Context.{u}} {A B : Family Γ} (e : A ≅ B) : contr A ⟶ contr B :=
  let σ := projection (contr A)
  let c := decodeContr (Term.map (contrReindexIso A σ).hom (generic (contr A)))
  let d := Contractible.map (Functor.isoWhiskerLeft σ.mapElements e) c
  decodeMap (lam (Term.map (contrReindexIso B σ).inv (encodeContr d)))

theorem map_decodeMap_lam {Γ : Context.{u}} {A B : Family Γ}
    (t : Term (reindex B (projection A))) (s : Term A) :
    Term.map (decodeMap (lam t)) s = Term.reindex t (pair (𝟙 Γ) s) := rfl

theorem contrReindex_hom_id {Γ : Context.{u}} (B : Family Γ) :
    (contrReindexIso B (𝟙 Γ)).hom = 𝟙 (contr B) := by
  ext x a
  apply Sigma.ext
  · rfl
  · apply heq_of_eq
    apply PiElement.ext
    intro y f b
    apply Subtype.ext
    apply PiElement.ext
    intro z g r
    rfl

theorem contrReindex_inv_id {Γ : Context.{u}} (B : Family Γ) :
    (contrReindexIso B (𝟙 Γ)).inv = 𝟙 (contr B) := by
  have h := (contrReindexIso B (𝟙 Γ)).hom_inv_id
  rw [contrReindex_hom_id] at h
  ext x a
  exact congrArg (fun m => m.app x a) h

theorem contrMap_encode {Γ : Context.{u}} {A B : Family Γ} (e : A ≅ B) (c : Contractible A) :
    Term.map (contrMap e) (encodeContr c) = encodeContr (Contractible.map e c) := by
  unfold contrMap
  rw [map_decodeMap_lam, contrInverse_reindex]
  rw [encodeContr_reindex]
  rw [Contractible.map_reindex]
  rw [← decodeContr_reindex]
  have hc : Term.map (contrReindexIso (reindex A (projection (contr A)))
      (pair (𝟙 Γ) (encodeContr c))).hom
      (Term.reindex (Term.map (contrReindexIso A (projection (contr A))).hom (generic (contr A)))
        (pair (𝟙 Γ) (encodeContr c))) = encodeContr c := by
    apply Term.ext
    intro x
    apply Sigma.ext
    · rfl
    · apply heq_of_eq
      apply PiElement.ext
      intro y f a
      apply Subtype.ext
      apply PiElement.ext
      intro z g r
      rfl
  rw [hc]
  erw [decode_encodeContr]
  change Term.map (contrReindexIso B (𝟙 Γ)).inv (encodeContr (Contractible.map e c)) = _
  rw [contrReindex_inv_id]
  rfl
end SquareKit.Cubical.Cartesian.EquivalenceFamilies

namespace SquareKit.Cubical.Cartesian.EquivalenceFamilies
open CategoryTheory
universe u
 theorem contrMap_section {Γ Δ : Context.{u}} {A B : Family Γ} (e : A ≅ B)
    (σ : Δ ⟶ Γ) (s : Term (reindex (contr A) σ)) :
    Term.map (Functor.whiskerLeft σ.mapElements (contrMap e)) s =
      Term.map (contrReindexIso B σ).inv
        (encodeContr (Contractible.map (Functor.isoWhiskerLeft σ.mapElements e)
          (decodeContr (Term.map (contrReindexIso A σ).hom s)))) := by
  change Term.reindex
    (Term.map (contrReindexIso B (projection (contr A))).inv
      (encodeContr (Contractible.map (Functor.isoWhiskerLeft (projection (contr A)).mapElements e)
        (decodeContr (Term.map (contrReindexIso A (projection (contr A))).hom (generic (contr A)))))))
    (pair σ s) = _
  rw [contrInverse_reindex, encodeContr_reindex, Contractible.map_reindex, ← decodeContr_reindex]
  have hc : Term.map (contrReindexIso (reindex A (projection (contr A))) (pair σ s)).hom
      (Term.reindex (Term.map (contrReindexIso A (projection (contr A))).hom (generic (contr A)))
        (pair σ s)) = Term.map (contrReindexIso A σ).hom s := by
    apply Term.ext
    intro x
    apply Sigma.ext
    · rfl
    · apply heq_of_eq
      apply PiElement.ext
      intro y f a
      apply Subtype.ext
      apply PiElement.ext
      intro z g r
      rfl
  rw [hc]
  rfl
theorem contrMap_reindexed_encode {Γ Δ : Context.{u}} {A B : Family Γ} (e : A ≅ B)
    (σ : Δ ⟶ Γ) (c : Contractible (reindex A σ)) :
    Term.map (Functor.whiskerLeft σ.mapElements (contrMap e))
      (Term.map (contrReindexIso A σ).inv (encodeContr c)) =
      Term.map (contrReindexIso B σ).inv
        (encodeContr (Contractible.map (Functor.isoWhiskerLeft σ.mapElements e) c)) := by
  rw [contrMap_section]
  erw [Term.map_iso_roundtrip (contrReindexIso A σ).symm, decode_encodeContr]

end SquareKit.Cubical.Cartesian.EquivalenceFamilies

namespace SquareKit.Cubical.Cartesian.EquivalenceFamilies
open CategoryTheory
universe u
def contrEval {Γ : Context.{u}} {A : Family Γ} (x : Γ.Elements) (p : (contr A).obj x)
    (b : A.obj x) (r : (interval Γ).obj x) : A.obj x :=
  ((p.2.val (𝟙 (extendObj A x p.1)) b).val.val
    (𝟙 (extendObj (reindex A (projection A)) (extendObj A x p.1) b)) r)
theorem contrEval_encode {Γ : Context.{u}} {A : Family Γ} (c : Contractible A)
    (x : Γ.Elements) (b : A.obj x) (r : (interval Γ).obj x) :
    contrEval x ((encodeContr c).val x) b r = (c.contraction x b).val.val (𝟙 x) r := by
  have h := congrArg (fun d : Contractible A => (d.contraction x b).val.val (𝟙 x) r)
    (decode_encodeContr c)
  change contrEval x ((encodeContr c).val x) (A.map (𝟙 x) b) r = _ at h
  simpa only [A.map_id_apply] using h
theorem contrEval_reindex {Γ Δ : Context.{u}} {A : Family Γ} (σ : Δ ⟶ Γ)
    (x : Δ.Elements) (p : (reindex (contr A) σ).obj x) (b : (reindex A σ).obj x)
    (r : (interval Δ).obj x) :
    contrEval x ((contrReindexIso A σ).hom.app x p) b r = contrEval (σ.mapElements.obj x) p b r := by
  let μ := liftSub A σ
  let ν := liftSub (reindex A (projection A)) μ
  let q := extendObj (reindex A σ) x p.1
  let w := extendObj (reindex (reindex A (projection A)) μ) q b
  change (p.2.val (μ.mapElements.map (𝟙 q)) b).val.val (ν.mapElements.map (𝟙 w)) r = _
  erw [μ.mapElements.map_id q, ν.mapElements.map_id w]
  rfl

theorem contrEval_map {Γ : Context.{u}} {A B : Family Γ} (e : A ≅ B)
    (x : Γ.Elements) (p : (contr A).obj x) (b : B.obj x) (r : (interval Γ).obj x) :
    contrEval x ((contrMap e).app x p) b r = e.hom.app x (contrEval x p (e.inv.app x b) r) := by
  let σ := projection (contr A)
  let z := extendObj (contr A) x p
  let c := decodeContr (Term.map (contrReindexIso A σ).hom (generic (contr A)))
  have h := congrArg (Term.map (contrReindexIso B σ).hom) (contrMap_section e σ (generic (contr A)))
  have h' := h.trans (Term.map_iso_roundtrip (contrReindexIso B σ).symm
    (encodeContr (Contractible.map (Functor.isoWhiskerLeft σ.mapElements e) c)))
  have hv := (congrArg (fun t => contrEval z (t.val z) b r) h').trans
    (contrEval_encode (Contractible.map (Functor.isoWhiskerLeft σ.mapElements e) c) z b r)
  change _ = e.hom.app x (contrEval x p (A.map (𝟙 x) (e.inv.app x b)) r) at hv
  change contrEval z ((contrReindexIso B σ).hom.app z ((contrMap e).app x p)) b r = _ at hv
  have hr := contrEval_reindex (A := B) σ z ((contrMap e).app x p) b r
  have out := hr.symm.trans hv
  change contrEval x ((contrMap e).app x p) b r =
    e.hom.app x (contrEval x p (A.map (𝟙 x) (e.inv.app x b)) r) at out
  rw [A.map_id_apply] at out
  exact out
theorem contractionAt_eval {Γ : Context.{u}} {A : Family Γ} (a : Term A)
    (x : Γ.Elements) (p : (reindex (contractions A) (pair (𝟙 Γ) a)).obj x)
    (q : (contr A).obj x) (h : a.val x = q.1) (hp : HEq p q.2)
    (b : A.obj x) (r : (interval Γ).obj x) :
    (((contractionsAtIso A a).hom.app x p).val (𝟙 x) b).val.val
      (𝟙 (extendObj A x b)) r = contrEval x q b r := by
  rcases q with ⟨v,q⟩
  cases h
  cases hp
  rfl
end SquareKit.Cubical.Cartesian.EquivalenceFamilies

namespace SquareKit.Cubical.Cartesian.EquivalenceFamilies.ContractiblePaths
open CategoryTheory
universe u
variable {Γ Δ : Context.{u}} {A : Family Γ} (c : Contractible A) (F : Filling A) (hF : F.Lawful)
  {a b : Term A} {φ : Subcontext Γ} (s : PartialSection (homogeneousPath A a b) φ)
  (σ : Δ ⟶ Γ) {B : Family Δ} (e : reindex A σ ≅ B) {a' b' : Term B}
  (t : PartialSection (homogeneousPath B a' b') (φ.reindex σ))
include hF in
theorem line_transport_boundary
    (ht : t.pathBoundary = (s.pathBoundary.reindex (intervalSub σ)).map
      (Functor.whiskerLeft (projection (interval Δ)).mapElements e.hom)) :
    line (Contractible.map e (c.reindex σ)) ((F.reindex σ).transport e) t =
      Term.map (Functor.whiskerLeft (projection (interval Δ)).mapElements e.hom)
        (Term.reindex (line c F s) (intervalSub σ)) := by
  unfold line
  rw [ht]
  have hm := ((c.reindex σ).reindex (projection (interval Δ))).extend_transport
    (Functor.isoWhiskerLeft (projection (interval Δ)).mapElements e)
    ((F.reindex σ).reindex (projection (interval Δ)))
    (s.pathBoundary.reindex (intervalSub σ))
  exact hm.trans (congrArg (Term.map (Functor.whiskerLeft (projection (interval Δ)).mapElements e.hom))
    ((c.reindex (projection (interval Γ))).extend_reindex
      (F.reindex (projection (interval Γ))) (hF.reindex _) s.pathBoundary (intervalSub σ)))
end SquareKit.Cubical.Cartesian.EquivalenceFamilies.ContractiblePaths

namespace SquareKit.Cubical.Cartesian.EquivalenceFamilies.ContractibilityExtension
open CategoryTheory
universe u
variable {Γ : Context.{u}} {A B : Family Γ} (e : A ≅ B) (c : Contractible A)
  (F : Filling A) (hF : F.Lawful) {φ : Subcontext Γ} (s : PartialSection (contr A) φ)
theorem center_transport : center (Contractible.map e c) (F.transport e) (s.map (contrMap e)) =
    Term.map e.hom (center c F s) := by
  change (Contractible.map e c).extend (F.transport e) (s.sigmaFst.map e.hom) = _
  exact c.extend_transport e F s.sigmaFst
def inverseContext : total B ⟶ total A := pair (projection B) (Term.map (Functor.whiskerLeft (projection B).mapElements e.inv) (generic B))
theorem partialAt_eval (a : Term A) (ha : ∀ x h, a.val x = (s.val x h).1)
    (x : (total (interval (total A))).Elements)
    (hx : (φ.reindex (projection (interval (total A)) ≫ projection A)).Holds x) :
    (partialAt s a ha).pathApp.val x hx =
      contrEval ((projection A).mapElements.obj ((projection (interval (total A))).mapElements.obj x))
        (s.val _ hx) x.val.1.2 x.val.2 := by
  erw [PartialSection.pathApp_val]
  unfold partialAt
  erw [PartialSection.app_val]
  exact contractionAt_eval a _ _ _ (ha _ hx) (s.sigmaSnd_val a ha _ hx) _ _

theorem partialAt_boundary_transport (a : Term A) (ha : ∀ x h, a.val x = (s.val x h).1) :
    (partialAt (s.map (contrMap e)) (Term.map e.hom a)
      (fun x h => congrArg (e.hom.app x) (ha x h))).pathBoundary =
    ((partialAt s a ha).pathBoundary.reindex (intervalSub (inverseContext e))).map
      (Functor.whiskerLeft (projection (interval (total B)) ≫ projection B).mapElements e.hom) := by
  apply PartialSection.ext
  intro x hx
  rcases (Subcontext.full_join _ _ x).mp hx with h | h
  · erw [PartialSection.pathBoundary_old _ x hx h]
    change _ = e.hom.app _ (((partialAt s a ha).pathBoundary).val
      ((intervalSub (inverseContext e)).mapElements.obj x) hx)
    erw [PartialSection.pathBoundary_old (partialAt s a ha) ((intervalSub (inverseContext e)).mapElements.obj x) hx h]
    erw [partialAt_eval, partialAt_eval]
    exact contrEval_map e _ _ _ _
  · rcases (Subcontext.full_join _ _ x).mp h with h | h
    · exact eq_of_heq ((PartialSection.pathBoundary_zero _ x hx h).trans
        (heq_of_eq (congrArg (e.hom.app _) (eq_of_heq
          ((partialAt s a ha).pathBoundary_zero ((intervalSub (inverseContext e)).mapElements.obj x) hx h)))).symm)
    · exact eq_of_heq ((PartialSection.pathBoundary_one _ x hx h).trans
        (heq_of_eq ((e.inv_hom_id_app_apply _ _).symm.trans
          (congrArg (e.hom.app _) (eq_of_heq ((partialAt s a ha).pathBoundary_one ((intervalSub (inverseContext e)).mapElements.obj x) hx h)).symm))))
theorem witnessAt_transport (a : Term A) (ha : ∀ x h, a.val x = (s.val x h).1) :
    witnessAt (Contractible.map e c) (F.transport e) (Filling.transport_lawful e F hF)
      (s.map (contrMap e)) (Term.map e.hom a) (fun x h => congrArg (e.hom.app x) (ha x h)) =
      Contractible.map e (witnessAt c F hF s a ha) := by
  let ρ := inverseContext e
  let i := Functor.isoWhiskerLeft (projection B).mapElements e
  have hb := ContractiblePaths.line_transport_boundary (c.reindex (projection A))
    (F.reindex (projection A)) (hF.reindex _) (partialAt s a ha) ρ i
    (partialAt (s.map (contrMap e)) (Term.map e.hom a)
      (fun x h => congrArg (e.hom.app x) (ha x h))) (partialAt_boundary_transport e s a ha)
  refine Contractible.ext (c := witnessAt (Contractible.map e c) (F.transport e)
    (Filling.transport_lawful e F hF) (s.map (contrMap e)) (Term.map e.hom a)
      (fun x h => congrArg (e.hom.app x) (ha x h)))
    (d := Contractible.map e (witnessAt c F hF s a ha)) rfl ?_
  intro x b y f r
  have hv := congrArg (fun t => t.val
    (extendObj (interval (total B)) (extendObj B y (B.map f b)) r)) hb
  change _ = e.hom.app y
    ((ContractiblePaths.line (c.reindex (projection A)) (F.reindex (projection A))
      (partialAt s a ha)).val (extendObj (interval (total A))
        (extendObj A y (e.inv.app y (B.map f b))) r)) at hv
  refine hv.trans ?_
  apply congrArg (e.hom.app y)
  exact congrArg (fun v => (show A.obj y from (ContractiblePaths.line (c.reindex (projection A))
    (F.reindex (projection A)) (partialAt s a ha)).val
      (extendObj (interval (total A)) (extendObj A y v) r))) (e.inv.naturality_apply f b)

 theorem witness_transport : witness (Contractible.map e c) (F.transport e)
    (Filling.transport_lawful e F hF) (s.map (contrMap e)) =
      Contractible.map e (witness c F hF s) := by
  change witnessAt (Contractible.map e c) (F.transport e) (Filling.transport_lawful e F hF)
    (s.map (contrMap e)) (center (Contractible.map e c) (F.transport e) (s.map (contrMap e))) _ = _
  have aux (u v : Term B) (hu : ∀ x h, u.val x = ((s.map (contrMap e)).val x h).1)
      (hv : ∀ x h, v.val x = ((s.map (contrMap e)).val x h).1) (h : u = v) :
      witnessAt (Contractible.map e c) (F.transport e) (Filling.transport_lawful e F hF)
        (s.map (contrMap e)) u hu =
      witnessAt (Contractible.map e c) (F.transport e) (Filling.transport_lawful e F hF)
        (s.map (contrMap e)) v hv := by cases h; rfl
  exact (aux _ _ _ _ (center_transport e c F s)).trans
    (witnessAt_transport e c F hF s _ (center_boundary c F hF s))
theorem extend_transport : extend (Contractible.map e c) (F.transport e)
    (Filling.transport_lawful e F hF) (s.map (contrMap e)) =
      Term.map (contrMap e) (extend c F hF s) :=
  (congrArg encodeContr (witness_transport e c F hF s)).trans
    (contrMap_encode e (witness c F hF s)).symm
end SquareKit.Cubical.Cartesian.EquivalenceFamilies.ContractibilityExtension

namespace SquareKit.Cubical.Cartesian.SmallUniverse.CodeFilling
open CategoryTheory
universe u
variable (fill : ∀ {Γ : Context.{u}} {φ : Subcontext Γ} {r : Term (interval Γ)},
  CodeSystem.Box Γ φ r → (raisedContext (total (interval Γ)) ⟶ smallFamilyCodes.{u}))
variable (source : ∀ {Γ : Context.{u}} {φ : Subcontext Γ} {r : Term (interval Γ)}
  (b : CodeSystem.Box Γ φ r), raisedSub (graph r) ≫ fill b = b.base)
variable (tube : ∀ {Γ : Context.{u}} {φ : Subcontext Γ} {r : Term (interval Γ)}
  (b : CodeSystem.Box Γ φ r),
  raisedSub (restrictInclusion (φ.reindex (projection (interval Γ)))) ≫ fill b = b.tube)
variable (uniform : ∀ {Γ Δ : Context.{u}} {φ : Subcontext Γ} {r : Term (interval Γ)}
  (b : CodeSystem.Box Γ φ r) (σ : Δ ⟶ Γ),
  raisedSub (intervalSub σ) ≫ fill b = fill (b.reindex σ))

def raiseRepresentedCode {I : Cube}
    (c : raisedContext (total (interval (representable.{u} I))) ⟶ smallFamilyCodes.{u}) :
    total (interval (representable.{u+1} I)) ⟶ smallFamilyCodes.{u} where
  app J := TypeCat.ofHom (fun x => c.app J ⟨⟨⟨x.1.down⟩,⟨x.2.down⟩⟩⟩)
  naturality J K f := by
    apply ConcreteCategory.hom_ext
    intro x
    exact c.naturality_apply f ⟨⟨⟨x.1.down⟩,⟨x.2.down⟩⟩⟩

def fillRepresented {I : Cube} {φ : Subcontext (representable.{u+1} I)}
    {r : Term (interval (representable.{u+1} I))}
    (b : OpenBox (family (total (interval (representable.{u+1} I)))) φ r) :
    Term (family (total (interval (representable.{u+1} I)))) :=
  term (raiseRepresentedCode (fill (chartBox b (NativeDecode.representedRaise I))))

include source tube in
theorem fillRepresented_fills {I : Cube} {φ : Subcontext (representable.{u+1} I)}
    {r : Term (interval (representable.{u+1} I))}
    (b : OpenBox (family (total (interval (representable.{u+1} I)))) φ r) :
    b.Fills (fillRepresented fill b) := by
  constructor
  · apply Term.ext
    intro x
    exact congrArg (fun c => c.app x.obj (ULift.up (ULift.up x.val.down)))
      (source (chartBox b (NativeDecode.representedRaise I)))
  · intro x hx
    exact congrArg (fun c => c.app x.obj
      (ULift.up (⟨⟨⟨x.val.1.down⟩,⟨x.val.2.down⟩⟩,hx⟩ :
        (restrictContext ((chartFace φ (NativeDecode.representedRaise I)).reindex
          (projection (interval (representable.{u} I))))).obj x.obj)))
      (tube (chartBox b (NativeDecode.representedRaise I)))

include uniform in
theorem fillRepresented_reindex {I J : Cube} {φ : Subcontext (representable.{u+1} I)}
    {r : Term (interval (representable.{u+1} I))}
    (b : OpenBox (family (total (interval (representable.{u+1} I)))) φ r) (f : J ⟶ I) :
    Term.reindex (fillRepresented fill b) (intervalSub (representableMap f)) =
      fillRepresented fill (b.reindex (representableMap f)) := by
  apply Term.ext
  intro x
  exact congrArg (fun c => c.app x.obj ⟨⟨⟨x.val.1.down⟩,⟨x.val.2.down⟩⟩⟩)
    (uniform (chartBox b (NativeDecode.representedRaise I)) (representableMap f))

def localFilling (Ω : Context.{u+1}) : LocalFilling (family Ω) where
  fill _ _ _ b := fillRepresented fill b

include source tube uniform in
theorem localFilling_lawful (Ω : Context.{u+1}) : (localFilling fill Ω).Lawful where
  fills _ _ _ b := fillRepresented_fills fill source tube b
  uniform _ _ _ b f := (fillRepresented_reindex fill uniform b f).symm

def filling (Ω : Context.{u+1}) : Filling (family Ω) :=
  (localFilling fill Ω).toFilling (localFilling_lawful fill source tube uniform Ω)

theorem filling_lawful (Ω : Context.{u+1}) : (filling fill source tube uniform Ω).Lawful :=
  (localFilling fill Ω).toFilling_lawful (localFilling_lawful fill source tube uniform Ω)

theorem filling_reindex {Ω Λ : Context.{u+1}} (σ : Λ ⟶ Ω) :
    (filling fill source tube uniform Ω).reindex σ = filling fill source tube uniform Λ := rfl
end SquareKit.Cubical.Cartesian.SmallUniverse.CodeFilling

namespace SquareKit.Cubical.Cartesian.UniversalTransport
open CategoryTheory
universe u
variable {Γ Δ : Context.{u}}
  (a : raisedContext (total (interval Γ)) ⟶ smallFamilyCodes.{u}) (r s : Term (interval Γ))
  (B C : Family Γ) (hr : decode (raisedSub (graph r) ≫ a) = B)
  (hs : decode (raisedSub (graph s) ≫ a) = C) (σ : Δ ⟶ Γ)
theorem mapTo_reindex :
    mapTo (raisedSub (intervalSub σ) ≫ a) (Term.reindex r σ) (Term.reindex s σ)
      (reindex B σ) (reindex C σ) (congrArg (fun A => reindex A σ) hr)
      (congrArg (fun A => reindex A σ) hs) =
    Functor.whiskerLeft σ.mapElements (mapTo a r s B C hr hs) := by
  subst B
  subst C
  exact smallMap_reindex a r s σ

theorem equivalenceTo_reindex :
    HEq ((equivalenceTo a r s B C hr hs).reindex σ)
      (equivalenceTo (raisedSub (intervalSub σ) ≫ a) (Term.reindex r σ) (Term.reindex s σ)
        (reindex B σ) (reindex C σ) (congrArg (fun A => reindex A σ) hr)
        (congrArg (fun A => reindex A σ) hs)) := by
  subst B
  subst C
  exact smallEquivalence_reindex a r s σ
end SquareKit.Cubical.Cartesian.UniversalTransport

namespace SquareKit.Cubical.Cartesian.CodeSystem.Box
open CategoryTheory
universe u
variable {Γ Δ : Context.{u}} {φ : Subcontext Γ} {r : Term (interval Γ)} (b : Box Γ φ r) (σ : Δ ⟶ Γ)
theorem ambientFamily_reindex :
    b.ambientFamily.reindex (intervalSub σ) = (b.reindex σ).ambientFamily :=
  (decodedLocalFamily_reindex _ _).symm

theorem faceFamily_reindex :
    b.faceFamily.reindex (restrictSubstitution face (intervalSub σ)) = (b.reindex σ).faceFamily := by
  change (decodedLocalFamily b.partialCode).reindex _ = decodedLocalFamily _
  rw [← decodedLocalFamily_reindex, partial_reindex]

theorem tubeVariable_reindex :
    Term.reindex (tubeVariable φ) (restrictSubstitution (φ.reindex (projection (interval Γ))) (intervalSub σ)) =
      tubeVariable (φ.reindex σ) := rfl

theorem tubeSourceTerm_reindex :
    Term.reindex (tubeSourceTerm φ r) (restrictSubstitution (φ.reindex (projection (interval Γ))) (intervalSub σ)) =
      tubeSourceTerm (φ.reindex σ) (Term.reindex r σ) := rfl

theorem tubeCode_reindex :
    raisedSub (intervalSub (restrictSubstitution (φ.reindex (projection (interval Γ))) (intervalSub σ))) ≫
      (raisedSub (tubeEvaluation φ) ≫ b.tube) =
    raisedSub (tubeEvaluation (φ.reindex σ)) ≫ (b.reindex σ).tube := rfl
end SquareKit.Cubical.Cartesian.CodeSystem.Box

namespace SquareKit.Cubical.Cartesian.CodeSystem.Maps
open CategoryTheory
universe u
variable {Γ Δ : Context.{u}} {φ ψ : Subcontext Γ}
  {A B : Family (restrictContext (φ.join ψ))}
  (a : reindex A (includeLeft φ ψ) ⟶ reindex B (includeLeft φ ψ))
  (b : reindex A (includeRight φ ψ) ⟶ reindex B (includeRight φ ψ))
  (c : Compatible a b) (σ : Δ ⟶ Γ)
include c in
theorem Compatible.reindex : Compatible (φ := φ.reindex σ) (ψ := ψ.reindex σ)
    (A := reindex A (restrictSubstitution (φ.join ψ) σ))
    (B := reindex B (restrictSubstitution (φ.join ψ) σ))
    (Functor.whiskerLeft (restrictSubstitution φ σ).mapElements a)
    (Functor.whiskerLeft (restrictSubstitution ψ σ).mapElements b) := by
  intro x h k z
  exact c ((restrictSubstitution (φ.join ψ) σ).mapElements.obj x) h k z

theorem glue_reindex :
    Functor.whiskerLeft (restrictSubstitution (φ.join ψ) σ).mapElements (glue a b c) =
    glue (φ := φ.reindex σ) (ψ := ψ.reindex σ)
      (A := reindex A (restrictSubstitution (φ.join ψ) σ))
      (B := reindex B (restrictSubstitution (φ.join ψ) σ))
      (Functor.whiskerLeft (restrictSubstitution φ σ).mapElements a)
      (Functor.whiskerLeft (restrictSubstitution ψ σ).mapElements b)
      (Compatible.reindex a b c σ) := by
  ext x z
  rfl
end SquareKit.Cubical.Cartesian.CodeSystem.Maps

namespace SquareKit.Cubical.Cartesian.UniversalTransport
open CategoryTheory
universe u
theorem equivalenceTo_congr {Γ : Context.{u}}
    (a : raisedContext (total (interval Γ)) ⟶ smallFamilyCodes.{u}) (r s : Term (interval Γ))
    (B C B' C' : Family Γ) (hr : decode (raisedSub (graph r) ≫ a) = B)
    (hs : decode (raisedSub (graph s) ≫ a) = C)
    (hr' : decode (raisedSub (graph r) ≫ a) = B')
    (hs' : decode (raisedSub (graph s) ≫ a) = C') :
    HEq (equivalenceTo a r s B C hr hs) (equivalenceTo a r s B' C' hr' hs') := by
  subst B
  subst C
  subst B'
  subst C'
  rfl
theorem mapTo_congr {Γ : Context.{u}}
    (a : raisedContext (total (interval Γ)) ⟶ smallFamilyCodes.{u}) (r s : Term (interval Γ))
    (B C B' C' : Family Γ) (hr : decode (raisedSub (graph r) ≫ a) = B)
    (hs : decode (raisedSub (graph s) ≫ a) = C)
    (hr' : decode (raisedSub (graph r) ≫ a) = B')
    (hs' : decode (raisedSub (graph s) ≫ a) = C') :
    HEq (mapTo a r s B C hr hs) (mapTo a r s B' C' hr' hs') := by
  subst B
  subst C
  subst B'
  subst C'
  rfl
end SquareKit.Cubical.Cartesian.UniversalTransport

namespace SquareKit.Cubical.Cartesian.CodeSystem.Box
open CategoryTheory
universe u
variable {Γ Δ : Context.{u}} {φ : Subcontext Γ} {r : Term (interval Γ)} (b : Box Γ φ r) (σ : Δ ⟶ Γ)
theorem tubeMap_reindex :
    HEq (Functor.whiskerLeft
      (restrictSubstitution (φ.reindex (projection (interval Γ))) (intervalSub σ)).mapElements b.tubeMap)
      (b.reindex σ).tubeMap := by
  unfold tubeMap
  exact (heq_of_eq (UniversalTransport.mapTo_reindex _ _ _ _ _ _ _ _).symm).trans
    (UniversalTransport.mapTo_congr _ _ _ _ _ _ _ _ _ _ _)

theorem tubeEquivalence_reindex :
    HEq (b.tubeEquivalence.reindex (restrictSubstitution (φ.reindex (projection (interval Γ))) (intervalSub σ)))
      (b.reindex σ).tubeEquivalence := by
  unfold tubeEquivalence
  exact (UniversalTransport.equivalenceTo_reindex _ _ _ _ _ _ _ _).trans
    (UniversalTransport.equivalenceTo_congr _ _ _ _ _ _ _ _ _ _ _)
end SquareKit.Cubical.Cartesian.CodeSystem.Box

namespace SquareKit.Cubical.Cartesian.CodeSystem.Maps
open CategoryTheory
universe u
theorem glue_congr {Γ : Context.{u}} {φ ψ : Subcontext Γ}
    {A B A' B' : Family (restrictContext (φ.join ψ))} (hA : A = A') (hB : B = B')
    (a : reindex A (includeLeft φ ψ) ⟶ reindex B (includeLeft φ ψ))
    (b : reindex A (includeRight φ ψ) ⟶ reindex B (includeRight φ ψ))
    (a' : reindex A' (includeLeft φ ψ) ⟶ reindex B' (includeLeft φ ψ))
    (b' : reindex A' (includeRight φ ψ) ⟶ reindex B' (includeRight φ ψ))
    (ha : HEq a a') (hb : HEq b b') (c : Compatible a b) (c' : Compatible a' b') :
    HEq (glue a b c) (glue a' b' c') := by
  subst A'
  subst B'
  cases eq_of_heq ha
  cases eq_of_heq hb
  rfl
end SquareKit.Cubical.Cartesian.CodeSystem.Maps
namespace SquareKit.Cubical.Cartesian.CodeSystem.Box
open CategoryTheory
universe u
private theorem eqMap_congr {Γ Δ : Context.{u}} {A B : Family Γ}
    (q : A = B) (σ : Δ ⟶ Γ) {A' B' : Family Δ}
    (hB : Cartesian.reindex B σ = B') (q' : A' = B') :
    HEq (Functor.whiskerLeft σ.mapElements (eqToHom q)) (eqToHom q') := by
  subst B'
  subst A'
  cases q
  rfl
variable {Γ Δ : Context.{u}} {φ : Subcontext Γ} {r : Term (interval Γ)} (b : Box Γ φ r) (σ : Δ ⟶ Γ)
theorem capMap_reindex :
    HEq (Functor.whiskerLeft (restrictSubstitution (Glue.sourceFace r) (intervalSub σ)).mapElements b.capMap)
      (b.reindex σ).capMap := by
  unfold capMap
  apply eqMap_congr
  exact congrArg (fun A => (A.reindex (restrictInclusion (Glue.sourceFace (Term.reindex r σ)))).family)
    (ambientFamily_reindex b σ)
end SquareKit.Cubical.Cartesian.CodeSystem.Box

namespace SquareKit.Cubical.Cartesian.CodeSystem.Sections
open CategoryTheory
universe u
variable {Γ Δ : Context.{u}} {φ ψ : Subcontext Γ}
  {A B : Family (restrictContext (φ.join ψ))}
  (a : Term (Cartesian.reindex A (includeLeft φ ψ)))
  (b : Term (Cartesian.reindex A (includeRight φ ψ)))
  (c : Compatible a b) (f : A ⟶ B)
include c in
theorem Compatible.map : Compatible
    (Term.map (Functor.whiskerLeft (includeLeft φ ψ).mapElements f) a)
    (Term.map (Functor.whiskerLeft (includeRight φ ψ).mapElements f) b) := by
  intro x h k
  exact congrArg (f.app x) (c x h k)

theorem glue_map : Term.map f (glue a b c) =
    glue (Term.map (Functor.whiskerLeft (includeLeft φ ψ).mapElements f) a)
      (Term.map (Functor.whiskerLeft (includeRight φ ψ).mapElements f) b)
      (Compatible.map a b c f) := by
  apply Term.ext
  intro x
  rcases x.val.property with h | k
  · exact (congrArg (f.app x) (value_left a b x h)).trans
      (value_left (Term.map (Functor.whiskerLeft (includeLeft φ ψ).mapElements f) a) (Term.map (Functor.whiskerLeft (includeRight φ ψ).mapElements f) b) x h).symm
  · exact (congrArg (f.app x) (value_right a b c x k)).trans
      (value_right (Term.map (Functor.whiskerLeft (includeLeft φ ψ).mapElements f) a) (Term.map (Functor.whiskerLeft (includeRight φ ψ).mapElements f) b) (Compatible.map a b c f) x k).symm

theorem overlap_map :
    (overlap (ψ := ψ) a).map (Functor.whiskerLeft (includeRight φ ψ).mapElements f) =
      overlap (ψ := ψ) (Term.map (Functor.whiskerLeft (includeLeft φ ψ).mapElements f) a) := rfl

theorem overlap_reindex (σ : Δ ⟶ Γ) :
    (overlap (ψ := ψ) a).reindex (restrictSubstitution ψ σ) =
      overlap (φ := φ.reindex σ) (ψ := ψ.reindex σ)
      (A := Cartesian.reindex A (restrictSubstitution (φ.join ψ) σ))
      (Term.reindex a (restrictSubstitution φ σ)) := rfl
end SquareKit.Cubical.Cartesian.CodeSystem.Sections

namespace SquareKit.Cubical.Cartesian.CodeSystem.Box
open CategoryTheory
universe u
private theorem ofEqLocalFamily_congr {Γ : Context.{u}}
    (A A' : Family Γ) (B B' : LocalFamily Γ) (hB : B = B')
    (q : A = B.family) (q' : A' = B'.family) :
    HEq (HomotopyEquivalence.ofIso (eqToIso q) B.toFilling B.toFilling_lawful)
      (HomotopyEquivalence.ofIso (eqToIso q') B'.toFilling B'.toFilling_lawful) := by
  subst B'
  subst A
  subst A'
  rfl

private theorem ofIso_whisker_eq {Γ Δ : Context.{u}} {A B : Family Γ}
    (q : A = B) (F : Filling B) (hF : F.Lawful) (σ : Δ ⟶ Γ) :
    HEq (HomotopyEquivalence.ofIso (Functor.isoWhiskerLeft σ.mapElements (eqToIso q))
      (F.reindex σ) (hF.reindex σ))
      (HomotopyEquivalence.ofIso (eqToIso (congrArg (fun C => Cartesian.reindex C σ) q))
        (F.reindex σ) (hF.reindex σ)) := by
  cases q
  rfl

variable {Γ Δ : Context.{u}} {φ : Subcontext Γ} {r : Term (interval Γ)} (b : Box Γ φ r) (σ : Δ ⟶ Γ)
theorem capEquivalence_reindex :
    HEq (b.capEquivalence.reindex (restrictSubstitution (Glue.sourceFace r) (intervalSub σ)))
      (b.reindex σ).capEquivalence := by
  unfold capEquivalence
  refine (heq_of_eq (HomotopyEquivalence.ofIso_reindex
    (eqToIso (congrArg LocalFamily.family b.faceFamily_left))
    ((b.ambientFamily.reindex (restrictInclusion (Glue.sourceFace r))).toFilling)
    ((b.ambientFamily.reindex (restrictInclusion (Glue.sourceFace r))).toFilling_lawful)
    (restrictSubstitution (Glue.sourceFace r) (intervalSub σ)))).trans ?_
  refine (ofIso_whisker_eq _ _
    (b.ambientFamily.reindex (restrictInclusion (Glue.sourceFace r))).toFilling_lawful _).trans ?_
  exact ofEqLocalFamily_congr _ _
    ((b.ambientFamily.reindex (restrictInclusion (Glue.sourceFace r))).reindex
      (restrictSubstitution (Glue.sourceFace r) (intervalSub σ)))
    ((b.reindex σ).ambientFamily.reindex (restrictInclusion (Glue.sourceFace (Term.reindex r σ))))
    (congrArg (fun A => A.reindex (restrictInclusion (Glue.sourceFace (Term.reindex r σ))))
      (ambientFamily_reindex b σ)) _ _
end SquareKit.Cubical.Cartesian.CodeSystem.Box

namespace SquareKit.Cubical.Cartesian.CodeSystem.Box
open CategoryTheory
universe u
variable {Γ Δ : Context.{u}} {φ : Subcontext Γ} {r : Term (interval Γ)} (b : Box Γ φ r) (σ : Δ ⟶ Γ)
theorem faceMap_reindex :
    HEq (Functor.whiskerLeft (restrictSubstitution face (intervalSub σ)).mapElements b.faceMap)
      (b.reindex σ).faceMap := by
  unfold faceMap
  refine (heq_of_eq (Maps.glue_reindex _ _ _ _)).trans ?_
  apply Maps.glue_congr (φ := Glue.sourceFace (Term.reindex r σ))
    (ψ := (φ.reindex σ).reindex (projection (interval Δ)))
    (congrArg LocalFamily.family (faceFamily_reindex b σ))
    (congrArg (fun A => Cartesian.reindex A.family (restrictInclusion (face (φ := φ.reindex σ) (r := Term.reindex r σ)))) (ambientFamily_reindex b σ))
  · exact capMap_reindex b σ
  · exact tubeMap_reindex b σ
end SquareKit.Cubical.Cartesian.CodeSystem.Box

namespace SquareKit.Cubical.Cartesian.CodeSystem.IsEquivSections
open CategoryTheory EquivalenceFamilies
universe u
noncomputable section
def piBodyMap {Γ : Context.{u}} (A : Family Γ) {B C : Family (total A)}
    (k : B ⟶ C) : pi A B ⟶ pi A C where
  app _x := TypeCat.ofHom (fun p => {
    val := fun f a => k.app _ (p.val f a)
    naturality := fun f g a => (k.naturality_apply (extendHom A g a) (p.val f a)).symm.trans
      (congrArg (k.app _) (p.naturality f g a)) })
  naturality _ _ _ := rfl

theorem piBodyMap_lam {Γ : Context.{u}} (A : Family Γ) {B C : Family (total A)}
    (k : B ⟶ C) (s : Term B) : Term.map (piBodyMap A k) (lam s) = lam (Term.map k s) := rfl

variable {Γ Δ : Context.{u}} {A B : Family Γ} (f : A ⟶ B)
  (F : Filling A) (hF : F.Lawful) (G : Filling B) (hG : G.Lawful) (σ : Δ ⟶ Γ)

theorem fiberWitness_input_reindex
    (c : Contractible (reindex (fiber f) (liftSub B σ)))
    {φ : Subcontext (total (reindex B σ))}
    (s : PartialSection (contr (reindex (fiber f) (liftSub B σ))) φ) :
    ContractibilityExtension.witness (Contractible.map (genericFiberReindexIso f σ) c)
      (genericFiberFilling (Functor.whiskerLeft σ.mapElements f)
        (F.reindex σ) (hF.reindex _) (G.reindex σ) (hG.reindex _))
      (genericFiberFilling_lawful (Functor.whiskerLeft σ.mapElements f)
        (F.reindex σ) (hF.reindex _) (G.reindex σ) (hG.reindex _))
      (s.map (contrMap (genericFiberReindexIso f σ))) =
    Contractible.map (genericFiberReindexIso f σ)
      (ContractibilityExtension.witness c ((genericFiberFilling f F hF G hG).reindex (liftSub B σ))
        ((genericFiberFilling_lawful f F hF G hG).reindex _) s) := by
  have h := ContractibilityExtension.witness_transport (genericFiberReindexIso f σ) c
    ((genericFiberFilling f F hF G hG).reindex (liftSub B σ))
    ((genericFiberFilling_lawful f F hF G hG).reindex _) s
  simpa only [genericFiberFilling_reindex f F hF G hG σ] using h


def inputMap : reindex (isEquiv f) σ ⟶ isEquiv (Functor.whiskerLeft σ.mapElements f) :=
  piReindex B (contr (fiber f)) σ ≫
    piBodyMap (reindex B σ) ((contrReindexIso (fiber f) (liftSub B σ)).hom ≫
      contrMap (genericFiberReindexIso f σ))

theorem piBodyMap_cancel {Ξ : Context.{u}} (X : Family Ξ)
    {Y Z W : Family (total X)} {D : Family Ξ} (j : D ≅ pi X Y)
    (i : Y ≅ Z) (k : Z ⟶ W) (c : Term Z) :
    Term.map (j.hom ≫ piBodyMap X (i.hom ≫ k))
      (Term.map j.inv (lam (Term.map i.inv c))) = lam (Term.map k c) := by
  change Term.map (piBodyMap X (i.hom ≫ k))
    (Term.map j.hom (Term.map j.inv (lam (Term.map i.inv c)))) = _
  refine (congrArg (Term.map (piBodyMap X (i.hom ≫ k)))
    (Term.map_iso_roundtrip j.symm (lam (Term.map i.inv c)))).trans ?_
  change lam (Term.map k (Term.map i.hom (Term.map i.inv c))) = _
  exact congrArg (fun t => lam (Term.map k t)) (Term.map_iso_roundtrip i.symm c)

theorem reindexed_apply (c : Contractible (reindex (fiber f) (liftSub B σ))) :
    reindexedIsEquivSections f σ c =
      Term.map (piReindexIso B (contr (fiber f)) σ).inv
        (lam (Term.map (contrReindexIso (fiber f) (liftSub B σ)).inv (encodeContr c))) := rfl

theorem inputMap_encoded (c : Contractible (reindex (fiber f) (liftSub B σ))) :
    Term.map (inputMap f σ) (reindexedIsEquivSections f σ c) =
      encodeIsEquiv ⟨Contractible.map (genericFiberReindexIso f σ) c⟩ := by
  rw [reindexed_apply]
  exact (piBodyMap_cancel (reindex B σ) (piReindexIso B (contr (fiber f)) σ)
    (contrReindexIso (fiber f) (liftSub B σ)) (contrMap (genericFiberReindexIso f σ)) (encodeContr c)).trans
      (congrArg lam (contrMap_encode (genericFiberReindexIso f σ) c))

theorem partialBody_input {φ : Subcontext Δ}
    (s : PartialSection (reindex (isEquiv f) σ) φ) :
    partialBody (Functor.whiskerLeft σ.mapElements f) (𝟙 Δ) φ (s.map (inputMap f σ)) =
      (partialBody f σ φ s).map (contrMap (genericFiberReindexIso f σ)) := by
  apply PartialSection.ext
  intro x hx
  change (contrReindexIso (fiber (Functor.whiskerLeft σ.mapElements f)) (𝟙 _)).hom.app x _ = _
  rw [contrReindex_hom_id]
  rfl

end
end SquareKit.Cubical.Cartesian.CodeSystem.IsEquivSections

namespace SquareKit.Cubical.Cartesian.LocalFamily
open CategoryTheory
universe u
theorem normalizedGlue_congr {Γ : Context.{u}} (φ : Subcontext Γ)
    (A A' : LocalFamily Γ) (T T' : LocalFamily (restrictContext φ))
    (hA : A = A') (hT : T = T')
    (e : T.family ⟶ Cartesian.reindex A.family (restrictInclusion φ))
    (e' : T'.family ⟶ Cartesian.reindex A'.family (restrictInclusion φ))
    (he : HEq e e') (E : HomotopyEquivalence e) (E' : HomotopyEquivalence e')
    (hE : HEq E E') : normalizedGlue φ A T e E = normalizedGlue φ A' T' e' E' := by
  subst A'
  subst T'
  cases eq_of_heq he
  cases eq_of_heq hE
  rfl
end SquareKit.Cubical.Cartesian.LocalFamily

namespace SquareKit.Cubical.Cartesian.CodeSystem.Box
open CategoryTheory
universe u
variable {Γ Δ : Context.{u}} {φ : Subcontext Γ} {r : Term (interval Γ)} (b : Box Γ φ r) (σ : Δ ⟶ Γ)
theorem fillCode_reindex_of_equivalence
    (hE : HEq (b.faceEquivalence.reindex (restrictSubstitution face (intervalSub σ)))
      (b.reindex σ).faceEquivalence) :
    raisedSub (intervalSub σ) ≫ b.fillCode = (b.reindex σ).fillCode := by
  have h : (b.glueFamily b.faceMap b.faceEquivalence).reindex (intervalSub σ) =
      (b.reindex σ).glueFamily (b.reindex σ).faceMap (b.reindex σ).faceEquivalence := by
    unfold glueFamily
    rw [LocalFamily.normalizedGlue_substitution]
    exact LocalFamily.normalizedGlue_congr _ _ _ _ _ (ambientFamily_reindex b σ)
      (faceFamily_reindex b σ) _ _ (faceMap_reindex b σ) _ _ hE
  exact (LocalFamily.code_reindex _ _).symm.trans (congrArg LocalFamily.code h)
end SquareKit.Cubical.Cartesian.CodeSystem.Box

namespace SquareKit.Cubical.Cartesian.EquivalenceFamilies
open CategoryTheory
universe u
private theorem contrMap_section_forward {Γ Δ : Context.{u}} {A B : Family Γ} (e : A ≅ B)
    (σ : Δ ⟶ Γ) (s : Term (reindex (contr A) σ)) :
    Term.map (contrReindexIso B σ).hom (Term.map (Functor.whiskerLeft σ.mapElements (contrMap e)) s) =
      encodeContr (Contractible.map (Functor.isoWhiskerLeft σ.mapElements e)
        (decodeContr (Term.map (contrReindexIso A σ).hom s))) := by
  rw [contrMap_section]
  exact Term.map_iso_roundtrip (contrReindexIso B σ).symm _

private theorem contrMap_square_sections {Γ Δ Θ : Context.{u}} {A B : Family Γ} (e : A ≅ B)
    (σ : Δ ⟶ Γ) (τ : Θ ⟶ Δ) (s : Term (reindex (contr A) (τ ≫ σ))) :
    Term.map (Functor.whiskerLeft τ.mapElements (contrReindexIso B σ).hom)
      (Term.map (Functor.whiskerLeft (τ ≫ σ).mapElements (contrMap e)) s) =
    Term.map (Functor.whiskerLeft τ.mapElements (contrMap (Functor.isoWhiskerLeft σ.mapElements e)))
      (Term.map (Functor.whiskerLeft τ.mapElements (contrReindexIso A σ).hom) s) := by
  apply Term.map_injective_of_iso (contrReindexIso (reindex B σ) τ)
  have hl := contrMap_section_forward e (τ ≫ σ) s
  have hr := contrMap_section_forward (Functor.isoWhiskerLeft σ.mapElements e) τ
    (Term.map (Functor.whiskerLeft τ.mapElements (contrReindexIso A σ).hom) s)
  change Term.map (Functor.whiskerLeft τ.mapElements (contrReindexIso B σ).hom ≫
    (contrReindexIso (reindex B σ) τ).hom)
    (Term.map (Functor.whiskerLeft (τ ≫ σ).mapElements (contrMap e)) s) = _
  rw [CodeSystem.IsEquivSections.contrReindex_hom_comp]
  rw [hl, hr]
  congr 3

theorem contrMap_reindex_square {Γ Δ : Context.{u}} {A B : Family Γ} (e : A ≅ B)
    (σ : Δ ⟶ Γ) :
    Functor.whiskerLeft σ.mapElements (contrMap e) ≫ (contrReindexIso B σ).hom =
      (contrReindexIso A σ).hom ≫ contrMap (Functor.isoWhiskerLeft σ.mapElements e) := by
  ext x p
  let τ := projection (reindex (contr A) σ)
  have h := contrMap_square_sections e σ τ (generic _)
  exact congrArg (fun t => t.val (extendObj (reindex (contr A) σ) x p)) h
end SquareKit.Cubical.Cartesian.EquivalenceFamilies

namespace SquareKit.Cubical.Cartesian.CodeSystem.Equivalences
open CategoryTheory
universe u
theorem glue_congr {Γ : Context.{u}} {φ ψ : Subcontext Γ}
    (A A' B B' : LocalFamily (restrictContext (φ.join ψ)))
    (hA : A = A') (hB : B = B') (f : A.family ⟶ B.family) (f' : A'.family ⟶ B'.family)
    (hf : HEq f f')
    (a : HomotopyEquivalence (Functor.whiskerLeft (includeLeft φ ψ).mapElements f))
    (a' : HomotopyEquivalence (Functor.whiskerLeft (includeLeft φ ψ).mapElements f'))
    (b : HomotopyEquivalence (Functor.whiskerLeft (includeRight φ ψ).mapElements f))
    (b' : HomotopyEquivalence (Functor.whiskerLeft (includeRight φ ψ).mapElements f'))
    (ha : HEq a a') (hb : HEq b b') :
    HEq (glue f A.toFilling A.toFilling_lawful B.toFilling B.toFilling_lawful a b)
      (glue f' A'.toFilling A'.toFilling_lawful B'.toFilling B'.toFilling_lawful a' b') := by
  subst A'
  subst B'
  cases eq_of_heq hf
  cases eq_of_heq ha
  cases eq_of_heq hb
  rfl

theorem cast_reindex_heq {Γ Δ : Context.{u}} {A B : Family Γ}
    {f g : A ⟶ B} (h : f = g) (e : HomotopyEquivalence f) (σ : Δ ⟶ Γ) :
    HEq ((h ▸ e).reindex σ) (e.reindex σ) := by
  cases h
  rfl
end SquareKit.Cubical.Cartesian.CodeSystem.Equivalences

namespace SquareKit.Cubical.Cartesian.CodeSystem
open CategoryTheory EquivalenceFamilies
universe u
namespace IsEquivSections
variable {Γ Δ : Context.{u}} {A B : Family Γ} (f : A ⟶ B) (σ : Δ ⟶ Γ)
theorem inputMap_sections (E : HomotopyEquivalence (Functor.whiskerLeft σ.mapElements f)) :
    Term.map (inputMap f σ) (isEquivReindexSections f σ E) = encodeIsEquiv E := by
  have h := inputMap_encoded f σ (Contractible.map (genericFiberReindexIso f σ).symm E.fibers)
  exact h.trans (congrArg (fun c => encodeIsEquiv (HomotopyEquivalence.mk c))
    (contrTransport_roundtrip (genericFiberReindexIso f σ).symm E.fibers))
theorem inputMap_reindex_encode (E : HomotopyEquivalence f) :
    Term.map (inputMap f σ) (Term.reindex (encodeIsEquiv E) σ) = encodeIsEquiv (E.reindex σ) :=
  (congrArg (Term.map (inputMap f σ)) (isEquivReindexSections_reindex E σ).symm).trans
    (inputMap_sections f σ (E.reindex σ))
end IsEquivSections
namespace Equivalences
noncomputable section
variable {Γ Δ : Context.{u}} {φ ψ : Subcontext Γ}
  {A B : Family (restrictContext (φ.join ψ))} (f : A ⟶ B)
  (F : Filling A) (hF : F.Lawful) (G : Filling B) (hG : G.Lawful)
  (a : HomotopyEquivalence (Functor.whiskerLeft (includeLeft φ ψ).mapElements f))
  (b : HomotopyEquivalence (Functor.whiskerLeft (includeRight φ ψ).mapElements f))
  (σ : Δ ⟶ Γ)

set_option backward.isDefEq.respectTransparency false in
theorem glue_reindex_of_sections
    (hl : Term.map (Functor.whiskerLeft (includeLeft (φ.reindex σ) (ψ.reindex σ)).mapElements (IsEquivSections.inputMap f (restrictSubstitution (φ.join ψ) σ)))
      (Term.reindex (leftWitness f a) (restrictSubstitution φ σ)) =
      leftWitness (φ := φ.reindex σ) (ψ := ψ.reindex σ) (Functor.whiskerLeft (restrictSubstitution (φ.join ψ) σ).mapElements f) (a.reindex (restrictSubstitution φ σ)))
    (hr : Term.map (Functor.whiskerLeft (includeRight (φ.reindex σ) (ψ.reindex σ)).mapElements (IsEquivSections.inputMap f (restrictSubstitution (φ.join ψ) σ)))
      (Term.reindex (rightWitness f F hF G hG a b) (restrictSubstitution ψ σ)) =
      rightWitness (φ := φ.reindex σ) (ψ := ψ.reindex σ) (Functor.whiskerLeft (restrictSubstitution (φ.join ψ) σ).mapElements f) (F.reindex (restrictSubstitution (φ.join ψ) σ)) (hF.reindex _) (G.reindex (restrictSubstitution (φ.join ψ) σ)) (hG.reindex _) (a.reindex (restrictSubstitution φ σ)) (b.reindex (restrictSubstitution ψ σ))) :
    (glue f F hF G hG a b).reindex (restrictSubstitution (φ.join ψ) σ) =
      glue (φ := φ.reindex σ) (ψ := ψ.reindex σ) (Functor.whiskerLeft (restrictSubstitution (φ.join ψ) σ).mapElements f) (F.reindex (restrictSubstitution (φ.join ψ) σ)) (hF.reindex _) (G.reindex (restrictSubstitution (φ.join ψ) σ)) (hG.reindex _) (a.reindex (restrictSubstitution φ σ)) (b.reindex (restrictSubstitution ψ σ)) := by
  apply (isEquivSections (Functor.whiskerLeft (restrictSubstitution (φ.join ψ) σ).mapElements f)).injective
  have hc := IsEquivSections.inputMap_reindex_encode f (restrictSubstitution (φ.join ψ) σ) (glue f F hF G hG a b)
  change Term.map (IsEquivSections.inputMap f (restrictSubstitution (φ.join ψ) σ)) (Term.reindex (encodeIsEquiv (glue f F hF G hG a b)) (restrictSubstitution (φ.join ψ) σ)) = _ at hc
  rw [glue, encode_decodeIsEquiv] at hc
  have hw : Term.map (IsEquivSections.inputMap f (restrictSubstitution (φ.join ψ) σ)) (Term.reindex (witness f F hF G hG a b) (restrictSubstitution (φ.join ψ) σ)) =
      witness (φ := φ.reindex σ) (ψ := ψ.reindex σ) (Functor.whiskerLeft (restrictSubstitution (φ.join ψ) σ).mapElements f) (F.reindex (restrictSubstitution (φ.join ψ) σ)) (hF.reindex _) (G.reindex (restrictSubstitution (φ.join ψ) σ)) (hG.reindex _) (a.reindex (restrictSubstitution φ σ)) (b.reindex (restrictSubstitution ψ σ)) := by
    let l := leftWitness f a
    let r := rightWitness f F hF G hG a b
    let l' := leftWitness (φ := φ.reindex σ) (ψ := ψ.reindex σ) (Functor.whiskerLeft (restrictSubstitution (φ.join ψ) σ).mapElements f) (a.reindex (restrictSubstitution φ σ))
    let r' := rightWitness (φ := φ.reindex σ) (ψ := ψ.reindex σ) (Functor.whiskerLeft (restrictSubstitution (φ.join ψ) σ).mapElements f) (F.reindex (restrictSubstitution (φ.join ψ) σ)) (hF.reindex _) (G.reindex (restrictSubstitution (φ.join ψ) σ)) (hG.reindex _) (a.reindex (restrictSubstitution φ σ)) (b.reindex (restrictSubstitution ψ σ))
    apply Term.ext
    intro x
    let y := (restrictSubstitution (φ.join ψ) σ).mapElements.obj x
    rcases x.val.property with h | k
    · exact (congrArg ((IsEquivSections.inputMap f (restrictSubstitution (φ.join ψ) σ)).app x) (Sections.value_left l r y h)).trans
        ((congrArg (fun t => t.val (Maps.left (φ := φ.reindex σ) (ψ := ψ.reindex σ) x h)) hl).trans (Sections.value_left l' r' x h).symm)
    · exact (congrArg ((IsEquivSections.inputMap f (restrictSubstitution (φ.join ψ) σ)).app x) (Sections.value_right l r (witnesses_compatible f F hF G hG a b) y k)).trans
        ((congrArg (fun t => t.val (Maps.right (φ := φ.reindex σ) (ψ := ψ.reindex σ) x k)) hr).trans
          (Sections.value_right l' r' (witnesses_compatible (φ := φ.reindex σ) (ψ := ψ.reindex σ) (Functor.whiskerLeft (restrictSubstitution (φ.join ψ) σ).mapElements f) (F.reindex (restrictSubstitution (φ.join ψ) σ)) (hF.reindex _) (G.reindex (restrictSubstitution (φ.join ψ) σ)) (hG.reindex _) (a.reindex (restrictSubstitution φ σ)) (b.reindex (restrictSubstitution ψ σ))) x k).symm)
  exact hc.symm.trans (hw.trans (encode_decodeIsEquiv _).symm)
end
end Equivalences
end SquareKit.Cubical.Cartesian.CodeSystem

namespace SquareKit.Cubical.Cartesian.CodeSystem.Equivalences
open CategoryTheory
universe u
variable (uniform : ∀ {Ω Λ : Context.{u}} {α β : Subcontext Ω}
    {A B : Family (restrictContext (α.join β))} (f : A ⟶ B)
    (F : Filling A) (hF : F.Lawful) (G : Filling B) (hG : G.Lawful)
    (a : HomotopyEquivalence (Functor.whiskerLeft (includeLeft α β).mapElements f))
    (b : HomotopyEquivalence (Functor.whiskerLeft (includeRight α β).mapElements f))
    (τ : Λ ⟶ Ω),
    (Equivalences.glue f F hF G hG a b).reindex (restrictSubstitution (α.join β) τ) =
      Equivalences.glue (φ := α.reindex τ) (ψ := β.reindex τ)
        (Functor.whiskerLeft (restrictSubstitution (α.join β) τ).mapElements f)
        (F.reindex (restrictSubstitution (α.join β) τ)) (hF.reindex _)
        (G.reindex (restrictSubstitution (α.join β) τ)) (hG.reindex _)
        (a.reindex (restrictSubstitution α τ)) (b.reindex (restrictSubstitution β τ)))
include uniform in
theorem glue_reindex_congr {Ω Λ : Context.{u}} {α β : Subcontext Ω}
    (τ : Λ ⟶ Ω) (A B : LocalFamily (restrictContext (α.join β)))
    (A' B' : LocalFamily (restrictContext ((α.reindex τ).join (β.reindex τ))))
    (hA : A.reindex (restrictSubstitution (α.join β) τ) = A')
    (hB : B.reindex (restrictSubstitution (α.join β) τ) = B')
    (f : A.family ⟶ B.family) (f' : A'.family ⟶ B'.family)
    (hf : HEq (Functor.whiskerLeft (restrictSubstitution (α.join β) τ).mapElements f) f')
    (a : HomotopyEquivalence (Functor.whiskerLeft (includeLeft α β).mapElements f))
    (b : HomotopyEquivalence (Functor.whiskerLeft (includeRight α β).mapElements f))
    (a' : HomotopyEquivalence (Functor.whiskerLeft (includeLeft (α.reindex τ) (β.reindex τ)).mapElements f'))
    (b' : HomotopyEquivalence (Functor.whiskerLeft (includeRight (α.reindex τ) (β.reindex τ)).mapElements f'))
    (ha : HEq (a.reindex (restrictSubstitution α τ)) a')
    (hb : HEq (b.reindex (restrictSubstitution β τ)) b') :
    HEq ((Equivalences.glue f A.toFilling A.toFilling_lawful B.toFilling B.toFilling_lawful a b).reindex
      (restrictSubstitution (α.join β) τ))
      (Equivalences.glue f' A'.toFilling A'.toFilling_lawful B'.toFilling B'.toFilling_lawful a' b') :=
  (heq_of_eq (uniform f A.toFilling A.toFilling_lawful B.toFilling B.toFilling_lawful a b τ)).trans
    (Equivalences.glue_congr (A.reindex _) A' (B.reindex _) B' hA hB _ _ hf _ _ _ _ ha hb)



theorem cast_reindex_congr {Γ Δ : Context.{u}} {A B : Family Γ} {A' B' : Family Δ}
    {f g : A ⟶ B} {f' g' : A' ⟶ B'} (h : f = g) (h' : f' = g')
    (e : HomotopyEquivalence f) (e' : HomotopyEquivalence f') (σ : Δ ⟶ Γ)
    (he : HEq (e.reindex σ) e') : HEq ((h ▸ e).reindex σ) (h' ▸ e') := by
  cases h
  cases h'
  exact he

include uniform in
theorem glueMaps_reindex_congr {Ω Λ : Context.{u}} {α β : Subcontext Ω}
    (τ : Λ ⟶ Ω) (A B : LocalFamily (restrictContext (α.join β)))
    (A' B' : LocalFamily (restrictContext ((α.reindex τ).join (β.reindex τ))))
    (hA : A.reindex (restrictSubstitution (α.join β) τ) = A')
    (hB : B.reindex (restrictSubstitution (α.join β) τ) = B')
    (a : Cartesian.reindex A.family (includeLeft α β) ⟶ Cartesian.reindex B.family (includeLeft α β))
    (b : Cartesian.reindex A.family (includeRight α β) ⟶ Cartesian.reindex B.family (includeRight α β))
    (a' : Cartesian.reindex A'.family (includeLeft (α.reindex τ) (β.reindex τ)) ⟶
      Cartesian.reindex B'.family (includeLeft (α.reindex τ) (β.reindex τ)))
    (b' : Cartesian.reindex A'.family (includeRight (α.reindex τ) (β.reindex τ)) ⟶
      Cartesian.reindex B'.family (includeRight (α.reindex τ) (β.reindex τ)))
    (ha : HEq (Functor.whiskerLeft (restrictSubstitution α τ).mapElements a) a')
    (hb : HEq (Functor.whiskerLeft (restrictSubstitution β τ).mapElements b) b')
    (c : Maps.Compatible a b) (c' : Maps.Compatible a' b')
    (ea : HomotopyEquivalence a) (eb : HomotopyEquivalence b)
    (ea' : HomotopyEquivalence a') (eb' : HomotopyEquivalence b')
    (hea : HEq (ea.reindex (restrictSubstitution α τ)) ea')
    (heb : HEq (eb.reindex (restrictSubstitution β τ)) eb') :
    HEq ((glueMaps A B a b c ea eb).reindex (restrictSubstitution (α.join β) τ))
      (glueMaps A' B' a' b' c' ea' eb') := by
  apply glue_reindex_congr uniform τ A B A' B' hA hB
  · exact (heq_of_eq (Maps.glue_reindex a b c τ)).trans
      (Maps.glue_congr (congrArg LocalFamily.family hA) (congrArg LocalFamily.family hB)
        _ _ a' b' ha hb _ c')
  · exact cast_reindex_congr _ _ _ _ _ hea
  · exact cast_reindex_congr _ _ _ _ _ heb
end SquareKit.Cubical.Cartesian.CodeSystem.Equivalences
namespace SquareKit.Cubical.Cartesian.CodeSystem.Box
open CategoryTheory
universe u
variable (uniform : ∀ {Ω Λ : Context.{u}} {α β : Subcontext Ω}
    {A B : Family (restrictContext (α.join β))} (f : A ⟶ B)
    (F : Filling A) (hF : F.Lawful) (G : Filling B) (hG : G.Lawful)
    (a : HomotopyEquivalence (Functor.whiskerLeft (includeLeft α β).mapElements f))
    (b : HomotopyEquivalence (Functor.whiskerLeft (includeRight α β).mapElements f))
    (τ : Λ ⟶ Ω),
    (Equivalences.glue f F hF G hG a b).reindex (restrictSubstitution (α.join β) τ) =
      Equivalences.glue (φ := α.reindex τ) (ψ := β.reindex τ)
        (Functor.whiskerLeft (restrictSubstitution (α.join β) τ).mapElements f)
        (F.reindex (restrictSubstitution (α.join β) τ)) (hF.reindex _)
        (G.reindex (restrictSubstitution (α.join β) τ)) (hG.reindex _)
        (a.reindex (restrictSubstitution α τ)) (b.reindex (restrictSubstitution β τ)))

variable {Γ Δ : Context.{u}} {φ : Subcontext Γ} {r : Term (interval Γ)} (b : Box Γ φ r) (σ : Δ ⟶ Γ)
include uniform in
theorem faceEquivalence_reindex_of_uniform :
    HEq ((faceEquivalence b).reindex (restrictSubstitution face (intervalSub σ)))
      (faceEquivalence (b.reindex σ)) := by
  exact Equivalences.glueMaps_reindex_congr uniform (intervalSub σ)
    (α := Glue.sourceFace r) (β := φ.reindex (projection (interval Γ)))
    b.faceFamily (b.ambientFamily.reindex (restrictInclusion (face (φ := φ) (r := r))))
    (b.reindex σ).faceFamily ((b.reindex σ).ambientFamily.reindex
      (restrictInclusion (face (φ := φ.reindex σ) (r := Term.reindex r σ))))
    (faceFamily_reindex b σ)
    (congrArg (fun A => A.reindex (restrictInclusion (face (φ := φ.reindex σ) (r := Term.reindex r σ))))
      (ambientFamily_reindex b σ)) _ _ _ _ (capMap_reindex b σ) (tubeMap_reindex b σ)
    _ _ _ _ _ _ (capEquivalence_reindex b σ) (tubeEquivalence_reindex b σ)
end SquareKit.Cubical.Cartesian.CodeSystem.Box

namespace SquareKit.Cubical.Cartesian.CodeSystem.IsEquivSections
open CategoryTheory EquivalenceFamilies
universe u
noncomputable section
theorem contrHom_inverse_comp {Ξ Ψ Ω : Context.{u}} (C : Family Ξ)
    (μ : Ψ ⟶ Ξ) (ν : Ω ⟶ Ψ) (c : Term (contr (reindex C (ν ≫ μ)))) :
    Term.map (Functor.whiskerLeft ν.mapElements (contrReindexIso C μ).hom)
      (Term.map (contrReindexIso C (ν ≫ μ)).inv c) =
      Term.map (contrReindexIso (reindex C μ) ν).inv c := by
  let d := contrReindexIso (reindex C μ) ν
  let e := contrReindexIso C (ν ≫ μ)
  apply Term.map_injective_of_iso d
  apply Term.ext
  intro x
  have h := congrArg (fun k => k.app x (e.inv.app x (c.val x))) (contrReindex_hom_comp C μ ν)
  exact h.trans ((e.inv_hom_id_app_apply x (c.val x)).trans
    (d.inv_hom_id_app_apply x (c.val x)).symm)

theorem piBodyMap_reindex {Ξ Ψ : Context.{u}} (X : Family Ξ)
    {Y Z : Family (total X)} (k : Y ⟶ Z) (μ : Ψ ⟶ Ξ) :
    Functor.whiskerLeft μ.mapElements (piBodyMap X k) ≫ piReindex X Z μ =
      piReindex X Y μ ≫ piBodyMap (reindex X μ) (Functor.whiskerLeft (liftSub X μ).mapElements k) := rfl

theorem piReindex_comp {Ξ Ψ Ω : Context.{u}} (X : Family Ξ) (Y : Family (total X))
    (μ : Ψ ⟶ Ξ) (ν : Ω ⟶ Ψ) :
    Functor.whiskerLeft ν.mapElements (piReindex X Y μ) ≫
      piReindex (reindex X μ) (reindex Y (liftSub X μ)) ν = piReindex X Y (ν ≫ μ) := rfl

theorem piInput_section {Γ Δ Θ : Context.{u}} (B : Family Γ) (C : Family (total B))
    (σ : Δ ⟶ Γ) (θ : Θ ⟶ Δ) {D : Family (total (reindex B σ))}
    (k : reindex C (liftSub B σ) ⟶ D)
    (c : Term (reindex C (liftSub B (θ ≫ σ)))) :
    Term.map (Functor.whiskerLeft θ.mapElements (piReindex B C σ ≫ piBodyMap (reindex B σ) k))
      (Term.map (piReindexIso B C (θ ≫ σ)).inv (lam c)) =
    Term.map (piReindexIso (reindex B σ) D θ).inv
      (lam (Term.map (Functor.whiskerLeft (liftSub (reindex B σ) θ).mapElements k) c)) := by
  let ρ := liftSub (reindex B σ) θ
  let j := piReindexIso (reindex B σ) D θ
  apply Term.map_injective_of_iso j
  have hp : Functor.whiskerLeft θ.mapElements (piReindex B C σ ≫ piBodyMap (reindex B σ) k) ≫ j.hom =
      (piReindexIso B C (θ ≫ σ)).hom ≫
        piBodyMap (reindex B (θ ≫ σ)) (Functor.whiskerLeft ρ.mapElements k) := by
    change Functor.whiskerLeft θ.mapElements (piReindex B C σ) ≫
      (Functor.whiskerLeft θ.mapElements (piBodyMap (reindex B σ) k) ≫ piReindex (reindex B σ) D θ) = _
    rw [piBodyMap_reindex, ← Category.assoc, piReindex_comp]
    rfl
  have hh := congrArg (fun m => Term.map m (Term.map (piReindexIso B C (θ ≫ σ)).inv (lam c))) hp
  refine hh.trans ?_
  have hi := Term.map_iso_roundtrip (piReindexIso B C (θ ≫ σ)).symm (lam c)
  refine (congrArg (Term.map (piBodyMap (reindex B (θ ≫ σ)) (Functor.whiskerLeft ρ.mapElements k))) hi).trans ?_
  exact (Term.map_iso_roundtrip j.symm _).symm

variable {Γ Δ Θ : Context.{u}} {A B : Family Γ} (f : A ⟶ B) (σ : Δ ⟶ Γ) (θ : Θ ⟶ Δ)

theorem contrPiInput_section {Ξ Ψ Ω : Context.{u}} (X : Family Ξ) (C : Family (total X))
    (μ : Ψ ⟶ Ξ) (ν : Ω ⟶ Ψ) {D : Family (total (reindex X μ))}
    (e : reindex C (liftSub X μ) ≅ D)
    (c : Contractible (reindex C (liftSub X (ν ≫ μ)))) :
    Term.map (Functor.whiskerLeft ν.mapElements
      (piReindex X (contr C) μ ≫ piBodyMap (reindex X μ)
        ((contrReindexIso C (liftSub X μ)).hom ≫ contrMap e)))
      (Term.map (piReindexIso X (contr C) (ν ≫ μ)).inv
        (lam (Term.map (contrReindexIso C (liftSub X (ν ≫ μ))).inv (encodeContr c)))) =
    Term.map (piReindexIso (reindex X μ) (contr D) ν).inv
      (lam (Term.map (contrReindexIso D (liftSub (reindex X μ) ν)).inv
        (encodeContr (Contractible.map
          (Functor.isoWhiskerLeft (liftSub (reindex X μ) ν).mapElements e) c)))) := by
  let ρ := liftSub (reindex X μ) ν
  let k := (contrReindexIso C (liftSub X μ)).hom ≫ contrMap e
  have hb := contrHom_inverse_comp C (liftSub X μ) ρ (encodeContr c)
  have he := contrMap_reindexed_encode e ρ c
  have he' := (congrArg (Term.map (Functor.whiskerLeft ρ.mapElements (contrMap e))) hb).trans he
  exact (piInput_section X (contr C) μ ν k
    (Term.map (contrReindexIso C (liftSub X (ν ≫ μ))).inv (encodeContr c))).trans
    (congrArg (fun z => Term.map (piReindexIso (reindex X μ) (contr D) ν).inv (lam z)) he')

theorem inputMap_encoded_reindex
    (c : Contractible (reindex (fiber f) (liftSub B (θ ≫ σ)))) :
    Term.map (Functor.whiskerLeft θ.mapElements (inputMap f σ))
      (reindexedIsEquivSections f (θ ≫ σ) c) =
    reindexedIsEquivSections (Functor.whiskerLeft σ.mapElements f) θ
      (Contractible.map (Functor.isoWhiskerLeft (liftSub (reindex B σ) θ).mapElements
        (genericFiberReindexIso f σ)) c) := by
  exact contrPiInput_section B (fiber f) σ θ (genericFiberReindexIso f σ) c

theorem fiberContractible_input
    (E : HomotopyEquivalence (Functor.whiskerLeft (θ ≫ σ).mapElements f)) :
    Contractible.map (Functor.isoWhiskerLeft (liftSub (reindex B σ) θ).mapElements
      (genericFiberReindexIso f σ)) (fiberContractible f (θ ≫ σ) E) =
    fiberContractible (Functor.whiskerLeft σ.mapElements f) θ E := by
  let i := Functor.isoWhiskerLeft (liftSub (reindex B σ) θ).mapElements (genericFiberReindexIso f σ)
  let j := genericFiberReindexIso (Functor.whiskerLeft σ.mapElements f) θ
  have hi : i ≪≫ j = genericFiberReindexIso f (θ ≫ σ) :=
    Homotopy.fiberReindexIso_comp (Functor.whiskerLeft (projection B).mapElements f)
      (generic B) (liftSub B σ) (liftSub (reindex B σ) θ)
  change Contractible.map i (Contractible.map (genericFiberReindexIso f (θ ≫ σ)).symm E.fibers) =
    Contractible.map j.symm E.fibers
  rw [← hi]
  change Contractible.map i (Contractible.map i.symm (Contractible.map j.symm E.fibers)) = _
  exact contrTransport_roundtrip i.symm (Contractible.map j.symm E.fibers)


theorem inputMap_sections_reindex
    (E : HomotopyEquivalence (Functor.whiskerLeft (θ ≫ σ).mapElements f)) :
    Term.map (Functor.whiskerLeft θ.mapElements (inputMap f σ))
      (isEquivReindexSections f (θ ≫ σ) E) =
    isEquivReindexSections (Functor.whiskerLeft σ.mapElements f) θ E := by
  change Term.map _ (reindexedIsEquivSections f (θ ≫ σ) (fiberContractible f (θ ≫ σ) E)) = _
  rw [inputMap_encoded_reindex, fiberContractible_input]
  rfl

theorem partialPiInput {Ξ Ψ Ω : Context.{u}} (X : Family Ξ) (Y : Family (total X))
    (μ : Ψ ⟶ Ξ) (ν : Ω ⟶ Ψ) {Z : Family (total (reindex X μ))}
    (k : reindex Y (liftSub X μ) ⟶ Z) {φ : Subcontext Ω}
    (s : PartialSection (reindex (pi X Y) (ν ≫ μ)) φ) :
    (((s.map (Functor.whiskerLeft ν.mapElements (piReindex X Y μ ≫ piBodyMap (reindex X μ) k))).map
      (piReindex (reindex X μ) Z ν)).app) =
    ((s.map (piReindex X Y (ν ≫ μ))).app).map
      (Functor.whiskerLeft (liftSub (reindex X μ) ν).mapElements k) := rfl

theorem partialPiInput_map {Ξ Ψ Ω : Context.{u}} (X : Family Ξ) (Y : Family (total X))
    (μ : Ψ ⟶ Ξ) (ν : Ω ⟶ Ψ) {Z : Family (total (reindex X μ))}
    {V W : Family (total (reindex X (ν ≫ μ)))}
    (k : reindex Y (liftSub X μ) ⟶ Z)
    (j : reindex Z (liftSub (reindex X μ) ν) ⟶ W)
    (k₀ : reindex Y (liftSub X (ν ≫ μ)) ⟶ V) (j₀ : V ⟶ W)
    (h : Functor.whiskerLeft (liftSub (reindex X μ) ν).mapElements k ≫ j = k₀ ≫ j₀)
    {φ : Subcontext Ω} (s : PartialSection (reindex (pi X Y) (ν ≫ μ)) φ) :
    ((((s.map (Functor.whiskerLeft ν.mapElements (piReindex X Y μ ≫ piBodyMap (reindex X μ) k))).map
      (piReindex (reindex X μ) Z ν)).app).map j) =
    ((((s.map (piReindex X Y (ν ≫ μ))).app).map k₀).map j₀) := by
  exact (congrArg (fun z => z.map j) (partialPiInput X Y μ ν k s)).trans
    (congrArg (fun m => (((s.map (piReindex X Y (ν ≫ μ))).app).map m)) h)

theorem contrPiInput_partial {Ξ Ψ Ω : Context.{u}} (X : Family Ξ) (C : Family (total X))
    (μ : Ψ ⟶ Ξ) (ν : Ω ⟶ Ψ) {D : Family (total (reindex X μ))}
    (e : reindex C (liftSub X μ) ≅ D) {φ : Subcontext Ω}
    (s : PartialSection (reindex (pi X (contr C)) (ν ≫ μ)) φ) :
    ((((s.map (Functor.whiskerLeft ν.mapElements
      (piReindex X (contr C) μ ≫ piBodyMap (reindex X μ)
        ((contrReindexIso C (liftSub X μ)).hom ≫ contrMap e)))).map
      (piReindex (reindex X μ) (contr D) ν)).app).map
        (contrReindexIso D (liftSub (reindex X μ) ν)).hom) =
    ((((s.map (piReindex X (contr C) (ν ≫ μ))).app).map
      (contrReindexIso C (liftSub X (ν ≫ μ))).hom).map
      (contrMap (Functor.isoWhiskerLeft (liftSub (reindex X μ) ν).mapElements e))) := by
  let ρ := liftSub (reindex X μ) ν
  let k := (contrReindexIso C (liftSub X μ)).hom ≫ contrMap e
  have hm : Functor.whiskerLeft ρ.mapElements k ≫ (contrReindexIso D ρ).hom =
      (contrReindexIso C (liftSub X (ν ≫ μ))).hom ≫
        contrMap (Functor.isoWhiskerLeft ρ.mapElements e) := by
    change Functor.whiskerLeft ρ.mapElements (contrReindexIso C (liftSub X μ)).hom ≫
      (Functor.whiskerLeft ρ.mapElements (contrMap e) ≫ (contrReindexIso D ρ).hom) = _
    rw [contrMap_reindex_square, ← Category.assoc, contrReindex_hom_comp]
    rfl
  exact partialPiInput_map X (contr C) μ ν k (contrReindexIso D ρ).hom
    (contrReindexIso C (liftSub X (ν ≫ μ))).hom
    (contrMap (Functor.isoWhiskerLeft ρ.mapElements e)) hm s


theorem partialBody_input_reindex {φ : Subcontext Θ}
    (s : PartialSection (reindex (isEquiv f) (θ ≫ σ)) φ) :
    partialBody (Functor.whiskerLeft σ.mapElements f) θ φ
      (s.map (Functor.whiskerLeft θ.mapElements (inputMap f σ))) =
    (partialBody f (θ ≫ σ) φ s).map
      (contrMap (Functor.isoWhiskerLeft (liftSub (reindex B σ) θ).mapElements (genericFiberReindexIso f σ))) := by
  exact contrPiInput_partial B (fiber f) σ θ (genericFiberReindexIso f σ) s

variable (F : Filling A) (hF : F.Lawful) (G : Filling B) (hG : G.Lawful)

theorem fiberWitness_input
    (c : Contractible (reindex (fiber f) (liftSub B (θ ≫ σ))))
    {φ : Subcontext (total (reindex B (θ ≫ σ)))}
    (s : PartialSection (contr (reindex (fiber f) (liftSub B (θ ≫ σ)))) φ) :
    ContractibilityExtension.witness
      (Contractible.map (Functor.isoWhiskerLeft (liftSub (reindex B σ) θ).mapElements
        (genericFiberReindexIso f σ)) c)
      ((genericFiberFilling (Functor.whiskerLeft σ.mapElements f)
        (F.reindex σ) (hF.reindex _) (G.reindex σ) (hG.reindex _)).reindex (liftSub (reindex B σ) θ))
      ((genericFiberFilling_lawful (Functor.whiskerLeft σ.mapElements f)
        (F.reindex σ) (hF.reindex _) (G.reindex σ) (hG.reindex _)).reindex _)
      (s.map (contrMap (Functor.isoWhiskerLeft (liftSub (reindex B σ) θ).mapElements
        (genericFiberReindexIso f σ)))) =
    Contractible.map (Functor.isoWhiskerLeft (liftSub (reindex B σ) θ).mapElements
        (genericFiberReindexIso f σ))
      (ContractibilityExtension.witness c ((genericFiberFilling f F hF G hG).reindex (liftSub B (θ ≫ σ)))
        ((genericFiberFilling_lawful f F hF G hG).reindex _) s) := by
  let ρ := liftSub (reindex B σ) θ
  let i := Functor.isoWhiskerLeft ρ.mapElements (genericFiberReindexIso f σ)
  have h := ContractibilityExtension.witness_transport i c
    ((genericFiberFilling f F hF G hG).reindex (liftSub B (θ ≫ σ)))
    ((genericFiberFilling_lawful f F hF G hG).reindex _) s
  have hf : ((genericFiberFilling f F hF G hG).reindex (liftSub B (θ ≫ σ))).transport i =
      (genericFiberFilling (Functor.whiskerLeft σ.mapElements f)
        (F.reindex σ) (hF.reindex _) (G.reindex σ) (hG.reindex _)).reindex ρ :=
    congrArg (fun K => K.reindex ρ) (genericFiberFilling_reindex f F hF G hG σ)
  simpa only [hf] using h

theorem extend_input_reindex
    (E : HomotopyEquivalence (Functor.whiskerLeft (θ ≫ σ).mapElements f))
    (φ : Subcontext Θ) (s : PartialSection (reindex (isEquiv f) (θ ≫ σ)) φ) :
    Term.map (Functor.whiskerLeft θ.mapElements (inputMap f σ))
      (extend f F hF G hG (θ ≫ σ) E φ s) =
    extend (Functor.whiskerLeft σ.mapElements f) (F.reindex σ) (hF.reindex _)
      (G.reindex σ) (hG.reindex _) θ E φ
      (s.map (Functor.whiskerLeft θ.mapElements (inputMap f σ))) := by
  have h := fiberWitness_input f σ θ F hF G hG (fiberContractible f (θ ≫ σ) E)
    (partialBody f (θ ≫ σ) φ s)
  rw [fiberContractible_input, ← partialBody_input_reindex] at h
  change Term.map _ (reindexedIsEquivSections f (θ ≫ σ)
    (ContractibilityExtension.witness _ _ _ (partialBody f (θ ≫ σ) φ s))) = _
  rw [inputMap_encoded_reindex]
  exact congrArg (reindexedIsEquivSections (Functor.whiskerLeft σ.mapElements f) θ) h.symm

end
end SquareKit.Cubical.Cartesian.CodeSystem.IsEquivSections

namespace SquareKit.Cubical.Cartesian.CodeSystem.Equivalences
open CategoryTheory EquivalenceFamilies
universe u
noncomputable section
variable {Γ Δ : Context.{u}} {φ ψ : Subcontext Γ}
  {A B : Family (restrictContext (φ.join ψ))} (f : A ⟶ B)
  (F : Filling A) (hF : F.Lawful) (G : Filling B) (hG : G.Lawful)
  (a : HomotopyEquivalence (Functor.whiskerLeft (includeLeft φ ψ).mapElements f))
  (b : HomotopyEquivalence (Functor.whiskerLeft (includeRight φ ψ).mapElements f))
  (σ : Δ ⟶ Γ)
theorem glue_reindex :
    (glue f F hF G hG a b).reindex (restrictSubstitution (φ.join ψ) σ) =
      glue (φ := φ.reindex σ) (ψ := ψ.reindex σ)
        (Functor.whiskerLeft (restrictSubstitution (φ.join ψ) σ).mapElements f)
        (F.reindex (restrictSubstitution (φ.join ψ) σ)) (hF.reindex _)
        (G.reindex (restrictSubstitution (φ.join ψ) σ)) (hG.reindex _)
        (a.reindex (restrictSubstitution φ σ)) (b.reindex (restrictSubstitution ψ σ)) := by
  let ρ := restrictSubstitution (φ.join ψ) σ
  let ιL := includeLeft (φ.reindex σ) (ψ.reindex σ)
  let θ := includeRight (φ.reindex σ) (ψ.reindex σ)
  let f' := Functor.whiskerLeft ρ.mapElements f
  let a' := a.reindex (restrictSubstitution φ σ)
  let b' := b.reindex (restrictSubstitution ψ σ)
  let M := IsEquivSections.inputMap f ρ
  have hl : Term.map (Functor.whiskerLeft ιL.mapElements M)
      (Term.reindex (leftWitness f a) (restrictSubstitution φ σ)) =
      leftWitness (φ := φ.reindex σ) (ψ := ψ.reindex σ) f' a' :=
    (congrArg (Term.map (Functor.whiskerLeft ιL.mapElements M))
      (isEquivReindexSections_comp f (includeLeft φ ψ) (restrictSubstitution φ σ) a)).trans
      (IsEquivSections.inputMap_sections_reindex f ρ ιL a')
  apply glue_reindex_of_sections f F hF G hG a b σ hl
  have hp : ((Sections.overlap (ψ := ψ) (leftWitness f a)).reindex (restrictSubstitution ψ σ)).map
      (Functor.whiskerLeft θ.mapElements M) =
      Sections.overlap (φ := φ.reindex σ) (ψ := ψ.reindex σ)
        (leftWitness (φ := φ.reindex σ) (ψ := ψ.reindex σ) f' a') := by
    apply PartialSection.ext
    intro x hx
    exact congrArg (fun t => t.val ((restrictContext (φ.reindex σ)).elementsMk x.obj ⟨x.val.val,hx⟩)) hl
  have h1 := IsEquivSections.extend_reindex f F hF G hG (includeRight φ ψ) b
    (φ.reindex (restrictInclusion ψ)) (Sections.overlap (leftWitness f a)) (restrictSubstitution ψ σ)
  have h2 := IsEquivSections.extend_input_reindex f ρ θ F hF G hG b'
    ((φ.reindex (restrictInclusion ψ)).reindex (restrictSubstitution ψ σ))
    ((Sections.overlap (leftWitness f a)).reindex (restrictSubstitution ψ σ))
  exact (congrArg (Term.map (Functor.whiskerLeft θ.mapElements M)) h1).trans
    (h2.trans (congrArg (fun s => IsEquivSections.extend f' (F.reindex ρ) (hF.reindex _)
      (G.reindex ρ) (hG.reindex _) θ b' ((φ.reindex σ).reindex (restrictInclusion (ψ.reindex σ))) s) hp))
end
end SquareKit.Cubical.Cartesian.CodeSystem.Equivalences

namespace SquareKit.Cubical.Cartesian.CodeSystem.Box
open CategoryTheory
universe u
variable {Γ Δ : Context.{u}} {φ : Subcontext Γ} {r : Term (interval Γ)} (b : Box Γ φ r) (σ : Δ ⟶ Γ)
theorem faceEquivalence_reindex :
    HEq (b.faceEquivalence.reindex (restrictSubstitution face (intervalSub σ)))
      (b.reindex σ).faceEquivalence :=
  faceEquivalence_reindex_of_uniform (@Equivalences.glue_reindex) b σ

theorem fillCode_reindex :
    raisedSub (intervalSub σ) ≫ b.fillCode = (b.reindex σ).fillCode :=
  fillCode_reindex_of_equivalence b σ (faceEquivalence_reindex b σ)
end SquareKit.Cubical.Cartesian.CodeSystem.Box

namespace SquareKit.Cubical.Cartesian.SmallUniverse
open CategoryTheory
universe u
noncomputable def filling (Ω : Context.{u+1}) : Filling (family Ω) :=
  CodeFilling.filling (@CodeSystem.Box.fillCode) (@CodeSystem.Box.fillCode_source)
    (@CodeSystem.Box.fillCode_tube) (@CodeSystem.Box.fillCode_reindex) Ω

theorem filling_lawful (Ω : Context.{u+1}) : (filling Ω).Lawful :=
  CodeFilling.filling_lawful (@CodeSystem.Box.fillCode) (@CodeSystem.Box.fillCode_source)
    (@CodeSystem.Box.fillCode_tube) (@CodeSystem.Box.fillCode_reindex) Ω

theorem filling_reindex {Ω Λ : Context.{u+1}} (σ : Λ ⟶ Ω) :
    (filling Ω).reindex σ = filling Λ := rfl
end SquareKit.Cubical.Cartesian.SmallUniverse
