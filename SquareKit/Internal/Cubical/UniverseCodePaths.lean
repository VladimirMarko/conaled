import SquareKit.Internal.Cubical.SmallFamilyGlue

/-! Dimension-dependent universe codes and native paths. These adapters do not
supply universe filling or an equivalence-to-path operation. -/
set_option autoImplicit false
set_option warningAsError true
namespace SquareKit.Cubical.Presheaf.SmallUniverse
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
    (term a).reindex σ = term (σ ≫ a) := rfl

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


end SquareKit.Cubical.Presheaf.SmallUniverse
