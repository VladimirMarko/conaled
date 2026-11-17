import SquareKit.Internal.Cubical.CartesianUniverseComposition

/-! Small fiber presentations over arbitrary larger contexts. The presentation
is explicit data; no smallness assertion is made about the context. -/
set_option autoImplicit false
set_option warningAsError true
namespace SquareKit.Cubical.Cartesian.SmallUniverse
open CategoryTheory
universe u

namespace LowerFilling

variable {Γ Δ Θ : Context.{u}}

def face (φ : Subcontext Γ) : Subcontext (raisedContext Γ) where
  holds x := φ.holds ((Raising.lowerElements Γ).obj x)
  natural f := φ.natural ((Raising.lowerElements Γ).map f)

def source (r : Term (interval Γ)) : Term (interval (raisedContext Γ)) where
  val x := ⟨(r.val ((Raising.lowerElements Γ).obj x)).down⟩
  property {x y} f := by
    have h := congrArg (fun z : (interval Γ).obj ((Raising.lowerElements Γ).obj y) => z.down)
      (r.property ((Raising.lowerElements Γ).map f))
    exact congrArg (fun z => (ULift.up z : ULift.{u+1} (Cube.Hom y.obj.unop ⟨1⟩))) h

def intervalSub (p : total (interval Δ) ⟶ Γ) :
    total (interval (raisedContext Δ)) ⟶ raisedContext Γ :=
  (raisedIntervalIso Δ).inv ≫ raisedSub p

def box {A : Family Γ} (p : total (interval Δ) ⟶ Γ)
    {φ : Subcontext Δ} {r : Term (interval Δ)} (b : OpenBox (reindex A p) φ r) :
    OpenBox (reindex (Raising.family A) (intervalSub p)) (face φ) (source r) where
  base := Raising.raiseTerm b.base
  tube :=
    { val := fun x hx => ⟨b.tube.val
        ((Raising.lowerElements (total (interval Δ))).obj
          ((raisedIntervalIso Δ).inv.mapElements.obj x)) hx⟩
      natural := fun f hx => congrArg ULift.up (b.tube.natural
        ((Raising.lowerElements (total (interval Δ))).map
          ((raisedIntervalIso Δ).inv.mapElements.map f)) hx) }
  boundary x hx := congrArg ULift.up (b.boundary ((Raising.lowerElements Δ).obj x) hx)

def operation {A : Family Γ} (F : Filling (Raising.family A)) : Filling A where
  fill p φ r b := Raising.lowerTerm
    (Term.reindex (F.fill (intervalSub p) (face φ) (source r) (box p b)) (raisedIntervalIso _).hom)

theorem lawful {A : Family Γ} (F : Filling (Raising.family A)) (hF : F.Lawful) :
    (operation F).Lawful where
  fills p φ r b := by
    constructor
    · apply Term.ext
      intro x
      exact congrArg (fun t => (t.val ((raisedElements _).obj x)).down)
        (hF.fills (intervalSub p) (face φ) (source r) (box p b)).1
    · intro x hx
      exact congrArg ULift.down ((hF.fills (intervalSub p) (face φ) (source r) (box p b)).2
        ((raisedIntervalIso _).hom.mapElements.obj ((raisedElements _).obj x)) hx)
  uniform p φ r b σ := by
    apply Term.ext
    intro x
    exact congrArg (fun t => (t.val
      ((raisedIntervalIso _).hom.mapElements.obj ((raisedElements _).obj x))).down)
      (hF.uniform (intervalSub p) (face φ) (source r) (box p b) (raisedSub σ))

end LowerFilling

open NativeUnivalence

namespace SmallPresentation

variable {Ξ : Context.{u+1}} (A : Family Ξ)

/-- A small representative of each fiber, with both inverse equations. -/
structure Data where
  fiber : Ξ.Elements → Type u
  equiv : ∀ x, fiber x ≃ A.obj x

namespace Data
variable {A} (P : Data A)

def family : Ξ.Elements ⥤ Type u where
  obj := P.fiber
  map f := TypeCat.ofHom (fun z => (P.equiv _).symm (A.map f (P.equiv _ z)))
  map_id x := by
    apply ConcreteCategory.hom_ext
    intro z
    simp
  map_comp f g := by
    apply ConcreteCategory.hom_ext
    intro z
    simp

def chartFamily {Γ : Context.{u}} (σ : raisedContext Γ ⟶ Ξ) : Family Γ :=
  raisedElements Γ ⋙ σ.mapElements ⋙ P.family

def chartIso {Γ : Context.{u}} (σ : raisedContext Γ ⟶ Ξ) :
    Raising.family (P.chartFamily σ) ≅ reindex A σ :=
  NatIso.ofComponents (fun x => Equiv.toIso
    ((Equiv.ulift).trans (P.equiv (σ.mapElements.obj x)))) (by
    intro x y f
    apply ConcreteCategory.hom_ext
    intro z
    exact (P.equiv _).apply_symm_apply _)

variable (F : Filling A) (hF : F.Lawful)

def localFamily {Γ : Context.{u}} (σ : raisedContext Γ ⟶ Ξ) : LocalFamily Γ :=
  LocalFamily.ofFilling (P.chartFamily σ)
    (LowerFilling.operation ((F.reindex σ).transport (P.chartIso σ).symm))
    (LowerFilling.lawful _ (Filling.transport_lawful _ _ (hF.reindex σ)))

theorem local_reindex {Γ Δ : Context.{u}} (σ : raisedContext Γ ⟶ Ξ) (τ : Δ ⟶ Γ) :
    (P.localFamily F hF σ).reindex τ = P.localFamily F hF (raisedSub τ ≫ σ) := rfl

/-- A code map on the original large context, constructed on represented charts. -/
def code : Ξ ⟶ smallFamilyCodes.{u} where
  app I := TypeCat.ofHom (fun x => P.localFamily F hF (chart (Ξ.elementsMk I x)))
  naturality I J f := by
    apply ConcreteCategory.hom_ext
    intro x
    exact (congrArg (P.localFamily F hF) (chart_restrict
      (Functor.Elements.homMk f rfl : Ξ.elementsMk I x ⟶ Ξ.elementsMk J (Ξ.map f x)))).symm

def chartElements (x : Ξ.Elements) : (representable.{u} x.obj.unop).Elements ⥤ Ξ.Elements :=
  raisedElements _ ⋙ (chart x).mapElements

theorem generic_source (x : Ξ.Elements) :
    (chartElements x).obj (representableGeneric.{u} x.obj.unop) = x :=
  Functor.Elements.ext _ _ rfl
    ((ConcreteCategory.congr_hom (Ξ.map_id x.obj) _).trans (chart_generic x))

private theorem map_heq (S : Ξ.Elements ⥤ Type u) {x y z : Ξ.Elements}
    (f : x ⟶ y) (g : x ⟶ z) (e : y = z) (h : HEq f.hom g.hom) (v : S.obj x) :
    HEq (S.map f v) (S.map g v) := by
  cases e
  have hf : f = g := Functor.Elements.hom_ext (eq_of_heq h)
  cases hf
  rfl

private theorem map_identity_heq (S : Ξ.Elements ⥤ Type u) {x y : Ξ.Elements}
    (f : x ⟶ y) (e : x = y) (h : HEq f.hom (𝟙 x.obj)) (v : S.obj x) :
    HEq (S.map f v) v := by
  cases e
  have hf : f = 𝟙 x := Functor.Elements.hom_ext (eq_of_heq h)
  cases hf
  exact heq_of_eq (ConcreteCategory.congr_hom (S.map_id x) v)

def decodeComponent (x : Ξ.Elements) :
    ((P.code F hF).mapElements ⋙ universalDecode).obj x ≅ P.family.obj x :=
  P.family.mapIso (eqToIso (generic_source x))

theorem decodeMap_heq {x y : Ξ.Elements} (f : x ⟶ y)
    (a : ((P.code F hF).mapElements ⋙ universalDecode).obj x) :
    HEq (((P.code F hF).mapElements ⋙ universalDecode).map f a)
      (P.family.map ((chartElements x).map (representableGenericHom f.hom.unop)) a) :=
  cast_heq _ _

def decodeIso : ((P.code F hF).mapElements ⋙ universalDecode) ≅ P.family :=
  NatIso.ofComponents (P.decodeComponent F hF) (by
    intro x y f
    apply ConcreteCategory.hom_ext
    intro a
    have ey := generic_source y
    have hy := map_identity_heq P.family (eqToHom ey) ey
      (heq_of_eq (elements_eqToHom_hom ey)) (((P.code F hF).mapElements ⋙ universalDecode).map f a)
    have targetRel : (chartElements x).obj
        ((representableMap f.hom.unop).mapElements.obj (representableGeneric.{u} y.obj.unop)) = y :=
      (congrArg (fun (σ : raisedContext (representable.{u} y.obj.unop) ⟶ Ξ) => (raisedElements _ ⋙ σ.mapElements).obj
        (representableGeneric.{u} y.obj.unop)) (chart_restrict f)).trans ey
    have hm := map_heq P.family
      (eqToHom (generic_source x) ≫ f)
      ((chartElements x).map (representableGenericHom f.hom.unop)) targetRel.symm
      (heq_of_eq (by
        change (eqToHom (generic_source x) : _ ⟶ x).hom ≫ f.hom = f.hom
        rw [elements_eqToHom_hom]
        exact Category.id_comp f.hom)) a
    have hc := ConcreteCategory.congr_hom
      (P.family.map_comp (eqToHom (generic_source x)) f) a
    exact eq_of_heq (hy.trans ((P.decodeMap_heq F hF f a).trans
      (hm.symm.trans (heq_of_eq hc)))))

/-- The constructed decoder comparison is a family isomorphism, not code equality. -/
def nativeIso : liftedDecode (P.code F hF) ≅ A :=
  NatIso.ofComponents (fun x =>
    (Equiv.ulift.trans (((P.decodeIso F hF).app x).toEquiv.trans (P.equiv x))).toIso) (by
      intro x y f
      apply ConcreteCategory.hom_ext
      intro z
      have h := ConcreteCategory.congr_hom ((P.decodeIso F hF).hom.naturality f) z.down
      exact (congrArg (P.equiv y) h).trans ((P.equiv y).apply_symm_apply _))

end Data

end SmallPresentation

end SquareKit.Cubical.Cartesian.SmallUniverse
