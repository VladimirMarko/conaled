import SquareKit.Internal.Cubical.Localization

/-! A dependent product presentation by natural sections of a localized display
map. The diagram's category depends only on the underlying cube. -/
namespace SquareKit.Cubical.Presheaf
open CategoryTheory
universe u v w

/-- A diagram of types with a chosen projection. -/
structure ProjectionDiagram (C : Type v) [Category.{w} C] where
  base : C ⥤ Type u
  total : C ⥤ Type u
  projection : total ⟶ base

namespace ProjectionDiagram
variable {C : Type v} [Category.{w} C]

abbrev Section (D : ProjectionDiagram.{u} C) :=
  {s : D.base ⟶ D.total // s ≫ D.projection = 𝟙 D.base}

def pull {E : Type*} [Category E] (F : E ⥤ C) (D : ProjectionDiagram.{u} C) :
    ProjectionDiagram E where
  base := F ⋙ D.base
  total := F ⋙ D.total
  projection := Functor.whiskerLeft F D.projection

def Section.pull {E : Type*} [Category E] {D : ProjectionDiagram.{u} C}
    (F : E ⥤ C) (s : Section D) : Section (pull F D) where
  val := Functor.whiskerLeft F s.val
  property := congrArg (Functor.whiskerLeft F) s.property

theorem Section.hext {D E : ProjectionDiagram.{u} C} (h : D = E)
    (s : Section D) (t : Section E)
    (hv : ∀ (c : C) (a : D.base.obj c) (b : E.base.obj c),
      HEq a b → HEq (s.val.app c a) (t.val.app c b)) : HEq s t := by
  cases h
  apply heq_of_eq
  apply Subtype.ext
  apply NatTrans.ext
  funext c
  apply ConcreteCategory.hom_ext
  intro a
  exact eq_of_heq (hv c a a HEq.rfl)

end ProjectionDiagram

def sigmaProjection {Γ : Context.{u}} (A : Family Γ) (B : Family (total A)) : sigma A B ⟶ A where
  app _ := TypeCat.ofHom Sigma.fst
  naturality _ _ _ := rfl

def productDiagram {Γ : Context.{u}} (A : Family Γ) (B : Family (total A)) :
    ProjectionDiagram Γ.Elements where
  base := A
  total := sigma A B
  projection := sigmaProjection A B

def localProductDiagram {Γ : Context.{u}} (A : Family Γ) (B : Family (total A)) (x : Γ.Elements) :
    ProjectionDiagram (Under x.obj) :=
  ProjectionDiagram.pull (localize Γ x) (productDiagram A B)

/-- Equality of diagrams supplies equality of the resulting section types. -/
theorem localProductDiagram_substitution {Γ Δ : Context.{u}} (A : Family Γ)
    (B : Family (total A)) (σ : Δ ⟶ Γ) (x : Δ.Elements) :
    localProductDiagram (reindex A σ) (reindex B (liftSub A σ)) x =
      localProductDiagram A B (σ.mapElements.obj x) := by
  change ProjectionDiagram.pull (localize Δ x ⋙ σ.mapElements) (productDiagram A B) = _
  rw [localize_substitution]
  rfl

abbrev LocalPi {Γ : Context.{u}} (A : Family Γ) (B : Family (total A)) (x : Γ.Elements) :=
  ProjectionDiagram.Section (localProductDiagram A B x)

theorem localPi_substitution {Γ Δ : Context.{u}} (A : Family Γ) (B : Family (total A))
    (σ : Δ ⟶ Γ) (x : Δ.Elements) :
    LocalPi (reindex A σ) (reindex B (liftSub A σ)) x = LocalPi A B (σ.mapElements.obj x) :=
  congrArg ProjectionDiagram.Section (localProductDiagram_substitution A B σ x)

def localArrow {Γ : Context.{u}} (x : Γ.Elements) (f : Under x.obj) :
    x ⟶ (localize Γ x).obj f := Functor.Elements.homMk f.hom rfl

theorem localArrow_comp {Γ : Context.{u}} (x : Γ.Elements) {f g : Under x.obj} (h : f ⟶ g) :
    localArrow x f ≫ (localize Γ x).map h = localArrow x g :=
  Functor.Elements.hom_ext (Under.w h)

/-- No generalized argument is lost when passing to local natural sections. -/
def PiElement.toLocal {Γ : Context.{u}} {A : Family Γ} {B : Family (total A)}
    {x : Γ.Elements} (p : PiElement A B x) : LocalPi A B x where
  val := {
    app := fun f => TypeCat.ofHom (fun a => ⟨a,p.val (localArrow x f) a⟩)
    naturality := by
      intro f g h
      apply ConcreteCategory.hom_ext
      intro a
      change (⟨A.map ((localize Γ x).map h) a,
        p.val (localArrow x g) (A.map ((localize Γ x).map h) a)⟩ :
        (sigma A B).obj ((localize Γ x).obj g)) =
        sigmaMap A B ((localize Γ x).map h) ⟨a,p.val (localArrow x f) a⟩
      apply congrArg (Sigma.mk _)
      have hp := p.naturality (localArrow x f) ((localize Γ x).map h) a
      rw [localArrow_comp] at hp
      exact hp.symm }
  property := rfl

private theorem sigma_mk_cast {α : Type u} {β : α → Type u} (z : Sigma β)
    {a : α} (h : z.1 = a) : z = ⟨a,h ▸ z.2⟩ := by
  cases h
  rfl

def LocalPi.value {Γ : Context.{u}} {A : Family Γ} {B : Family (total A)}
    {x : Γ.Elements} (s : LocalPi A B x) (f : Under x.obj)
    (a : A.obj ((localize Γ x).obj f)) : B.obj (extendObj A ((localize Γ x).obj f) a) := by
  have h : (s.val.app f a).1 = a := congrArg (fun t => t.app f a) s.property
  exact h ▸ (s.val.app f a).2

theorem LocalPi.pair_value {Γ : Context.{u}} {A : Family Γ} {B : Family (total A)}
    {x : Γ.Elements} (s : LocalPi A B x) (f : Under x.obj)
    (a : A.obj ((localize Γ x).obj f)) : s.val.app f a = ⟨a,s.value f a⟩ :=
  sigma_mk_cast _ _

theorem LocalPi.value_natural {Γ : Context.{u}} {A : Family Γ} {B : Family (total A)}
    {x : Γ.Elements} (s : LocalPi A B x) {f g : Under x.obj} (h : f ⟶ g)
    (a : A.obj ((localize Γ x).obj f)) :
    B.map (extendHom A ((localize Γ x).map h) a) (s.value f a) =
      s.value g (A.map ((localize Γ x).map h) a) := by
  have hs := s.val.naturality_apply h a
  change s.val.app g (A.map ((localize Γ x).map h) a) =
    sigmaMap A B ((localize Γ x).map h) (s.val.app f a) at hs
  rw [s.pair_value g, s.pair_value f] at hs
  exact (Sigma.mk.inj hs).2.eq.symm

/-- Pulling the normalized section back along element arrows recovers the ordinary display diagram. -/
def LocalPi.onElements {Γ : Context.{u}} {A : Family Γ} {B : Family (total A)}
    {x : Γ.Elements} (s : LocalPi A B x) :
    ProjectionDiagram.Section (ProjectionDiagram.pull (Under.forget x) (productDiagram A B)) :=
  Eq.mp (congrArg ProjectionDiagram.Section
    (congrArg (fun F => ProjectionDiagram.pull F (productDiagram A B)) (localize_forget x)))
      (s.pull (Under.post (Functor.Elements.π Γ)))

private theorem section_cast_app {C : Type v} [Category.{w} C]
    {D E : ProjectionDiagram.{u} C} (h : D = E) (s : ProjectionDiagram.Section D)
    (c : C) {a : D.base.obj c} {b : E.base.obj c} (hab : HEq a b) :
    HEq ((Eq.mp (congrArg ProjectionDiagram.Section h) s).val.app c b) (s.val.app c a) := by
  cases h
  cases hab
  rfl

theorem LocalPi.onElements_localArrow {Γ : Context.{u}} {A : Family Γ} {B : Family (total A)}
    {x : Γ.Elements} (s : LocalPi A B x) (f : Under x.obj)
    (a : A.obj ((localize Γ x).obj f)) :
    s.onElements.val.app (Under.mk (localArrow x f)) a = s.val.app f a := by
  have h := section_cast_app
    (congrArg (fun F => ProjectionDiagram.pull F (productDiagram A B)) (localize_forget x))
    (s.pull (Under.post (Functor.Elements.π Γ))) (Under.mk (localArrow x f)) (a := a) (b := a) HEq.rfl
  exact eq_of_heq h

def LocalPi.fromLocal {Γ : Context.{u}} {A : Family Γ} {B : Family (total A)}
    {x : Γ.Elements} (s : LocalPi A B x) : PiElement A B x := by
  let t := s.onElements
  have ht (f : Under x) (a : A.obj f.right) : (t.val.app f a).1 = a :=
    congrArg (fun η => η.app f a) t.property
  let v (f : Under x) (a : A.obj f.right) : B.obj (extendObj A f.right a) :=
    ht f a ▸ (t.val.app f a).2
  have hv (f : Under x) (a : A.obj f.right) : t.val.app f a = ⟨a,v f a⟩ :=
    sigma_mk_cast _ _
  exact {
    val := fun f a => v (Under.mk f) a
    naturality := by
      intro y z f g a
      have h := t.val.naturality_apply (Under.homMk g rfl : Under.mk f ⟶ Under.mk (f ≫ g)) a
      change t.val.app (Under.mk (f ≫ g)) (A.map g a) =
        sigmaMap A B g (t.val.app (Under.mk f) a) at h
      rw [hv, hv] at h
      exact (Sigma.mk.inj h).2.eq.symm }

theorem LocalPi.fromLocal_value {Γ : Context.{u}} {A : Family Γ} {B : Family (total A)}
    {x : Γ.Elements} (s : LocalPi A B x) (f : Under x.obj)
    (a : A.obj ((localize Γ x).obj f)) :
    s.fromLocal.val (localArrow x f) a = s.value f a := by
  have h : s.onElements.val.app (Under.mk (localArrow x f)) a =
      ⟨a,s.fromLocal.val (localArrow x f) a⟩ := sigma_mk_cast _ _
  rw [s.onElements_localArrow, s.pair_value] at h
  exact (Sigma.mk.inj h).2.eq.symm

theorem LocalPi.fromLocal_toLocal {Γ : Context.{u}} {A : Family Γ} {B : Family (total A)}
    {x : Γ.Elements} (p : PiElement A B x) : p.toLocal.fromLocal = p := by
  apply PiElement.ext
  intro y f a
  obtain ⟨⟨J,g⟩,h⟩ := (elementArrowEquiv Γ x).symm.surjective ⟨y,f⟩
  cases h
  exact p.toLocal.fromLocal_value (Under.mk g) a

theorem LocalPi.toLocal_fromLocal {Γ : Context.{u}} {A : Family Γ} {B : Family (total A)}
    {x : Γ.Elements} (s : LocalPi A B x) : s.fromLocal.toLocal = s := by
  apply Subtype.ext
  apply NatTrans.ext
  funext f
  apply ConcreteCategory.hom_ext
  intro a
  change (⟨a, s.fromLocal.val (localArrow x f) a⟩ :
    Σ a : A.obj ((localize Γ x).obj f), B.obj (extendObj A ((localize Γ x).obj f) a)) = _
  exact (congrArg (fun b => Sigma.mk a b) (s.fromLocal_value f a)).trans
    (s.pair_value f a).symm

theorem PiElement.pair_heq {Γ : Context.{u}} {A : Family Γ} {B : Family (total A)}
    {x y z : Γ.Elements} (p : PiElement A B x) (h : y = z)
    (f : x ⟶ y) (g : x ⟶ z) (hf : HEq f g)
    (a : A.obj y) (b : A.obj z) (ha : HEq a b) :
    HEq (⟨a,p.val f a⟩ : Σ a : A.obj y, B.obj (extendObj A y a))
      (⟨b,p.val g b⟩ : Σ b : A.obj z, B.obj (extendObj A z b)) := by
  cases h
  cases eq_of_heq hf
  cases eq_of_heq ha
  rfl

def localPiEquiv {Γ : Context.{u}} (A : Family Γ) (B : Family (total A)) (x : Γ.Elements) :
    PiElement A B x ≃ LocalPi A B x where
  toFun := PiElement.toLocal
  invFun := LocalPi.fromLocal
  left_inv := LocalPi.fromLocal_toLocal
  right_inv := LocalPi.toLocal_fromLocal

end SquareKit.Cubical.Presheaf
