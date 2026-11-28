import SquareKit.SheafGroupoidAction
import SquareKit.Internal.PseudofunctorCoherence

/-! Group-sheaf maps on trivial-action groupoids, with identity and composition comparisons. -/
noncomputable section
set_option autoImplicit false
set_option warningAsError true
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
namespace SquareKit.SheafGroupoidAction
open CategoryTheory Opposite
universe u v
variable {C : Type u} [Category.{v} C] {J : GrothendieckTopology C}
variable (G H : Sheaf J GrpCat.{max u v}) (M : Sheaf J (Type (max u v)))
def trivialAction : SheafActionQuotient.Action G M where
  act _ _ m := m
  one_act _ _ := rfl
  mul_act _ _ _ _ := rfl
  natural _ _ _ := rfl
variable {G H M}
def trivialMapArrow (φ : G ⟶ H) {X : Sheaf J (Type (max u v))}
    {m n : (operations (trivialAction G M)).Object X}
    (f : (operations (trivialAction G M)).Arrow m n) :
    (operations (trivialAction H M)).Arrow ⟨m.map⟩ ⟨n.map⟩ where
  map := ⟨{ app U := ↾fun x => (φ.hom.app U (f.map.hom.app U x).1, (f.map.hom.app U x).2)
            naturality := by
              intro U V k
              apply ConcreteCategory.hom_ext
              intro x
              apply Prod.ext
              · exact (congrArg (fun a => φ.hom.app V a.1)
                  (ConcreteCategory.congr_hom (f.map.hom.naturality k) x)).trans
                  (ConcreteCategory.congr_hom (φ.hom.naturality k) (f.map.hom.app U x).1)
              · change (f.map.hom.app V (X.obj.map k x)).2 = M.obj.map k (f.map.hom.app U x).2
                exact congrArg Prod.snd (ConcreteCategory.congr_hom (f.map.hom.naturality k) x) }⟩
  source := f.source
  target := f.target

def trivialMapFunctor (φ : G ⟶ H) {X : Sheaf J (Type (max u v))} :
    (operations (trivialAction G M)).Object X ⥤
      (operations (trivialAction H M)).Object X where
  obj m := ⟨m.map⟩
  map := trivialMapArrow φ
  map_id m := by
    apply SheafGroupoid.Operations.Arrow.ext
    ext U x
    exact Prod.ext (map_one (φ.hom.app U).hom) rfl
  map_comp f g := by
    apply SheafGroupoid.Operations.Arrow.ext
    have value {K : Sheaf J GrpCat.{max u v}} {m n p : (operations (trivialAction K M)).Object X}
        (f : m ⟶ n) (g : n ⟶ p) (U : Cᵒᵖ) (x : X.obj.obj U) :
        (f ≫ g).map.hom.app U x =
          ((show K.obj.obj U from (g.map.hom.app U x).1) * (show K.obj.obj U from (f.map.hom.app U x).1),
            (f.map.hom.app U x).2) := by
      have h₁ : (f ≫ g).map ≫ label =
          SheafTorsor.labelMul (g.map ≫ label) (f.map ≫ label) := by
        change CategoryTheory.Limits.pullback.lift f.map g.map _ ≫ SheafTorsor.labelMul _ _ = _
        rw [SheafTorsor.labelMul_precomp]
        simp only [← Category.assoc, CategoryTheory.Limits.pullback.lift_fst,
          CategoryTheory.Limits.pullback.lift_snd]
      have h₂ : (f ≫ g).map ≫ source = f.map ≫ source := by
        change CategoryTheory.Limits.pullback.lift f.map g.map _ ≫ _ ≫ source = _
        simp only [CategoryTheory.Limits.pullback.lift_fst_assoc]
      exact Prod.ext (congrArg (fun a => a.hom.app U x) h₁)
        (congrArg (fun a => a.hom.app U x) h₂)
    ext U x
    change (φ.hom.app U ((f ≫ g).map.hom.app U x).1, ((f ≫ g).map.hom.app U x).2) = _
    refine (congrArg (fun z : (operations (trivialAction G M)).arrows.obj.obj U =>
      (φ.hom.app U z.1,z.2)) (value f g U x)).trans ?_
    refine Eq.trans ?_ (value (trivialMapArrow φ f) (trivialMapArrow φ g) U x).symm
    exact Prod.ext (map_mul (φ.hom.app U).hom _ _) rfl
open scoped CategoryTheory.Pseudofunctor.StrongTrans

def trivialMapTransformation (φ : G ⟶ H) :
    (operations (trivialAction G M)).pseudofunctor ⟶
      (operations (trivialAction H M)).pseudofunctor where
  app X := (trivialMapFunctor (M := M) (X := X.as.unop) φ).toCatHom
  naturality _ := Iso.refl _
  naturality_naturality := by
    intro X Y f g h
    obtain rfl := LocallyDiscrete.eq_of_hom h
    have hh : h = 𝟙 f := Subsingleton.elim _ _
    subst h
    simp only [PrelaxFunctor.map₂_id]
    apply Cat.Hom₂.ext
    ext m
    simp
  naturality_id X := by
    cases X
    apply Cat.Hom₂.ext
    ext m
    dsimp [SheafGroupoid.Operations.pseudofunctor, SheafGroupoid.Operations.functor,
      Functor.toPseudofunctor']
    simp
    exact ((trivialMapFunctor φ).map_id _).symm
  naturality_comp f g := by
    cases f
    cases g
    apply Cat.Hom₂.ext
    ext m
    dsimp [SheafGroupoid.Operations.pseudofunctor, SheafGroupoid.Operations.functor,
      Functor.toPseudofunctor']
    simp
    exact ((trivialMapFunctor φ).map_id _).symm

variable {K : Sheaf J GrpCat.{max u v}}

def trivialMapComp (φ : G ⟶ H) (ψ : H ⟶ K) :
    trivialMapTransformation (M := M) φ ≫ trivialMapTransformation ψ ≅
      trivialMapTransformation (φ ≫ ψ) :=
  Pseudofunctor.StrongTrans.isoMk (fun _ => Iso.refl _) (by
    intro X Y f
    apply Cat.Hom₂.ext
    ext m
    simp [trivialMapTransformation]
    exact (Category.id_comp _).symm)

def trivialMapId : trivialMapTransformation (M := M) (𝟙 G) ≅
    𝟙 (operations (trivialAction G M)).pseudofunctor :=
  Pseudofunctor.StrongTrans.isoMk (fun _ => Iso.refl _) (by
    intro X Y f
    apply Cat.Hom₂.ext
    ext m
    simp [trivialMapTransformation]
    rfl)

end SquareKit.SheafGroupoidAction
