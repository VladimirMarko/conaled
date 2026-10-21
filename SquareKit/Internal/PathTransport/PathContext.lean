import SquareKit.Internal.PathTransport.SplitFamily
import SquareKit.Internal.PathTransport.TelescopeElimination

/-!
# Based paths in actual context comprehension

The path context is the successive extension by an endpoint and its identity
witness. Its reflexive inclusion has a normalized contraction for every split
groupoid family, including nonconstant families.
-/
noncomputable section
open CategoryTheory
namespace SquareKit.Internal.PathTransport.GroupoidModel
namespace PathComparison
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
universe u v w z
variable {Γ : Type u} [Category.{v} Γ]
variable (A : Γ ⥤ Grpd.{z,w}) (x : Section A)
abbrev PathFamily := identityFamily (weaken A ⋙ A) (x.reindex (weaken A)) («variable» A)
abbrev PathCtx := Extend (PathFamily A x)

def arrow (a : PathCtx A x) : x.lift.obj a.base.base ⟶ a.base :=
  (Grothendieck.ι (A ⋙ Grpd.forgetToCat) a.base.base).map a.fiber.as

@[simp] theorem arrow_base (a : PathCtx A x) : (arrow A x a).base = 𝟙 _ := rfl

theorem arrow_natural {a b : PathCtx A x} (f : a ⟶ b) :
    x.lift.map f.base.base ≫ arrow A x b = arrow A x a ≫ f.base := by
  have h := f.fiber.eq
  change inv (x.map f.base.base) ≫ (A.map f.base.base).map a.fiber.as ≫ f.base.fiber = b.fiber.as at h
  fapply Grothendieck.ext
  · simp [Section.lift]
  · dsimp [arrow, Grothendieck.ι, Section.lift, Grpd.forgetToCat]
    rw [← h]
    simp [eqToHom_map]
    have hn := NatIso.naturality_2 (eqToIso (A.map_id b.base.base)) (x.map f.base.base)
    simp only [eqToIso.hom, eqToHom_app, Grpd.id_eq_id, Functor.id_map] at hn
    rw [← hn]
    simp

def retract : PathCtx A x ⥤ Γ := weaken (PathFamily A x) ⋙ weaken A

def reflexive : Γ ⥤ PathCtx A x where
  obj γ := ⟨x.lift.obj γ, Discrete.mk (𝟙 _)⟩
  map f := ⟨x.lift.map f, Discrete.eqToHom (by
    change inv (x.map f) ≫ (A.map f).map (𝟙 _) ≫ x.map f = 𝟙 _
    simp)⟩
  map_id γ := by
    fapply Grothendieck.ext
    · exact x.lift.map_id γ
    · exact congrArg Discrete.Hom.mk rfl
  map_comp f g := by
    fapply Grothendieck.ext
    · exact x.lift.map_comp f g
    · exact congrArg Discrete.Hom.mk rfl

instance forget_faithful : (weaken (PathFamily A x)).Faithful where
  map_injective {a b} f g h := by
    fapply Grothendieck.ext
    · exact h
    · exact congrArg Discrete.Hom.mk rfl

theorem reflexive_retract : reflexive A x ⋙ retract A x = 𝟭 Γ := rfl

def contractionArrow (a : PathCtx A x) :
    (reflexive A x).obj ((retract A x).obj a) ⟶ a :=
  ⟨arrow A x a, Discrete.eqToHom (by
    change inv (x.map (𝟙 a.base.base)) ≫
      (A.map (𝟙 a.base.base)).map (𝟙 _) ≫ (arrow A x a).fiber = a.fiber.as
    rw [x.map_id]
    simp [arrow, Grothendieck.ι]
  )⟩

variable [IsGroupoid Γ]

def contraction : retract A x ⋙ reflexive A x ≅ 𝟭 (PathCtx A x) :=
  NatIso.ofComponents (fun a => asIso (contractionArrow A x a)) (by
    intro a b f
    apply (weaken (PathFamily A x)).map_injective
    exact arrow_natural A x f)

@[simp] theorem contraction_reflexive (γ : Γ) :
    (contraction A x).hom.app ((reflexive A x).obj γ) = 𝟙 _ := by
  apply (weaken (PathFamily A x)).map_injective
  change arrow A x ((reflexive A x).obj γ) = 𝟙 _
  fapply Grothendieck.ext
  · rfl
  · simp [arrow, reflexive, Grothendieck.ι]
    exact Category.comp_id _

def pathEquivalence : Γ ≌ PathCtx A x where
  functor := reflexive A x
  inverse := retract A x
  unitIso := Iso.refl _
  counitIso := contraction A x
  functor_unitIso_comp γ := by simp

end PathComparison
end SquareKit.Internal.PathTransport.GroupoidModel

namespace SquareKit.Internal.PathTransport.GroupoidModel.PathComparison
open CategoryTheory CategoryTheory.Functor
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
variable {Γ : Type u} [Category.{v} Γ]
variable {Δ : Type*} [Category* Δ]
variable (A : Γ ⥤ Grpd.{z,w}) (x : Section A) (σ : Δ ⥤ Γ)

def substitution : PathCtx (σ ⋙ A) (x.reindex σ) ⥤ PathCtx A x :=
  Grothendieck.pre (PathFamily A x ⋙ Grpd.forgetToCat)
    (Grothendieck.pre (A ⋙ Grpd.forgetToCat) σ)

theorem substitution_retract :
    substitution A x σ ⋙ retract A x = retract (σ ⋙ A) (x.reindex σ) ⋙ σ := rfl

theorem substitution_reflexive :
    reflexive (σ ⋙ A) (x.reindex σ) ⋙ substitution A x σ = σ ⋙ reflexive A x := rfl

theorem substitution_arrow (a : PathCtx (σ ⋙ A) (x.reindex σ)) :
    (Grothendieck.pre (A ⋙ Grpd.forgetToCat) σ).map (arrow (σ ⋙ A) (x.reindex σ) a) =
      arrow A x ((substitution A x σ).obj a) := by
  fapply Grothendieck.ext
  · exact σ.map_id _
  · simp [arrow, Grothendieck.ι, Grothendieck.pre]
    rfl

variable [IsGroupoid Γ] [IsGroupoid Δ]

theorem substitution_contraction :
    isoWhiskerRight (contraction (σ ⋙ A) (x.reindex σ)) (substitution A x σ) =
      isoWhiskerLeft (substitution A x σ) (contraction A x) := by
  apply Iso.ext
  apply NatTrans.ext
  funext a
  apply (weaken (PathFamily A x)).map_injective
  exact substitution_arrow A x σ a
end SquareKit.Internal.PathTransport.GroupoidModel.PathComparison
