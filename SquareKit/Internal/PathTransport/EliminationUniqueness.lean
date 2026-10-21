import SquareKit.Internal.PathTransport.GroupoidElimination

/-!
# Uniqueness of elimination into discrete fibers

Restriction along an essentially surjective functor determines a section when
all fibers are discrete. This gives strict uniqueness of contextual elimination
for primitive set-valued and identity motives. Arbitrary groupoid-valued motives
can have distinct sections with the same restriction, so discreteness is an
explicit assumption.
-/
noncomputable section
namespace SquareKit.Internal.PathTransport.GroupoidModel
open CategoryTheory ContextualElimination
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
universe u v w z u' v'

/-- Set-valued motives have discrete fibers at every context object. -/
instance setFamily_isDiscrete {Γ : Type u} [Category.{v} Γ] (B : Γ ⥤ Type w) :
    ∀ γ, IsDiscrete ((setFamily B).obj γ) := fun _ =>
  inferInstanceAs (IsDiscrete (Discrete _))

instance identityFamily_isDiscrete {Γ : Type u} [Category.{v} Γ]
    (A : Γ ⥤ Grpd.{z,w}) (x y : Section A) : ∀ γ, IsDiscrete ((identityFamily A x y).obj γ) :=
  setFamily_isDiscrete (directIdentity A x y)

instance primitiveFiber_isDiscrete {Γ : Type u} [Category.{v} Γ]
    {C : Type w} [Groupoid.{z} C] (B : C ⥤ Type w)
    (x : Section (constant (Γ := Γ) C)) : ∀ γ, IsDiscrete ((primitiveFiber B x).obj γ) :=
  setFamily_isDiscrete (baseFunctor x ⋙ B)

/-- Substitution preserves pointwise discreteness. -/
instance reindex_isDiscrete {Γ : Type u} [Category.{v} Γ] {Δ : Type u'} [Category.{v'} Δ]
    (A : Γ ⥤ Grpd.{z,w}) [∀ γ, IsDiscrete (A.obj γ)] (F : Δ ⥤ Γ) :
    ∀ δ, IsDiscrete ((F ⋙ A).obj δ) := fun δ => inferInstanceAs (IsDiscrete (A.obj (F.obj δ)))

namespace Section
variable {Γ : Type u} [Category.{v} Γ] {A : Γ ⥤ Grpd.{z,w}}
variable [∀ γ, IsDiscrete (A.obj γ)]

/-- With discrete fibers, object components determine a section. -/
theorem ext_discrete {s t : Section A} (h : ∀ γ, s.obj γ = t.obj γ) : s = t := by
  cases s with
  | mk so sm si sc =>
    cases t with
    | mk tobj tm ti tc =>
      have ho : so = tobj := funext h
      cases ho
      congr
      funext γ δ f
      exact Subsingleton.elim _ _

/-- Every context object is isomorphic to one in the image, and discrete fibers
turn the section arrow over that isomorphism into an equality. -/
theorem reindex_injective_of_essSurj {Δ : Type u'} [Category.{v'} Δ]
    (F : Δ ⥤ Γ) [F.EssSurj] : Function.Injective (fun s : Section A => s.reindex F) := by
  intro s t h
  apply ext_discrete
  intro γ
  let f := (F.objObjPreimageIso γ).hom
  have hs := IsDiscrete.eq_of_hom (s.map f)
  have ht := IsDiscrete.eq_of_hom (t.map f)
  have hi : s.obj (F.obj (F.objPreimage γ)) = t.obj (F.obj (F.objPreimage γ)) :=
    congrArg (fun q : Section (F ⋙ A) => q.obj (F.objPreimage γ)) h
  exact hs.symm.trans ((congrArg (A.map f).obj hi).trans ht)
end Section

variable {D C : Cat.{u,u}} (e : NormalizedEquivalence D C) (A : C ⥤ Grpd.{u,u})
variable [∀ c, IsDiscrete (A.obj c)]

/-- Any section extending the same reflexive branch equals the chosen eliminator. -/
theorem eliminateSection_unique (d : Section (e.equiv.functor ⋙ A)) (s : Section A)
    (h : s.reindex e.equiv.functor = d) : eliminateSection e A d = s := by
  apply Section.reindex_injective_of_essSurj e.equiv.functor
  exact (eliminateSection_beta e A d).trans h.symm

end SquareKit.Internal.PathTransport.GroupoidModel

namespace SquareKit.Internal.PathTransport.GroupoidModel
open CategoryTheory ContextualElimination
universe u
variable {D C : Cat.{u,u}} (e : NormalizedEquivalence D C)

/-- A set-valued motive has a unique extension of its reflexive branch. -/
example (B : C ⥤ Type u) (d : Section (e.equiv.functor ⋙ setFamily B))
    (s : Section (setFamily B)) (h : s.reindex e.equiv.functor = d) :
    eliminateSection e (setFamily B) d = s := eliminateSection_unique e _ d s h

/-- Identity motives retain strict uniqueness, including identities of arbitrary
objects of groupoid-valued families. -/
example (A : C ⥤ Grpd.{u,u}) (x y : Section A)
    (d : Section (e.equiv.functor ⋙ identityFamily A x y))
    (s : Section (identityFamily A x y)) (h : s.reindex e.equiv.functor = d) :
    eliminateSection e (identityFamily A x y) d = s := eliminateSection_unique e _ d s h
end SquareKit.Internal.PathTransport.GroupoidModel
