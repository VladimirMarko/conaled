import SquareKit.Internal.PathTransport.ComparisonElimination

noncomputable section
namespace SquareKit.Internal.PathTransport.GroupoidModel.Comparison
open CategoryTheory CategoryTheory.Functor ContextualElimination PathComparison
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
universe u

private theorem familyMapTo_base {Γ : Type u} [Category.{u} Γ]
    {A B : Γ ⥤ Grpd.{u,u}} (α : A ⟶ B) (x : GroupoidModel.Section A)
    (y : GroupoidModel.Section B) (h : x.familyImage α = y) :
    PathComparison.familyMapTo α x y h ⋙ weaken (PathFamily B y) =
      weaken (PathFamily A x) ⋙ Grothendieck.map (whiskerRight α Grpd.forgetToCat) := by
  cases h
  rfl

private theorem familyMapTo_fiber {Γ : Type u} [Category.{u} Γ]
    {A B : Γ ⥤ Grpd.{u,u}} (α : A ⟶ B) (x : GroupoidModel.Section A)
    (y : GroupoidModel.Section B) (h : x.familyImage α = y) (p : PathCtx A x) :
    HEq ((PathComparison.familyMapTo α x y h).obj p).fiber
      (Discrete.mk ((α.app p.base.base).map p.fiber.as)) := by
  cases h
  rfl

private theorem groth_obj_ext {C : Type u} [Category.{u} C] {F : C ⥤ Cat.{u,u}}
    {X Y : Grothendieck F} (h : X.base = Y.base) (hf : HEq X.fiber Y.fiber) : X = Y := by
  cases X; cases Y; cases h; cases eq_of_heq hf; rfl

private theorem family_transport_obj {C : Type u} [Category.{u} C]
    {A B : C ⥤ Grpd.{u,u}} (h : A = B) (γ : C) (x : A.obj γ) :
    HEq (((eqToHom h).app γ).obj x) x := by cases h; rfl

variable (S : Signature.{u})
local notation "M" => structuralModel S

/-- The actual structural path context uses the comparison from the shared
path-contraction theorem, including its selected identity arrows. -/
theorem path_map {Γ : Context.{u}} (A : Family Γ) (x : Section A) :
    (Typed.StructuralModel.pathContext M A x).map =
      PathComparison.familyMapTo A.map x.left (x.right.reindex Γ.map) x.commutes ⋙
        PathComparison.substitution A.right x.right Γ.map := by
  have hb : (PathComparison.familyMapTo A.map x.left (x.right.reindex Γ.map) x.commutes ⋙
        PathComparison.substitution A.right x.right Γ.map) ⋙
      weaken (PathFamily A.right x.right) =
        weaken (PathFamily A.left x.left) ⋙ A.extend.map := by
    change (PathComparison.familyMapTo A.map x.left (x.right.reindex Γ.map) x.commutes ⋙
      weaken (PathFamily (Γ.map ⋙ A.right) (x.right.reindex Γ.map))) ⋙
        Grothendieck.pre (A.right ⋙ Grpd.forgetToCat) Γ.map = _
    rw [familyMapTo_base]
    rfl
  fapply CategoryTheory.Functor.ext
  · intro p
    apply groth_obj_ext (CategoryTheory.Functor.congr_obj hb p).symm
    apply HEq.trans ?_ (familyMapTo_fiber A.map x.left (x.right.reindex Γ.map) x.commutes p).symm
    change HEq (((Typed.StructuralModel.pathFamily M A x).map.app p.base).obj p.fiber) _
    change HEq (((Family.identity (A.reindex A.weaken) (x.reindex A.weaken)
      A.variable).map.app p.base).obj p.fiber) _
    simp only [Family.identity, NatTrans.comp_app, Grpd.comp_eq_comp, CategoryTheory.Functor.comp_obj]
    exact family_transport_obj _ _ _
  · intro p q f
    apply (weaken (PathFamily A.right x.right)).map_injective
    have ht : (Typed.StructuralModel.pathContext M A x).map ⋙ weaken (PathFamily A.right x.right) =
        (PathComparison.familyMapTo A.map x.left (x.right.reindex Γ.map) x.commutes ⋙
          PathComparison.substitution A.right x.right Γ.map) ⋙ weaken (PathFamily A.right x.right) := hb.symm
    have hm := CategoryTheory.Functor.congr_hom ht f
    simpa only [CategoryTheory.Functor.comp_map, CategoryTheory.Functor.map_comp, eqToHom_map] using hm

/-- The ordinary path contractions form a coherent comparison, derived from
our actual structural path map and the shared base/family square. -/
def rootContraction {Γ : Context.{u}} (A : Family Γ) (x : Section A) :
    Contraction Γ (Typed.StructuralModel.pathContext M A x) where
  left := Instance.rootEquivalence S.base.left S.leftFiber A.left x.left
  right := Instance.rootEquivalence S.base.right S.rightFiber A.right x.right
  square := by
    have hs := PathComparison.baseFamilySquare A.right A.left Γ.map A.map x.right x.left x.commutes
    rw [← path_map S A x] at hs
    exact EquivalenceSquare.changeFunctorSquare
      (Instance.pathEquivalence S.base.right S.rightFiber A.right x.right)
      (Instance.pathEquivalence S.base.left S.leftFiber A.left x.left)
      _ _ hs _ _ (Instance.pathEquivalence_functor _ _ _ _) (Instance.pathEquivalence_functor _ _ _ _)

theorem rootContraction_forward {Γ : Context.{u}} (A : Family Γ) (x : Section A) :
    (rootContraction S A x).forward = Typed.StructuralModel.rootSub M A x := by
  apply Substitution.ext
  · exact congrArg ULift.down (eq_of_heq ((leftProjection S).rootSub A x)).symm
  · exact congrArg ULift.down (eq_of_heq ((rightProjection S).rootSub A x)).symm

end SquareKit.Internal.PathTransport.GroupoidModel.Comparison
