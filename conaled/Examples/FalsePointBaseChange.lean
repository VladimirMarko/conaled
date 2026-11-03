import Examples.FalsePointProduct

/-! Experimental substitution of the false-point dependent product by Boolean
negation, through the canonical Beck–Chevalley isomorphism. -/
noncomputable section
namespace Examples.FalsePointBaseChange
open CategoryTheory Limits Opposite SquareKit
open Examples.SheafImage Examples.SheafImage.Diamond Examples.SheafBaseChange
open Examples.SheafFamilies Examples.FalsePointProduct

def negationIso : D ≅ D where
  hom := Examples.SheafFunctions.negation
  inv := Examples.SheafFunctions.negation
  hom_inv_id := by ext M b; exact Bool.not_not b
  inv_hom_id := by ext M b; exact Bool.not_not b

theorem square : IsPullback truePoint (𝟙 SheafImage.terminal) negationIso.hom falsePoint :=
  IsPullback.of_vert_isIso ⟨rfl⟩

abbrev trueActual := (SheafDependentProduct.pi truePoint).obj input

def substitution : (Over.pullback negationIso.hom).obj actual ≅ trueActual :=
  (SheafDependentProduct.baseChange falsePoint square).app input ≪≫
    (SheafDependentProduct.pi truePoint).mapIso ((Over.pullbackId (X := SheafImage.terminal)).app input)

/-- The unnormalized forward map is exactly the canonical mate, with its actual counit law. -/
abbrev evaluation := SheafDependentProduct.baseChange_evaluation falsePoint square input

/-- Any isomorphism over D induces an equivalence of its actual section fibers. -/
def fiberIso {P Q : Over D} (i : P ≅ Q) (M : Diamond) (b : Bool) :
    {x : P.left.obj.obj (op M) // P.hom.hom.app (op M) x = b} ≃
    {x : Q.left.obj.obj (op M) // Q.hom.hom.app (op M) x = b} :=
  (((sheafToPresheaf _ _).mapIso ((SheafSlice.forward D).mapIso i)).app
    (op (ElementSite.point D.obj M b))).toEquiv

/-- Pullback by negation exchanges the two actual fibers. -/
def pullbackFiber (M : Diamond) (b : Bool) :
    {x : ((Over.pullback negationIso.hom).obj actual).left.obj.obj (op M) //
      ((Over.pullback negationIso.hom).obj actual).hom.hom.app (op M) x = b} ≃ Fiber M (!b) where
  toFun z := ⟨(SheafFamily.sectionsEquiv actual.hom negationIso.hom (op M) z.val).val.1, by
    have hp := (SheafFamily.sectionsEquiv actual.hom negationIso.hom (op M) z.val).property
    have hb := (SheafFamily.sectionsEquiv_snd actual.hom negationIso.hom (op M) z.val).trans z.property
    exact hp.trans (congrArg Bool.not hb)⟩
  invFun z := ⟨(SheafFamily.sectionsEquiv actual.hom negationIso.hom (op M)).symm ⟨(z.val,b),z.property⟩, by
    have h := SheafFamily.sectionsEquiv_snd actual.hom negationIso.hom (op M)
      ((SheafFamily.sectionsEquiv actual.hom negationIso.hom (op M)).symm ⟨(z.val,b),z.property⟩)
    exact h.symm.trans (congrArg (fun p => p.val.2)
      ((SheafFamily.sectionsEquiv actual.hom negationIso.hom (op M)).apply_symm_apply _))⟩
  left_inv z := by
    apply Subtype.ext
    apply (SheafFamily.sectionsEquiv actual.hom negationIso.hom (op M)).injective
    rw [Equiv.apply_symm_apply]
    apply Subtype.ext
    apply Prod.ext
    · rfl
    · exact ((SheafFamily.sectionsEquiv_snd actual.hom negationIso.hom (op M) z.val).trans z.property).symm
  right_inv z := by
    apply Subtype.ext
    exact congrArg (fun p => p.val.1)
      ((SheafFamily.sectionsEquiv actual.hom negationIso.hom (op M)).apply_symm_apply _)

/-- Canonical base change carries the Boolean output fiber to true. -/
def trueFiber (M : Diamond) :
    {x : trueActual.left.obj.obj (op M) // trueActual.hom.hom.app (op M) x = true} ≃ Bool :=
  (fiberIso substitution M true).symm.trans ((pullbackFiber M true).trans (falseFiberEquiv M))

/-- Its false fiber is the empty-index singleton, without an argument there. -/
def falseFiber (M : Diamond) :
    {x : trueActual.left.obj.obj (op M) // trueActual.hom.hom.app (op M) x = false} ≃ Unit :=
  (fiberIso substitution M false).symm.trans ((pullbackFiber M false).trans (trueFiberEquiv M))

end Examples.FalsePointBaseChange
