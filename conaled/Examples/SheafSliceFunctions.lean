import SquareKit.SheafSliceFunction
import Examples.SheafSlices

/-! Experimental function-space consumers in the ordinary slice over D.
False-point arguments, parameter substitution and nonconstant E arguments use
actual slice products and the public element-site operation comparisons. -/
noncomputable section
namespace Examples.SheafSliceFunctions
open CategoryTheory Limits Opposite SquareKit
open Examples.SheafImage Examples.SheafImage.Diamond Examples.SheafBaseChange
open Examples.SheafFamilies

abbrev argument : Over D := Over.mk falsePoint
abbrev result : Over D := Over.mk (SheafRelation.snd D D)
abbrev varyingArgument : Over D := Over.mk SheafSlices.varyingDisplay
abbrev parameter : Over D := Over.mk (𝟙 D)
abbrev F := SheafSlice.forward D

/-- A nontrivial result fiber has both Boolean values over either base value. -/
def resultValue (M : Diamond) (b c : Bool) :
    (F.obj result).obj.obj (op (ElementSite.point D.obj M c)) :=
  (SheafSlice.fiberEquiv D (SheafRelation.snd D D) M c).symm ⟨(b,c),rfl⟩

def argumentValue (M : Diamond) :
    (F.obj argument).obj.obj (op (ElementSite.point D.obj M false)) :=
  (SheafSlice.fiberEquiv D falsePoint M false).symm ⟨(),rfl⟩

theorem argument_empty_true (M : Diamond) :
    IsEmpty ((F.obj argument).obj.obj (op (ElementSite.point D.obj M true))) :=
  SheafSlices.true_fiber_empty M

/-- The function returns the parameter's value whenever its false argument exists. -/
def returnParameter : result ⟶ SheafSliceFunction.exponential D argument result :=
  SheafSliceFunction.curry D (prod.snd : argument ⨯ result ⟶ result)

private theorem transported_snd :
    (SheafSliceFunction.productComparison D argument result).inv ≫
      F.map (prod.snd : argument ⨯ result ⟶ result) = SheafRelation.snd _ _ := by
  rw [← SheafSliceFunction.productComparison_snd D argument result]
  simp only [← Category.assoc, Iso.inv_hom_id, Category.id_comp]

theorem evaluate_returnParameter (M : Diamond) (b : Bool) :
    (SheafFunction.evaluation (F.obj argument) (F.obj result)).hom.app
      (op (ElementSite.point D.obj M false))
      (argumentValue M, (SheafSliceFunction.exponentialIso D argument result).hom.hom.app _
        ((F.map returnParameter).hom.app _ (resultValue M b false))) = resultValue M b false := by
  have h := SheafSliceFunction.evaluation_curry_apply D
    (prod.snd : argument ⨯ result ⟶ result)
    (op (ElementSite.point D.obj M false)) (argumentValue M) (resultValue M b false)
  rw [transported_snd] at h
  exact h

/-- Negation of the value leaves the base coordinate unchanged. -/
def negateParameter : result ⟶ result := Over.homMk
  (SheafRelation.lift (SheafRelation.fst D D ≫ Examples.SheafFunctions.negation) (SheafRelation.snd D D)) rfl

theorem substitute_parameter :
    SheafSliceFunction.curry D
      (prod.map (𝟙 argument) negateParameter ≫ (prod.snd : argument ⨯ result ⟶ result)) =
      negateParameter ≫ returnParameter :=
  SheafSliceFunction.curry_parameter D _ _

theorem substituted_value (M : Diamond) (b : Bool) :
    (F.map negateParameter).hom.app (op (ElementSite.point D.obj M false))
      (resultValue M b false) = resultValue M (!b) false := rfl

/-- Parameter substitution is observed by the existing element-site evaluation. -/
theorem evaluate_substituted (M : Diamond) (b : Bool) :
    (SheafFunction.evaluation (F.obj argument) (F.obj result)).hom.app
      (op (ElementSite.point D.obj M false))
      (argumentValue M, (SheafSliceFunction.exponentialIso D argument result).hom.hom.app _
        ((F.map (SheafSliceFunction.curry D
          (prod.map (𝟙 argument) negateParameter ≫ (prod.snd : argument ⨯ result ⟶ result)))).hom.app _
            (resultValue M b false))) = resultValue M (!b) false := by
  rw [substitute_parameter]
  change (SheafFunction.evaluation (F.obj argument) (F.obj result)).hom.app _
    (argumentValue M, (SheafSliceFunction.exponentialIso D argument result).hom.hom.app _
      ((F.map returnParameter).hom.app _ ((F.map negateParameter).hom.app _ (resultValue M b false)))) = _
  rw [substituted_value]
  exact evaluate_returnParameter M (!b)

/-- The slice product exposes the existing dependent-family pullback projection. -/
theorem family_product_projection :
    (SheafSliceFunction.familyProduct D argument result).hom ≫
      Family.reindex falsePoint (SheafRelation.snd D D) = (prod.snd : argument ⨯ result ⟶ result).left :=
  SheafSliceFunction.familyProduct_snd D argument result

/-- The nonconstant argument retains E's two different restrictions. -/
theorem varying_wu (b : Bool) (a : (F.obj varyingArgument).obj.obj (op (ElementSite.point D.obj U b))) :
    SheafSlices.varyingEquiv W b
      ((F.obj varyingArgument).obj.map (ElementSite.arrow D.obj Arrow.wu b).op a) = false :=
  SheafSlices.varying_wu b a

theorem varying_wv (b : Bool) (a : (F.obj varyingArgument).obj.obj (op (ElementSite.point D.obj V b))) :
    SheafSlices.varyingEquiv W b
      ((F.obj varyingArgument).obj.map (ElementSite.arrow D.obj Arrow.wv b).op a) = true :=
  SheafSlices.varying_wv b a

/-- Two constant values define maps of dependent families, preserving the base. -/
def constantMap (b : Bool) : varyingArgument ⟶ result := Over.homMk
  (SheafRelation.lift
    (SheafRelation.fst E D ≫ Examples.SheafFunctions.constant b)
    (SheafRelation.snd E D)) rfl

def constantName (b : Bool) : parameter ⟶ SheafSliceFunction.exponential D varyingArgument result :=
  SheafSliceFunction.curry D ((prod.fst : varyingArgument ⨯ parameter ⟶ varyingArgument) ≫ constantMap b)

def parameterValue (M : Diamond) (c : Bool) :
    (F.obj parameter).obj.obj (op (ElementSite.point D.obj M c)) := ⟨c,rfl⟩

/-- A name transported through the actual exponential comparison. -/
def nameInElements (b : Bool) : F.obj parameter ⟶
    SheafFunction.exponential (F.obj varyingArgument) (F.obj result) :=
  F.map (constantName b) ≫ (SheafSliceFunction.exponentialIso D varyingArgument result).hom

/-- Evaluate the natural name at the specified element of the Bool base. -/
def namedSection (M : Diamond) (b c : Bool) :
    (SheafFunction.exponential (F.obj varyingArgument) (F.obj result)).obj.obj
      (op (ElementSite.point D.obj M c)) :=
  (nameInElements b).hom.app _ (parameterValue M c)

private theorem transported_constant (b : Bool) :
    (SheafSliceFunction.productComparison D varyingArgument parameter).inv ≫
      F.map ((prod.fst : varyingArgument ⨯ parameter ⟶ varyingArgument) ≫ constantMap b) =
        SheafRelation.fst _ _ ≫ F.map (constantMap b) := by
  rw [F.map_comp, ← SheafSliceFunction.productComparison_fst D varyingArgument parameter]
  simp only [← Category.assoc, Iso.inv_hom_id, Category.id_comp]

theorem evaluate_constant (M : Diamond) (b c : Bool)
    (a : (F.obj varyingArgument).obj.obj (op (ElementSite.point D.obj M c))) :
    (SheafFunction.evaluation (F.obj varyingArgument) (F.obj result)).hom.app _
      (a, namedSection M b c) = resultValue M b c := by
  have h := SheafSliceFunction.evaluation_curry_apply D
    ((prod.fst : varyingArgument ⨯ parameter ⟶ varyingArgument) ≫ constantMap b)
    (op (ElementSite.point D.obj M c)) a (parameterValue M c)
  rw [transported_constant] at h
  refine h.trans ?_
  apply Subtype.ext
  exact Prod.ext rfl a.property

/-- Names restrict as natural sections of the element-site exponential. -/
theorem named_restrict (b c : Bool) :
    (SheafFunction.exponential (F.obj varyingArgument) (F.obj result)).obj.map
      (ElementSite.arrow D.obj Arrow.wx c).op (namedSection X b c) = namedSection W b c := by
  have hn := NatTrans.naturality_apply (nameInElements b).hom
    (ElementSite.arrow D.obj Arrow.wx c).op (parameterValue X c)
  have hp : (F.obj parameter).obj.map (ElementSite.arrow D.obj Arrow.wx c).op
      (parameterValue X c) = parameterValue W c := rfl
  rw [hp] at hn
  exact hn.symm

/-- Distinct natural operations survive at X, although its argument fiber is empty. -/
theorem names_distinct (c : Bool) : namedSection X false c ≠ namedSection X true c := by
  intro h
  have hr := congrArg
    ((SheafFunction.exponential (F.obj varyingArgument) (F.obj result)).obj.map
      (ElementSite.arrow D.obj Arrow.wx c).op) h
  rw [named_restrict, named_restrict] at hr
  let a := (SheafSlices.varyingEquiv W c).symm false
  have he := congrArg (fun z => (SheafFunction.evaluation (F.obj varyingArgument) (F.obj result)).hom.app
    (op (ElementSite.point D.obj W c)) (a,z)) hr
  have hv := (evaluate_constant W false c a).symm.trans (he.trans (evaluate_constant W true c a))
  exact Bool.noConfusion (congrArg (fun z => z.val.1) hv)

/-- Actual element-site exponential sections cannot be naive fiberwise functions. -/
theorem no_pointwise_equivalence (c : Bool) :
    ¬ Nonempty ((SheafFunction.exponential (F.obj varyingArgument) (F.obj result)).obj.obj
      (op (ElementSite.point D.obj X c)) ≃
      ((F.obj varyingArgument).obj.obj (op (ElementSite.point D.obj X c)) →
        (F.obj result).obj.obj (op (ElementSite.point D.obj X c)))) := by
  rintro ⟨e⟩
  apply names_distinct c
  apply e.injective
  funext a
  exact (SheafSlices.varying_empty_X c).false a |>.elim

/-- The same obstruction concerns the constructed slice exponential, through
its public natural comparison, rather than a separately defined function space. -/
theorem slice_no_pointwise_equivalence (c : Bool) :
    ¬ Nonempty ((F.obj (SheafSliceFunction.exponential D varyingArgument result)).obj.obj
      (op (ElementSite.point D.obj X c)) ≃
      ((F.obj varyingArgument).obj.obj (op (ElementSite.point D.obj X c)) →
        (F.obj result).obj.obj (op (ElementSite.point D.obj X c)))) := by
  rintro ⟨e⟩
  let i := (SheafSliceFunction.exponentialIso D varyingArgument result)
  let k := (sheafToPresheaf _ _).mapIso i
  exact no_pointwise_equivalence c ⟨(k.app (op (ElementSite.point D.obj X c))).toEquiv.symm.trans e⟩

end Examples.SheafSliceFunctions
