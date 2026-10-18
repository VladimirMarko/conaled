import SquareKit.SmoothGeometricScalar
import SquareKit.SheafFunction

/-! Experimental presentation-based scalar geometry for any topology with proved
scalar sheafness. No coefficient extraction or KL law is assumed.
The subtype sheaf condition follows from scalar gluing and separatedness. -/
noncomputable section
namespace SquareKit.PresentationGeometry
open CategoryTheory Opposite SmoothAlgebra SmoothPresentationSite SheafRelation SheafFunction

abbrev ringMap {A B : Code} (f : A ⟶ B) : Carrier A →+* Carrier B :=
  (smoothMap f).toAlgHom.toRingHom
abbrev infinitesimalData : Siteᵒᵖ ⥤ Type where
  obj A := {d : Carrier A.unop.unop // d*d=0}
  map f := ↾fun d => ⟨ringMap f.unop.unop d, by rw [← map_mul, d.property, map_zero]⟩

variable (J : GrothendieckTopology Site) [Fact (Presieve.IsSheaf J scalarData)]

/-- Only scalar sheafness is required for the infinitesimal and KL construction. -/
abbrev scalar : Sheaf J Type :=
  ⟨scalarData,(isSheaf_iff_isSheaf_of_type _ _).mpr (Fact.out : Presieve.IsSheaf J scalarData)⟩

theorem infinitesimal_isSheaf : Presieve.IsSheaf J infinitesimalData := by
  intro U R hR x hx
  let y : Presieve.FamilyOfElements scalarData R.arrows := fun {_} f hf => (x f hf).val
  have hy : y.Compatible := by
    intro V W Z f g i j hi hj he
    exact congrArg Subtype.val (hx f g hi hj he)
  obtain ⟨a, ha, hua⟩ := (Fact.out : Presieve.IsSheaf J scalarData) R hR y hy
  have hs : a*a=0 := by
    apply ((Fact.out : Presieve.IsSheaf J scalarData) R hR).isSeparatedFor.ext
    intro V f hf
    change ringMap f.unop (a*a) = ringMap f.unop 0
    rw [map_mul, map_zero]
    have he := ha f hf
    change ringMap f.unop a = (x f hf).val at he
    rw [he]
    exact (x f hf).property
  refine ⟨⟨a,hs⟩, ?_, ?_⟩
  · intro V f hf; exact Subtype.ext (ha f hf)
  · intro b hb
    exact Subtype.ext (hua b.val (fun {_} f hf => congrArg Subtype.val (hb f hf)))

abbrev infinitesimal : Sheaf J Type :=
  ⟨infinitesimalData, (isSheaf_iff_isSheaf_of_type _ _).mpr (infinitesimal_isSheaf J)⟩
variable {J}

def inclusion : (infinitesimal J) ⟶ (scalar J) := ⟨{app _ := ↾Subtype.val}⟩

def add : product (scalar J) (scalar J) ⟶ (scalar J) :=
  ⟨{app _ := ↾fun p => p.1+p.2
    naturality _ _ f := by ext p; exact ((smoothMap f.unop.unop).map_add p.1 p.2).symm}⟩
def mul : product (scalar J) (scalar J) ⟶ (scalar J) :=
  ⟨{app _ := ↾fun p => p.1*p.2
    naturality _ _ f := by ext p; exact ((smoothMap f.unop.unop).map_mul p.1 p.2).symm}⟩
def affineBody : product (infinitesimal J) (product (scalar J) (scalar J)) ⟶ (scalar J) :=
  ⟨{app _ := ↾fun p => p.2.1+p.2.2*p.1.val
    naturality _ _ f := by
      ext p
      change _ = ringMap f.unop.unop (p.2.1+p.2.2*p.1.val)
      change _ = (smoothMap f.unop.unop) (p.2.1+p.2.2*p.1.val)
      rw [Hom.map_add,Hom.map_mul]; rfl}⟩
def affine : product (scalar J) (scalar J) ⟶ exponential (infinitesimal J) (scalar J) := curry affineBody

theorem affine_evaluation (A : Code) (d : Carrier A) (hd : d*d=0) (a b : Carrier A) :
    (evaluation (infinitesimal J) (scalar J)).hom.app (op (op A))
      (⟨d,hd⟩, affine.hom.app (op (op A)) (a,b)) = a+b*d :=
  evaluation_curry_apply affineBody (op (op A)) ⟨d,hd⟩ (a,b)

theorem inclusion_injective (A : Siteᵒᵖ) : Function.Injective ((inclusion (J := J)).hom.app A) :=
  Subtype.val_injective

theorem affine_parameters {X : Sheaf J Type} (p : X ⟶ product (scalar J) (scalar J)) :
    curry (parameterMap (infinitesimal J) p ≫ affineBody) = p ≫ affine := curry_parameter affineBody p


end SquareKit.PresentationGeometry
