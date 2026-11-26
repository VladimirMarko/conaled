import SquareKit.FunctionInitial
import SquareKit.CodeCategory
import Examples.ClosedTransport

/-! Empty-domain code and a different presentation of the initial object. -/
namespace Examples.InitialTransport
open SquareKit CategoricalCompiler
open Examples.ClosedTransport (Box)

/-- The base type is empty in this interpretation; other types remain inhabited. -/
inductive Prim : Ty → Ty → Type where
  | eliminate : Prim .base a

def meaning : {a b : Ty} → Prim a b → Val Empty a → Val Empty b
  | _, _, .eliminate, x => Empty.elim x

def codeInitial : InitialOps (CodeCategory.ops Prim) :=
  ⟨.base, .primitive .eliminate⟩

def comparison : InitialMap (CodeCategory.evaluation meaning) codeInitial FunctionCategory.initial :=
  ⟨Empty.elim, PEmpty.elim⟩

theorem inverse : ComparisonLaws (equality _) comparison :=
  ⟨funext fun x => PEmpty.elim x, funext fun x => Empty.elim x⟩

theorem preserves : InitialMapLaws (equality _) comparison :=
  ⟨funext fun x => Empty.elim x⟩

theorem codeInitial_laws : InitialLaws (CodeCategory.equiv meaning) codeInitial :=
  InitialMap.transport_laws (CodeCategory.evaluation_reflects meaning) (equality_congr _)
    FunctionCategory.laws inverse.inv_hom preserves FunctionCategory.initialLaws

/-- Initial uniqueness holds for every raw arrow out of the interpreted empty base. -/
example {a : Ty} (f : Code Prim .base a) :
    CodeCategory.equiv meaning |>.Rel f (.primitive .eliminate) := codeInitial_laws.unique f

/-- These witnesses are semantic laws, not constructor equations. -/
theorem raw_initial_not_unique : ¬ InitialLaws (equality _) codeInitial := by
  intro h
  have bad := h.unique (Code.ident (Prim := Prim) (a := .base))
  cases bad

/-- A second interpretation changes the initial object's carrier. -/
def wrappedInitial : InitialOps FunctionCategory.ops where
  zero := Box PEmpty
  initial x := PEmpty.elim x.value

def wrap : InitialMap (RawMap.id FunctionCategory.ops) FunctionCategory.initial wrappedInitial :=
  ⟨Box.mk, Box.value⟩

theorem wrap_inverse : ComparisonLaws (equality _) wrap := ⟨rfl, rfl⟩
theorem wrap_preserves : InitialMapLaws (equality _) wrap :=
  ⟨funext fun x => PEmpty.elim x⟩

theorem wrapped_laws : InitialLaws (equality _) wrappedInitial :=
  ⟨fun _ => funext fun x => PEmpty.elim x.value⟩

def composed := InitialMap.comp comparison wrap

theorem composed_preserves : InitialMapLaws (equality _) composed :=
  InitialMap.comp_laws (RawMap.id_laws _) (equality_congr _) FunctionCategory.laws
    preserves wrap_preserves

theorem composed_inverse : ComparisonLaws (equality _) composed :=
  InitialMap.comp_inverse (RawMap.id_laws _) (equality_congr _) FunctionCategory.laws
    inverse wrap_inverse

/-- Initial laws are recovered after two interpretations, without product assumptions. -/
example : InitialLaws (CodeCategory.equiv meaning) codeInitial :=
  InitialMap.transport_laws (CodeCategory.evaluation_reflects meaning) (equality_congr _)
    FunctionCategory.laws composed_inverse.inv_hom composed_preserves wrapped_laws

/-- Quotienting retains precisely the selected semantic relation. -/
example {a : Ty} (f : Code Prim .base a) :
    HomQuotient.classOf (E := CodeCategory.equiv meaning) f =
      HomQuotient.classOf (E := CodeCategory.equiv meaning) (Code.primitive (Prim.eliminate (a := a))) :=
  (HomQuotient.mk_eq_iff _ _).mpr (codeInitial_laws.unique f)

noncomputable def quotientInitial :
    letI := HomQuotient.category (CodeCategory.congruence meaning) (CodeCategory.laws meaning)
    CategoryTheory.Limits.IsInitial
      (HomQuotient.initial (CodeCategory.congruence meaning) (CodeCategory.laws meaning)
        codeInitial).zero := by
  letI := HomQuotient.category (CodeCategory.congruence meaning) (CodeCategory.laws meaning)
  exact InitialOps.isInitial _ (HomQuotient.initialLaws _ _ _ codeInitial_laws)

/-- The lawful adapter recovers the chosen initial arrow into a nonempty target. -/
example :
    letI := HomQuotient.category (CodeCategory.congruence meaning) (CodeCategory.laws meaning)
    (InitialOps.ofIsInitial quotientInitial).initial
    (a := (⟨.unit⟩ : HomQuotient (CodeCategory.ops Prim) (CodeCategory.equiv meaning))) =
      HomQuotient.classOf (E := CodeCategory.equiv meaning)
        (Code.primitive (Prim.eliminate (a := .unit))) := rfl

end Examples.InitialTransport
