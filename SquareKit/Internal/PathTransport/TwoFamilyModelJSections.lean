import SquareKit.Internal.PathTransport.TwoFamilyModelJObjects
namespace SquareKit.Internal.PathTransport.HigherInterpretation
open CategoryTheory Bicategory
set_option backward.isDefEq.respectTransparency true
set_option backward.isDefEq.respectTransparency.types true
set_option backward.defeqAttrib.useBackward false
set_option backward.dsimp.instances true
set_option maxHeartbeats 1000000
universe u
namespace SourceContraction
variable {Γ Δ : Context.{u}} {i : StrictPseudofunctor Δ Γ}
def SectionConstructor (c : SourceContraction i) (E : Family Γ)
 (j : TwoFamily.Section (TwoFamily.reindex i E.data) → TwoFamily.Section E.data) : Prop :=
 j = TwoFamily.retractionJ i c.retraction c.homotopy E.data
def BranchConstructor (c : SourceContraction i) (E : Family Γ) (F : Family Δ)
 (e : F = E.reindex i) (j : TwoFamily.Section F.data → TwoFamily.Section E.data) : Prop :=
 j = fun d => TwoFamily.retractionJ i c.retraction c.homotopy E.data
  (TwoFamily.Section.cast (congrArg Family.data e) d)
theorem SectionConstructor.cast_input (c : SourceContraction i) (E : Family Γ)
 (j : TwoFamily.Section (TwoFamily.reindex i E.data) → TwoFamily.Section E.data)
 (h : c.SectionConstructor E j) (F : Family Δ) (e : F = E.reindex i) :
 c.BranchConstructor E F e (fun d => j (TwoFamily.Section.cast (congrArg Family.data e) d)) := by
 cases h
 rfl
end SourceContraction
variable (C D : Context.{u}) {Γ : Context.{u}} (A : Family Γ)
 (x : ULift.{u+1} (TwoFamily.Section A.data))
variable (E : Family (((A.reindex (Δ := A.total) (TwoFamily.projectionHigher A.data)).identity
 (x.down.reindex A.data (TwoFamily.projectionHigher A.data)) (TwoFamily.variableSection A.data)).total))
theorem j_sections : (rootContraction C D A x).val.SectionConstructor E
 (fun d => ((fullModel C D).j A x .nil E ⟨d⟩).down) := rfl
end SquareKit.Internal.PathTransport.HigherInterpretation

namespace SquareKit.Internal.PathTransport.TwoFamily
open CategoryTheory Bicategory
universe u v w uA vA wA uE vE wE
variable {Γ : Type u} [Bicategory.{w,v} Γ] [Strict Γ]
variable {A : Type uA} [Bicategory.{wA,vA} A] [Strict A]
variable (i : StrictPseudofunctor A Γ) (r : StrictPseudofunctor Γ A)
variable (η : Pseudofunctor.StrongTrans (r.comp i).toPseudofunctor (StrictPseudofunctor.id Γ).toPseudofunctor)
theorem retractionJ_cast {E F : Family.{u,v,w,uE,vE,wE} Γ} (e : E = F)
 (d : Section (reindex i E)) :
 Section.cast e (retractionJ i r η E d) =
  retractionJ i r η F (Section.cast (congrArg (reindex i) e) d) := by cases e; rfl
end SquareKit.Internal.PathTransport.TwoFamily
