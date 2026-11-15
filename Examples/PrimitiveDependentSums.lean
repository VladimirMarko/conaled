import SquareKit.Internal.DependentJudgments.PrimitiveSigma.Comparison
import SquareKit.Internal.DependentJudgments.PrimitiveSigma.Separation
import SquareKit.Internal.DependentJudgments.Sigma.Native

/-! Primitive sums retain genuine dependent motives in the native provider,
while the complete constant-family provider separates the stronger eta law. -/
namespace Examples.PrimitiveDependentSums
open SquareKit.Internal.DependentJudgments
open SquareKit.Internal.PathTransport.Typed

abbrev strong := Sigma.Native.capability Unit (fun _ => Unit)
abbrev weak := PrimitiveSigma.ofStrong strong

/-- Both the second family and motive depend on the first component. -/
example (n : Nat) (i : Fin (n + 1)) :
    (weak.split (fun _ : Unit => Nat) (fun p => Fin (p.2 + 1))
      (fun p => Fin (p.2.1 + 1)) ⟨Sigma.Native.boundedBranch⟩).down ⟨(), n, i⟩ = i :=
  Sigma.Native.bounded_split n i

/-- Recovery includes the selected unpacking substitution, not just its type. -/
example (n : Nat) (i : Fin (n + 1)) :
    (weak.unpack (fun _ : Unit => Nat) (fun p => Fin (p.2 + 1))).down ⟨(), n, i⟩ =
      ⟨⟨(), n⟩, i⟩ := by
  exact congrArg (fun f => f.down ⟨(), n, i⟩)
    (PrimitiveSigma.ofStrong_unpack strong (fun _ : Unit => Nat) (fun p => Fin (p.2 + 1)))

/-- Composition retains primitive eliminator preservation as an actual map. -/
def twice : PrimitiveSigma.Map weak weak :=
  PrimitiveSigma.Map.compose (PrimitiveSigma.Map.identityMap weak) (PrimitiveSigma.Map.identityMap weak)

example : twice.toStructuralMap = StructuralMap.identityMap
    (NativeType.structuralModel Unit (fun _ => Unit)) := rfl

namespace NonconstantSubstitution
abbrev M := NativeType.structuralModel Nat (fun n => Fin (n + 1))
abbrev S := PrimitiveSigma.Stable.ofStrong (Sigma.Native.stable Nat (fun n => Fin (n + 1)))
def first : M.Family Nat := fun n => Fin (n + 1)
def second : M.Family (M.extend Nat first) := fun p => Fin (p.2.val + 1)
def shift : M.Substitution Nat Nat := ⟨fun n => n + 1⟩
def double : M.Substitution Nat Nat := ⟨fun n => 2 * n⟩

/-- Sequential substitution retains the comparison of dependent sum contexts. -/
example :
    M.compSub (S.toStableFormation.sumMap first second shift)
      (S.toStableFormation.sumMap (M.subTy first shift)
        (M.subTy second (M.lift first shift)) double) =
    M.compSub (S.toStableFormation.sumMap first second (M.compSub shift double))
      (M.familyComparison (S.toStableFormation.sigma_comp first second shift double)) :=
  S.toStableFormation.sumMap_comp first second shift double

example : (M.compSub shift double).down 3 = 7 := rfl
example : (M.compSub double shift).down 3 = 8 := rfl
end NonconstantSubstitution

namespace Separator
abbrev S := PrimitiveSigma.ConstantFamilies.stable PUnit
abbrev M := PrimitiveSigma.ConstantFamilies.model PUnit

example : S.toCapability.repack (Γ := PUnit) PUnit PUnit ≠
    M.idSub (M.extend PUnit (S.sigma (Γ := PUnit) PUnit PUnit)) :=
  PrimitiveSigma.ConstantFamilies.stable_repack_ne_identity PUnit

/-- Both projection components are retained even at the extra flag-true point. -/
example : (S.toCapability.unpack (Γ := Nat) Nat Bool).down (7, ((4, true), true)) =
    ((7, 4), true) := rfl

/-- Propositional eta is a term of modeled identity despite failed host eta. -/
example : M.Section (M.extend PUnit (S.sigma (Γ := PUnit) PUnit PUnit))
    (S.toCapability.etaMotive (Γ := PUnit) PUnit PUnit) :=
  S.toCapability.eta PUnit PUnit

example : SquareKit.GuardedTheory.Derivation PrimitiveSigma.Reindexing.theory
    (List.ofFn PrimitiveSigma.splitEtaRule.premise) PrimitiveSigma.splitEtaRule.conclusion → False :=
  PrimitiveSigma.Separation.stable_splitEta_not_derivable
end Separator
end Examples.PrimitiveDependentSums
