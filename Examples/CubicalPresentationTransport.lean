import Examples.CubicalPathConversion
import Examples.CubicalConversion
import Mathlib.CategoryTheory.Category.Preorder
import Mathlib.Logic.Equiv.Bool

/-! Representation transport supplies functor laws, but does not choose
substitution-compatible representations. -/
namespace Examples.CubicalPresentationTransport
open CategoryTheory SquareKit.Cubical.Presheaf
universe u v

section Generic
variable {C : Type u} [Category C] (F : C ⥤ Type v)

theorem identity_presentation :
    F.copyObj F.obj (fun x => Iso.refl (F.obj x)) = F := by
  apply CategoryTheory.Functor.hext (fun _ => rfl)
  intro x y f
  apply heq_of_eq
  simp [Functor.copyObj]

/-- Sequential changes use the composite pointwise isomorphism. -/
theorem sequential_presentation (X Y : C → Type v)
    (e : ∀ x, F.obj x ≅ X x) (d : ∀ x, X x ≅ Y x) :
    (F.copyObj X e).copyObj Y d = F.copyObj Y (fun x => e x ≪≫ d x) := by
  apply CategoryTheory.Functor.hext (fun _ => rfl)
  intro x y f
  apply heq_of_eq
  simp [Functor.copyObj, Category.assoc]

end Generic

abbrev booleanDiagram : ℕ ⥤ Type := (Functor.const ℕ).obj Bool

def varyingRepresentation (n : ℕ) : Bool ≅ Bool :=
  (if n = 0 then Equiv.refl Bool else Equiv.boolNot).toIso

abbrev changed : ℕ ⥤ Type :=
  booleanDiagram.copyObj (fun _ => Bool) varyingRepresentation

theorem changed_arrow : changed.map (homOfLE (show 0 ≤ 1 by decide)) false = true := rfl

/-- Even identical object types do not make arbitrary pointwise choices compatible
with the identity substitution and an unchanged target presentation. -/
theorem incompatible_identity_substitution : (𝟭 ℕ) ⋙ changed ≠ booleanDiagram := by
  intro h
  have obs : HEq (((𝟭 ℕ) ⋙ changed).map (homOfLE (show 0 ≤ 1 by decide)))
      (booleanDiagram.map (homOfLE (show 0 ≤ 1 by decide))) := by rw [h]
  have vals := congrArg (fun f : Bool ⟶ Bool => f false) (eq_of_heq obs)
  contradiction

/-- Path conversion retains a second substitution as well as endpoint constraints. -/
theorem path_two_substitutions {Δ : Context} (τ : Δ ⟶ terminal) :
    ((Examples.CubicalPathConversion.contraction.reindex
      Examples.CubicalPathConversion.chooseLine).convert
      Examples.CubicalPathConversion.selected_path_formation).reindex τ =
    (Examples.CubicalPathConversion.contraction.reindex
      (τ ≫ Examples.CubicalPathConversion.chooseLine)).convert
      (congrArg (fun A : Family terminal => reindex A τ)
        Examples.CubicalPathConversion.selected_path_formation) :=
  Term.convert_reindex Examples.CubicalPathConversion.selected_path_formation
    (Examples.CubicalPathConversion.contraction.reindex
      Examples.CubicalPathConversion.chooseLine) τ

end Examples.CubicalPresentationTransport
