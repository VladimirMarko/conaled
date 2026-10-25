import SquareKit.SubfunctorLattice
import SquareKit.Internal.ComplementaryModel
import SquareKit.Internal.PresheafSetting

/-! Comparison of the existing finite and presheaf models with the categorical
complementary-model interface. Both predicates are preserved by morphisms. -/
set_option autoImplicit false
namespace SquareKit.Internal
open CategoryTheory
universe u v
namespace FiniteSetting
variable {X : Type u} {T : Presentation X}

/-- The three existing source axioms give a complementary partition in the predicate lattice. -/
def Model.asComplementary (M : Model T) : ComplementaryModel.Model T.parameter where
  p := M.P
  q := M.Q
  complementary := IsCompl.of_eq
    (by funext x; apply propext; exact ⟨(satisfies_iff T M.P M.Q).mp M.satisfies |>.2.1 x, False.elim⟩)
    (by funext x; apply propext; exact ⟨fun _ => trivial, fun _ => (satisfies_iff T M.P M.Q).mp M.satisfies |>.1 x⟩)
  bounded := (satisfies_iff T M.P M.Q).mp M.satisfies |>.2.2

/-- Recover precisely the original three source sequents. -/
def Model.ofComplementary (M : ComplementaryModel.Model T.parameter) : Model T where
  P := M.p
  Q := M.q
  satisfies := (satisfies_iff T M.p M.q).mpr ⟨
    fun x => by have h := congrFun M.complementary.sup_eq_top x; exact h.mpr trivial,
    fun x h => by have e := congrFun M.complementary.inf_eq_bot x; exact e.mp h,
    M.bounded⟩

/-- This comparison preserves the actual predicates, not only model cardinalities. -/
def modelComplementaryEquiv (T : Presentation X) : Model T ≃ ComplementaryModel.Model T.parameter where
  toFun := Model.asComplementary
  invFun := Model.ofComplementary
  left_inv _ := Model.ext rfl rfl
  right_inv _ := ComplementaryModel.Model.ext rfl rfl
end FiniteSetting

namespace PresheafSetting
variable {J : Type v} [SmallCategory J] {X : Jᵒᵖ ⥤ Type} {T : Presentation X}

/-- Complementarity holds in the subfunctor lattice, not just at selected stages. -/
def Model.asComplementary (M : Model T) : ComplementaryModel.Model T where
  p := M.P
  q := M.Q
  complementary := IsCompl.of_eq
    (by ext j x; exact ⟨(FiniteSetting.satisfies_iff _ _ _).mp (M.satisfies j) |>.2.1 x, False.elim⟩)
    (by ext j x; exact ⟨fun _ => trivial, fun _ => (FiniteSetting.satisfies_iff _ _ _).mp (M.satisfies j) |>.1 x⟩)
  bounded j x h := (FiniteSetting.satisfies_iff _ _ _).mp (M.satisfies j) |>.2.2 x h

/-- Recover stagewise satisfaction from the subfunctor lattice laws. -/
def Model.ofComplementary (M : ComplementaryModel.Model T) : Model T where
  P := M.p
  Q := M.q
  satisfies j := (FiniteSetting.satisfies_iff _ _ _).mpr ⟨
    fun x => by
      have h := congrArg (fun S : Subfunctor X => S.obj j x) M.complementary.sup_eq_top
      exact h.mpr trivial,
    fun x h => by
      have e := congrArg (fun S : Subfunctor X => S.obj j x) M.complementary.inf_eq_bot
      exact e.mp h,
    fun x h => M.bounded j h⟩

/-- The existing presheaf models are exactly these complementary subfunctors. -/
def modelComplementaryEquiv (T : Presentation X) : Model T ≃ ComplementaryModel.Model T where
  toFun := Model.asComplementary
  invFun := Model.ofComplementary
  left_inv _ := Model.ext (fun _ => FiniteSetting.Model.ext rfl rfl)
  right_inv _ := ComplementaryModel.Model.ext rfl rfl
end PresheafSetting
end SquareKit.Internal

namespace SquareKit.Internal.FiniteSetting
open CategoryTheory
universe u
variable {X : Type u} {T : Presentation X}

/-- Morphisms of the original model presentation preserve both named predicates. -/
instance : Category (Model T) where
  Hom M N := M.asComplementary ⟶ N.asComplementary
  id M := 𝟙 M.asComplementary
  comp α β := α ≫ β

instance (M N : Model T) : Subsingleton (M ⟶ N) :=
  inferInstanceAs (Subsingleton (M.asComplementary ⟶ N.asComplementary))

/-- The original and complementary presentations agree on objects and predicate-preserving maps. -/
def modelComplementaryEquivalence (T : Presentation X) : Model T ≌ ComplementaryModel.Model T.parameter where
  functor := { obj := Model.asComplementary, map := fun α => α }
  inverse := {
    obj := Model.ofComplementary
    map α := ⟨⟨α.down.p_le, α.down.q_le⟩⟩ }
  unitIso := NatIso.ofComponents (fun M => eqToIso ((modelComplementaryEquiv T).left_inv M).symm)
    (by intros; apply Subsingleton.elim)
  counitIso := NatIso.ofComponents (fun M => eqToIso ((modelComplementaryEquiv T).right_inv M))
    (by intros; apply Subsingleton.elim)
end SquareKit.Internal.FiniteSetting

namespace SquareKit.Internal.PresheafSetting
open CategoryTheory
universe v
variable {J : Type v} [SmallCategory J] {X : Jᵒᵖ ⥤ Type} {T : Presentation X}

/-- The original presheaf-model arrows preserve both predicate subfunctors. -/
instance : Category (Model T) where
  Hom M N := M.asComplementary ⟶ N.asComplementary
  id M := 𝟙 M.asComplementary
  comp α β := α ≫ β

instance (M N : Model T) : Subsingleton (M ⟶ N) :=
  inferInstanceAs (Subsingleton (M.asComplementary ⟶ N.asComplementary))

/-- The comparison preserves presheaf-model morphisms, not only the object set. -/
def modelComplementaryEquivalence (T : Presentation X) : Model T ≌ ComplementaryModel.Model T where
  functor := { obj := Model.asComplementary, map := fun α => α }
  inverse := {
    obj := Model.ofComplementary
    map α := ⟨⟨α.down.p_le, α.down.q_le⟩⟩ }
  unitIso := NatIso.ofComponents (fun M => eqToIso ((modelComplementaryEquiv T).left_inv M).symm)
    (by intros; apply Subsingleton.elim)
  counitIso := NatIso.ofComponents (fun M => eqToIso ((modelComplementaryEquiv T).right_inv M))
    (by intros; apply Subsingleton.elim)
end SquareKit.Internal.PresheafSetting
