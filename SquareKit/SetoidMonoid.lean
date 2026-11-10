import SquareKit.CategoryMap
import Mathlib.CategoryTheory.SingleObj

/-! One-object categories retain raw monoid data and a separate setoid law package. -/
namespace SquareKit.SetoidMonoid
universe u
structure Ops (M : Type u) where
  unit : M
  mul : M → M → M

structure Laws {M : Type u} (m : Ops M) (s : Setoid M) : Prop where
  mul_congr : ∀ {a b c d}, s.r a b → s.r c d → s.r (m.mul a c) (m.mul b d)
  unit_mul : ∀ a, s.r (m.mul m.unit a) a
  mul_unit : ∀ a, s.r (m.mul a m.unit) a
  assoc : ∀ a b c, s.r (m.mul (m.mul a b) c) (m.mul a (m.mul b c))

variable {M : Type u}
def ops (m : Ops M) : CategoryOps Unit := ⟨fun _ _ => M, m.unit, m.mul⟩
def equiv (m : Ops M) (s : Setoid M) : HomEquiv (ops m) := ⟨fun _ _ => s⟩
theorem congr {m : Ops M} {s : Setoid M} (h : Laws m s) : CategoryCongr (ops m) (equiv m s) :=
  ⟨h.mul_congr⟩
theorem laws {m : Ops M} {s : Setoid M} (h : Laws m s) : CategoryLaws (ops m) (equiv m s) :=
  ⟨h.unit_mul,h.mul_unit,h.assoc⟩

def ofMonoid [Monoid M] : Ops M := ⟨1,(· * ·)⟩
theorem ofMonoid_laws [Monoid M] : Laws (ofMonoid (M := M)) (⟨Eq, ⟨Eq.refl, Eq.symm, Eq.trans⟩⟩) :=
  ⟨fun h k => congrArg₂ (· * ·) h k, one_mul, mul_one, mul_assoc⟩

def toSingleObj [Monoid M] : RawMap (ops (ofMonoid (M := M)))
    (ofCategory (CategoryTheory.SingleObj M)) := ⟨fun _ => CategoryTheory.SingleObj.star M, id⟩
def fromSingleObj [Monoid M] : RawMap (ofCategory (CategoryTheory.SingleObj M))
    (ops (ofMonoid (M := M))) := ⟨fun _ => (), id⟩
theorem toSingleObj_laws [Monoid M] : MapLaws (toSingleObj (M := M))
    (equiv ofMonoid (⟨Eq, ⟨Eq.refl, Eq.symm, Eq.trans⟩⟩)) (equality _) :=
  ⟨fun h => h, rfl, fun _ _ => rfl⟩
theorem fromSingleObj_laws [Monoid M] : MapLaws (fromSingleObj (M := M))
    (equality _) (equiv ofMonoid (⟨Eq, ⟨Eq.refl, Eq.symm, Eq.trans⟩⟩)) :=
  ⟨fun h => h, rfl, fun _ _ => rfl⟩
@[simp] theorem roundtrip [Monoid M] {a b : Unit} (f : (ops (ofMonoid (M := M))).Hom a b) :
    fromSingleObj.map (toSingleObj.map f) = f := rfl
end SquareKit.SetoidMonoid
