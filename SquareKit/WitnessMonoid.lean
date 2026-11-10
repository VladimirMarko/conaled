import SquareKit.SetoidMonoid
import SquareKit.WitnessEquivalence

namespace SquareKit.WitnessMonoid
universe u w
variable {M : Type u}
/-- The raw monoid relation retains its chosen witnesses independently of arrows. -/
structure Relation (M : Type u) where
  Rel : M → M → Type w
  refl : ∀ x, Rel x x
  symm : ∀ {x y}, Rel x y → Rel y x
  trans : ∀ {x y z}, Rel x y → Rel y z → Rel x z

structure Laws (m : SetoidMonoid.Ops M) (R : Relation M) where
  mul_congr : ∀ {a b c d}, R.Rel a b → R.Rel c d → R.Rel (m.mul a c) (m.mul b d)
  unit_mul : ∀ a, R.Rel (m.mul m.unit a) a
  mul_unit : ∀ a, R.Rel (m.mul a m.unit) a
  assoc : ∀ a b c, R.Rel (m.mul (m.mul a b) c) (m.mul a (m.mul b c))

def equiv (m : SetoidMonoid.Ops M) (R : Relation M) : WitnessEquivalence (SetoidMonoid.ops m) :=
  ⟨fun f g => R.Rel f g,R.refl,R.symm,R.trans⟩
def congr {m : SetoidMonoid.Ops M} {R : Relation M} (L : Laws m R) : (equiv m R).Congr :=
  ⟨L.mul_congr⟩
def laws {m : SetoidMonoid.Ops M} {R : Relation M} (L : Laws m R) : (equiv m R).Laws :=
  ⟨L.unit_mul,L.mul_unit,L.assoc⟩
def Relation.erase (R : Relation M) : Setoid M :=
  ⟨fun x y => Nonempty (R.Rel x y),⟨fun x => ⟨R.refl x⟩,
    fun ⟨h⟩ => ⟨R.symm h⟩, fun ⟨h⟩ ⟨k⟩ => ⟨R.trans h k⟩⟩⟩
theorem Laws.erase {m : SetoidMonoid.Ops M} {R : Relation M} (L : Laws m R) :
    SetoidMonoid.Laws m R.erase :=
  ⟨fun ⟨h⟩ ⟨k⟩ => ⟨L.mul_congr h k⟩,fun x => ⟨L.unit_mul x⟩,
    fun x => ⟨L.mul_unit x⟩,fun x y z => ⟨L.assoc x y z⟩⟩
theorem erase_equiv (m : SetoidMonoid.Ops M) (R : Relation M) :
    (equiv m R).erase = SetoidMonoid.equiv m R.erase := rfl
end SquareKit.WitnessMonoid
