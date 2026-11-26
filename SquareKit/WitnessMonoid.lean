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
  mulCongr : ∀ {a b c d}, R.Rel a b → R.Rel c d → R.Rel (m.mul a c) (m.mul b d)
  unitMul : ∀ a, R.Rel (m.mul m.unit a) a
  mulUnit : ∀ a, R.Rel (m.mul a m.unit) a
  assoc : ∀ a b c, R.Rel (m.mul (m.mul a b) c) (m.mul a (m.mul b c))

def equiv (m : SetoidMonoid.Ops M) (R : Relation M) : WitnessEquivalence (SetoidMonoid.ops m) :=
  ⟨fun f g => R.Rel f g,R.refl,R.symm,R.trans⟩
def congr {m : SetoidMonoid.Ops M} {R : Relation M} (L : Laws m R) : (equiv m R).Congr :=
  ⟨L.mulCongr⟩
def laws {m : SetoidMonoid.Ops M} {R : Relation M} (L : Laws m R) : (equiv m R).Laws :=
  ⟨L.unitMul,L.mulUnit,L.assoc⟩
def Relation.erase (R : Relation M) : Setoid M :=
  ⟨fun x y => Nonempty (R.Rel x y),⟨fun x => ⟨R.refl x⟩,
    fun ⟨h⟩ => ⟨R.symm h⟩, fun ⟨h⟩ ⟨k⟩ => ⟨R.trans h k⟩⟩⟩
theorem Laws.erase {m : SetoidMonoid.Ops M} {R : Relation M} (L : Laws m R) :
    SetoidMonoid.Laws m R.erase :=
  ⟨fun ⟨h⟩ ⟨k⟩ => ⟨L.mulCongr h k⟩,fun x => ⟨L.unitMul x⟩,
    fun x => ⟨L.mulUnit x⟩,fun x y z => ⟨L.assoc x y z⟩⟩
theorem erase_equiv (m : SetoidMonoid.Ops M) (R : Relation M) :
    (equiv m R).erase = SetoidMonoid.equiv m R.erase := rfl
end SquareKit.WitnessMonoid
