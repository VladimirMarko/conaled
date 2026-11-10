import SquareKit.WitnessStructure
import SquareKit.SetoidCategory

/-! Setoids whose equivalence relations retain computational witnesses. -/
namespace SquareKit.WitnessSetoids
universe u v

structure Obj where
  Carrier : Type u
  Rel : Carrier → Carrier → Type v
  refl : ∀ x, Rel x x
  symm : ∀ {x y}, Rel x y → Rel y x
  trans : ∀ {x y z}, Rel x y → Rel y z → Rel x z

structure Hom (A B : Obj.{u,v}) where
  toFun : A.Carrier → B.Carrier
  congr : ∀ {x y}, A.Rel x y → B.Rel (toFun x) (toFun y)

def ops : CategoryOps Obj.{u,v} where
  Hom := Hom
  ident := ⟨id, fun h => h⟩
  comp g f := ⟨g.toFun ∘ f.toFun, fun h => g.congr (f.congr h)⟩

def equiv : WitnessEquivalence ops.{u,v} where
  Rel := fun {_ B} f g => ∀ x, B.Rel (f.toFun x) (g.toFun x)
  refl := fun {_ B} f x => B.refl (f.toFun x)
  symm := fun {_ B} {_ _} h x => B.symm (h x)
  trans := fun {_ B} {_ _ _} h k x => B.trans (h x) (k x)

def congr : equiv.Congr (C := ops.{u,v}) :=
  ⟨fun {_ _ c} {_ g'} {_ _} hg hf x => c.trans (hg _) (g'.congr (hf x))⟩
def laws : equiv.Laws (C := ops.{u,v}) :=
  ⟨fun {_ b} _ _ => b.refl _, fun {_ b} _ _ => b.refl _,
    fun {_ _ _ d} _ _ _ _ => d.refl _⟩

def unit : Obj.{u,v} := ⟨PUnit, fun _ _ => PUnit, fun _ => ⟨⟩, fun _ => ⟨⟩, fun _ _ => ⟨⟩⟩
def zero : Obj.{u,v} := ⟨PEmpty, fun _ _ => PEmpty, PEmpty.elim,
  fun {x} => x.elim, fun {x} => x.elim⟩
def prod (A B : Obj.{u,v}) : Obj.{u,v} :=
  ⟨A.Carrier × B.Carrier, fun x y => A.Rel x.1 y.1 × B.Rel x.2 y.2,
    fun _ => ⟨A.refl _, B.refl _⟩,
    fun h => ⟨A.symm h.1, B.symm h.2⟩,
    fun h k => ⟨A.trans h.1 k.1, B.trans h.2 k.2⟩⟩

def SumRel (A B : Obj.{u,v}) : Sum A.Carrier B.Carrier → Sum A.Carrier B.Carrier → Type v
  | .inl x, .inl y => A.Rel x y
  | .inr x, .inr y => B.Rel x y
  | .inl _, .inr _ => PEmpty
  | .inr _, .inl _ => PEmpty

def sum (A B : Obj.{u,v}) : Obj.{u,v} where
  Carrier := Sum A.Carrier B.Carrier
  Rel := SumRel A B
  refl := fun x => match x with
    | .inl a => A.refl a
    | .inr b => B.refl b
  symm := by
    intro x y h
    cases x <;> cases y
    · exact A.symm h
    · exact h.elim
    · exact h.elim
    · exact B.symm h
  trans := by
    intro x y z h k
    cases x <;> cases y <;> cases z
    · exact A.trans h k
    · exact k.elim
    · exact h.elim
    · exact h.elim
    · exact h.elim
    · exact h.elim
    · exact k.elim
    · exact B.trans h k

def terminal : TerminalOps ops.{u,v} := ⟨unit,⟨fun _ => PUnit.unit,fun _ => PUnit.unit⟩⟩
def initial : InitialOps ops.{u,v} := ⟨zero,⟨PEmpty.elim,fun {x} => x.elim⟩⟩
def products : ProductOps ops.{u,v} where
  prod := prod
  fst := ⟨Prod.fst,fun h => h.1⟩
  snd := ⟨Prod.snd,fun h => h.2⟩
  pair f g := ⟨fun x => (f.toFun x,g.toFun x),fun h => ⟨f.congr h,g.congr h⟩⟩
def coproducts : CoproductOps ops.{u,v} where
  sum := sum
  inl := ⟨Sum.inl,fun h => h⟩
  inr := ⟨Sum.inr,fun h => h⟩
  copair f g := ⟨Sum.elim f.toFun g.toFun,by
    intro x y h; cases x <;> cases y
    · exact f.congr h
    · exact h.elim
    · exact h.elim
    · exact g.congr h⟩

def terminal_laws : WitnessEquivalence.TerminalLaws equiv terminal.{u,v} := ⟨fun _ _ => PUnit.unit⟩
def initial_laws : WitnessEquivalence.InitialLaws equiv initial.{u,v} := ⟨fun _ x => x.elim⟩
def product_congr : WitnessEquivalence.ProductCongr equiv products.{u,v} := ⟨fun h k x => ⟨h x,k x⟩⟩
def product_laws : WitnessEquivalence.ProductLaws equiv products.{u,v} :=
  ⟨fun {_ b _} _ _ _ => b.refl _,fun {_ _ c} _ _ _ => c.refl _,
    fun {_ b c} _ _ => ⟨b.refl _,c.refl _⟩⟩
def coproduct_congr : WitnessEquivalence.CoproductCongr equiv coproducts.{u,v} := by
  constructor
  intro a b c f f' g g' h k x
  cases x with
  | inl x => exact h x
  | inr x => exact k x
def coproduct_laws : WitnessEquivalence.CoproductLaws equiv coproducts.{u,v} := by
  constructor
  · intro a b c f g x; exact c.refl _
  · intro a b c f g x; exact c.refl _
  · intro a b c f x; cases x <;> exact c.refl _


end SquareKit.WitnessSetoids
