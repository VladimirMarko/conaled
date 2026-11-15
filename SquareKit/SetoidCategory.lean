import SquareKit.Initial
import SquareKit.RightDistribution

/-! Congruent total functions with pointwise relation, specializing Felix's relation witnesses to Prop. -/
namespace SquareKit.SetoidCategory
universe u
structure Obj where
  Carrier : Type u
  relation : Setoid Carrier
structure Hom (A B : Obj.{u}) where
  toFun : A.Carrier → B.Carrier
  congr : ∀ {x y}, A.relation.r x y → B.relation.r (toFun x) (toFun y)

def ops : CategoryOps Obj.{u} where
  Hom := Hom
  ident := ⟨id,fun h => h⟩
  comp g f := ⟨g.toFun ∘ f.toFun,fun h => g.congr (f.congr h)⟩
def equiv : HomEquiv ops.{u} where
  homSetoid _ B := {
    r := fun f g => ∀ x, B.relation.r (f.toFun x) (g.toFun x)
    iseqv := ⟨fun _ _ => B.relation.refl _,fun h x => B.relation.symm (h x),
      fun h k x => B.relation.trans (h x) (k x)⟩ }
theorem congr : CategoryCongr ops.{u} equiv :=
  ⟨fun {_ _ c} {_ g'} {_ _} hg hf x => c.relation.trans (hg _) (g'.congr (hf x))⟩
theorem laws : CategoryLaws ops.{u} equiv :=
  ⟨fun {_ b} _ _ => b.relation.refl _,fun {_ b} _ _ => b.relation.refl _,
    fun {_ _ _ d} _ _ _ _ => d.relation.refl _⟩

def unit : Obj.{u} := ⟨PUnit,⟨fun _ _ => True,⟨fun _ => True.intro,fun _ => True.intro,fun _ _ => True.intro⟩⟩⟩
def zero : Obj.{u} := ⟨PEmpty,⟨Eq,⟨Eq.refl,Eq.symm,Eq.trans⟩⟩⟩
def prod (A B : Obj.{u}) : Obj.{u} := ⟨A.Carrier × B.Carrier,{
  r := fun x y => A.relation.r x.1 y.1 ∧ B.relation.r x.2 y.2
  iseqv := ⟨fun _ => ⟨A.relation.refl _,B.relation.refl _⟩,
    fun h => ⟨A.relation.symm h.1,B.relation.symm h.2⟩,
    fun h k => ⟨A.relation.trans h.1 k.1,B.relation.trans h.2 k.2⟩⟩ }⟩
def sum (A B : Obj.{u}) : Obj.{u} := ⟨Sum A.Carrier B.Carrier,{
  r := Sum.LiftRel A.relation.r B.relation.r
  iseqv := ⟨by intro x; cases x with
    | inl a => exact .inl (A.relation.refl a)
    | inr b => exact .inr (B.relation.refl b),
    by intro x y h; cases h with
    | inl h => exact .inl (A.relation.symm h)
    | inr h => exact .inr (B.relation.symm h),
    by intro x y z h k; cases h <;> cases k
       · exact .inl (A.relation.trans ‹_› ‹_›)
       · exact .inr (B.relation.trans ‹_› ‹_›)⟩ }⟩

def terminal : TerminalOps ops.{u} := ⟨unit,⟨fun _ => PUnit.unit,fun _ => True.intro⟩⟩
def initial : InitialOps ops.{u} := ⟨zero,⟨PEmpty.elim,fun {x} => x.elim⟩⟩
def products : ProductOps ops.{u} where
  prod := prod
  fst := ⟨Prod.fst,fun h => h.1⟩
  snd := ⟨Prod.snd,fun h => h.2⟩
  pair f g := ⟨fun x => (f.toFun x,g.toFun x),fun h => ⟨f.congr h,g.congr h⟩⟩
def coproducts : CoproductOps ops.{u} where
  sum := sum
  inl := ⟨Sum.inl,fun h => .inl h⟩
  inr := ⟨Sum.inr,fun h => .inr h⟩
  copair f g := ⟨Sum.elim f.toFun g.toFun,by
    intro x y h; cases h with
    | inl h => exact f.congr h
    | inr h => exact g.congr h⟩

theorem terminal_laws : TerminalLaws equiv terminal.{u} := ⟨fun _ _ => True.intro⟩
theorem initial_laws : InitialLaws equiv initial.{u} := ⟨fun _ x => x.elim⟩
theorem product_congr : ProductCongr equiv products.{u} := ⟨fun h k x => ⟨h x,k x⟩⟩
theorem product_laws : ProductLaws equiv products.{u} :=
  ⟨fun {_ b _} _ _ _ => b.relation.refl _,fun {_ _ c} _ _ _ => c.relation.refl _,
    fun {_ b c} _ _ => ⟨b.relation.refl _,c.relation.refl _⟩⟩
theorem coproduct_congr : CoproductCongr ops equiv coproducts.{u} := by
  constructor
  intro a b c f f' g g' h k x
  cases x with
  | inl x => exact h x
  | inr x => exact k x
theorem coproduct_laws : CoproductLaws ops equiv coproducts.{u} := by
  constructor
  · intro a b c f g x; exact c.relation.refl _
  · intro a b c f g x; exact c.relation.refl _
  · intro a b c f x; cases x <;> exact c.relation.refl _

def exponential (A B : Obj.{u}) : Obj.{u} := ⟨Hom A B,{
  r := fun f g => ∀ x, B.relation.r (f.toFun x) (g.toFun x)
  iseqv := ⟨fun _ _ => B.relation.refl _,fun h x => B.relation.symm (h x),
    fun h k x => B.relation.trans (h x) (k x)⟩ }⟩
def closed : ClosedOps ops.{u} products where
  exp := exponential
  evaluation {_ b} := ⟨fun p => p.1.toFun p.2,fun {_ y} h =>
    b.relation.trans (h.1 _) (y.1.congr h.2)⟩
  curry {x a _} f := ⟨fun z => ⟨fun y => f.toFun (z,y),fun h => f.congr ⟨x.relation.refl _,h⟩⟩,
    fun h y => f.congr ⟨h,a.relation.refl y⟩⟩
theorem closed_congr : ClosedCongr equiv products closed.{u} := ⟨fun h x a => h (x,a)⟩
theorem closed_laws : ClosedLaws equiv products closed.{u} :=
  ⟨fun {_ _ b} _ _ => b.relation.refl _,fun {_ _ b} _ _ _ => b.relation.refl _,
    fun {_ _ _ b} _ _ _ _ => b.relation.refl _⟩

def distribution : DistributionOps ops.{u} products coproducts where
  distribute := ⟨fun p => match p.2 with
    | .inl b => .inl (p.1,b)
    | .inr c => .inr (p.1,c),by
      intro x y h
      rcases x with ⟨x₁,x₂⟩; rcases y with ⟨y₁,y₂⟩
      rcases h with ⟨h,k⟩
      cases k with
      | inl k => exact .inl ⟨h,k⟩
      | inr k => exact .inr ⟨h,k⟩⟩
def rightDistribution : RightDistributionOps products coproducts.{u} where
  distribute := ⟨fun p => match p.1 with
    | .inl b => .inl (b,p.2)
    | .inr c => .inr (c,p.2),by
      intro x y h
      rcases x with ⟨x₁,x₂⟩; rcases y with ⟨y₁,y₂⟩
      rcases h with ⟨k,h⟩
      cases k with
      | inl k => exact .inl ⟨k,h⟩
      | inr k => exact .inr ⟨k,h⟩⟩

theorem distribution_laws : DistributionLaws ops equiv products coproducts distribution.{u} := by
  constructor
  · intro a b c x; rcases x with ⟨x,y⟩; cases y <;> exact (prod a (sum b c)).relation.refl _
  · intro a b c x; cases x <;> exact (sum (prod a b) (prod a c)).relation.refl _
theorem rightDistribution_laws : RightDistributionLaws (E := equiv) products coproducts rightDistribution.{u} := by
  constructor
  · intro a b c x; rcases x with ⟨y,x⟩; cases y <;> exact (prod (sum b c) a).relation.refl _
  · intro a b c x; cases x <;> exact (sum (prod b a) (prod c a)).relation.refl _
end SquareKit.SetoidCategory
