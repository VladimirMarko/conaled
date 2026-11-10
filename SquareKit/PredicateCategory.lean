import SquareKit.FunctionInitial
import SquareKit.FunctionOptionalLaws
import SquareKit.CoproductMap

/-! Predicates carry Type-valued witnesses; arrows retain total underlying functions. -/
namespace SquareKit.PredicateCategory
universe u w
structure Obj where
  Carrier : Type u
  pred : Carrier → Type w
structure Hom (A B : Obj.{u,w}) where
  toFun : A.Carrier → B.Carrier
  imp : ∀ x, A.pred x → B.pred (toFun x)

def ops : CategoryOps Obj.{u,w} where
  Hom := Hom
  ident := ⟨id,fun _ => id⟩
  comp g f := ⟨g.toFun ∘ f.toFun,fun x h => g.imp _ (f.imp x h)⟩
def forget : RawMap ops.{u,w} FunctionCategory.ops.{u} := ⟨Obj.Carrier,Hom.toFun⟩
def equiv : HomEquiv ops.{u,w} := forget.induced (equality _)
theorem forget_laws : MapLaws forget.{u,w} equiv (equality _) :=
  forget.inducedLaws _ rfl (fun _ _ => rfl)
theorem congr : CategoryCongr ops.{u,w} equiv :=
  RawMap.transportCongr forget_laws (forget.induced_reflects _) (equalityCongr _)
theorem laws : CategoryLaws ops.{u,w} equiv :=
  RawMap.transportLaws forget_laws (forget.induced_reflects _) (equalityCongr _) FunctionCategory.laws

def terminal : TerminalOps ops.{u,w} where
  unit := ⟨PUnit,fun _ => PUnit⟩
  terminal := ⟨fun _ => PUnit.unit,fun _ _ => PUnit.unit⟩
def products : ProductOps ops.{u,w} where
  prod A B := ⟨A.Carrier × B.Carrier,fun p => A.pred p.1 × B.pred p.2⟩
  fst := ⟨Prod.fst,fun _ h => h.1⟩
  snd := ⟨Prod.snd,fun _ h => h.2⟩
  pair f g := ⟨fun x => (f.toFun x,g.toFun x),fun x h => (f.imp x h,g.imp x h)⟩
def initial : InitialOps ops.{u,w} where
  zero := ⟨PEmpty,fun _ => PEmpty⟩
  initial := ⟨PEmpty.elim,fun x => x.elim⟩
def coproducts : CoproductOps ops.{u,w} where
  sum A B := ⟨Sum A.Carrier B.Carrier,Sum.elim A.pred B.pred⟩
  inl := ⟨Sum.inl,fun _ h => h⟩
  inr := ⟨Sum.inr,fun _ h => h⟩
  copair f g := ⟨Sum.elim f.toFun g.toFun,fun x => by cases x with
    | inl a => exact f.imp a
    | inr b => exact g.imp b⟩

theorem terminal_laws : TerminalLaws equiv terminal.{u,w} := by
  constructor
  intro a f
  funext x
  exact @Subsingleton.elim PUnit inferInstance _ _
theorem product_congr : ProductCongr equiv products.{u,w} :=
  by
  constructor
  intro a b c f f' g g' h k
  funext x
  exact Prod.ext (congrFun h x) (congrFun k x)
theorem product_laws : ProductLaws equiv products.{u,w} :=
  ⟨fun _ _ => rfl,fun _ _ => rfl,fun _ => rfl⟩
theorem initial_laws : InitialLaws equiv initial.{u,w} := by
  constructor
  intro a f
  funext x
  exact x.elim
theorem coproduct_congr : CoproductCongr ops equiv coproducts.{u,w} :=
  ⟨fun h k => congrArg₂ Sum.elim h k⟩
theorem coproduct_laws : CoproductLaws ops equiv coproducts.{u,w} := by
  constructor
  · intro a b c f g; rfl
  · intro a b c f g; rfl
  · intro a b c f; funext x; cases x <;> rfl

def terminalComparison : TerminalMap forget.{u,w} terminal FunctionCategory.terminal := ⟨id,id⟩
def productComparison : ProductMap forget.{u,w} products FunctionCategory.products := fun _ _ => ⟨id,id⟩
def initialComparison : InitialMap forget.{u,w} initial FunctionCategory.initial := ⟨id,id⟩
def coproductComparison : CoproductMap forget.{u,w} coproducts FunctionCategory.coproducts := fun _ _ => ⟨id,id⟩
theorem forget_terminal : TerminalMapLaws (equality _) terminalComparison.{u,w} := ⟨rfl⟩
theorem forget_products : ProductMapLaws (equality _) productComparison.{u,w} := ⟨rfl,rfl,fun _ _ => rfl⟩
theorem forget_initial : InitialMapLaws (equality _) initialComparison.{u,w} := ⟨rfl⟩
theorem forget_coproducts : CoproductMapLaws (equality _) coproductComparison.{u,w} := ⟨rfl,rfl,fun _ _ => rfl⟩
theorem terminalComparison_inverse : ComparisonLaws (equality _) terminalComparison.{u,w} := ⟨rfl,rfl⟩
theorem productComparison_inverse (a b : Obj.{u,w}) : ComparisonLaws (equality _) (productComparison a b) := ⟨rfl,rfl⟩
theorem initialComparison_inverse : ComparisonLaws (equality _) initialComparison.{u,w} := ⟨rfl,rfl⟩
theorem coproductComparison_inverse (a b : Obj.{u,w}) : ComparisonLaws (equality _) (coproductComparison a b) := ⟨rfl,rfl⟩
end SquareKit.PredicateCategory
