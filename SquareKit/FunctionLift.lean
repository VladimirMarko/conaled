import SquareKit.FunctionCategory
import SquareKit.CartesianMap

/-! Function lifting permits independent source and lift universe levels. -/
namespace SquareKit.FunctionLift
universe u v
def map : RawMap FunctionCategory.ops.{u} FunctionCategory.ops.{max u v} where
  obj A := ULift.{v} A
  map f x := ⟨f x.down⟩

theorem map_laws : MapLaws map.{u,v} (equality _) (equality _) :=
  by
  constructor
  · intros; subst_vars; rfl
  · intro; rfl
  · intros; rfl

def terminal : TerminalMap map.{u,v} FunctionCategory.terminal FunctionCategory.terminal :=
  ⟨fun _ => PUnit.unit, fun _ => ⟨PUnit.unit⟩⟩
def products : ProductMap map.{u,v} FunctionCategory.products FunctionCategory.products :=
  fun _ _ => ⟨fun x => (⟨x.down.1⟩,⟨x.down.2⟩), fun x => ⟨(x.1.down,x.2.down)⟩⟩

theorem terminal_inverse : ComparisonLaws (equality _) terminal.{u,v} := by
  constructor <;> funext x <;> cases x <;> rfl

theorem products_inverse (A B : Type u) : ComparisonLaws (equality _) (products.{u,v} A B) :=
  ⟨rfl,rfl⟩
theorem terminal_laws : TerminalMapLaws (equality _) terminal.{u,v} := ⟨rfl⟩
theorem products_laws : ProductMapLaws (equality _) products.{u,v} :=
  ⟨rfl,rfl,fun _ _ => rfl⟩

@[simp] theorem unary {A B : Type u} (f : A → B) (a : A) :
    map.{u,v}.map f (ULift.up a) = ULift.up (f a) := rfl
@[simp] theorem binary {A B D : Type u} (f : A → B → D) (a : A) (b : B) :
    map.{u,v}.map (fun p : A × B => f p.1 p.2)
      ((products A B).inv (ULift.up a, ULift.up b)) = ULift.up (f a b) := rfl
@[simp] theorem constant {A B : Type u} (b : B) (a : ULift.{v} A) :
    map.{u,v}.map (fun _ : A => b) a = ULift.up b := rfl
def lift0' {A : Type u} (a : A) : ULift.{v} A := ⟨a⟩
def lift0 {A : Type u} (a : A) : PUnit.{max u v+1} → ULift.{v} A := fun _ => ⟨a⟩
def lift1 {A B : Type u} (f : A → B) : ULift.{v} A → ULift.{v} B := map.map f
def lift2' {A B D : Type u} (f : A → B → D) (a : ULift.{v} A) (b : ULift.{v} B) :
    ULift.{v} D := ⟨f a.down b.down⟩
def lift2 {A B D : Type u} (f : A → B → D) : ULift.{v} A × ULift.{v} B → ULift.{v} D :=
  fun p => lift2' f p.1 p.2

@[simp] theorem lift0_apply {A : Type u} (a : A) (x : PUnit.{max u v+1}) :
    lift0.{u,v} a x = lift0'.{u,v} a := rfl
@[simp] theorem lift2_map {A B D : Type u} (f : A → B → D) :
    lift2.{u,v} f = FunctionCategory.ops.comp (map.map (fun p : A × B => f p.1 p.2))
      (products A B).inv := rfl
end SquareKit.FunctionLift
