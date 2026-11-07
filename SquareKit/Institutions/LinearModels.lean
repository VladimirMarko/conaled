import SquareKit.Institutions.LinearCartesian

/-! Primitive semantic operations, local laws, and their recursive extension.
The source model class includes resource models, not only cartesian reducts. -/
namespace SquareKit.Institutions
namespace Linear

/-- An algebra for the categorical proof constructors, independently of any
proof translator. Model arrows retain data in Type. -/
structure Algebra (α : Type) where
  Hom : Formula α → Formula α → Type
  identity : ∀ A, Hom A A
  compose : ∀ {A B C}, Hom B C → Hom A B → Hom A C
  tensor : ∀ {A B C D}, Hom A B → Hom C D → Hom (.tensor A C) (.tensor B D)
  swap : ∀ A B, Hom (.tensor A B) (.tensor B A)
  assoc : ∀ A B C, Hom (.tensor (.tensor A B) C) (.tensor A (.tensor B C))
  unassoc : ∀ A B C, Hom (.tensor A (.tensor B C)) (.tensor (.tensor A B) C)
  unit : ∀ A, Hom (.tensor .unit A) A
  ununit : ∀ A, Hom A (.tensor .unit A)
  curry : ∀ {A B C}, Hom (.tensor A B) C → Hom A (.hom B C)
  uncurry : ∀ {A B C}, Hom A (.hom B C) → Hom (.tensor A B) C

/-- The laws of the equation fragment are primitive laws of operations.
Congruence and soundness for arbitrary derivations are derived below. -/
structure Lawful (M : Algebra α) : Prop where
  id_left : ∀ {A B} (f : M.Hom A B), M.compose (M.identity B) f = f
  id_right : ∀ {A B} (f : M.Hom A B), M.compose f (M.identity A) = f
  compose_assoc : ∀ {A B C D} (f : M.Hom A B) (g : M.Hom B C) (h : M.Hom C D),
    M.compose h (M.compose g f) = M.compose (M.compose h g) f
  beta : ∀ {A B C} (f : M.Hom (.tensor A B) C), M.uncurry (M.curry f) = f
  eta : ∀ {A B C} (f : M.Hom A (.hom B C)), M.curry (M.uncurry f) = f

  tensor_id : ∀ A B, M.tensor (M.identity A) (M.identity B) = M.identity (.tensor A B)
  tensor_comp : ∀ {A B C D E F} (f : M.Hom A B) (g : M.Hom B C) (h : M.Hom D E) (k : M.Hom E F),
    M.tensor (M.compose g f) (M.compose k h) = M.compose (M.tensor g k) (M.tensor f h)
  swap_swap : ∀ A B, M.compose (M.swap B A) (M.swap A B) = M.identity (.tensor A B)
  swap_natural : ∀ {A B C D} (f : M.Hom A B) (g : M.Hom C D),
    M.compose (M.swap B D) (M.tensor f g) = M.compose (M.tensor g f) (M.swap A C)
  assoc_unassoc : ∀ A B C, M.compose (M.assoc A B C) (M.unassoc A B C) = M.identity (.tensor A (.tensor B C))
  unassoc_assoc : ∀ A B C, M.compose (M.unassoc A B C) (M.assoc A B C) = M.identity (.tensor (.tensor A B) C)
  unit_ununit : ∀ A, M.compose (M.unit A) (M.ununit A) = M.identity A
  ununit_unit : ∀ A, M.compose (M.ununit A) (M.unit A) = M.identity (.tensor .unit A)
  curry_natural : ∀ {A B C D} (f : M.Hom (.tensor B C) D) (g : M.Hom A B),
    M.curry (M.compose f (M.tensor g (M.identity C))) = M.compose (M.curry f) g

  assoc_natural : ∀ {A B C D E F} (f : M.Hom A B) (g : M.Hom C D) (h : M.Hom E F),
    M.compose (M.assoc B D F) (M.tensor (M.tensor f g) h) =
      M.compose (M.tensor f (M.tensor g h)) (M.assoc A C E)
  unit_natural : ∀ {A B} (f : M.Hom A B),
    M.compose (M.unit B) (M.tensor (M.identity .unit) f) = M.compose f (M.unit A)
  right_unit_natural : ∀ {A B} (f : M.Hom A B),
    M.compose (M.compose (M.unit B) (M.swap B .unit)) (M.tensor f (M.identity .unit)) =
      M.compose f (M.compose (M.unit A) (M.swap A .unit))
  pentagon : ∀ A B C D,
    M.compose (M.assoc A B (.tensor C D)) (M.assoc (.tensor A B) C D) =
      M.compose (M.tensor (M.identity A) (M.assoc B C D))
        (M.compose (M.assoc A (.tensor B C) D) (M.tensor (M.assoc A B C) (M.identity D)))
  triangle : ∀ A B,
    M.compose (M.tensor (M.identity A) (M.unit B)) (M.assoc A .unit B) =
      M.tensor (M.compose (M.unit A) (M.swap A .unit)) (M.identity B)
  hexagon_forward : ∀ A B C,
    M.compose (M.assoc B C A) (M.compose (M.swap A (.tensor B C)) (M.assoc A B C)) =
      M.compose (M.tensor (M.identity B) (M.swap A C))
        (M.compose (M.assoc B A C) (M.tensor (M.swap A B) (M.identity C)))
  hexagon_reverse : ∀ A B C,
    M.compose (M.unassoc C A B) (M.compose (M.swap (.tensor A B) C) (M.unassoc A B C)) =
      M.compose (M.tensor (M.swap A C) (M.identity B))
        (M.compose (M.unassoc A C B) (M.tensor (M.identity A) (M.swap B C)))

structure Model (α : Type) extends Algebra α where
  laws : Lawful toAlgebra

def Algebra.interpret (M : Algebra α) {A B} : Proof A B → M.Hom A B
  | .id => M.identity _
  | .comp g f => M.compose (M.interpret g) (M.interpret f)
  | .tensor f g => M.tensor (M.interpret f) (M.interpret g)
  | .swap => M.swap _ _
  | .assoc => M.assoc _ _ _
  | .unassoc => M.unassoc _ _ _
  | .unit => M.unit _
  | .ununit => M.ununit _
  | .curry f => M.curry (M.interpret f)
  | .uncurry f => M.uncurry (M.interpret f)

theorem Model.equation (M : Model α) {A B} {f g : Proof A B} (h : Equation f g) :
    M.toAlgebra.interpret f = M.toAlgebra.interpret g := by
  induction h with
  | refl => rfl
  | symm _ ih => exact ih.symm
  | trans _ _ ih ih' => exact ih.trans ih'
  | comp _ _ ih ih' => exact congrArg₂ (fun g f => M.compose g f) ih ih'
  | tensor _ _ ih ih' => exact congrArg₂ (fun f g => M.tensor f g) ih ih'
  | curry _ ih => exact congrArg M.curry ih
  | uncurry _ ih => exact congrArg M.uncurry ih
  | beta => exact M.laws.beta _
  | eta => exact M.laws.eta _
  | id_left => exact M.laws.id_left _
  | id_right => exact M.laws.id_right _
  | assoc => exact M.laws.compose_assoc _ _ _
  | tensor_id => exact M.laws.tensor_id _ _
  | tensor_comp => exact M.laws.tensor_comp _ _ _ _
  | swap_swap => exact M.laws.swap_swap _ _
  | swap_natural => exact M.laws.swap_natural _ _
  | assoc_unassoc => exact M.laws.assoc_unassoc _ _ _
  | unassoc_assoc => exact M.laws.unassoc_assoc _ _ _
  | unit_ununit => exact M.laws.unit_ununit _
  | ununit_unit => exact M.laws.ununit_unit _
  | curry_natural => exact M.laws.curry_natural _ _
  | assoc_natural => exact M.laws.assoc_natural _ _ _
  | unit_natural => exact M.laws.unit_natural _
  | right_unit_natural => exact M.laws.right_unit_natural _
  | pentagon => exact M.laws.pentagon _ _ _ _
  | triangle => exact M.laws.triangle _ _
  | hexagon_forward => exact M.laws.hexagon_forward _ _ _
  | hexagon_reverse => exact M.laws.hexagon_reverse _ _ _

/-- Finite-resource arrows. The order proof is lifted into Type, so this model
has the same evidence interface as data-bearing models. -/
def resourceAlgebra (v : α → Int) : Algebra α where
  Hom A B := PLift (resource v A ≤ resource v B)
  identity _ := ⟨le_refl _⟩
  compose g f := ⟨le_trans f.down g.down⟩
  tensor f g := ⟨by have := f.down; have := g.down; dsimp [resource] at *; omega⟩
  swap _ _ := ⟨by dsimp [resource]; omega⟩
  assoc _ _ _ := ⟨by dsimp [resource]; omega⟩
  unassoc _ _ _ := ⟨by dsimp [resource]; omega⟩
  unit _ := ⟨by dsimp [resource]; omega⟩
  ununit _ := ⟨by dsimp [resource]; omega⟩
  curry f := ⟨by have := f.down; dsimp [resource] at *; omega⟩
  uncurry f := ⟨by have := f.down; dsimp [resource] at *; omega⟩

def resourceModel (v : α → Int) : Model α where
  toAlgebra := resourceAlgebra v
  laws := by constructor <;> intros <;> rfl

def cartesianModel (v : α → Type) : Model α where
  Hom A B := (linearFormula A).denote v → (linearFormula B).denote v
  identity _ := id
  compose g f := g ∘ f
  tensor f g := fun (x,y) => (f x,g y)
  swap _ _ := fun (x,y) => (y,x)
  assoc _ _ _ := fun ((x,y),z) => (x,(y,z))
  unassoc _ _ _ := fun (x,(y,z)) => ((x,y),z)
  unit _ := Prod.snd
  ununit _ := fun x => ((),x)
  curry f := fun x y => f (x,y)
  uncurry f := fun (x,y) => f x y
  laws := by constructor <;> intros <;> rfl

theorem cartesian_interpret (v : α → Type) {A B} (p : Proof A B) :
    (cartesianModel v).toAlgebra.interpret p = linearMeaning v p := by
  induction p with
  | id => rfl
  | comp _ _ ih ih' => exact congrArg₂ (fun g f => g ∘ f) ih ih'
  | tensor _ _ ih ih' => exact congrArg₂ (fun f g => fun (x,y) => (f x,g y)) ih ih'
  | swap => rfl
  | assoc => rfl
  | unassoc => rfl
  | unit => rfl
  | ununit => rfl
  | curry _ ih => exact congrArg (fun f => fun x y => f (x,y)) ih
  | uncurry _ ih => exact congrArg (fun f => fun (x,y) => f x y) ih

end Linear

def linearModelSetting (α : Type) : Setting.{0,1,0} where
  Sentence := Linear.Formula α × Linear.Formula α
  Model := Linear.Model α
  Evidence M p := M.Hom p.1 p.2

def modelConnection (α : Type) : Connection (linearModelSetting α) (cartesianSetting α) where
  sentence p := (linearFormula p.1,linearFormula p.2)
  reduct := Linear.cartesianModel
  evidence _ _ := id

theorem modelConnection_reflects (α : Type) : (modelConnection α).Reflects := ⟨fun _ _ => id⟩

def modelProofs (α : Type) : Proofs (linearModelSetting α) :=
  ⟨fun p => Linear.Proof p.1 p.2, fun M _ => M.toAlgebra.interpret⟩

def modelProofMap (α : Type) : ProofMap (modelConnection α) (modelProofs α) (cartesianProofs α) :=
  ⟨fun _ => linearProof, fun v _ p =>
    (linearMeaning_translation v p).trans (Linear.cartesian_interpret v p).symm⟩

/-- A reverse proof translator preserving these formula meanings cannot exist.
This uses the same model interface as the forward interpretation. -/
theorem no_reverse_contraction : ¬ Nonempty
    (Linear.Proof (.atom () : Linear.Formula Unit) (.tensor (.atom ()) (.atom ()))) := by
  rintro ⟨p⟩
  have h := (Linear.resourceModel (fun _ : Unit => (-1 : Int))).toAlgebra.interpret p
  have h' := h.down
  norm_num [Linear.resourceModel, Linear.resourceAlgebra, Linear.resource] at h'

end SquareKit.Institutions
