import SquareKit.Institutions.Capabilities
import Mathlib.Tactic.NormNum

/-! Independently specified linear and cartesian combinator calculi. Contexts
are tensor/product objects; substitution is composition. The equation fragment
includes category laws and the closed beta/eta laws. -/
namespace SquareKit.Institutions
set_option backward.isDefEq.respectTransparency false
namespace Linear
inductive Formula (α : Type) where
  | atom : α → Formula α
  | unit : Formula α
  | tensor : Formula α → Formula α → Formula α
  | hom : Formula α → Formula α → Formula α

inductive Proof {α : Type} : Formula α → Formula α → Type
  | id {A} : Proof A A
  | comp {A B C} : Proof B C → Proof A B → Proof A C
  | tensor {A B C D} : Proof A B → Proof C D → Proof (.tensor A C) (.tensor B D)
  | swap {A B} : Proof (.tensor A B) (.tensor B A)
  | assoc {A B C} : Proof (.tensor (.tensor A B) C) (.tensor A (.tensor B C))
  | unassoc {A B C} : Proof (.tensor A (.tensor B C)) (.tensor (.tensor A B) C)
  | unit {A} : Proof (.tensor .unit A) A
  | ununit {A} : Proof A (.tensor .unit A)
  | curry {A B C} : Proof (.tensor A B) C → Proof A (.hom B C)
  | uncurry {A B C} : Proof A (.hom B C) → Proof (.tensor A B) C

/-- The integer resource interpretation is independent of translation. -/
def resource (v : α → Int) : Formula α → Int
  | .atom a => v a
  | .unit => 0
  | .tensor A B => resource v A + resource v B
  | .hom A B => resource v B - resource v A

theorem sound {α} (v : α → Int) {A B} (p : Proof A B) : resource v A ≤ resource v B := by
  induction p with
  | id => exact le_refl _
  | comp _ _ ihg ihf => exact le_trans ihf ihg
  | tensor _ _ ihf ihg => dsimp [resource]; omega
  | swap => dsimp [resource]; omega
  | assoc => dsimp [resource]; omega
  | unassoc => dsimp [resource]; omega
  | unit => dsimp [resource]; omega
  | ununit => dsimp [resource]; omega
  | curry _ ih => dsimp [resource] at *; omega
  | uncurry _ ih => dsimp [resource] at *; omega

theorem no_contraction : ¬ Nonempty (Proof (.atom () : Formula Unit) (.tensor (.atom ()) (.atom ()))) := by
  rintro ⟨p⟩
  have h := sound (fun _ => (-1 : Int)) p
  norm_num [resource] at h

inductive Equation {α : Type} : {A B : Formula α} → Proof A B → Proof A B → Prop
  | refl (p) : Equation p p
  | symm {p q : Proof A B} : Equation p q → Equation q p
  | trans {p q r : Proof A B} : Equation p q → Equation q r → Equation p r
  | comp {f f' : Proof A B} {g g' : Proof B C} : Equation g g' → Equation f f' → Equation (.comp g f) (.comp g' f')
  | tensor {f f' : Proof A B} {g g' : Proof C D} : Equation f f' → Equation g g' → Equation (.tensor f g) (.tensor f' g')
  | curry {f g : Proof (.tensor A B) C} : Equation f g → Equation (.curry f) (.curry g)
  | uncurry {f g : Proof A (.hom B C)} : Equation f g → Equation (.uncurry f) (.uncurry g)
  | beta (f : Proof (.tensor A B) C) : Equation (.uncurry (.curry f)) f
  | eta (f : Proof A (.hom B C)) : Equation (.curry (.uncurry f)) f
  | id_left (f : Proof A B) : Equation (.comp .id f) f
  | id_right (f : Proof A B) : Equation (.comp f .id) f
  | assoc (f : Proof A B) (g : Proof B C) (h : Proof C D) : Equation (.comp h (.comp g f)) (.comp (.comp h g) f)
end Linear

namespace Cartesian
inductive Formula (α : Type) where
  | atom : α → Formula α
  | one : Formula α
  | product : Formula α → Formula α → Formula α
  | function : Formula α → Formula α → Formula α

inductive Proof {α : Type} : Formula α → Formula α → Type
  | id {A} : Proof A A
  | comp {A B C} : Proof B C → Proof A B → Proof A C
  | pair {A B C} : Proof A B → Proof A C → Proof A (.product B C)
  | fst {A B} : Proof (.product A B) A
  | snd {A B} : Proof (.product A B) B
  | terminal {A} : Proof A .one
  | curry {A B C} : Proof (.product A B) C → Proof A (.function B C)
  | uncurry {A B C} : Proof A (.function B C) → Proof (.product A B) C

def Formula.denote (v : α → Type) : Formula α → Type
  | .atom a => v a
  | .one => Unit
  | .product A B => A.denote v × B.denote v
  | .function A B => A.denote v → B.denote v

def Proof.denote (v : α → Type) {A B} : Proof A B → A.denote v → B.denote v
  | .id => fun x => x
  | .comp g f => g.denote v ∘ f.denote v
  | .pair f g => fun x => (f.denote v x, g.denote v x)
  | .fst => Prod.fst
  | .snd => Prod.snd
  | .terminal => fun _ => ()
  | .curry f => fun x y => f.denote v (x,y)
  | .uncurry f => fun (x,y) => f.denote v x y

/-- Independent semantic equation specification, including all beta/eta and
product equations of functions. No equality reflection into linear syntax. -/
def Equation {α} {A B : Formula α} (f g : Proof A B) : Prop :=
  ∀ v : α → Type, f.denote v = g.denote v

def Formula.rename (r : α → β) : Formula α → Formula β
  | .atom a => .atom (r a)
  | .one => .one
  | .product A B => .product (A.rename r) (B.rename r)
  | .function A B => .function (A.rename r) (B.rename r)
def Proof.rename (r : α → β) {A B} : Proof A B → Proof (A.rename r) (B.rename r)
  | .id => .id
  | .comp g f => .comp (g.rename r) (f.rename r)
  | .pair f g => .pair (f.rename r) (g.rename r)
  | .fst => .fst
  | .snd => .snd
  | .terminal => .terminal
  | .curry f => .curry (f.rename r)
  | .uncurry f => .uncurry (f.rename r)

end Cartesian

def linearFormula : Linear.Formula α → Cartesian.Formula α
  | .atom a => .atom a
  | .unit => .one
  | .tensor A B => .product (linearFormula A) (linearFormula B)
  | .hom A B => .function (linearFormula A) (linearFormula B)

/-- Each primitive assignment is a cartesian proof. The recursive extension
translates arbitrary source proofs; no whole-proof translation field is given. -/
def linearProof {A B : Linear.Formula α} : Linear.Proof A B → Cartesian.Proof (linearFormula A) (linearFormula B)
  | .id => .id
  | .comp g f => .comp (linearProof g) (linearProof f)
  | .tensor f g => .pair (.comp (linearProof f) .fst) (.comp (linearProof g) .snd)
  | .swap => .pair .snd .fst
  | .assoc => .pair (.comp .fst .fst) (.pair (.comp .snd .fst) .snd)
  | .unassoc => .pair (.pair .fst (.comp .fst .snd)) (.comp .snd .snd)
  | .unit => .snd
  | .ununit => .pair .terminal .id
  | .curry f => .curry (linearProof f)
  | .uncurry f => .uncurry (linearProof f)

theorem translate_equation {A B : Linear.Formula α} {f g : Linear.Proof A B}
    (h : Linear.Equation f g) : Cartesian.Equation (linearProof f) (linearProof g) := by
  induction h with
  | refl => intro _; rfl
  | symm _ ih => intro v; exact (ih v).symm
  | trans _ _ ih ih' => intro v; exact (ih v).trans (ih' v)
  | comp _ _ ih ih' => intro v; simp only [linearProof, Cartesian.Proof.denote, ih v, ih' v]
  | tensor _ _ ih ih' => intro v; simp only [linearProof, Cartesian.Proof.denote, ih v, ih' v]
  | curry _ ih => intro v; simp only [linearProof, Cartesian.Proof.denote, ih v]
  | uncurry _ ih => intro v; simp only [linearProof, Cartesian.Proof.denote, ih v]
  | beta => intro _; rfl
  | eta => intro _; rfl
  | id_left => intro _; rfl
  | id_right => intro _; rfl
  | assoc => intro _; rfl

/-- Context substitution is categorical composition in this presentation. -/
theorem translate_substitution {A B C : Linear.Formula α}
    (t : Linear.Proof B C) (σ : Linear.Proof A B) :
    linearProof (.comp t σ) = .comp (linearProof t) (linearProof σ) := rfl

end SquareKit.Institutions

namespace SquareKit.Institutions
/-- Independent evaluation of the source constructors in a cartesian model.
The source type interpretation uses the stated tensor/product assignment. -/
def linearMeaning (v : α → Type) {A B : Linear.Formula α} :
    Linear.Proof A B → (linearFormula A).denote v → (linearFormula B).denote v
  | .id => fun x => x
  | .comp g f => linearMeaning v g ∘ linearMeaning v f
  | .tensor f g => fun (x,y) => (linearMeaning v f x, linearMeaning v g y)
  | .swap => fun (x,y) => (y,x)
  | .assoc => fun ((x,y),z) => (x,(y,z))
  | .unassoc => fun (x,(y,z)) => ((x,y),z)
  | .unit => Prod.snd
  | .ununit => fun x => ((),x)
  | .curry f => fun x y => linearMeaning v f (x,y)
  | .uncurry f => fun (x,y) => linearMeaning v f x y

theorem linearMeaning_translation (v : α → Type) {A B} (p : Linear.Proof A B) :
    (linearProof p).denote v = linearMeaning v p := by
  induction p with
  | id => rfl
  | comp _ _ ih ih' => simp only [linearProof, Cartesian.Proof.denote, linearMeaning, ih, ih']
  | tensor _ _ ih ih' => simp only [linearProof, Cartesian.Proof.denote, linearMeaning, ih, ih']; rfl
  | swap => rfl
  | assoc => rfl
  | unassoc => rfl
  | unit => rfl
  | ununit => rfl
  | curry _ ih => exact funext (fun x => funext (fun y => congrFun ih (x,y)))
  | uncurry _ ih => exact funext (fun x => congrFun (congrFun ih x.1) x.2)

/-- These are the cartesian-reduct source models, not all linear models.
The integer countermodel above deliberately lies outside this chosen class. -/
def linearSetting (α : Type) : Setting.{0,1,0} where
  Sentence := Linear.Formula α × Linear.Formula α
  Model := α → Type
  Evidence v p := (linearFormula p.1).denote v → (linearFormula p.2).denote v

def cartesianSetting (α : Type) : Setting.{0,1,0} where
  Sentence := Cartesian.Formula α × Cartesian.Formula α
  Model := α → Type
  Evidence v p := p.1.denote v → p.2.denote v

def linearConnection (α : Type) : Connection (linearSetting α) (cartesianSetting α) where
  sentence p := (linearFormula p.1, linearFormula p.2)
  reduct := id
  evidence _ _ := id

def linearProofs (α : Type) : Proofs (linearSetting α) :=
  ⟨fun p => Linear.Proof p.1 p.2, fun v _ => linearMeaning v⟩
def cartesianProofs (α : Type) : Proofs (cartesianSetting α) :=
  ⟨fun p => Cartesian.Proof p.1 p.2, fun v _ => Cartesian.Proof.denote v⟩
def linearProofMap (α : Type) : ProofMap (linearConnection α) (linearProofs α) (cartesianProofs α) :=
  ⟨fun _ => linearProof, fun v _ p => linearMeaning_translation v p⟩

/-- Formula denotations under atom renaming are canonically equivalent. -/
def Cartesian.Formula.renameEquiv (r : α → β) (v : β → Type) :
    (A : Cartesian.Formula α) → Equiv (A.denote (v ∘ r)) ((A.rename r).denote v)
  | .atom _ => Equiv.refl _
  | .one => Equiv.refl _
  | .product A B => Equiv.prodCongr (A.renameEquiv r v) (B.renameEquiv r v)
  | .function A B => Equiv.arrowCongr (A.renameEquiv r v) (B.renameEquiv r v)

def renameConnection (r : α → β) : Connection (cartesianSetting α) (cartesianSetting β) where
  sentence p := (p.1.rename r, p.2.rename r)
  reduct v := v ∘ r
  evidence v p f := (p.2.renameEquiv r v) ∘ f ∘ (p.1.renameEquiv r v).symm

theorem rename_meaning (r : α → β) (v : β → Type) {A B : Cartesian.Formula α}
    (p : Cartesian.Proof A B) :
    (p.rename r).denote v = (B.renameEquiv r v) ∘ p.denote (v ∘ r) ∘ (A.renameEquiv r v).symm := by
  induction p with
  | @id A => funext x; exact ((A.renameEquiv r v).apply_symm_apply x).symm
  | comp g f ihg ihf =>
    funext x
    simp only [Cartesian.Proof.rename, Cartesian.Proof.denote, ihg, ihf, Function.comp_apply,
      Equiv.symm_apply_apply]
  | pair f g ihf ihg =>
    simp only [Cartesian.Proof.rename, Cartesian.Proof.denote, Cartesian.Formula.renameEquiv,
      ihf, ihg]
    rfl
  | fst => funext x; exact (Equiv.apply_symm_apply _ x.1).symm
  | snd => funext x; exact (Equiv.apply_symm_apply _ x.2).symm
  | terminal => rfl
  | curry f ih => exact funext (fun x => funext (fun y => congrFun ih (x,y)))
  | uncurry f ih => exact funext (fun x => congrFun (congrFun ih x.1) x.2)

def renameProofMap (r : α → β) : ProofMap (renameConnection r) (cartesianProofs α) (cartesianProofs β) :=
  ⟨fun _ => Cartesian.Proof.rename r, fun v _ p => rename_meaning r v p⟩

end SquareKit.Institutions
