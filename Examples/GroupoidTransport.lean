import SquareKit.Internal.PathTransport.Syntax
import SquareKit.Internal.PathTransport.GroupoidIdentity
import SquareKit.Internal.PathTransport.BasedPath
import Mathlib.CategoryTheory.SingleObj
import Mathlib.Data.ZMod.Basic

/-!
# Raw and semantic comparison cases

These preliminary cases exercise raw substitution, arrow-valued identity and
set-valued semantic elimination. Their independent action calculations are
expected results. `Examples.AgdaTransferModels` connects those results to the
complete transferred source proof and its all-rule interpreter.
-/
namespace Examples.GroupoidTransport

open CategoryTheory
open SquareKit.Internal.PathTransport

abbrev C4 := SingleObj (Multiplicative (ZMod 4))
def point : C4 := SingleObj.star _

/-- Translation on C₄. Mathlib's `SingleObj` composes `p ≫ q` as `q * p`,
so this action applies `q` after `p`. -/
def faithful : C4 ⥤ Type where
  obj _ := ZMod 4
  map p := ↾fun b => Multiplicative.toAdd p + b
  map_id _ := by ext b; exact zero_add b
  map_comp p q := by ext b; exact add_assoc _ _ _

/-- All arrows act trivially on this fiber; their base labels remain intact. -/
def ineffective : C4 ⥤ Type where
  obj _ := Fin 2
  map _ := 𝟙 _
  map_id _ := rfl
  map_comp _ _ := rfl

/-- Embed each label in the arrow-valued identity family over the context C₄. -/
def label (n : ZMod 4) : (GroupoidIdentity.family (𝟭 C4) (𝟭 C4)).obj point :=
  Multiplicative.ofAdd n

/-- All four labels remain distinct, independently of a chosen action family. -/
theorem labels_injective : Function.Injective label := by
  intro a b h
  have h' := congrArg (GroupoidIdentity.basePathEquiv (𝟭 C4) (𝟭 C4) point) h
  exact congrArg Multiplicative.toAdd h'

example : label 1 ≠ GroupoidIdentity.reflexivity (𝟭 C4) point := by
  intro h
  have h' : (1 : ZMod 4) = 0 := labels_injective h
  exact (by decide : (1 : ZMod 4) ≠ 0) h'

example : faithful.map (label 1) (0 : ZMod 4) = (1 : ZMod 4) := by
  change (1 : ZMod 4) + 0 = 1
  decide

example : faithful.map (label 1 ≫ label 1) (0 : ZMod 4) = (2 : ZMod 4) := by
  change (1 : ZMod 4) + 1 + 0 = 2
  decide

example : faithful.map (label 1) (faithful.map (label 1) (0 : ZMod 4)) = (2 : ZMod 4) := by
  change (1 : ZMod 4) + (1 + 0) = 2
  decide

example (p : point ⟶ point) (b : Fin 2) : ineffective.map p b = b := rfl

/-- The faithful interpretation of semantic based elimination moves zero by one. -/
example : BasedPath.eliminate
    (Functor.Elements.π (coyoneda.obj (Opposite.op point)) ⋙ faithful)
    (0 : ZMod 4) (.mk (label 1)) = (1 : ZMod 4) := by
  change (1 : ZMod 4) + 0 = 1
  decide

/-- The same semantic elimination in the ineffective family fixes every element. -/
example (p : point ⟶ point) (b : Fin 2) : BasedPath.eliminate
    (Functor.Elements.π (coyoneda.obj (Opposite.op point)) ⋙ ineffective)
    b (.mk p) = b := rfl

example (b : ZMod 4) : BasedPath.eliminate
    (Functor.Elements.π (coyoneda.obj (Opposite.op point)) ⋙ faithful)
    b (BasedPath.root point) = b := BasedPath.eliminate_root _ _

/-- A three-parameter generalized tail keeps its newest variable bound,
while simultaneous substitution acts on the external parameter. -/
example (σ : Nat → Expr) :
    Expr.sub σ (.pathInduction 3 .base (.var 0)
      (.identity (.fiber (.var 3)) (.var 0) (.var 5))
      (.var 3) (.var 1) (.var 2) (fun i => .var i.val)) =
    .pathInduction 3 .base (σ 0)
      (.identity (.fiber (.var 3)) (.var 0) (Expr.rename (fun n => n + 5) (σ 0)))
      (Expr.rename (fun n => n + 3) (σ 0)) (σ 1) (σ 2) (fun i => σ i.val) := by
  simp only [Expr.sub, Expr.liftSubN, Expr.liftSub, Expr.rename_comp]
  rfl

/-- Renaming and substitution compose even for a term containing contextual J. -/
example (t : Expr) (ρ : Nat → Nat) (σ : Nat → Expr) :
    Expr.sub σ (Expr.rename ρ t) = Expr.sub (σ ∘ ρ) t :=
  Expr.sub_rename t ρ σ

end Examples.GroupoidTransport
