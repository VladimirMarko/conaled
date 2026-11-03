import SquareKit.CategoryMap
import Mathlib.CategoryTheory.Types.Basic

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
namespace SquareKit.FunctionCategory
open CategoryTheory
universe u

def ops : CategoryOps (Type u) where
  Hom a b := a → b
  ident := id
  comp g f := g ∘ f

def terminal : TerminalOps ops where
  unit := PUnit
  terminal := fun _ => PUnit.unit

def products : ProductOps ops where
  prod := Prod
  fst := Prod.fst
  snd := Prod.snd
  pair f g x := (f x, g x)

theorem terminalLaws : TerminalLaws (equality ops) terminal where
  unique f := by change f = fun _ => PUnit.unit; funext x; exact @Subsingleton.elim PUnit inferInstance _ _

theorem productCongr : ProductCongr (equality ops) products where
  pair := by intros; subst_vars; rfl

theorem productLaws : ProductLaws (equality ops) products where
  fst_pair _ _ := rfl
  snd_pair _ _ := rfl
  pair_eta _ := rfl

/-- Mathlib's bundled arrows and ordinary functions have the same evaluation. -/
def toTypes : RawMap ops (ofCategory (Type u)) where
  obj := id
  map f := TypeCat.ofHom f

theorem toTypes_laws : MapLaws toTypes (equality _) (equality _) where
  congr := by intros; subst_vars; rfl
  ident := rfl
  comp _ _ := rfl

/-- Function equality is reflected by Mathlib's bundled function arrows. -/
theorem toTypes_reflects : toTypes.Reflects (equality _) (equality _) := by
  intro a b f g h
  exact funext (fun x => congrArg (fun k : a ⟶ b => k x) h)

theorem laws : CategoryLaws ops (equality ops) :=
  RawMap.transportLaws toTypes_laws toTypes_reflects (equalityCongr _) (ofCategoryLaws _)

end SquareKit.FunctionCategory
