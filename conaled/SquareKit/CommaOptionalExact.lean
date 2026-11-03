import SquareKit.CommaProductsExact
import SquareKit.OptionalQuotient

/-! Optional structure for the identity/identity comma over types. No closure
assumption is made about arbitrary comma categories. -/
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
namespace SquareKit.Comma.Exact
universe u

def coproducts : CoproductOps categoryOps.{u} where
  sum a b := ofRep (Squares.coproduct (toRep a) (toRep b))
  inl {a b} := ofSquare (Squares.injectLeft (toRep a) (toRep b))
  inr {a b} := ofSquare (Squares.injectRight (toRep a) (toRep b))
  copair f g := ofSquare (Squares.copair (toSquare f) (toSquare g))

def distribution : DistributionOps categoryOps.{u} products coproducts where
  distribute {a b c} := ofSquare (Squares.distribution (toRep a) (toRep b) (toRep c))

def closed : ClosedOps categoryOps.{u} products where
  exp a b := ofRep (Squares.exponential (toRep a) (toRep b))
  evaluation {a b} := ofSquare (Squares.evaluation (toRep a) (toRep b))
  curry {x a b} f := ofSquare (Squares.curry (X := toRep x) (A := toRep a) (B := toRep b) (toSquare f))

theorem coproductCongr : CoproductCongr categoryOps.{u} (equality _) coproducts where
  copair := by intros; subst_vars; rfl

theorem coproductLaws : CoproductLaws categoryOps.{u} (equality _) coproducts where
  left f g := congrArg ofSquare (Squares.copair_left (toSquare f) (toSquare g))
  right f g := congrArg ofSquare (Squares.copair_right (toSquare f) (toSquare g))
  eta f := congrArg ofSquare (Squares.copair_eta (toSquare f))

theorem distributionLaws : DistributionLaws categoryOps.{u} (equality _) products coproducts distribution where
  collect_distribute a b c := by
    apply Hom.ext <;> funext p <;> rcases p with ⟨a, b | c⟩ <;> rfl
  distribute_collect a b c := by
    apply Hom.ext <;> funext p <;> cases p <;> rfl

theorem closedCongr : ClosedCongr (equality categoryOps.{u}) products closed where
  curry := by intros; subst_vars; rfl

theorem closedLaws : ClosedLaws (equality categoryOps.{u}) products closed where
  beta {x a b} f := congrArg ofSquare (Squares.uncurry_curry (X := toRep x) (A := toRep a) (B := toRep b) (toSquare f))
  eta {x a b} f := congrArg ofSquare (Squares.curry_uncurry (X := toRep x) (A := toRep a) (B := toRep b) (toSquare f))
  natural {x y a b} f g := congrArg ofSquare (Squares.curry_natural (X := toRep x) (Y := toRep y) (A := toRep a) (B := toRep b) (toSquare f) (toSquare g))

@[simp] theorem ofRep_coproduct (a b : Squares.Rep.{u}) :
    ofRep (Squares.coproduct a b) = coproducts.sum (ofRep a) (ofRep b) := rfl
@[simp] theorem ofRep_exponential (a b : Squares.Rep.{u}) :
    ofRep (Squares.exponential a b) = closed.exp (ofRep a) (ofRep b) := rfl
/-- The represented function carrier still stores both functions and compatibility. -/
@[simp] theorem exponential_carrier (a b : Squares.Rep.{u}) :
    (closed.exp (ofRep a) (ofRep b)).left = Squares.FunctionRep a b := rfl
@[simp] theorem ofSquare_inl (a b : Squares.Rep.{u}) :
    ofSquare (Squares.injectLeft a b) = coproducts.inl (a := ofRep a) (b := ofRep b) := rfl
@[simp] theorem ofSquare_inr (a b : Squares.Rep.{u}) :
    ofSquare (Squares.injectRight a b) = coproducts.inr (a := ofRep a) (b := ofRep b) := rfl
@[simp] theorem ofSquare_copair {a b c : Squares.Rep.{u}} (f : Squares.Square a c) (g : Squares.Square b c) :
    ofSquare (Squares.copair f g) = coproducts.copair (ofSquare f) (ofSquare g) := rfl
@[simp] theorem ofSquare_distribution (a b c : Squares.Rep.{u}) :
    ofSquare (Squares.distribution a b c) = distribution.distribute (a := ofRep a) (b := ofRep b) (c := ofRep c) := rfl
@[simp] theorem ofSquare_evaluation (a b : Squares.Rep.{u}) :
    ofSquare (Squares.evaluation a b) = closed.evaluation (a := ofRep a) (b := ofRep b) := rfl
@[simp] theorem ofSquare_curry {x a b : Squares.Rep.{u}} (f : Squares.Square (Squares.product x a) b) :
    ofSquare (Squares.curry f) = closed.curry (x := ofRep x) (a := ofRep a) (b := ofRep b) (ofSquare f) := rfl
@[simp] theorem ofSquare_uncurry {x a b : Squares.Rep.{u}} (f : Squares.Square x (Squares.exponential a b)) :
    ofSquare (Squares.uncurry f) = closed.uncurry (x := ofRep x) (a := ofRep a) (b := ofRep b) (ofSquare f) := rfl

theorem uncurry_curry {x a b : Squares.Rep.{u}} (f : Squares.Square (Squares.product x a) b) :
    Squares.uncurry (Squares.curry f) = f :=
  congrArg toSquare (closedLaws.beta (x := ofRep x) (a := ofRep a) (b := ofRep b) (ofSquare f))

theorem curry_uncurry {x a b : Squares.Rep.{u}} (f : Squares.Square x (Squares.exponential a b)) :
    Squares.curry (Squares.uncurry f) = f :=
  congrArg toSquare (closedLaws.eta (x := ofRep x) (a := ofRep a) (b := ofRep b) (ofSquare f))
theorem copair_left {a b c : Squares.Rep.{u}} (f : Squares.Square a c) (g : Squares.Square b c) :
    Squares.compose (Squares.copair f g) (Squares.injectLeft a b) = f :=
  congrArg toSquare (coproductLaws.left (ofSquare f) (ofSquare g))

theorem copair_right {a b c : Squares.Rep.{u}} (f : Squares.Square a c) (g : Squares.Square b c) :
    Squares.compose (Squares.copair f g) (Squares.injectRight a b) = g :=
  congrArg toSquare (coproductLaws.right (ofSquare f) (ofSquare g))

theorem copair_eta {a b c : Squares.Rep.{u}} (f : Squares.Square (Squares.coproduct a b) c) :
    Squares.copair (Squares.compose f (Squares.injectLeft a b))
      (Squares.compose f (Squares.injectRight a b)) = f :=
  congrArg toSquare (coproductLaws.eta (a := ofRep a) (b := ofRep b) (c := ofRep c) (ofSquare f))
end SquareKit.Comma.Exact
