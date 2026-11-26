import SquareKit.Internal.Cubical.CocycleComparisonValues
import SquareKit.Internal.Cubical.IdentityMaps

/-! Evaluation of typed higher comparisons, allowing a non-reflexive lower loop. -/
noncomputable section
namespace SquareKit.Cubical.CategoryCocycles
open CategoryTheory Presheaf
variable {Γ : Context.{0}} {v : Term (firstIdentityFamily Γ)}
abbrev loopSquareFamily (v : Term (firstIdentityFamily Γ)) := normalizedIdentity (firstIdentityFamily Γ) v v

def loopSquareElementValue {x : Γ.Elements} (p : (loopSquareFamily v).obj x)
    (r s : (interval Γ).obj x) : CubeCocycle x.obj.unop := (p.eval r).eval s

def loopSquareValue (p : Term (loopSquareFamily v)) (x : Γ.Elements)
    (r s : (interval Γ).obj x) : CubeCocycle x.obj.unop := loopSquareElementValue (p.val x) r s

theorem loopSquareElementValue_map {x y : Γ.Elements} (f : x ⟶ y)
    (p : (loopSquareFamily v).obj x) (r s : (interval Γ).obj x) :
    cocycles.map f.hom (loopSquareElementValue p r s) =
      loopSquareElementValue ((loopSquareFamily v).map f p) ((interval Γ).map f r) ((interval Γ).map f s) :=
  (LocalIdentity.eval_map f (p.eval r) s).trans
    (congrArg (fun q : (firstIdentityFamily Γ).obj y => q.eval ((interval Γ).map f s))
      (LocalIdentity.eval_map f p r))

theorem loopSquareValue_map (p : Term (loopSquareFamily v)) {x y : Γ.Elements}
    (f : x ⟶ y) (r s : (interval Γ).obj x) :
    cocycles.map f.hom (loopSquareValue p x r s) =
      loopSquareValue p y ((interval Γ).map f r) ((interval Γ).map f s) :=
  (loopSquareElementValue_map f (p.val x) r s).trans
    (congrArg (fun q => loopSquareElementValue q ((interval Γ).map f r) ((interval Γ).map f s)) (p.property f))

theorem loopSquareElementValue_root {x : Γ.Elements} (p : (loopSquareFamily v).obj x)
    (s : (interval Γ).obj x) (e : Bool) :
    loopSquareElementValue p ((endpoint Γ e).val x) s = (v.val x).eval s := by
  cases e
  · exact congrArg (fun q : (firstIdentityFamily Γ).obj x => q.eval s) p.eval_zero
  · exact congrArg (fun q : (firstIdentityFamily Γ).obj x => q.eval s) p.eval_one

theorem loopSquareElementValue_side {x : Γ.Elements} (p : (loopSquareFamily v).obj x)
    (r : (interval Γ).obj x) (e : Bool) :
    loopSquareElementValue p r ((endpoint Γ e).val x) = zeroCocycle (Over x.obj.unop) := by
  cases e
  · exact (p.eval r).eval_zero
  · exact (p.eval r).eval_one

def bridgeValue {a b : Term (loopSquareFamily v)}
    (H : Term (normalizedIdentity (loopSquareFamily v) a b)) (x : Γ.Elements)
    (r s z : (interval Γ).obj x) : CubeCocycle x.obj.unop :=
  loopSquareElementValue ((H.val x).eval s) r z

theorem bridgeValue_map {a b : Term (loopSquareFamily v)}
    (H : Term (normalizedIdentity (loopSquareFamily v) a b)) {x y : Γ.Elements}
    (f : x ⟶ y) (r s z : (interval Γ).obj x) :
    cocycles.map f.hom (bridgeValue H x r s z) =
      bridgeValue H y ((interval Γ).map f r) ((interval Γ).map f s) ((interval Γ).map f z) := by
  have e := (LocalIdentity.eval_map f (H.val x) s).trans
    (congrArg (fun p : (normalizedIdentity (loopSquareFamily v) a b).obj y =>
      p.eval ((interval Γ).map f s)) (H.property f))
  exact (loopSquareElementValue_map f ((H.val x).eval s) r z).trans
    (congrArg (fun p => loopSquareElementValue p ((interval Γ).map f r) ((interval Γ).map f z)) e)

theorem bridgeValue_start {a b : Term (loopSquareFamily v)}
    (H : Term (normalizedIdentity (loopSquareFamily v) a b)) (x : Γ.Elements)
    (r z : (interval Γ).obj x) :
    bridgeValue H x r ((endpoint Γ false).val x) z = loopSquareValue a x r z :=
  congrArg (fun p => loopSquareElementValue p r z) (H.val x).eval_zero

theorem bridgeValue_finish {a b : Term (loopSquareFamily v)}
    (H : Term (normalizedIdentity (loopSquareFamily v) a b)) (x : Γ.Elements)
    (r z : (interval Γ).obj x) :
    bridgeValue H x r ((endpoint Γ true).val x) z = loopSquareValue b x r z :=
  congrArg (fun p => loopSquareElementValue p r z) (H.val x).eval_one

theorem bridgeValue_root {a b : Term (loopSquareFamily v)}
    (H : Term (normalizedIdentity (loopSquareFamily v) a b)) (x : Γ.Elements)
    (s z : (interval Γ).obj x) (e : Bool) :
    bridgeValue H x ((endpoint Γ e).val x) s z = (v.val x).eval z :=
  loopSquareElementValue_root ((H.val x).eval s) z e

theorem bridgeValue_side {a b : Term (loopSquareFamily v)}
    (H : Term (normalizedIdentity (loopSquareFamily v) a b)) (x : Γ.Elements)
    (r s : (interval Γ).obj x) (e : Bool) :
    bridgeValue H x r s ((endpoint Γ e).val x) = zeroCocycle (Over x.obj.unop) :=
  loopSquareElementValue_side ((H.val x).eval s) r e

variable (t : Term (reindex (firstIdentityFamily Γ) (projection (firstIdentityFamily Γ))))
abbrev mappedPoint := (firstIdentityPoint Γ).map (sectionMap t)
def mappedHigher (h : Term (secondIdentityFamily Γ)) : Term (loopSquareFamily (mappedPoint t)) :=
  h.map (normalizedIdentityMap (sectionMap t) (firstIdentityPoint Γ) (firstIdentityPoint Γ))

theorem mappedHigher_value (h : Term (secondIdentityFamily Γ)) (x : Γ.Elements)
    (r s : (interval Γ).obj x) : loopSquareValue (mappedHigher t h) x r s = actionValue (t := t) h x r s :=
  congrArg (fun p : (firstIdentityFamily Γ).obj x => p.eval s)
    (normalizedIdentityMap_eval (sectionMap t) (h.val x) r)

end SquareKit.Cubical.CategoryCocycles
