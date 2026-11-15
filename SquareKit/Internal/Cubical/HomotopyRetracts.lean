import SquareKit.Internal.Cubical.UniverseFilling
import SquareKit.Internal.Cubical.PathFilling

/-! Native concatenation and contraction of a homotopy retract. -/
set_option autoImplicit false
set_option warningAsError true
namespace SquareKit.Cubical.Presheaf
open CategoryTheory
universe u

namespace NativeConcat
variable {Γ : Context.{u}} {A : Family Γ} {a b c : Term A}
  (q : Term (homogeneousPath A b c))

abbrev line := homogeneousPath (reindex A (projection (interval Γ)))
  (a.reindex (projection (interval Γ))) (pathApp q)

def endpointIso (ε : Bool) :
    reindex (line (a := a) q) (endpointSub Γ ε) ≅
      homogeneousPath A a ((pathApp q).reindex (endpointSub Γ ε)) :=
  pathReindexIso _ _ _ (endpointSub Γ ε)

def startIso : reindex (line (a := a) q) (endpointSub Γ false) ≅ homogeneousPath A a b :=
  endpointIso q false ≪≫ eqToIso (congrArg (homogeneousPath A a) (pathApp_zero q))

def finishIso : reindex (line (a := a) q) (endpointSub Γ true) ≅ homogeneousPath A a c :=
  endpointIso q true ≪≫ eqToIso (congrArg (homogeneousPath A a) (pathApp_one q))

noncomputable def filling (F : Filling A) (hF : F.Lawful) : Filling (line (a := a) q) :=
  pathFilling (F.reindex (projection (interval (total (interval Γ))) ≫ projection (interval Γ)))
    (hF.reindex _) (a.reindex (projection (interval Γ))) (pathApp q)

end NativeConcat

/-- Concatenation is constructed by filling the family of paths with moving
right endpoint; it is not a postulated operation on native paths. -/
noncomputable def homogeneousConcat {Γ : Context.{u}} {A : Family Γ}
    (F : Filling A) (hF : F.Lawful) {a b c : Term A}
    (p : Term (homogeneousPath A a b)) (q : Term (homogeneousPath A b c)) :
    Term (homogeneousPath A a c) :=
  Term.map ((NativeConcat.startIso q).inv ≫
    IntervalTransport.map (NativeConcat.filling q F hF) ≫ (NativeConcat.finishIso q).hom) p

/-- A native homotopy retract of a contractible family is contractible. The
specified retraction homotopy is composed with the transported contraction. -/
noncomputable def HomotopyContractible.retract {Γ : Context.{u}} {A B : Family Γ}
    (c : HomotopyContractible A) (F : Filling B) (hF : F.Lawful)
    (f : A ⟶ B) (g : B ⟶ A)
    (h : Term (homogeneousPath (Presheaf.reindex B (projection B))
      (Term.map (Functor.whiskerLeft (projection B).mapElements f)
        (Term.map (Functor.whiskerLeft (projection B).mapElements g) (generic B)))
      (generic B))) : HomotopyContractible B where
  center := Term.map f c.center
  contraction := homogeneousConcat (F.reindex (projection B)) (hF.reindex _)
    (homogeneousPathMap (Functor.whiskerLeft (projection B).mapElements f)
      ((c.reindex (projection B)).pathTo
        (Term.map (Functor.whiskerLeft (projection B).mapElements g) (generic B)))) h

end SquareKit.Cubical.Presheaf
