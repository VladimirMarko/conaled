import SquareKit.Internal.Cubical.IdentitySingleton
import SquareKit.Internal.Cubical.Composition

/-! Eliminate marked identities by actual motive composition. The marked face
supplies the branch tube and forces strict computation at reflexivity. -/
namespace SquareKit.Cubical.Presheaf
open CategoryTheory
universe u

namespace IdentityElimination
variable {Γ : Context.{u}} (A : Family Γ) (a : Term A)
  (C : Family (IdentitySingleton.context A a))
  (d : Term (reindex C (IdentitySingleton.reflexivity A a)))

open IdentitySingleton

def tube : PartialSection (reindex C (contraction A a))
    ((markedFace A a).reindex (projection (interval (context A a)))) :=
  PartialSection.ofRestricted
    ((d.reindex (restrictInclusion ((markedFace A a).reindex (projection (interval (context A a)))) ≫
      projection (interval (context A a)) ≫ base A a)).convert
      (congrArg (fun σ => reindex C σ) (contraction_full A a).symm))

def cap : Term (reindex C (endpointSub (context A a) false ≫ contraction A a)) :=
  (d.reindex (base A a)).convert (congrArg (fun σ => reindex C σ) (contraction_zero A a).symm)

def box : OpenBox (reindex C (contraction A a)) (markedFace A a) where
  tube := tube A a C d
  base := cap A a C d
  boundary x h := by
    apply eq_of_heq
    exact (Term.convert_val_heq _ _ _).trans (Term.convert_val_heq _ (d.reindex (base A a)) x).symm

theorem tube_val_heq (x : (total (interval (context A a))).Elements)
    (hx : ((markedFace A a).reindex (projection (interval (context A a)))).full x) :
    HEq ((tube A a C d).val x hx)
      (d.val ((projection (interval (context A a)) ≫ base A a).mapElements.obj x)) :=
  Term.convert_val_heq _ _ _

theorem cap_val_heq (x : (context A a).Elements) :
    HEq ((cap A a C d).val x) (d.val ((base A a).mapElements.obj x)) :=
  Term.convert_val_heq _ _ _

def eliminate (G : Composition C) : Term C :=
  (G.comp (contraction A a) (markedFace A a) (box A a C d)).convert
    (congrArg (fun σ => reindex C σ) (contraction_one A a))

theorem eliminate_beta (G : Composition C) (hG : G.Lawful) :
    (eliminate A a C d G).reindex (reflexivity A a) = d := by
  apply Term.ext
  intro x
  apply eq_of_heq
  apply (Term.convert_val_heq _ _ ((reflexivity A a).mapElements.obj x)).trans
  have h := hG.boundary (contraction A a) (markedFace A a) (box A a C d)
    ((reflexivity A a).mapElements.obj x) (show (markedFace A a).full
      ((reflexivity A a).mapElements.obj x) from rfl)
  apply (heq_of_eq h).trans
  exact Term.convert_val_heq _ _ _

end IdentityElimination
end SquareKit.Cubical.Presheaf
