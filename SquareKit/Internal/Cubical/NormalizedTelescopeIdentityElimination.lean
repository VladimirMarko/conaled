import SquareKit.Internal.Cubical.TelescopeFilling
import SquareKit.Internal.Cubical.NormalizedIdentityElimination

/-! Normalized identity elimination under arbitrary finite dependent tails. Iterated
products bind the tail, and their constructed filling supplies the motive. -/
namespace SquareKit.Cubical.Presheaf
open CategoryTheory
universe u
namespace NormalizedTelescopeIdentityElimination
open NormalizedIdentitySingleton
variable {Γ : Context.{u}} (A : Family Γ) (a : Term A)
  (T : Telescope (context A a)) (C : Family T.context)
  (d : Term (reindex C (T.map (reflexivity A a))))

def branch : Term (reindex (T.pi C) (reflexivity A a)) :=
  ((T.reindex (reflexivity A a)).abstract d).convert (T.pi_reindex C (reflexivity A a)).symm

noncomputable def eliminate (fs : T.Fillings) (hs : fs.Lawful) (G : Filling C) : Term C :=
  T.apply (NormalizedIdentityElimination.eliminate A a (T.pi C) (branch A a T C d)
    (fs.pi hs G).toComposition)

theorem eliminate_beta (fs : T.Fillings) (hs : fs.Lawful) (G : Filling C) (hG : G.Lawful) :
    (eliminate A a T C d fs hs G).reindex (T.map (reflexivity A a)) = d := by
  let j := NormalizedIdentityElimination.eliminate A a (T.pi C) (branch A a T C d) (fs.pi hs G).toComposition
  have hj := NormalizedIdentityElimination.eliminate_beta A a (T.pi C) (branch A a T C d)
    (fs.pi hs G).toComposition (Filling.toComposition_lawful (fs.pi_lawful hs G hG))
  calc
    _ = (T.reindex (reflexivity A a)).apply
        ((j.reindex (reflexivity A a)).convert (T.pi_reindex C (reflexivity A a))) :=
      (T.apply_reindex j (reflexivity A a)).symm
    _ = (T.reindex (reflexivity A a)).apply
        ((branch A a T C d).convert (T.pi_reindex C (reflexivity A a))) :=
      congrArg (fun t => (T.reindex (reflexivity A a)).apply
        (t.convert (T.pi_reindex C (reflexivity A a)))) hj
    _ = d :=
      (congrArg (T.reindex (reflexivity A a)).apply
        (Term.convert_symm (T.pi_reindex C (reflexivity A a)).symm _)).trans
          ((T.reindex (reflexivity A a)).apply_abstract d)

end NormalizedTelescopeIdentityElimination
end SquareKit.Cubical.Presheaf
