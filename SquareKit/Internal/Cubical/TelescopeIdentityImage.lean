import SquareKit.Internal.Cubical.NormalizedTelescopeIdentitySubstitution

namespace SquareKit.Cubical.Presheaf
open CategoryTheory
universe u
namespace NormalizedTelescopeIdentityElimination
open NormalizedIdentitySingleton

def Generated {Γ : Context.{u}} (A : Family Γ) (a : Term A) (T : Telescope (context A a))
    (C : Family T.context) (fs : T.Fillings) (hs : fs.Lawful) (G : Filling C) (t : Term C) : Prop :=
  ∃ d : Term (reindex C (T.map (reflexivity A a))), t = eliminate A a T C d fs hs G

theorem generated_eliminate {Γ : Context.{u}} (A : Family Γ) (a : Term A) (T : Telescope (context A a))
    (C : Family T.context) (d : Term (reindex C (T.map (reflexivity A a))))
    (fs : T.Fillings) (hs : fs.Lawful) (G : Filling C) :
    Generated A a T C fs hs G (eliminate A a T C d fs hs G) := ⟨d,rfl⟩

theorem generated_reindex {Γ Δ : Context.{u}} (A : Family Γ) (a : Term A) (T : Telescope (context A a))
    (C : Family T.context) (fs : T.Fillings) (hs : fs.Lawful) (G : Filling C) (hG : G.Lawful)
    (t : Term C) (ht : Generated A a T C fs hs G t) (σ : Δ ⟶ Γ) :
    Generated (reindex A σ) (a.reindex σ) (substitutedTail A a T σ) (substitutedMotive A a T C σ)
      (fs.reindex (reindexMap A a σ)) (hs.reindex _) (G.reindex (T.map (reindexMap A a σ)))
      (t.reindex (T.map (reindexMap A a σ))) := by
  obtain ⟨d,rfl⟩ := ht
  exact ⟨substitutedBranch A a T C d σ,(eliminate_reindex A a T C d σ fs hs G hG).symm⟩

theorem generated_heq {Γ : Context.{u}} (A : Family Γ) (a : Term A)
    {T U : Telescope (context A a)} (hT : T = U)
    {C : Family T.context} {D : Family U.context} (hC : HEq C D)
    {fs : T.Fillings} {gs : U.Fillings} (hfs : HEq fs gs)
    (hs : fs.Lawful) (hg : gs.Lawful) {F : Filling C} {G : Filling D} (hF : HEq F G)
    {t : Term C} {s : Term D} (ht : HEq t s) :
    Generated A a T C fs hs F t ↔ Generated A a U D gs hg G s := by
  cases hT
  cases hC
  cases hfs
  cases hF
  cases ht
  rfl

end NormalizedTelescopeIdentityElimination
end SquareKit.Cubical.Presheaf
