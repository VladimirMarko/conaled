import SquareKit.SheafImage
import Mathlib.CategoryTheory.Sites.Limits
import Mathlib.CategoryTheory.Limits.Types.Pullbacks
import Mathlib.CategoryTheory.Limits.FunctorCategory.Basic

/-! Experimental substitution law for local existential images.
Categorical sheaf pullbacks give sectionwise pullbacks via limit preservation.
-/
namespace SquareKit.SheafImage
open CategoryTheory Opposite
universe u v w
variable {C : Type u} [Category.{v} C] {J : GrothendieckTopology C}
variable {A B A' B' : Sheaf J (Type w)}

/-- Evaluating a sheaf pullback gives a pullback of section types. -/
theorem sections_isPullback {g' : A' ⟶ A} {f' : A' ⟶ B'} {f : A ⟶ B} {g : B' ⟶ B}
    (h : IsPullback g' f' f g) (U : Cᵒᵖ) :
    IsPullback (g'.hom.app U) (f'.hom.app U) (f.hom.app U) (g.hom.app U) :=
  (h.map (sheafToPresheaf J (Type w))).map ((evaluation Cᵒᵖ (Type w)).obj U)

/-- Local existential images commute with substitution along a sheaf pullback.
Q is unrestricted and the witnesses on the covering sieve need not agree. -/
theorem beckChevalley (Q : Subfunctor A.obj)
    {g' : A' ⟶ A} {f' : A' ⟶ B'} {f : A ⟶ B} {g : B' ⟶ B}
    (h : IsPullback g' f' f g) :
    (localImage Q f).preimage g.hom = localImage (Q.preimage g'.hom) f' := by
  apply le_antisymm
  · intro U b hb
    apply J.superset_covering _ hb
    intro V k hk
    rcases hk with ⟨a, ha, he⟩
    have he' : f.hom.app (op V) a = g.hom.app (op V) (B'.obj.map k.op b) := by
      rw [NatTrans.naturality_apply]
      exact he
    obtain ⟨a', hg', hf'⟩ := Limits.Types.exists_of_isPullback (sections_isPullback h (op V))
      a (B'.obj.map k.op b) he'
    exact ⟨a', by change Q.obj _ (g'.hom.app _ a'); rw [hg']; exact ha, hf'⟩
  · intro U b hb
    apply J.superset_covering _ hb
    intro V k hk
    rcases hk with ⟨a', ha, he⟩
    refine ⟨g'.hom.app (op V) a', ha, ?_⟩
    have hw := congrArg (fun t => t.hom.app (op V) a') h.w
    change f.hom.app _ (g'.hom.app _ a') = g.hom.app _ (f'.hom.app _ a') at hw
    rw [hw, he, NatTrans.naturality_apply]

/-- Both predicates in Beck–Chevalley are closed, without closure of Q. -/
theorem beckChevalley_isSheaf (Q : Subfunctor A.obj)
    (g' : A' ⟶ A) (f' : A' ⟶ B') (f : A ⟶ B) (g : B' ⟶ B) :
    Presieve.IsSheaf J ((localImage Q f).preimage g.hom).toFunctor ∧
    Presieve.IsSheaf J (localImage (Q.preimage g'.hom) f').toFunctor :=
  ⟨preimage_isSheaf _ _ (localImage_isSheaf _ _), localImage_isSheaf _ _⟩

end SquareKit.SheafImage
