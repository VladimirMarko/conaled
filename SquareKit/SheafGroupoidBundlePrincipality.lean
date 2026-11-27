import SquareKit.SheafGroupoidActionLocal
import SquareKit.SplitSheafDescent
import SquareKit.SheafCover

/-! Principality of a groupoid action is local on the parameter. -/
noncomputable section
set_option autoImplicit false
set_option warningAsError true
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
namespace SquareKit.SheafGroupoid.Bundle.Action
open CategoryTheory Opposite
universe u v
variable {C : Type u} [Category.{v} C] {J : GrothendieckTopology C}
variable {G : Operations J} [G.Laws] {X : Sheaf J (Type (max u v))}
variable (Q : Action G X) (A : SplitSheaf.Ty X)
variable [hA : Presheaf.IsLocallySurjective J (SplitSheaf.p A).hom]
variable (hp : ∀ (x : X.obj.Elements), A.family.obj x →
  ∀ (m n : G.Section x.obj) (p : Fiber G X Q.family x m) (q : Fiber G X Q.family x n),
    ∃! g : n ⟶ m, Q.act x g p = q)

include hp hA
/-- The tautological map is an isomorphism when connector arrows exist uniquely
on a cover. This uses descent for ordinary sheaf displays. -/
theorem localFamilyMap_isIso_of_cover : IsIso (localFamilyMap Q) := by
  let B := SplitSheaf.tySub A (SheafRelation.fst (total Q) G.objects ≫ Q.projection)
  have : Presheaf.IsLocallySurjective J (SplitSheaf.p B).hom :=
    SheafCover.baseChangeCover_isLocallySurjective (A := A)
      (SheafRelation.fst (total Q) G.objects ≫ Q.projection)
  apply SplitSheafDescent.isIso_of_local_bijective B
    (S := regularFamily G (localObject Q)) (T := (Q.reindex Q.projection).family)
  intro z a
  rcases z with @⟨U, ⟨⟨⟨x,m⟩,p⟩,n⟩⟩
  let y := X.obj.elementsMk U x
  let t := (total Q).obj.elementsMk U ⟨(x,m),p⟩
  let e := regularFiberEquiv G (localObject Q) t ⟨n⟩
  change Function.Bijective (fun g => Q.act y (e g) p)
  constructor
  · intro g h he
    obtain ⟨k,_,hu⟩ := hp y a ⟨m⟩ ⟨n⟩ p (Q.act y (e g) p)
    apply e.injective
    exact (hu (e g) rfl).trans (hu (e h) he.symm).symm
  · intro q
    obtain ⟨g,hg,_⟩ := hp y a ⟨m⟩ ⟨n⟩ p q
    exact ⟨e.symm g, (congrArg (fun g => Q.act y g p) (e.apply_symm_apply g)).trans hg⟩

/-- Actual unique connector arrows descend, without a chosen lift of the cover. -/
theorem principal_of_cover (x : X.obj.Elements) (m n : G.Section x.obj)
    (p : Fiber G X Q.family x m) (q : Fiber G X Q.family x n) :
    ∃! g : n ⟶ m, Q.act x g p = q := by
  let := Q.localFamilyMap_isIso_of_cover A hp
  let t := (total Q).obj.elementsMk x.obj ⟨(x.val,m.val),p⟩
  let e := regularFiberEquiv G (localObject Q) t n
  let z := point G (total Q) t n
  let f := (localFamilyMap Q).app z
  let ei := (asIso f).toEquiv
  refine ⟨e (ei.symm q), ?_, ?_⟩
  · exact ei.apply_symm_apply q
  · intro g hg
    apply e.symm.injective
    have hh : f (e.symm g) = q := by
      change Q.act x (e (e.symm g)) p = q
      rw [e.apply_symm_apply]
      exact hg
    exact (ei.injective (hh.trans (ei.apply_symm_apply q).symm)).trans
      (e.symm_apply_apply (ei.symm q)).symm

end SquareKit.SheafGroupoid.Bundle.Action
