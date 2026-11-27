import SquareKit.SheafGroupoidRegular

/-! The tautological map from a regular bundle to an arbitrary groupoid action. -/
noncomputable section
set_option autoImplicit false
set_option warningAsError true
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
namespace SquareKit.SheafGroupoid.Bundle
namespace Action
open CategoryTheory Opposite
universe u v
variable {C : Type u} [Category.{v} C] {J : GrothendieckTopology C}
variable {G : Operations J} [G.Laws] {X : Sheaf J (Type (max u v))}
variable (P : Action G X)

abbrev total := SplitSheaf.extension P.family
def anchor : total P ⟶ G.objects := SplitSheaf.p P.family ≫ SheafRelation.snd X G.objects
def localObject : G.Object (total P) := ⟨anchor P⟩

def localMapValue (x : (total P).obj.Elements) (a : G.Section x.obj)
    (g : Fiber G (total P) (regularFamily G (localObject P)) x a) :
    Fiber G (total P) (P.reindex P.projection).family x a :=
  P.act (X.obj.elementsMk x.obj x.val.1.1)
    (regularFiberEquiv G (localObject P) x a g) x.val.2

theorem localMapValue_restrict {U V : Cᵒᵖ} (k : U ⟶ V) (x : X.obj.obj U)
    (n a : G.Section U) (p : Fiber G X P.family (X.obj.elementsMk U x) n)
    (g : Fiber G (total P) (regularFamily G (localObject P))
      ((total P).obj.elementsMk U ⟨(x,n.val),p⟩) a) :
    let z := (total P).obj.elementsMk U ⟨(x,n.val),p⟩
    let l := ElementFamilies.along (total P).obj k z.val
    localMapValue P ((total P).obj.elementsMk V ((total P).obj.map k z.val)) (a.restrict G k)
        ((regularFamily G (localObject P)).family.map (pointArrow G (total P) l a) g) =
      (P.reindex P.projection).family.family.map (pointArrow G (total P) l a)
        (localMapValue P z a g) := by
  dsimp only
  let z := (total P).obj.elementsMk U ⟨(x,n.val),p⟩
  let l := ElementFamilies.along (total P).obj k z.val
  have he : regularFiberEquiv G (localObject P)
      ((total P).obj.elementsMk V ((total P).obj.map k z.val)) (a.restrict G k)
      ((regularFamily G (localObject P)).family.map (pointArrow G (total P) l a) g) =
    Operations.SectionArrow.restrict G k (regularFiberEquiv G (localObject P) z a g) := by
      apply Operations.Arrow.ext
      exact (regularFiberEquiv_natural_map G (localObject P) l a g).trans
        (Operations.SectionArrow.restrict_map G k (regularFiberEquiv G (localObject P) z a g)).symm
  change P.act (X.obj.elementsMk V (X.obj.map k x))
      (regularFiberEquiv G (localObject P)
      ((total P).obj.elementsMk V ((total P).obj.map k z.val)) (a.restrict G k)
        ((regularFamily G (localObject P)).family.map (pointArrow G (total P) l a) g))
      (P.family.family.map (pointArrow G X (ElementFamilies.along X.obj k x) n) p) =
    P.family.family.map (pointArrow G X (ElementFamilies.along X.obj k x) a)
      (P.act (X.obj.elementsMk U x) (regularFiberEquiv G (localObject P) z a g) p)
  rw [he]
  exact (P.natural (ElementFamilies.along X.obj k x) _ p).symm

/-- The tautological point acts on every regular arrow fiber. -/
def localFamilyMap : (regularFamily G (localObject P)).family ⟶
    (P.reindex P.projection).family.family where

    app z := ↾localMapValue P ((total P).obj.elementsMk z.obj z.val.1) ⟨z.val.2⟩
    naturality := by
      intro z w k
      apply ConcreteCategory.hom_ext
      intro g
      rcases z with @⟨U, ⟨⟨⟨x,n⟩,p⟩,a⟩⟩
      rcases w with @⟨V, ⟨y,b⟩⟩
      rcases k with ⟨k,hk⟩
      change U ⟶ V at k
      have hy : (total P).obj.map k ⟨(x,n),p⟩ = y := congrArg Prod.fst hk
      have hb : G.objects.obj.map k a = b := congrArg Prod.snd hk
      subst y; subst b
      exact localMapValue_restrict P k x ⟨n⟩ ⟨a⟩ p g

end Action
end SquareKit.SheafGroupoid.Bundle
