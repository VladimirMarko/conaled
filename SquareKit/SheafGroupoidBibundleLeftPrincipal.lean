import SquareKit.SheafGroupoidBibundleOpposite

/-! Left connectors, restriction and principality of the opposite. -/
noncomputable section
set_option autoImplicit false
set_option warningAsError true
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
namespace SquareKit.SheafGroupoid.Bibundle
open CategoryTheory Opposite SquareKit SquareKit.SheafGroupoid
open SquareKit.SheafGroupoid.Bundle SquareKit.SheafGroupoid.Bibundle
open scoped CategoryTheory.Pseudofunctor.StrongTrans
universe u v
variable {C : Type u} [Category.{v} C] {J : GrothendieckTopology C}
variable {G H : Operations J} [G.Laws] [H.Laws]
variable (P : Bibundle G H)

variable (hP : LeftPrincipal P)

def leftConnector {U : Cᵒᵖ} {x y : G.Section U} {k : H.Section U}
    (p : Fiber H G.objects P.right.family (atSection x) k)
    (q : Fiber H G.objects P.right.family (atSection y) k) : x ⟶ y :=
  (hP.principal x y k p q).choose

theorem leftConnector_spec {U : Cᵒᵖ} {x y : G.Section U} {k : H.Section U}
    (p : Fiber H G.objects P.right.family (atSection x) k)
    (q : Fiber H G.objects P.right.family (atSection y) k) :
    P.left.act (leftConnector P hP p q) k p = q :=
  (hP.principal x y k p q).choose_spec.1

theorem leftConnector_unique {U : Cᵒᵖ} {x y : G.Section U} {k : H.Section U}
    (p : Fiber H G.objects P.right.family (atSection x) k)
    (q : Fiber H G.objects P.right.family (atSection y) k)
    (g : x ⟶ y) (hg : P.left.act g k p = q) : g = leftConnector P hP p q :=
  (hP.principal x y k p q).choose_spec.2 g hg

theorem leftConnector_natural {U V : Cᵒᵖ} (f : U ⟶ V)
    {x y : G.Section U} {k : H.Section U}
    (p : Fiber H G.objects P.right.family (atSection x) k)
    (q : Fiber H G.objects P.right.family (atSection y) k) :
    (G.sectionRestriction f).map (leftConnector P hP p q) =
      leftConnector P hP
        (P.right.family.family.map (pointArrow H G.objects (ElementFamilies.along G.objects.obj f x.val) k) p)
        (P.right.family.family.map (pointArrow H G.objects (ElementFamilies.along G.objects.obj f y.val) k) q) := by
  apply leftConnector_unique
  rw [← P.left.natural, leftConnector_spec]

theorem leftConnector_rightAct {U : Cᵒᵖ} {x y : G.Section U} {k l : H.Section U}
    (g : k ⟶ l) (p : Fiber H G.objects P.right.family (atSection x) l)
    (q : Fiber H G.objects P.right.family (atSection y) l) :
    leftConnector P hP (P.right.act (atSection x) g p) (P.right.act (atSection y) g q) =
      leftConnector P hP p q := by
  symm
  apply leftConnector_unique
  rw [P.left.commute, leftConnector_spec]

theorem leftConnector_postact {U : Cᵒᵖ} {x y z : G.Section U} {k : H.Section U}
    (p : Fiber H G.objects P.right.family (atSection x) k)
    (q : Fiber H G.objects P.right.family (atSection y) k) (g : y ⟶ z) :
    leftConnector P hP p (P.left.act g k q) = leftConnector P hP p q ≫ g := by
  symm
  apply leftConnector_unique
  rw [← P.left.comp, leftConnector_spec]

theorem leftConnector_preact {U : Cᵒᵖ} {x y z : G.Section U} {k : H.Section U}
    (p : Fiber H G.objects P.right.family (atSection x) k)
    (q : Fiber H G.objects P.right.family (atSection y) k) (g : x ⟶ z) :
    leftConnector P hP (P.left.act g k p) q = Groupoid.inv g ≫ leftConnector P hP p q := by
  symm
  apply leftConnector_unique
  rw [← P.left.comp, P.left.comp g (Groupoid.inv g), Groupoid.comp_inv, P.left.identity,
    leftConnector_spec]

theorem opposite_leftPrincipal : LeftPrincipal (opposite P hP) where
  principal x y k p q := by
    obtain ⟨g,hg,hu⟩ := P.right.principal (atSection k) x y p q
    refine ⟨Groupoid.inv g, ?_, ?_⟩
    · change P.right.act (atSection k) (Groupoid.inv (Groupoid.inv g)) p = q
      simpa using hg
    · intro a ha
      have h := hu (Groupoid.inv a) ha
      simpa using congrArg Groupoid.inv h
  locallySurjective := by
    have : Presheaf.IsLocallySurjective J (oppositeTotalIso P).hom.hom := inferInstance
    change Presheaf.IsLocallySurjective J
      ((oppositeTotalIso P).hom.hom ≫ P.right.toAction.projection.hom)
    infer_instance

end SquareKit.SheafGroupoid.Bibundle
