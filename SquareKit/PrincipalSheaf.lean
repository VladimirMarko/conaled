import Mathlib.Algebra.Category.Grp.Limits
import Mathlib.CategoryTheory.Sites.Sheaf

/-! Principal actions on a sheaf, specified by section operations and local inhabitation. -/
noncomputable section
set_option autoImplicit false
set_option warningAsError true
namespace SquareKit.PrincipalSheaf
open CategoryTheory Opposite
universe u v w
variable {C : Type u} [Category.{v} C] {J : GrothendieckTopology C}

/-- Restricting an inhabited section gives an inhabited section. -/
def inhabitedSieve (Q : Sheaf J (Type w)) (X : C) : Sieve X where
  arrows {Y} _ := Nonempty (Q.obj.obj (op Y))
  downward_closed := by
    rintro Y Z f ⟨s⟩ g
    exact ⟨Q.obj.map g.op s⟩

/-- Primitive principal-action laws; local inhabitation need not give a global point. -/
structure Structure (G : Sheaf J GrpCat.{w}) (Q : Sheaf J (Type w)) where
  act (X : Cᵒᵖ) : G.obj.obj X → Q.obj.obj X → Q.obj.obj X
  one_act (X) (p : Q.obj.obj X) : act X 1 p = p
  mul_act (X) (g h : G.obj.obj X) (p) : act X (g * h) p = act X g (act X h p)
  natural {X Y} (f : X ⟶ Y) (g) (p) :
    Q.obj.map f (act X g p) = act Y (G.obj.map f g) (Q.obj.map f p)
  principal (X) (p q : Q.obj.obj X) : ∃! g, act X g p = q
  locallyInhabited (X : C) : inhabitedSieve Q X ∈ J X

@[ext] theorem Structure.ext {G : Sheaf J GrpCat.{w}} {Q : Sheaf J (Type w)}
    {A B : Structure G Q} (h : ∀ X g p, A.act X g p = B.act X g p) : A = B := by
  cases A
  cases B
  congr
  funext X g p
  exact h X g p

variable {G : Sheaf J GrpCat.{w}} {Q R : Sheaf J (Type w)}

/-- Every equivariant sheaf map is admitted, without supplied inverse data. -/
def Equivariant (A : Structure G Q) (B : Structure G R) (f : Q ⟶ R) : Prop :=
  ∀ X g p, f.hom.app X (A.act X g p) = B.act X g (f.hom.app X p)

/-- The unique group section carrying the first section to the second. -/
def division (A : Structure G Q) (X : Cᵒᵖ) (p q : Q.obj.obj X) : G.obj.obj X :=
  (A.principal X p q).choose

theorem division_act (A : Structure G Q) (X : Cᵒᵖ) (p q : Q.obj.obj X) :
    A.act X (division A X p q) p = q := (A.principal X p q).choose_spec.1

theorem division_unique (A : Structure G Q) (X : Cᵒᵖ) (p q : Q.obj.obj X)
    (g : G.obj.obj X) (h : A.act X g p = q) : g = division A X p q :=
  (A.principal X p q).choose_spec.2 g h

theorem division_natural (A : Structure G Q) {X Y : Cᵒᵖ} (f : X ⟶ Y)
    (p q : Q.obj.obj X) :
    G.obj.map f (division A X p q) = division A Y (Q.obj.map f p) (Q.obj.map f q) := by
  apply division_unique
  rw [← A.natural, division_act]

/-- Transfer primitive structure along an isomorphism of the underlying sheaf. -/
def transport (A : Structure G Q) (e : R ≅ Q) : Structure G R where
  act X g p := e.inv.hom.app X (A.act X g (e.hom.hom.app X p))
  one_act X p := by
    rw [A.one_act]
    exact congrArg (fun h : R ⟶ R => h.hom.app X p) e.hom_inv_id
  mul_act X g h p := by
    rw [A.mul_act]
    congr 1
    rw [← types_comp_apply (e.inv.hom.app X) (e.hom.hom.app X),
      ← NatTrans.comp_app, ← ObjectProperty.FullSubcategory.comp_hom]
    simp
  natural f g p := by
    rw [← NatTrans.naturality_apply, A.natural, NatTrans.naturality_apply]
  principal X p q := by
    obtain ⟨g, hg, hu⟩ := A.principal X (e.hom.hom.app X p) (e.hom.hom.app X q)
    refine ⟨g, ?_, ?_⟩
    · change e.inv.hom.app X (A.act X g (e.hom.hom.app X p)) = q
      rw [hg]
      exact congrArg (fun h : R ⟶ R => h.hom.app X q) e.hom_inv_id
    · intro h hh
      apply hu
      apply_fun e.hom.hom.app X at hh
      have he := congrArg (fun f : Q ⟶ Q => f.hom.app X
        (A.act X h (e.hom.hom.app X p))) e.inv_hom_id
      exact he.symm.trans hh
  locallyInhabited X := by
    apply J.superset_covering ?_ (A.locallyInhabited X)
    rintro Y f ⟨s⟩
    exact ⟨e.inv.hom.app (op Y) s⟩

end SquareKit.PrincipalSheaf
