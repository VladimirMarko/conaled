import SquareKit.SheafBaseChange
import Mathlib.CategoryTheory.Limits.Shapes.BinaryProducts.ProdComparison

/-! Experimental ordinary closed relations on type-valued sheaves.
Products have explicit pair sections, compared to Mathlib's chosen product.
Composition uses local intermediate witnesses, with no syntax dependency.
-/
namespace SquareKit.SheafRelation
open CategoryTheory Opposite Limits
universe u v w
variable {C : Type u} [Category.{v} C] {J : GrothendieckTopology C}

def productData (A B : Sheaf J (Type w)) : Cᵒᵖ ⥤ Type w where
  obj U := A.obj.obj U × B.obj.obj U
  map f := ↾fun p => (A.obj.map f p.1, B.obj.map f p.2)
  map_id U := by ext p <;> simp
  map_comp f g := by ext p <;> simp

theorem product_isSheaf (A B : Sheaf J (Type w)) : Presieve.IsSheaf J (productData A B) := by
  classical
  intro U R hR x hx
  let xa : Presieve.FamilyOfElements A.obj R.arrows := fun {_} f hf => (x f hf).1
  let xb : Presieve.FamilyOfElements B.obj R.arrows := fun {_} f hf => (x f hf).2
  have ha : xa.Compatible := by
    intro V W Z f g i j hi hj he
    exact congrArg Prod.fst (hx f g hi hj he)
  have hb : xb.Compatible := by
    intro V W Z f g i j hi hj he
    exact congrArg Prod.snd (hx f g hi hj he)
  obtain ⟨a, ha, hua⟩ := ((isSheaf_iff_isSheaf_of_type _ _).mp A.property) R hR xa ha
  obtain ⟨b, hb, hub⟩ := ((isSheaf_iff_isSheaf_of_type _ _).mp B.property) R hR xb hb
  refine ⟨(a,b), ?_, ?_⟩
  · intro V f hf; exact Prod.ext (ha f hf) (hb f hf)
  · intro p hp
    exact Prod.ext (hua p.1 (fun {_} f hf => congrArg Prod.fst (hp f hf)))
      (hub p.2 (fun {_} f hf => congrArg Prod.snd (hp f hf)))

abbrev product (A B : Sheaf J (Type w)) : Sheaf J (Type w) :=
  ⟨productData A B, (isSheaf_iff_isSheaf_of_type _ _).mpr (product_isSheaf A B)⟩

def fst (A B : Sheaf J (Type w)) : product A B ⟶ A := ⟨{ app _ := ↾Prod.fst }⟩
def snd (A B : Sheaf J (Type w)) : product A B ⟶ B := ⟨{ app _ := ↾Prod.snd }⟩

def lift {A B D : Sheaf J (Type w)} (f : D ⟶ A) (g : D ⟶ B) : D ⟶ product A B :=
  ⟨{ app U := ↾fun x => (f.hom.app U x, g.hom.app U x)
     naturality := by
       intro U V k; ext x
       change (f.hom.app V (D.obj.map k x), g.hom.app V (D.obj.map k x)) =
         (A.obj.map k (f.hom.app U x), B.obj.map k (g.hom.app U x))
       exact Prod.ext (NatTrans.naturality_apply f.hom k x) (NatTrans.naturality_apply g.hom k x) }⟩

/-- Comparison retains the actual first and second projections. -/
noncomputable def productIso (A B : Sheaf J (Type w)) : product A B ≅ Limits.prod A B where
  hom := Limits.prod.lift (fst A B) (snd A B)
  inv := lift Limits.prod.fst Limits.prod.snd
  hom_inv_id := by
    ext U p
    apply Prod.ext
    · exact congrArg (fun (f : product A B ⟶ A) => f.hom.app U p) (Limits.prod.lift_fst _ _)
    · exact congrArg (fun (f : product A B ⟶ B) => f.hom.app U p) (Limits.prod.lift_snd _ _)
  inv_hom_id := by
    apply Limits.prod.hom_ext <;> simp only [Category.assoc, Limits.prod.lift_fst,
      Limits.prod.lift_snd, Category.id_comp]
    · rfl
    · rfl

theorem productIso_fst (A B : Sheaf J (Type w)) :
    (productIso A B).hom ≫ Limits.prod.fst = fst A B := Limits.prod.lift_fst _ _

theorem productIso_snd (A B : Sheaf J (Type w)) :
    (productIso A B).hom ≫ Limits.prod.snd = snd A B := Limits.prod.lift_snd _ _

abbrev Relation (A B : Sheaf J (Type w)) := Subfunctor (product A B).obj

variable {A B D : Sheaf J (Type w)}

/-- Triples are parenthesized as (intermediate, (source, target)). -/
def firstPair : product B (product A D) ⟶ product A B :=
  lift (snd _ _ ≫ fst _ _) (fst _ _)
def secondPair : product B (product A D) ⟶ product B D :=
  lift (fst _ _) (snd _ _ ≫ snd _ _)
def endpoints : product B (product A D) ⟶ product A D := snd _ _

def joined (R : Relation A B) (S : Relation B D) : Subfunctor (product B (product A D)).obj :=
  R.preimage firstPair.hom ⊓ S.preimage secondPair.hom

/-- Apply R first and S second, with locally existing intermediate sections. -/
def comp (R : Relation A B) (S : Relation B D) : Relation A D :=
  SheafImage.localImage (joined R S) endpoints

theorem comp_isSheaf (R : Relation A B) (S : Relation B D) :
    Presieve.IsSheaf J (comp R S).toFunctor := SheafImage.localImage_isSheaf _ _

def witnessSieve (R : Relation A B) (S : Relation B D) {U : Cᵒᵖ}
    (p : (product A D).obj.obj U) : Sieve U.unop :=
  ((joined R S).image endpoints.hom).sieveOfSection p

theorem mem_comp (R : Relation A B) (S : Relation B D) {U : Cᵒᵖ}
    (p : (product A D).obj.obj U) :
    (comp R S).obj U p ↔ witnessSieve R S p ∈ J U.unop := Iff.rfl

theorem witness_comp (R : Relation A B) (S : Relation B D) {U V : C} (f : V ⟶ U)
    (a : A.obj.obj (op U)) (d : D.obj.obj (op U)) :
    witnessSieve R S (a,d) f ↔ ∃ b : B.obj.obj (op V),
      R.obj (op V) (A.obj.map f.op a,b) ∧ S.obj (op V) (b,D.obj.map f.op d) := by
  constructor
  · rintro ⟨⟨b,a',d'⟩, ⟨hr,hs⟩, he⟩
    cases he
    exact ⟨b,hr,hs⟩
  · rintro ⟨b,hr,hs⟩
    exact ⟨(b,A.obj.map f.op a,D.obj.map f.op d), ⟨hr,hs⟩, rfl⟩

end SquareKit.SheafRelation
