import Mathlib.CategoryTheory.Whiskering
import SquareKit.SplitFunctionTerms
import SquareKit.SplitSheaf
import SquareKit.SheafFunction

/-! Experimental sheaf condition for dependent natural functions. The auxiliary
sum diagram is used only to express dependent sections as an equalizer. -/
noncomputable section
namespace SquareKit.SplitFunctionSheaf
open CategoryTheory Limits Opposite ElementFamilies SplitFunctionDiagram
universe u v w
variable {C : Type u} [Category.{v} C] {J : GrothendieckTopology C}
variable {Γ : Sheaf J (Type (max u v))}

abbrev sumFamily (A : SplitSheaf.Ty Γ) (B : SplitSheaf.Ty (SplitSheaf.Ext A)) :=
  total A.family (totalDiagram A.family (𝟭 Γ.obj.Elements) ⋙ B.family)

/-- Flattening the two actual dependent pairs preserves their restrictions. -/
def flatten (A : SplitSheaf.Ty Γ) (B : SplitSheaf.Ty (SplitSheaf.Ext A)) :
    SplitPresheaf.Ext (sumFamily A B) ≅ (SplitSheaf.Ext B).obj where
  hom.app U := ↾fun x => ⟨⟨x.1,x.2.1⟩,x.2.2⟩
  hom.naturality {U V} f := by
    apply ConcreteCategory.hom_ext
    intro x
    rfl
  inv.app U := ↾fun x => ⟨x.1.1,⟨x.1.2,x.2⟩⟩
  inv.naturality {U V} f := by
    apply ConcreteCategory.hom_ext
    intro x
    rfl
  hom_inv_id := rfl
  inv_hom_id := rfl

def sumType (A : SplitSheaf.Ty Γ) (B : SplitSheaf.Ty (SplitSheaf.Ext A)) : SplitSheaf.Ty Γ where
  family := sumFamily A B
  isSheaf := (Presheaf.isSheaf_of_iso_iff (flatten A B)).2 (SplitSheaf.Ext B).property

abbrev argument (A : SplitSheaf.Ty Γ) := SplitSheaf.elementSheaf A
abbrev result (A : SplitSheaf.Ty Γ) (B : SplitSheaf.Ty (SplitSheaf.Ext A)) :=
  SplitSheaf.elementSheaf (sumType A B)

def projection (A : SplitSheaf.Ty Γ) (B : SplitSheaf.Ty (SplitSheaf.Ext A)) : result A B ⟶ argument A :=
  ⟨Functor.whiskerLeft (opOpEquivalence Γ.obj.Elements).functor
    (display A.family (totalDiagram A.family (𝟭 Γ.obj.Elements) ⋙ B.family))⟩


/-- The equalizer predicate is local because its target is separated. -/
def equalizerData {D : Type*} [Category D] {K : GrothendieckTopology D}
    {X Y : Sheaf K (Type w)} (f g : X ⟶ Y) : Subfunctor X.obj where
  obj U := {x | f.hom.app U x = g.hom.app U x}
  map := by
    intro U V k x hx
    change f.hom.app V (X.obj.map k x) = g.hom.app V (X.obj.map k x)
    rw [NatTrans.naturality_apply, NatTrans.naturality_apply, hx]

theorem equalizer_isSheaf {D : Type*} [Category D] {K : GrothendieckTopology D}
    {X Y : Sheaf K (Type w)} (f g : X ⟶ Y) :
    Presieve.IsSheaf K (equalizerData f g).toFunctor := by
  apply (Subfunctor.isSheaf_iff _ ((isSheaf_iff_isSheaf_of_type _ _).1 X.property)).2
  intro U x hx
  apply (((isSheaf_iff_isSheaf_of_type _ _).1 Y.property) _ hx).isSeparatedFor.ext
  intro V k hk
  change f.hom.app _ (X.obj.map k.op x) = g.hom.app _ (X.obj.map k.op x) at hk
  simpa only [NatTrans.naturality_apply] using hk

abbrev functions (A : SplitSheaf.Ty Γ) (B : SplitSheaf.Ty (SplitSheaf.Ext A)) :=
  SheafFunction.exponential (argument A) (result A B)
abbrev endomorphisms (A : SplitSheaf.Ty Γ) := SheafFunction.exponential (argument A) (argument A)

def post (A : SplitSheaf.Ty Γ) (B : SplitSheaf.Ty (SplitSheaf.Ext A)) :
    functions A B ⟶ endomorphisms A := (ihom (argument A)).map (projection A B)

def identity (A : SplitSheaf.Ty Γ) (B : SplitSheaf.Ty (SplitSheaf.Ext A)) :
    functions A B ⟶ endomorphisms A :=
  ⟨{ app _ := ↾fun _ => Functor.HomObj.id _ }⟩

/-- Natural functions whose projection is the actual input are dependent sections. -/
abbrev sectionData (A : SplitSheaf.Ty Γ) (B : SplitSheaf.Ty (SplitSheaf.Ext A)) :=
  equalizerData (post A B) (identity A B)

abbrev sections (A : SplitSheaf.Ty Γ) (B : SplitSheaf.Ty (SplitSheaf.Ext A)) :
    SheafSlice.ElementSheaves Γ :=
  ⟨(sectionData A B).toFunctor,
    (isSheaf_iff_isSheaf_of_type _ _).2 (equalizer_isSheaf (post A B) (identity A B))⟩


/-- A dependent function gives a function into the dependent total with fixed input. -/
def functionValue (A : SplitSheaf.Ty Γ) (B : SplitSheaf.Ty (SplitSheaf.Ext A))
    (x : Γ.obj.Elements) (t : Value A.family B.family x) :
    (functions A B).obj.obj (op (op x)) where
  app y f := ↾fun a => ⟨a, evaluate A.family B.family y.unop.unop
    (restrict A.family B.family f.unop.unop t) a⟩
  naturality {y z} g f := by
    apply ConcreteCategory.hom_ext
    intro a
    apply Sigma.ext
    · rfl
    apply heq_of_eq
    have hn := evaluate_natural A.family B.family g.unop.unop
      (restrict A.family B.family f.unop.unop t) a
    rw [restrict_comp] at hn
    exact hn.symm

def sectionValue (A : SplitSheaf.Ty Γ) (B : SplitSheaf.Ty (SplitSheaf.Ext A))
    (x : Γ.obj.Elements) (t : Value A.family B.family x) :
    (sections A B).obj.obj (op (op x)) := ⟨functionValue A B x t, by
  apply Functor.HomObj.ext
  funext y f
  rfl⟩

theorem sectionValue_natural (A : SplitSheaf.Ty Γ) (B : SplitSheaf.Ty (SplitSheaf.Ext A))
    {x y : Γ.obj.Elements} (f : x ⟶ y) (t : Value A.family B.family x) :
    (sections A B).obj.map f.op.op (sectionValue A B x t) =
      sectionValue A B y (restrict A.family B.family f t) := by
  apply Subtype.ext
  apply Functor.HomObj.ext
  funext z g
  apply ConcreteCategory.hom_ext
  intro a
  apply Sigma.ext
  · rfl
  apply heq_of_eq
  change evaluate _ _ _ (restrict _ _ (f ≫ g.unop.unop) t) a = _
  exact congrArg (fun t => evaluate A.family B.family z.unop.unop t a)
    (restrict_comp A.family B.family f g.unop.unop t).symm

def rawRead {D : Type*} [Category D] {F : D ⥤ Type w} (B : SplitPresheaf.Ty F)
    {σ : F ⟶ F} (k : F ⟶ SplitPresheaf.Ext B) (h : k ≫ SplitPresheaf.p B = σ) :
    SplitPresheaf.Tm (SplitPresheaf.tySub B σ) :=
  SplitPresheaf.transport (congrArg (SplitPresheaf.tySub B) h)
    (SplitPresheaf.tmSub (SplitPresheaf.q B) k)

theorem rawRead_pair {D : Type*} [Category D] {F : D ⥤ Type w} (B : SplitPresheaf.Ty F)
    (t : SplitPresheaf.Tm B) : rawRead B (SplitPresheaf.pair B (𝟙 F) t) rfl = t := rfl

/-- A section of the exponential equalizer supplies values on the restriction diagram. -/
def valueMap (A : SplitSheaf.Ty Γ) (B : SplitSheaf.Ty (SplitSheaf.Ext A))
    (x : Γ.obj.Elements) (h : (sections A B).obj.obj (op (op x))) :
    restrictions Γ.obj x ⋙ A.family ⟶
      SplitPresheaf.Ext (diagram A.family B.family (restrictions Γ.obj x)).2 where
  app k := h.val.app (op (op ((restrictions Γ.obj x).obj k))) (along Γ.obj k.hom x.val).op.op
  naturality {k l} f := by
    have hn := h.val.naturality ((restrictions Γ.obj x).map f).op.op (along Γ.obj k.hom x.val).op.op
    have he : (along Γ.obj k.hom x.val).op.op ≫ ((restrictions Γ.obj x).map f).op.op =
        (along Γ.obj l.hom x.val).op.op := by
      apply Quiver.Hom.unop_inj
      apply Quiver.Hom.unop_inj
      apply Functor.Elements.hom_ext
      exact Under.w f
    change _ ≫ h.val.app _ ((along Γ.obj k.hom x.val).op.op ≫ ((restrictions Γ.obj x).map f).op.op) = _ at hn
    rw [he] at hn
    exact hn

theorem valueMap_display (A : SplitSheaf.Ty Γ) (B : SplitSheaf.Ty (SplitSheaf.Ext A))
    (x : Γ.obj.Elements) (h : (sections A B).obj.obj (op (op x))) :
    valueMap A B x h ≫ SplitPresheaf.p (diagram A.family B.family (restrictions Γ.obj x)).2 = 𝟙 _ := by
  apply NatTrans.ext
  funext k
  exact congrArg (fun t => t.app (op (op ((restrictions Γ.obj x).obj k)))
    (along Γ.obj k.hom x.val).op.op) h.property

def diagramValue (A : SplitSheaf.Ty Γ) (B : SplitSheaf.Ty (SplitSheaf.Ext A))
    (x : Γ.obj.Elements) (h : (sections A B).obj.obj (op (op x))) : Value A.family B.family x :=
  rawRead _ (valueMap A B x h) (valueMap_display A B x h)


theorem pair_rawRead {D : Type*} [Category D] {F : D ⥤ Type w} (B : SplitPresheaf.Ty F)
    {σ : F ⟶ F} (k : F ⟶ SplitPresheaf.Ext B) (h : k ≫ SplitPresheaf.p B = σ) :
    SplitPresheaf.pair B σ (rawRead B k h) = k := by cases h; rfl

theorem valueMap_sectionValue (A : SplitSheaf.Ty Γ) (B : SplitSheaf.Ty (SplitSheaf.Ext A))
    (x : Γ.obj.Elements) (t : Value A.family B.family x) :
    valueMap A B x (sectionValue A B x t) =
      SplitPresheaf.pair (diagram A.family B.family (restrictions Γ.obj x)).2 (𝟙 _) t := by
  apply NatTrans.ext
  funext k
  apply ConcreteCategory.hom_ext
  intro a
  apply Sigma.ext
  · rfl
  apply heq_of_eq
  exact congrFun (eq_of_heq (evaluate_restrict_heq A.family B.family (along Γ.obj k.hom x.val) t)) a

@[simp] theorem diagramValue_sectionValue (A : SplitSheaf.Ty Γ) (B : SplitSheaf.Ty (SplitSheaf.Ext A))
    (x : Γ.obj.Elements) (t : Value A.family B.family x) :
    diagramValue A B x (sectionValue A B x t) = t := by
  unfold diagramValue
  simp only [valueMap_sectionValue]
  rfl

theorem homApp_heq (A : SplitSheaf.Ty Γ) (B : SplitSheaf.Ty (SplitSheaf.Ext A))
    {x y y' : Γ.obj.Elements} (h : (functions A B).obj.obj (op (op x)))
    (hy : y = y') {f : x ⟶ y} {g : x ⟶ y'} (hf : HEq f g) :
    HEq (h.app (op (op y)) f.op.op) (h.app (op (op y')) g.op.op) := by
  cases hy; cases hf; rfl

theorem valueMap_injective (A : SplitSheaf.Ty Γ) (B : SplitSheaf.Ty (SplitSheaf.Ext A))
    (x : Γ.obj.Elements) : Function.Injective (valueMap A B x) := by
  intro h k hk
  apply Subtype.ext
  apply Functor.HomObj.ext
  funext y f
  have hy : Γ.obj.elementsMk y.unop.unop.obj (Γ.obj.map f.unop.unop.hom x.val) = y.unop.unop := by
    rw [f.unop.unop.map_val]
  have hf := elements_hom_hext (F := Γ.obj) rfl hy (f := along Γ.obj f.unop.unop.hom x.val)
    (g := f.unop.unop) HEq.rfl
  have hh := congrArg (fun m => m.app (Under.mk f.unop.unop.hom)) hk
  exact eq_of_heq ((homApp_heq A B h.val hy hf).symm.trans
    ((heq_of_eq hh).trans (homApp_heq A B k.val hy hf)))

@[simp] theorem sectionValue_diagramValue (A : SplitSheaf.Ty Γ) (B : SplitSheaf.Ty (SplitSheaf.Ext A))
    (x : Γ.obj.Elements) (h : (sections A B).obj.obj (op (op x))) :
    sectionValue A B x (diagramValue A B x h) = h := by
  apply valueMap_injective A B x
  rw [valueMap_sectionValue]
  exact pair_rawRead _ _ _

/-- The compatible-function formula is isomorphic to a proved sheaf equalizer. -/
def diagramIso (A : SplitSheaf.Ty Γ) (B : SplitSheaf.Ty (SplitSheaf.Ext A)) :
    ElementSheaf.presheaf Γ.obj (pi A.family B.family) ≅ (sections A B).obj :=
  NatIso.ofComponents (fun x => {
    hom := ↾sectionValue A B x.unop.unop
    inv := ↾diagramValue A B x.unop.unop
    hom_inv_id := by apply ConcreteCategory.hom_ext; intro t; exact diagramValue_sectionValue A B _ t
    inv_hom_id := by apply ConcreteCategory.hom_ext; intro h; exact sectionValue_diagramValue A B _ h })
    (fun f => by apply ConcreteCategory.hom_ext; intro t; exact (sectionValue_natural A B f.unop.unop t).symm)

/-- The total dependent-function presheaf is a sheaf, by the element-site equivalence. -/
def piType (A : SplitSheaf.Ty Γ) (B : SplitSheaf.Ty (SplitSheaf.Ext A)) : SplitSheaf.Ty Γ where
  family := pi A.family B.family
  isSheaf := (SheafSlice.totalSheaf Γ
    ⟨ElementSheaf.presheaf Γ.obj (pi A.family B.family),
      (Presheaf.isSheaf_of_iso_iff (diagramIso A B)).2 (sections A B).property⟩).property

end SquareKit.SplitFunctionSheaf
