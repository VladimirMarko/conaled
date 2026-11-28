import SquareKit.SheafGroupoidBibundleSectionTerms

/-! Primitive left principality is equivalent to tensor and stack invertibility. -/
noncomputable section
set_option autoImplicit false
set_option warningAsError true
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
namespace SquareKit.SheafGroupoid.Bibundle
open CategoryTheory Opposite SquareKit SquareKit.SheafGroupoid
open SquareKit.SheafGroupoid.Bundle SquareKit.SheafGroupoid.Bibundle
open SquareKit.SheafGroupoid.Bibundle SquareKit.SheafGroupoid.Bundle
open SquareKit.SheafGroupoid.Bibundle
open scoped CategoryTheory.Pseudofunctor.StrongTrans
universe u v
variable {C : Type u} [Category.{v} C] {J : GrothendieckTopology C}
variable {G H : Operations J} [G.Laws] [H.Laws]

variable {X : Sheaf J (Type (max u v))}
def mapPointTerm {R S : Principal H X} (f : R ⟶ S) (k : H.Object X)
    (p : PointTerm R k) : PointTerm S k where
  val z := f.hom.app (point H X z (value H k z)) (p.val z)
  natural h := (NatTrans.naturality_apply f.hom
    ((SheafRelation.lift (𝟙 X) k.map).hom.mapElements.map h) _).symm.trans
      (congrArg (f.hom.app _) (p.natural h))

variable (P : Bibundle G H)
theorem leftAct_heq {U : Cᵒᵖ} {x y x' y' : G.Section U} {k k' : H.Section U}
    (hx : x = x') (hy : y = y') (hk : k = k') {g : x ⟶ y} {g' : x' ⟶ y'}
    (hg : HEq g g') {p : Fiber H G.objects P.right.family (atSection x) k}
    {p' : Fiber H G.objects P.right.family (atSection x') k'} (hp : HEq p p') :
    HEq (P.left.act g k p) (P.left.act g' k' p') := by
  cases hx; cases hy; cases hk; cases hg; cases hp; rfl

theorem sectionConnector
    (ff : ∀ X : Sheaf J (Type (max u v)), (sourceFunctor P (X := X)).FullyFaithful)
    {U : Cᵒᵖ} (x y : G.Section U) (k : H.Section U)
    (p : Fiber H G.objects P.right.family (atSection x) k)
    (q : Fiber H G.objects P.right.family (atSection y) k) :
    ∃! g : x ⟶ y, P.left.act g k p = q := by
  let S := (sectionParameter J).obj U.unop
  let pt := sectionTerm P x k p
  let qt := sectionTerm P y k q
  obtain ⟨g,hg,hu⟩ := globalConnector P (ff S) (x.represent G) (y.represent G) (k.represent H) pt qt
  have evaluate (f : x ⟶ y) :
      HEq (P.left.act (arrowValue G f (universalPoint U))
        (value H (k.represent H) (universalPoint U)) (pt.val (universalPoint U)))
        (P.left.act f k p) :=
    leftAct_heq P (value_represent_universal x) (value_represent_universal y)
      (value_represent_universal k) (arrowValue_universal f) (sectionTerm_value P x k p)
  refine ⟨g, eq_of_heq ((evaluate g).symm.trans
    ((heq_of_eq (hg (universalPoint U))).trans (sectionTerm_value P y k q))), ?_⟩
  intro f hf
  apply hu f
  have et : mapPointTerm (sourceMap P f) (k.represent H) pt = qt := by
    apply term_ext_universal
    change P.left.act (arrowValue G f (universalPoint U))
      (value H (k.represent H) (universalPoint U)) (pt.val (universalPoint U)) = qt.val (universalPoint U)
    exact eq_of_heq ((evaluate f).trans ((heq_of_eq hf).trans (sectionTerm_value P y k q).symm))
  intro z
  have he := congrArg (fun t => t.val z) et
  exact he

theorem TensorInverse.leftPrincipal (i : TensorInverse P) : LeftPrincipal P where
  principal := sectionConnector P (i.sourceFullyFaithful P)
  locallySurjective := i.anchor_locallySurjective P

theorem leftPrincipal_iff_tensorInverse : LeftPrincipal P ↔ Nonempty (TensorInverse P) :=
  ⟨fun h => ⟨TensorInverse.ofLeftPrincipal P h⟩, fun ⟨i⟩ => i.leftPrincipal P⟩

theorem leftPrincipal_iff_stackEquivalence : LeftPrincipal P ↔
    ∃ e : CategoryTheory.Bicategory.Equivalence (Bundle.pseudofunctor G) (Bundle.pseudofunctor H),
      e.hom = tensorTransformation P :=
  (leftPrincipal_iff_tensorInverse P).trans (tensorInverse_iff_stackEquivalence P)

end SquareKit.SheafGroupoid.Bibundle
