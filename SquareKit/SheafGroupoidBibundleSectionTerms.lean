import SquareKit.SheafGroupoidBibundleConnector

/-! Generalized points represented without subcanonicality. -/
noncomputable section
set_option autoImplicit false
set_option warningAsError true
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
namespace SquareKit.SheafGroupoid.Bibundle
open CategoryTheory Opposite SquareKit SquareKit.SheafGroupoid
open SquareKit.SheafGroupoid.Bundle SquareKit.SheafGroupoid.Bibundle
open SquareKit.SheafGroupoid.Bibundle SquareKit.SheafGroupoid.Bundle
universe u v
variable {C : Type u} [Category.{v} C] {J : GrothendieckTopology C}
variable {G H : Operations J} [G.Laws] [H.Laws]

abbrev universalPoint (U : Cᵒᵖ) :=
  ((sectionParameter J).obj U.unop).obj.elementsMk U (sectionEquiv (𝟙 ((sectionParameter J).obj U.unop)))

theorem universalPoint_eval {U : Cᵒᵖ} {F : Sheaf J (Type (max u v))}
    (f : (sectionParameter J).obj U.unop ⟶ F) :
    f.hom.app U (universalPoint (J := J) U).val = sectionEquiv f := by
  simpa only [Category.id_comp] using (sectionEquiv_comp (𝟙 _) f).symm

theorem term_ext_universal {U : Cᵒᵖ} {F : Sheaf J (Type (max u v))}
    (A : SplitSheaf.Ty F) (σ : (sectionParameter J).obj U.unop ⟶ F)
    (p q : SplitSheaf.Tm (SplitSheaf.tySub A σ))
    (h : p.val (universalPoint U) = q.val (universalPoint U)) : p = q := by
  have e : SplitSheaf.pair A σ p = SplitSheaf.pair A σ q := by
    apply sectionEquiv.injective
    rw [← universalPoint_eval, ← universalPoint_eval]
    exact congrArg (fun t => Sigma.mk (σ.hom.app U (universalPoint U).val) t) h
  apply SplitPresheaf.Tm.ext
  funext z
  have he := congrArg (fun f : (sectionParameter J).obj U.unop ⟶ SplitSheaf.extension A =>
    f.hom.app z.obj z.val) e
  exact eq_of_heq (Sigma.mk.inj he).2

omit [G.Laws] in
theorem value_represent_universal {U : Cᵒᵖ} (x : G.Section U) :
    value G (x.represent G) (universalPoint U) = x := by
  change Operations.Section.mk ((sectionEquiv.symm x.val).hom.app U (universalPoint U).val) = x
  rw [universalPoint_eval, sectionEquiv.apply_symm_apply]

theorem arrowValue_universal {U : Cᵒᵖ} {x y : G.Section U} (g : x ⟶ y) :
    HEq (arrowValue G g (universalPoint U)) g := by
  apply Descent.sectionArrow_heq (value_represent_universal x) (value_represent_universal y)
  rw [arrowValue_map]
  change sectionEquiv.symm (sectionEquiv (𝟙 _)) ≫ g.map = g.map
  rw [sectionEquiv.symm_apply_apply, Category.id_comp]

variable (P : Bibundle G H) {U : Cᵒᵖ} (x : G.Section U) (k : H.Section U)

def sectionTermMap (p : Fiber H G.objects P.right.family (atSection x) k) :
    (sectionParameter J).obj U.unop ⟶ SplitSheaf.extension P.right.family :=
  (sectionEquiv (F := SplitSheaf.extension P.right.family)).symm ⟨(x.val,k.val),p⟩

theorem sectionTermMap_base (p : Fiber H G.objects P.right.family (atSection x) k) :
    sectionTermMap P x k p ≫ SplitSheaf.p P.right.family =
      SheafRelation.lift (x.represent G).map (k.represent H).map := by
  apply sectionEquiv.injective
  rw [sectionEquiv_comp]
  change (sectionEquiv ((sectionEquiv (F := SplitSheaf.extension P.right.family)).symm ⟨(x.val,k.val),p⟩)).1 = _
  rw [sectionEquiv.apply_symm_apply, ← universalPoint_eval]
  change (x.val,k.val) = ((x.represent G).map.hom.app U (universalPoint U).val,
    (k.represent H).map.hom.app U (universalPoint U).val)
  rw [universalPoint_eval, universalPoint_eval]
  change (x.val,k.val) = (sectionEquiv (sectionEquiv.symm x.val),sectionEquiv (sectionEquiv.symm k.val))
  simp only [Equiv.apply_symm_apply]

def sectionTerm (p : Fiber H G.objects P.right.family (atSection x) k) :
    PointTerm (Bundle.reindex P.right (x.represent G).map) (k.represent H) :=
  SplitSheaf.readTerm P.right.family (sectionTermMap P x k p) (sectionTermMap_base P x k p)

theorem sectionTerm_value (p : Fiber H G.objects P.right.family (atSection x) k) :
    HEq ((sectionTerm P x k p).val (universalPoint U)) p := by
  have he := congrArg sectionEquiv (SplitSheaf.pair_read P.right.family
    (sectionTermMap P x k p) (sectionTermMap_base P x k p))
  rw [← universalPoint_eval] at he
  change (show (SplitSheaf.extension P.right.family).obj.obj U from
    ⟨_,(sectionTerm P x k p).val (universalPoint U)⟩) =
    sectionEquiv ((sectionEquiv (F := SplitSheaf.extension P.right.family)).symm ⟨(x.val,k.val),p⟩) at he
  rw [Equiv.apply_symm_apply] at he
  exact (Sigma.mk.inj he).2

end SquareKit.SheafGroupoid.Bibundle
