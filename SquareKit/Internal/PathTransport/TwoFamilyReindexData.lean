import SquareKit.Internal.PathTransport.TwoFamilyHigherReindex
import SquareKit.Internal.PathTransport.TwoFunctorData
namespace SquareKit.Internal.PathTransport.TwoFamily
open CategoryTheory Bicategory
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option backward.defeqAttrib.useBackward true
set_option maxHeartbeats 1000000
universe u v w uΓ vΓ wΓ uΔ vΔ wΔ
variable {Γ : Type uΓ} [Bicategory.{wΓ,vΓ} Γ] [Bicategory.Strict Γ]
variable {Δ : Type uΔ} [Bicategory.{wΔ,vΔ} Δ] [Bicategory.Strict Δ]
variable (F : Family.{uΓ,vΓ,wΓ,u,v,w} Γ) (σ : StrictPseudofunctor Δ Γ)
/-- A proved family equality transports its entire higher total context. -/
def totalCast {C : Type*} [Bicategory C] [Bicategory.Strict C]
    {A B : Family.{_,_,_,u,v,w} C} (e : A = B) :
    StrictPseudofunctor (Total A) (Total B) := by
  cases e
  exact StrictPseudofunctor.id _

theorem totalCast_obj_base {C : Type*} [Bicategory C] [Bicategory.Strict C]
    {A B : Family.{_,_,_,u,v,w} C} (e : A = B) (x : Total A) :
    ((totalCast e).obj x).base = x.base := by cases e; rfl

theorem totalCast_obj_fiber {C : Type*} [Bicategory C] [Bicategory.Strict C]
    {A B : Family.{_,_,_,u,v,w} C} (e : A = B) (x : Total A) :
    HEq ((totalCast e).obj x).fiber x.fiber := by cases e; rfl

theorem totalCast_map_base {C : Type*} [Bicategory C] [Bicategory.Strict C]
    {A B : Family.{_,_,_,u,v,w} C} (e : A = B) {x y : Total A} (p : x ⟶ y) :
    HEq ((totalCast e).map p).base p.base := by cases e; rfl

theorem totalCast_map_fiber {C : Type*} [Bicategory C] [Bicategory.Strict C]
    {A B : Family.{_,_,_,u,v,w} C} (e : A = B) {x y : Total A} (p : x ⟶ y) :
    HEq ((totalCast e).map p).fiber p.fiber := by cases e; rfl

theorem totalCast_cell_base {C : Type*} [Bicategory C] [Bicategory.Strict C]
    {A B : Family.{_,_,_,u,v,w} C} (e : A = B) {x y : Total A} {p q : x ⟶ y}
    (α : p ⟶ q) : HEq ((totalCast e).map₂ α).base α.base := by cases e; rfl

theorem totalCast_cell_fiber {C : Type*} [Bicategory C] [Bicategory.Strict C]
    {A B : Family.{_,_,_,u,v,w} C} (e : A = B) {x y : Total A} {p q : x ⟶ y}
    (α : p ⟶ q) : HEq ((totalCast e).map₂ α).fiber α.fiber := by cases e; rfl

private theorem higher_map_heq {C D : Type*} [Bicategory C] [Bicategory D]
    (H : StrictPseudofunctor C D) {x x' y y' : C} (hx : x = x') (hy : y = y')
    {p : x ⟶ y} {q : x' ⟶ y'} (hp : HEq p q) : HEq (H.map p) (H.map q) := by
  subst x'
  subst y'
  cases eq_of_heq hp
  rfl
private theorem higher_cell_heq {C D : Type*} [Bicategory C] [Bicategory D]
    (H : StrictPseudofunctor C D) {x x' y y' : C} (hx : x = x') (hy : y = y')
    {p q : x ⟶ y} {p' q' : x' ⟶ y'} (hp : HEq p p') (hq : HEq q q')
    {α : p ⟶ q} {β : p' ⟶ q'} (ha : HEq α β) : HEq (H.map₂ α) (H.map₂ β) := by
  subst x'
  subst y'
  cases eq_of_heq hp
  cases eq_of_heq hq
  cases eq_of_heq ha
  rfl
private theorem total_hom_hext {C : Type*} [Bicategory C] [Strict C] (H : Family C)
    {x x' y y' : Total H} (hx : x = x') (hy : y = y')
    (p : Hom H x y) (q : Hom H x' y') (hb : HEq p.base q.base)
    (hf : HEq p.fiber q.fiber) : HEq p q := by
  subst x'
  subst y'
  apply heq_of_eq
  exact Pseudofunctor.CoGrothendieck.ext (eq_of_heq hb) hf
private theorem total_cell_hext {C : Type*} [Bicategory C] [Strict C] (H : Family C)
    {x x' y y' : Total H} (hx : x = x') (hy : y = y')
    {p q : Hom H x y} {p' q' : Hom H x' y'} (hp : HEq p p') (hq : HEq q q')
    (α : p ⟶ q) (β : p' ⟶ q') (hb : HEq α.base β.base)
    (hf : HEq α.fiber β.fiber) : HEq α β := by
  subst x'
  subst y'
  cases eq_of_heq hp
  cases eq_of_heq hq
  apply heq_of_eq
  apply Pseudofunctor.CoGrothendieck.Hom.ext _ _ (eq_of_heq hb)
  exact eq_of_heq (HEq.trans hf (comp_eqToHom_heq _ _).symm)

private theorem total_obj_hext {C : Type*} [Bicategory C] [Strict C] (H : Family C)
    {x y : Total H} (hb : x.base = y.base) (hf : HEq x.fiber y.fiber) : x = y := by
  rcases x with ⟨x,a⟩
  rcases y with ⟨y,b⟩
  dsimp only at hb hf
  subst y
  cases eq_of_heq hf
  rfl

/-- Substitute through a proved equality with the pullback family. -/
def reindexFromEqualFamily {G : Family.{uΔ,vΔ,wΔ,u,v,w} Δ} (e : G = reindex σ F) :
    StrictPseudofunctor (Total G) (Total F) :=
  (totalCast e).comp (reindexHigher F σ)

variable {G : Family.{uΔ,vΔ,wΔ,u,v,w} Δ} (e : G = reindex σ F)
    (D : PrelaxFunctorStruct (Total G) (Total F))
    (hob : ∀ x, (D.obj x).base = σ.obj x.base)
    (hof : ∀ x, HEq (D.obj x).fiber x.fiber)
    (hmb : ∀ {x y} (p : x ⟶ y), HEq (D.map p).base (σ.map p.base))
    (hmf : ∀ {x y} (p : x ⟶ y), HEq (D.map p).fiber p.fiber)
    (hcb : ∀ {x y} {p q : x ⟶ y} (α : p ⟶ q), HEq (D.map₂ α).base (σ.map₂ α.base))
    (hcf : ∀ {x y} {p q : x ⟶ y} (α : p ⟶ q), HEq (D.map₂ α).fiber α.fiber)

include hob hof hmb hmf hcb hcf
/-- The six component observations determine the exact existing substitution map. -/
theorem reindexData_eq : D = (reindexFromEqualFamily F σ e).toPrelaxFunctorStruct := by
  have ho (x : Total G) : D.obj x = (reindexFromEqualFamily F σ e).obj x := by
    apply total_obj_hext F
    · exact (hob x).trans (congrArg σ.obj (totalCast_obj_base e x)).symm
    · exact (hof x).trans (totalCast_obj_fiber e x).symm
  have hm {x y : Total G} (p : x ⟶ y) :
      HEq (D.map p) ((reindexFromEqualFamily F σ e).map p) := by
    apply total_hom_hext F (ho x) (ho y)
    · exact (hmb p).trans (higher_map_heq σ (totalCast_obj_base e x)
        (totalCast_obj_base e y) (totalCast_map_base e p)).symm
    · exact (hmf p).trans (totalCast_map_fiber e p).symm
  apply prelaxData_ext D _ ho (fun p => hm p)
  intro x y p q α
  apply total_cell_hext F (ho x) (ho y) (hm p) (hm q)
  · exact (hcb α).trans (higher_cell_heq σ (totalCast_obj_base e x)
      (totalCast_obj_base e y) (totalCast_map_base e p) (totalCast_map_base e q)
      (totalCast_cell_base e α)).symm
  · exact (hcf α).trans (totalCast_cell_fiber e α).symm

/-- Build substitution with explicit operations and derive all its higher laws.
The observations mention only base/fiber data; no final coherence law is supplied. -/
def reindexOfData : StrictPseudofunctor (Total G) (Total F) :=
  strictFunctorOfEqualData (reindexFromEqualFamily F σ e) D
    (reindexData_eq F σ e D hob hof hmb hmf hcb hcf)
end SquareKit.Internal.PathTransport.TwoFamily
