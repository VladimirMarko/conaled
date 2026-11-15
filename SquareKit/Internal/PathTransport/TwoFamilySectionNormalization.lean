import SquareKit.Internal.PathTransport.TwoFamilySectionLaws
import SquareKit.Internal.PathTransport.TwoFamilyHEq
/-! Normalize the displayed base in every dimension of a section. Equality of
the full functor data transports its laws and recovers the original section. -/
namespace SquareKit.Internal.PathTransport.TwoFamily
open CategoryTheory Bicategory
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option backward.defeqAttrib.useBackward true
universe u v w uΓ vΓ wΓ
variable {Γ : Type uΓ} [Bicategory.{wΓ,vΓ} Γ] [Strict Γ]
variable (F : Family.{uΓ,vΓ,wΓ,u,v,w} Γ)

def Total.withBase (x : Total F) (γ : Γ) (e : x.base = γ) : Total F :=
  ⟨γ,cast (congrArg (fun δ => (F.obj δ : Type u)) e) x.fiber⟩
omit [Strict Γ] in
theorem Total.withBase_eq (x : Total F) (γ : Γ) (e : x.base = γ) :
    x.withBase F γ e = x := by cases e; rfl

def Hom.withBase {x y : Total F} (p : Hom F x y) (f : x.base ⟶ y.base) (e : p.base = f) :
    Hom F x y :=
  ⟨f,eqToHom (congrArg (fun g => (F.map g).obj x.fiber) e.symm) ≫ p.fiber⟩
omit [Strict Γ] in
theorem Hom.withBase_eq {x y : Total F} (p : Hom F x y) (f : x.base ⟶ y.base) (e : p.base = f) :
    p.withBase F f e = p := by
  cases e
  cases p
  simp [Hom.withBase]

def cellWithBase {x y : Total F} {p q : Hom F x y} (α : p ⟶ q)
    (β : p.base ⟶ q.base) (e : α.base = β) : p ⟶ q :=
  ⟨β,α.fiber ≫ eqToHom (congrArg (fun b => (F.map₂ b).app x.fiber ≫ q.fiber) e)⟩
omit [Strict Γ] in
theorem cellWithBase_eq {x y : Total F} {p q : Hom F x y} (α : p ⟶ q)
    (β : p.base ⟶ q.base) (e : α.base = β) : cellWithBase F α β e = α := by
  cases e
  cases α
  simp [cellWithBase]

namespace Section
variable (s : Section F)
theorem objBase (x : Γ) : (s.lift.obj x).base = x := congrArg (fun H => H.obj x) s.over

def normalObj (x : Γ) : Total F := (s.lift.obj x).withBase F x (s.objBase F x)
theorem normalObj_eq (x : Γ) : s.normalObj F x = s.lift.obj x := Total.withBase_eq _ _ _ _

def castMap {x y : Γ} (p : x ⟶ y) : s.normalObj F x ⟶ s.normalObj F y :=
  (eqToHom (s.normalObj_eq F x) ≫ s.lift.map p) ≫ eqToHom (s.normalObj_eq F y).symm

theorem castMap_base {x y : Γ} (p : x ⟶ y) : (s.castMap F p).base = p := by
  change (projection F).map (s.castMap F p) = p
  simp only [castMap, Functor.map_comp, eqToHom_map]
  apply eq_of_heq
  simp only [eqToHom_comp_heq_iff, comp_eqToHom_heq_iff]
  exact congr_arg_heq (fun H => H.map p) s.over

def normalMap {x y : Γ} (p : x ⟶ y) : s.normalObj F x ⟶ s.normalObj F y :=
  (s.castMap F p).withBase F p (s.castMap_base F p)

theorem normalMap_eq {x y : Γ} (p : x ⟶ y) : s.normalMap F p = s.castMap F p :=
  Hom.withBase_eq _ _ _ _
theorem normalMap_heq {x y : Γ} (p : x ⟶ y) : HEq (s.normalMap F p) (s.lift.map p) := by
  rw [normalMap_eq]
  simp only [castMap, eqToHom_comp_heq_iff, comp_eqToHom_heq_iff]
  rfl

def castCell {x y : Γ} {p q : x ⟶ y} (α : p ⟶ q) : s.normalMap F p ⟶ s.normalMap F q :=
  eqToHom (s.normalMap_eq F p) ≫
    ((eqToHom (s.normalObj_eq F x) ◁ s.lift.map₂ α) ▷ eqToHom (s.normalObj_eq F y).symm) ≫
      eqToHom (s.normalMap_eq F q).symm

theorem castCell_heq {x y : Γ} {p q : x ⟶ y} (α : p ⟶ q) :
    HEq (s.castCell F α) (s.lift.map₂ α) := by
  change HEq (eqToHom _ ≫ _ ≫ eqToHom _) _
  apply HEq.trans (eqToHom_comp_heq _ _)
  apply HEq.trans (comp_eqToHom_heq _ _)
  exact (eqToHom_right_heq (B := Total F) _ _).trans (eqToHom_left_heq (B := Total F) _ _)

theorem castCell_base {x y : Γ} {p q : x ⟶ y} (α : p ⟶ q) :
    (s.castCell F α).base = α := by
  apply eq_of_heq
  exact (total_cell_base_heq_family (F := F) rfl
    (heq_of_eq (s.normalObj_eq F x)) (heq_of_eq (s.normalObj_eq F y))
    (s.normalMap_heq F p) (s.normalMap_heq F q) (s.castCell_heq F α)).trans
      (congr_arg_heq (fun H => H.map₂ α) s.over)

def normalCell {x y : Γ} {p q : x ⟶ y} (α : p ⟶ q) : s.normalMap F p ⟶ s.normalMap F q :=
  cellWithBase F (s.castCell F α) α (s.castCell_base F α)

theorem normalCell_heq {x y : Γ} {p q : x ⟶ y} (α : p ⟶ q) :
    HEq (s.normalCell F α) (s.lift.map₂ α) :=
  (heq_of_eq (cellWithBase_eq F _ _ _)).trans (s.castCell_heq F α)

def normalData : PrelaxFunctorStruct Γ (Total F) where
  obj := s.normalObj F
  map := s.normalMap F
  map₂ := s.normalCell F

theorem normalData_eq : s.normalData F = s.lift.toPrelaxFunctorStruct :=
  prelaxData_ext _ _ (s.normalObj_eq F) (fun p => s.normalMap_heq F p)
    (fun α => s.normalCell_heq F α)

def normalized : Section F where
  lift := strictFunctorOfEqualData s.lift (s.normalData F) (s.normalData_eq F)
  over := by rw [strictFunctorOfEqualData_eq]; exact s.over

theorem normalized_eq : s.normalized F = s := by
  have h := strictFunctorOfEqualData_eq s.lift (s.normalData F) (s.normalData_eq F)
  change (s.normalized F).lift = s.lift at h
  have aux (a b : Section F) (e : a.lift = b.lift) : a = b := by
    cases a
    cases b
    cases e
    rfl
  exact aux _ _ h
theorem normalized_obj_base (x : Γ) : ((s.normalized F).lift.obj x).base = x := rfl

theorem normalized_map_base {x y : Γ} (p : x ⟶ y) :
    ((s.normalized F).lift.map p).base = p := rfl

theorem normalized_cell_base {x y : Γ} {p q : x ⟶ y} (α : p ⟶ q) :
    ((s.normalized F).lift.map₂ α).base = α := rfl

end Section
end SquareKit.Internal.PathTransport.TwoFamily
