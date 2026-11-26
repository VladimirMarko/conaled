import SquareKit.PrincipalSheaf
import SquareKit.SheafRelation
import Mathlib.CategoryTheory.Sites.DenseSubsite.SheafEquiv

/-! Principal actions extend along dense subsite comparisons by lifting action and division maps. -/
noncomputable section
set_option autoImplicit false
set_option warningAsError true
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
namespace SquareKit.PrincipalSheaf
open CategoryTheory Opposite
universe u
variable {C D : Type u} [Category.{u} C] [Category.{u} D]
variable (J : GrothendieckTopology C) (K : GrothendieckTopology D) (F : C ⥤ D)
variable [F.IsDenseSubsite J K]

/-- Dense restriction is bijective on maps into a sheaf, for arbitrary presheaf domains. -/
def extendHom {P : Dᵒᵖ ⥤ Type u} (Q : Sheaf K (Type u)) :
    (F.op ⋙ P ⟶ F.op ⋙ Q.obj) ≃ (P ⟶ Q.obj) := by
  letI := Functor.IsDenseSubsite.isCoverDense J K F
  letI := Functor.IsDenseSubsite.isLocallyFull J K F
  exact Functor.IsCoverDense.restrictHomEquivHom (G := F) (ℱ' := Q)

include J in
theorem section_ext (Q : Sheaf K (Type u)) (X : D) {s t : Q.obj.obj (op X)}
    (h : ∀ ⦃Y : C⦄ (f : F.obj Y ⟶ X), Q.obj.map f.op s = Q.obj.map f.op t) : s = t := by
  let := Functor.IsDenseSubsite.isCoverDense J K F
  exact Functor.IsCoverDense.ext F Q X h

abbrev restrictSheaf (Q : Sheaf K (Type u)) : Sheaf J (Type u) :=
  (F.sheafPushforwardContinuous (Type u) J K).obj Q
abbrev restrictGroup (G : Sheaf K GrpCat.{u}) : Sheaf J GrpCat.{u} :=
  (F.sheafPushforwardContinuous GrpCat.{u} J K).obj G

/-- Restriction keeps the section operation and all its primitive laws. -/
def restrict {G : Sheaf K GrpCat.{u}} {Q : Sheaf K (Type u)} (A : Structure G Q) :
    Structure (restrictGroup J K F G) (restrictSheaf J K F Q) where
  act X := A.act (F.op.obj X)
  one_act X := A.one_act (F.op.obj X)
  mul_act X := A.mul_act (F.op.obj X)
  natural f := A.natural (F.op.map f)
  principal X := A.principal (F.op.obj X)
  locally_inhabited X := F.cover_lift J K (A.locally_inhabited (F.obj X))

abbrev groupSheaf (G : Sheaf K GrpCat.{u}) : Sheaf K (Type u) :=
  (sheafCompose K (forget GrpCat.{u})).obj G

variable {J K F}
variable {G : Sheaf K GrpCat.{u}} {Q : Sheaf K (Type u)}
variable (A : Structure (restrictGroup J K F G) (restrictSheaf J K F Q))

def restrictedActionMap :
    F.op ⋙ SheafRelation.productData (groupSheaf K G) Q ⟶ F.op ⋙ Q.obj where
  app X := ↾fun p => A.act X p.1 p.2
  naturality := by intro X Y f; ext p; exact (A.natural f p.1 p.2).symm

def extendedActionMap : SheafRelation.productData (groupSheaf K G) Q ⟶ Q.obj :=
  extendHom J K F Q (restrictedActionMap A)

def extendedAct (X : Dᵒᵖ) (g : G.obj.obj X) (p : Q.obj.obj X) : Q.obj.obj X :=
  (extendedActionMap A).app X (g, p)

theorem extendedAct_image (X : C) (g : G.obj.obj (op (F.obj X)))
    (p : Q.obj.obj (op (F.obj X))) : extendedAct A (op (F.obj X)) g p = A.act (op X) g p := by
  have h := (extendHom J K F Q).symm_apply_apply (restrictedActionMap A)
  exact congrArg (fun k => k.app (op X) (g, p)) h

theorem extendedAct_natural {X Y : Dᵒᵖ} (f : X ⟶ Y) (g : G.obj.obj X)
    (p : Q.obj.obj X) :
    Q.obj.map f (extendedAct A X g p) =
      extendedAct A Y (G.obj.map f g) (Q.obj.map f p) :=
  (congrArg (fun k : (SheafRelation.productData (groupSheaf K G) Q).obj X ⟶ Q.obj.obj Y =>
    k (g,p)) ((extendedActionMap A).naturality f)).symm

def restrictedDivisionMap :
    F.op ⋙ SheafRelation.productData Q Q ⟶ F.op ⋙ (groupSheaf K G).obj where
  app X := ↾fun p => division A X p.1 p.2
  naturality := by intro X Y f; ext p; exact (division_natural A f p.1 p.2).symm

def extendedDivisionMap : SheafRelation.productData Q Q ⟶ (groupSheaf K G).obj :=
  extendHom J K F (groupSheaf K G)
    (restrictedDivisionMap A)

def extendedDivision (X : Dᵒᵖ) (p q : Q.obj.obj X) : G.obj.obj X :=
  (extendedDivisionMap A).app X (p,q)

theorem extendedDivision_image (X : C) (p q : Q.obj.obj (op (F.obj X))) :
    extendedDivision A (op (F.obj X)) p q = division A (op X) p q := by
  have h := (extendHom J K F (groupSheaf K G)).symm_apply_apply (restrictedDivisionMap A)
  exact congrArg (fun k => k.app (op X) (p,q)) h

theorem extendedDivision_natural {X Y : Dᵒᵖ} (f : X ⟶ Y) (p q : Q.obj.obj X) :
    G.obj.map f (extendedDivision A X p q) =
      extendedDivision A Y (Q.obj.map f p) (Q.obj.map f q) :=
  (congrArg (fun k : (SheafRelation.productData Q Q).obj X ⟶ (groupSheaf K G).obj.obj Y =>
    k (p,q)) ((extendedDivisionMap A).naturality f)).symm

theorem extendedAct_one (X : Dᵒᵖ) (p : Q.obj.obj X) : extendedAct A X 1 p = p := by
  apply section_ext J K F Q X.unop
  intro Y f
  rw [extendedAct_natural, map_one, extendedAct_image A Y]
  exact A.one_act _ _

theorem extendedAct_mul (X : Dᵒᵖ) (g h : G.obj.obj X) (p : Q.obj.obj X) :
    extendedAct A X (g*h) p = extendedAct A X g (extendedAct A X h p) := by
  apply section_ext J K F Q X.unop
  intro Y f
  rw [extendedAct_natural, extendedAct_natural, extendedAct_natural, map_mul,
    extendedAct_image A Y, extendedAct_image A Y, extendedAct_image A Y]
  exact A.mul_act _ _ _ _

theorem extendedDivision_act (X : Dᵒᵖ) (p q : Q.obj.obj X) :
    extendedAct A X (extendedDivision A X p q) p = q := by
  apply section_ext J K F Q X.unop
  intro Y f
  rw [extendedAct_natural, extendedDivision_natural, extendedDivision_image A Y, extendedAct_image A Y]
  exact division_act A _ _ _

theorem extendedDivision_unique (X : Dᵒᵖ) (p q : Q.obj.obj X) (g : G.obj.obj X)
    (h : extendedAct A X g p = q) : g = extendedDivision A X p q := by
  apply section_ext J K F (groupSheaf K G) X.unop
  intro Y f
  change G.obj.map f.op g = G.obj.map f.op (extendedDivision A X p q)
  rw [extendedDivision_natural, extendedDivision_image A Y]
  apply division_unique A
  have hh := congrArg (fun p => Q.obj.map f.op p) h
  rw [extendedAct_natural, extendedAct_image A Y] at hh
  exact hh

include A in
theorem extended_locally_inhabited (X : D) : inhabitedSieve Q X ∈ K X := by
  let := Functor.IsDenseSubsite.isCoverDense J K F
  apply K.transitive (F.is_cover_of_isCoverDense K X)
  rintro Y g ⟨⟨Z, l, m, rfl⟩⟩
  rw [Sieve.pullback_comp]
  apply K.pullback_stable
  apply K.superset_covering ?_
    ((Functor.IsDenseSubsite.coverPreserving J K F).cover_preserve (A.locally_inhabited Z))
  rintro W q ⟨V, h, t, ⟨s⟩, heq⟩
  exact ⟨Q.obj.map t.op s⟩

/-- The extended action and division satisfy all principal-sheaf laws. -/
def extend : Structure G Q where
  act := extendedAct A
  one_act := extendedAct_one A
  mul_act := extendedAct_mul A
  natural := extendedAct_natural A
  principal X p q := ⟨extendedDivision A X p q, extendedDivision_act A X p q,
    fun g h => extendedDivision_unique A X p q g h⟩
  locally_inhabited := extended_locally_inhabited A

/-- Extension recovers the specified section action on every source-site object. -/
theorem extend_act_image (X : C) (g : G.obj.obj (op (F.obj X)))
    (p : Q.obj.obj (op (F.obj X))) :
    (extend A).act (op (F.obj X)) g p = A.act (op X) g p := extendedAct_image A X g p

/-- Restriction of the extension is the original principal structure. -/
theorem restrict_extend : restrict J K F (extend A) = A := by
  apply Structure.ext
  intro X g p
  exact extend_act_image A X.unop g p

variable (J K F)

/-- Extending the restriction recovers the original principal structure. -/
theorem extend_restrict {G : Sheaf K GrpCat.{u}} {Q : Sheaf K (Type u)}
    (A : Structure G Q) : extend (restrict J K F A) = A := by
  apply Structure.ext
  intro X g p
  apply section_ext J K F Q X.unop
  intro Y f
  rw [(extend (restrict J K F A)).natural, A.natural]
  exact extend_act_image (restrict J K F A) Y _ _

/-- Equivariance is detected on the dense subsite, for every sheaf map. -/
theorem equivariant_iff {G : Sheaf K GrpCat.{u}} {Q R : Sheaf K (Type u)}
    (A : Structure G Q) (B : Structure G R) (f : Q ⟶ R) :
    Equivariant A B f ↔ Equivariant (restrict J K F A) (restrict J K F B)
      ((F.sheafPushforwardContinuous (Type u) J K).map f) := by
  constructor
  · intro h X g p
    exact h (F.op.obj X) g p
  · intro h X g p
    apply section_ext J K F R X.unop
    intro Y k
    rw [← NatTrans.naturality_apply, A.natural, B.natural, ← NatTrans.naturality_apply]
    exact h (op Y) (G.obj.map k.op g) (Q.obj.map k.op p)

/-- Every equivariant restricted map extends, with its restriction computed exactly. -/
def extendMap {R : Sheaf K (Type u)}
    (f : restrictSheaf J K F Q ⟶ restrictSheaf J K F R) : Q ⟶ R :=
  ⟨extendHom J K F R f.hom⟩

theorem extendMap_restrict {R : Sheaf K (Type u)}
    (f : restrictSheaf J K F Q ⟶ restrictSheaf J K F R) :
    (F.sheafPushforwardContinuous (Type u) J K).map (extendMap J K F f) = f := by
  apply Sheaf.hom_ext
  exact (extendHom J K F R).symm_apply_apply f.hom

/-- Lifting a restricted equivariant map preserves equivariance. -/
theorem extendMap_equivariant {G : Sheaf K GrpCat.{u}} {Q R : Sheaf K (Type u)}
    (A : Structure G Q) (B : Structure G R)
    (f : restrictSheaf J K F Q ⟶ restrictSheaf J K F R)
    (h : Equivariant (restrict J K F A) (restrict J K F B) f) :
    Equivariant A B (extendMap J K F f) := by
  apply (equivariant_iff J K F A B _).mpr
  rwa [extendMap_restrict]

end SquareKit.PrincipalSheaf
