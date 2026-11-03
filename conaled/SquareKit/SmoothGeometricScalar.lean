import SquareKit.SmoothPresentationSheaf

/-! Experimental representable geometric scalar, its finite smooth operations,
and restriction comparisons with the earlier bottom-topology model. -/
noncomputable section
namespace SquareKit.SmoothPresentationSite
open CategoryTheory Opposite SmoothAlgebra

abbrev powerData (n : ℕ) : Siteᵒᵖ ⥤ Type where
  obj X := Fin n → Carrier X.unop.unop
  map f := ↾fun z i => (smoothMap f.unop.unop).toFun (z i)

/-- Free finite-coordinate codes represent the actual tuple presheaves. -/
def representablePowerIso (n : ℕ) : yoneda.obj (op (free n)) ≅ powerData n :=
  NatIso.ofComponents (fun X => Equiv.toIso
    {toFun := fun h => freeHomEquiv n X.unop.unop h.unop
     invFun := fun x => ((freeHomEquiv n X.unop.unop).symm x).op
     left_inv := fun h => congrArg Quiver.Hom.op ((freeHomEquiv n X.unop.unop).symm_apply_apply h.unop)
     right_inv := fun x => (freeHomEquiv n X.unop.unop).apply_symm_apply x}) (by
      intro X Y f
      ext h i
      rfl)

def powerScalarIso : powerData 1 ≅ scalarData :=
  NatIso.ofComponents (fun X => Equiv.toIso
    {toFun := fun x => x 0
     invFun := fun x _ => x
     left_inv := fun x => by funext i; fin_cases i; rfl
     right_inv := fun _ => rfl}) (by intros; rfl)

def representableScalarIso : yoneda.obj (op (free 1)) ≅ scalarData :=
  representablePowerIso 1 ≪≫ powerScalarIso

def scalarPower (n : ℕ) : Sheaf topology Type :=
  ⟨powerData n,(isSheaf_iff_isSheaf_of_type _ _).mpr
    (Presieve.isSheaf_iso topology (representablePowerIso n) (yoneda_isSheaf _))⟩

def operation {n : ℕ} (f : Operation n) : scalarPower n ⟶ scalar :=
  ⟨{app X := ↾fun z => act (A := Carrier X.unop.unop) f z
    naturality _ _ h := by ext z; exact ((smoothMap h.unop.unop).map_act f z).symm}⟩

def projection (n : ℕ) (i : Fin n) : scalarPower n ⟶ scalar :=
  ⟨{app _ := ↾fun z => z i}⟩

def tuple {n : ℕ} {F : Sheaf topology Type} (h : Fin n → (F ⟶ scalar)) : F ⟶ scalarPower n :=
  ⟨{app X := ↾fun x i => (h i).hom.app X x
    naturality X Y f := by
      ext x
      funext i
      exact congrFun (congrArg (fun k => k.hom) ((h i).hom.naturality f)) x}⟩

theorem tuple_projection {n : ℕ} {F : Sheaf topology Type} (h : Fin n → (F ⟶ scalar)) (i : Fin n) :
    tuple h ≫ projection n i=h i := rfl

theorem tuple_unique {n : ℕ} {F : Sheaf topology Type} (h : Fin n → (F ⟶ scalar))
    (g : F ⟶ scalarPower n) (hg : ∀ i, g ≫ projection n i=h i) : g=tuple h := by
  ext X x
  funext i
  exact congrArg (fun f : F ⟶ scalar => f.hom.app X x) (hg i)

/-- The tuple sheaf is the categorical finite product of the scalar sheaf. -/
def powerIsLimit (n : ℕ) : Limits.IsLimit (Limits.Fan.mk (scalarPower n) (projection n)) :=
  Limits.Fan.IsLimit.mk _ (fun c => tuple c.proj) (fun c i => tuple_projection c.proj i)
    (fun c g hg => tuple_unique c.proj g hg)

def representedScalar : Sheaf topology Type :=
  ⟨yoneda.obj (op (free 1)),(isSheaf_iff_isSheaf_of_type _ _).mpr (yoneda_isSheaf _)⟩

def scalarRepresentation : representedScalar ≅ scalar :=
  (fullyFaithfulSheafToPresheaf topology (Type)).preimageIso representableScalarIso

/-- Forgetting geometric sheafness keeps exactly the same presheaf. -/
def toBottom : Sheaf topology Type ⥤ Sheaf (⊥ : GrothendieckTopology Site) Type where
  obj F := ⟨F.obj,Presheaf.isSheaf_bot _⟩
  map f := ⟨f.hom⟩

/-- Restriction of the earlier coded-stage scalar to the common presentation category. -/
def bottomScalar : Sheaf (⊥ : GrothendieckTopology Site) Type :=
  ⟨toStage.op.op ⋙ SmoothStage.scalarData,Presheaf.isSheaf_bot _⟩
def bottomPower (n : ℕ) : Sheaf (⊥ : GrothendieckTopology Site) Type :=
  ⟨toStage.op.op ⋙ (SmoothStage.scalarPower n).obj,Presheaf.isSheaf_bot _⟩

def bottomScalarComparison : toBottom.obj scalar ≅ bottomScalar := Iso.refl _
def bottomPowerComparison (n : ℕ) : toBottom.obj (scalarPower n) ≅ bottomPower n := Iso.refl _

/-- Finite operations agree with restriction of the preceding model; no exponential assertion is made. -/
theorem operation_restriction {n : ℕ} (f : Operation n) :
    (toBottom.map (operation f)).hom = Functor.whiskerLeft toStage.op.op (SmoothStage.operation f).hom := rfl

end SquareKit.SmoothPresentationSite
