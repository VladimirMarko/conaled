import SquareKit.SmoothTorsorDual

/-! Canonical lifting of torsors through represented dual parameters. -/
noncomputable section
namespace SquareKit.SmoothOpenSite
open CategoryTheory Opposite SmoothPresentationSite SmoothGeometricKL SheafTorsor

variable {H : Type} [Group H]
local notation "G" => locallyConstantGroup H
local notation:max "Y" A:max => representable (J := topology) A
local notation "D" => PresentationGeometry.infinitesimal topology

/-- A generalized point of D × yA has a universal D-parameter path. -/
def universalPath (A : Code) : Y (dual A) ⟶ dualSheaf (Y (dual A)) := ⟨{
  app T := ↾fun h => (dualMap (inl A ≫ h.unop)).op
  naturality T U f := by
    ext h
    apply Quiver.Hom.unop_inj
    change dualMap (inl A ≫ (h.unop ≫ f.unop.unop)) =
      dualMap (inl A ≫ h.unop) ≫ dualMap f.unop.unop
    rw [← Category.assoc, dualMap_comp] }⟩

/-- At zero, the universal path forgets only the infinitesimal coordinate. -/
theorem universalPath_zero (A : Code) :
    universalPath A ≫ dualSheafZero (Y (dual A)) =
      representableMap (dualZero A ≫ inl A) := by
  ext T h
  apply Quiver.Hom.unop_inj
  change dualMap (inl A ≫ h.unop) ≫ dualZero T.unop.unop =
    (dualZero A ≫ inl A) ≫ h.unop
  rw [dualZero_natural, Category.assoc]

/-- Evaluate the universal path at the generalized point's own nilpotent. -/
def evaluationElement {A : Code} (x : (Y (dual A)).obj.Elements) :
    (dualElements (Y (dual A))).obj ((universalPath A).hom.mapElements.obj x) ⟶ x :=
  Functor.Elements.homMk (stageMap (parameterEvaluation x.val.unop))
    (congrArg Quiver.Hom.op (parameter_factorization x.val.unop))

theorem evaluationElement_natural {A : Code} {x y : (Y (dual A)).obj.Elements}
    (f : x ⟶ y) :
    (dualElements (Y (dual A))).map ((universalPath A).hom.mapElements.map f) ≫
      evaluationElement y = evaluationElement x ≫ f := by
  apply Functor.Elements.hom_ext
  have he : x.val.unop ≫ f.hom.unop.unop = y.val.unop :=
    congrArg Quiver.Hom.unop f.map_val
  change stageMap (dualMap f.hom.unop.unop ≫ parameterEvaluation y.val.unop) =
    stageMap (parameterEvaluation x.val.unop ≫ f.hom.unop.unop)
  rw [← he, parameterEvaluation_natural]

theorem evaluation_equivariant (A : Code) (P : Torsor G (Y (dual A)))
    (x : (Y (dual A)).obj.Elements) (g : (G).obj.obj x.obj)
    (p : P.family.family.obj ((dualElements _).obj ((universalPath A).hom.mapElements.obj x))) :
    P.family.family.map (evaluationElement x)
      (P.act _ ((G).obj.map (stageMap (inl x.obj.unop.unop)) g) p) =
        P.act x g (P.family.family.map (evaluationElement x) p) := by
  rw [P.natural]
  congr 1
  change (G).obj.map (stageMap (parameterEvaluation x.val.unop))
    ((G).obj.map (stageMap (inl x.obj.unop.unop)) g) = g
  rw [← ConcreteCategory.comp_apply, ← (G).obj.map_comp]
  change (G).obj.map (stageMap (inl x.obj.unop.unop ≫ parameterEvaluation x.val.unop)) g = g
  rw [parameterEvaluation_inl]
  exact congrArg (fun k => k g) ((G).obj.map_id x.obj)

/-- Evaluation of an actual torsor's universal path is equivariant. -/
def evaluationTorsorMap (A : Code) (P : Torsor G (Y (dual A))) :
    EquivariantMap (reindex (dualTorsor P) (universalPath A)) P where
  hom := {
    app x := P.family.family.map (evaluationElement x)
    naturality {x y} f := by
      change P.family.family.map ((dualElements _).map ((universalPath A).hom.mapElements.map f)) ≫
        P.family.family.map (evaluationElement y) =
        P.family.family.map (evaluationElement x) ≫ P.family.family.map f
      rw [← P.family.family.map_comp, ← P.family.family.map_comp, evaluationElement_natural] }
  equivariant := evaluation_equivariant A P

/-- The base map obtained by first taking the universal path and then zero. -/
abbrev contractionBase (A : Code) : Y (dual A) ⟶ Y (dual A) :=
  universalPath A ≫ dualSheafZero (Y (dual A))

/-- Two constructed equivariant isomorphisms compare contraction with the
original torsor. Neither comparison assumes that the torsor has a section. -/
def contractionIso (A : Code) (P : Torsor G (Y (dual A))) :
    reindex P (contractionBase A) ≅ P :=
  (SheafTorsor.Arrow.toIso (show reindex (dualTorsor P) (universalPath A) ⟶ reindex P (contractionBase A) from
    (dualTorsorZero P).reindex (universalPath A))).symm ≪≫
    SheafTorsor.Arrow.toIso (show reindex (dualTorsor P) (universalPath A) ⟶ P from
      (evaluationTorsorMap A P).toArrow)

theorem evaluationTorsor_natural (A : Code) {P Q : Torsor G (Y (dual A))} (f : P ⟶ Q) :
    (restriction (universalPath A)).map ((dualTorsorFunctor _).map f) ≫
      (evaluationTorsorMap A Q).toArrow = (evaluationTorsorMap A P).toArrow ≫ f := by
  apply SheafTorsor.Arrow.ext
  ext x p
  exact (NatTrans.naturality_apply f.iso.hom (evaluationElement x) p).symm

theorem contraction_natural (A : Code) {P Q : Torsor G (Y (dual A))} (f : P ⟶ Q) :
    (restriction (contractionBase A)).map f ≫ (contractionIso A Q).hom =
      (contractionIso A P).hom ≫ f := by
  let aP : reindex (dualTorsor P) (universalPath A) ⟶ reindex P (contractionBase A) :=
    (dualTorsorZero P).reindex (universalPath A)
  let aQ : reindex (dualTorsor Q) (universalPath A) ⟶ reindex Q (contractionBase A) :=
    (dualTorsorZero Q).reindex (universalPath A)
  let k : reindex (dualTorsor P) (universalPath A) ⟶
      reindex (dualTorsor Q) (universalPath A) :=
    (restriction (universalPath A)).map ((dualTorsorFunctor _).map f)
  have ha : k ≫ aQ = aP ≫ (restriction (contractionBase A)).map f := by
    exact congrArg (fun h => (restriction (universalPath A)).map h) (dualTorsorZero_natural f)
  have ha' := congrArg (fun h => h.iso.hom) ha
  have he := congrArg (fun h => h.iso.hom) (evaluationTorsor_natural A f)
  apply SheafTorsor.Arrow.ext
  change ((restriction (contractionBase A)).map f).iso.hom ≫
    (aQ.iso.inv ≫ (evaluationTorsorMap A Q).toArrow.iso.hom) =
      (aP.iso.inv ≫ (evaluationTorsorMap A P).toArrow.iso.hom) ≫ f.iso.hom
  apply (cancel_epi aP.iso.hom).mp
  change k.iso.hom ≫ aQ.iso.hom = aP.iso.hom ≫ _ at ha'
  dsimp only [restriction] at ha' ⊢
  simp only [← Category.assoc]
  rw [← ha']
  simp only [Category.assoc, Iso.hom_inv_id_assoc]
  exact he

def contractionNatIso (A : Code) :
    (restriction (contractionBase A) :
      Torsor G (Y (dual A)) ⥤ Torsor G (Y (dual A))) ≅ 𝟭 _ :=
  NatIso.ofComponents (contractionIso A) (fun {_ _} f => contraction_natural A f)

/-- The projection and zero section, expressed on the existing represented
dual product. -/
abbrev torsorProjection (A : Code) : Y (dual A) ⟶ Y A :=
  representableMap (inl A)

abbrev torsorZero (A : Code) : Y A ⟶ Y (dual A) :=
  representableMap (dualZero A)

theorem torsorZero_projection (A : Code) :
    torsorZero A ≫ torsorProjection A = 𝟙 (Y A) := by
  ext T h
  apply Quiver.Hom.unop_inj
  change inl A ≫ (dualZero A ≫ h.unop) = h.unop
  rw [← Category.assoc, inl_dualZero, Category.id_comp]

theorem torsorProjection_zero (A : Code) :
    torsorProjection A ≫ torsorZero A = contractionBase A := by
  rw [contractionBase, universalPath_zero]
  ext T h
  apply Quiver.Hom.unop_inj
  exact (Category.assoc _ _ _).symm

def torsorProjectionUnit (A : Code) :
    𝟭 (Torsor G (Y A)) ≅ restriction (torsorProjection A) ⋙ restriction (torsorZero A) :=
  eqToIso (by rw [restriction_comp, torsorZero_projection, restriction_id])

def torsorProjectionCounit (A : Code) :
    (restriction (torsorZero A) ⋙ restriction (torsorProjection A) :
      Torsor G (Y (dual A)) ⥤ Torsor G (Y (dual A))) ≅ 𝟭 _ :=
  eqToIso (by rw [restriction_comp, torsorProjection_zero]) ≪≫ contractionNatIso A

/-- Infinitesimal pullback on all locally trivial group-sheaf torsors is an
equivalence. Its inverse is exactly restriction along zero. -/
def torsorProjectionEquivalence (A : Code) :
    Torsor G (Y A) ≌ Torsor G (Y (dual A)) :=
  CategoryTheory.Equivalence.mk (restriction (torsorProjection A)) (restriction (torsorZero A))
    (torsorProjectionUnit A) (torsorProjectionCounit A)

theorem projection_baseChange {A B : Code} (f : A ⟶ B) :
    representableMap (dualMap f) ≫ torsorProjection A =
      torsorProjection B ≫ representableMap f := by
  ext T h
  apply Quiver.Hom.unop_inj
  change inl A ≫ (dualMap f ≫ h.unop) = f ≫ (inl B ≫ h.unop)
  rw [← Category.assoc, dualMap_inl, Category.assoc]

theorem zero_baseChange {A B : Code} (f : A ⟶ B) :
    representableMap f ≫ torsorZero A =
      torsorZero B ≫ representableMap (dualMap f) := by
  ext T h
  apply Quiver.Hom.unop_inj
  change dualZero A ≫ (f ≫ h.unop) = dualMap f ≫ (dualZero B ≫ h.unop)
  rw [← Category.assoc, ← dualZero_natural, Category.assoc]

/-- Pullback equivalences commute with every presentation map, on objects
and equivariant arrows. -/
theorem torsorProjection_baseChange {A B : Code} (f : A ⟶ B) :
    (restriction (representableMap f) ⋙ (torsorProjectionEquivalence B).functor :
      Torsor G (Y A) ⥤ Torsor G (Y (dual B))) =
      (torsorProjectionEquivalence A).functor ⋙ restriction (representableMap (dualMap f)) := by
  change restriction _ ⋙ restriction _ = restriction _ ⋙ restriction _
  rw [restriction_comp, restriction_comp, projection_baseChange]

/-- The prescribed inverse commutes with those same maps. -/
theorem torsorZero_baseChange {A B : Code} (f : A ⟶ B) :
    (restriction (representableMap (dualMap f)) ⋙ (torsorProjectionEquivalence B).inverse :
      Torsor G (Y (dual A)) ⥤ Torsor G (Y B)) =
      (torsorProjectionEquivalence A).inverse ⋙ restriction (representableMap f) := by
  change restriction _ ⋙ restriction _ = restriction _ ⋙ restriction _
  rw [restriction_comp, restriction_comp, zero_baseChange]

/-- Change a torsor's base along an actual sheaf isomorphism. -/
def torsorBaseEquivalence {X Z : Sheaf topology Type} (e : X ≅ Z) :
    Torsor G X ≌ Torsor G Z :=
  CategoryTheory.Equivalence.mk (restriction e.inv) (restriction e.hom)
    (eqToIso (by rw [restriction_comp, e.hom_inv_id, restriction_id]))
    (eqToIso (by rw [restriction_comp, e.inv_hom_id, restriction_id]))

theorem dualRepresentable_projection (A : Code) :
    (dualRepresentable A).hom ≫ torsorProjection A =
      SheafRelation.snd D (Y A) := by
  ext T p
  exact congrArg Quiver.Hom.op (dualLift_inl _ _ _ _)

/-- The zero section of the product sends a generalized point to (0, point). -/
abbrev torsorProductZero (A : Code) : Y A ⟶ SheafRelation.product D (Y A) :=
  torsorZero A ≫ (dualRepresentable A).inv

theorem torsorProductZero_apply (A : Code) (T : Siteᵒᵖ) (x : (Y A).obj.obj T) :
    (torsorProductZero A).hom.app T x = (⟨0, by simp⟩, x) := by
  apply Prod.ext
  · apply Subtype.ext
    change (smoothMap (dualZero A ≫ x.unop)) (eps A).val = 0
    change (smoothMap x.unop) ((smoothMap (dualZero A)) (eps A).val) = 0
    rw [dualZero, dualLift_eps]
    exact (smoothMap x.unop).toAlgHom.map_zero
  · apply Quiver.Hom.unop_inj
    change inl A ≫ (dualZero A ≫ x.unop) = x.unop
    rw [← Category.assoc, inl_dualZero, Category.id_comp]

/-- The advertised projection D × yA → yA, with its literal zero restriction
as inverse, acts by an equivalence on all locally trivial torsors. -/
def infinitesimalTorsorEquivalence (A : Code) :
    Torsor G (Y A) ≌ Torsor G (SheafRelation.product D (Y A)) :=
  (torsorProjectionEquivalence A).trans (torsorBaseEquivalence (dualRepresentable A).symm)

theorem infinitesimalTorsorEquivalence_functor (A : Code) :
    (infinitesimalTorsorEquivalence (H := H) A).functor =
      restriction (SheafRelation.snd D (Y A)) := by
  change restriction _ ⋙ restriction _ = _
  rw [restriction_comp]
  change restriction ((dualRepresentable A).hom ≫ torsorProjection A) = _
  rw [dualRepresentable_projection]

theorem infinitesimalTorsorEquivalence_inverse (A : Code) :
    (infinitesimalTorsorEquivalence (H := H) A).inverse =
      restriction (torsorProductZero A) := rfl

theorem infinitesimalTorsor_baseChange {A B : Code} (f : A ⟶ B) :
    restriction (representableMap f) ⋙ (infinitesimalTorsorEquivalence (H := H) B).functor =
      (infinitesimalTorsorEquivalence (H := H) A).functor ⋙
        restriction (SheafFunction.parameterMap D (representableMap f)) := by
  rw [infinitesimalTorsorEquivalence_functor, infinitesimalTorsorEquivalence_functor,
    restriction_comp, restriction_comp]
  rfl

theorem torsorProductZero_baseChange {A B : Code} (f : A ⟶ B) :
    representableMap f ≫ torsorProductZero A =
      torsorProductZero B ≫ SheafFunction.parameterMap D (representableMap f) := by
  ext T x
  change (torsorProductZero A).hom.app T ((representableMap f).hom.app T x) =
    (SheafFunction.parameterMap D (representableMap f)).hom.app T
      ((torsorProductZero B).hom.app T x)
  rw [torsorProductZero_apply, torsorProductZero_apply]
  rfl

theorem infinitesimalTorsorZero_baseChange {A B : Code} (f : A ⟶ B) :
    restriction (SheafFunction.parameterMap D (representableMap f)) ⋙
        (infinitesimalTorsorEquivalence (H := H) B).inverse =
      (infinitesimalTorsorEquivalence (H := H) A).inverse ⋙
        restriction (representableMap f) := by
  rw [infinitesimalTorsorEquivalence_inverse, infinitesimalTorsorEquivalence_inverse,
    restriction_comp, restriction_comp, torsorProductZero_baseChange]

/-- An empty real locus admits the empty principal cover, so every sheaf has
exactly one section there. Infinitesimal equivalence includes these stages. -/
theorem empty_stage_unique (F : Sheaf topology Type) (A : Code)
    (h : ∀ _r : SmoothAlgebra.Hom (Carrier A) ℝ, False) : Nonempty (Unique (F.obj.obj (atStage A))) := by
  have hs := (isSheaf_iff_principal F.obj).mp
    ((isSheaf_iff_isSheaf_of_type _ _).mp F.property) A Empty Empty.elim (fun r => (h r).elim)
  have hn {V : Site} (f : V ⟶ op A) : ¬ principalPresieve A (Empty.elim : Empty → Carrier A) f := by
    rintro ⟨i⟩; cases i
  obtain ⟨t, ht⟩ := hs (fun _ f hf => (hn f hf).elim) (by
    intro V W Z g₁ g₂ f₁ f₂ h₁ h₂ he
    exact (hn f₁ h₁).elim)
  exact ⟨⟨⟨t⟩, fun a => ht.2 a (by rintro _ _ ⟨i⟩; cases i)⟩⟩

end SquareKit.SmoothOpenSite
