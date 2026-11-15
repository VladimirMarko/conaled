import SquareKit.Internal.PathTransport.CechMatchingComprehensionTransportComparison

/-! Identity and composition coherence of the selected evaluation transport
comparisons, with the endpoint equalities retained explicitly. -/
noncomputable section
namespace SquareKit.Internal.PathTransport.CechMatching.Comprehension.Evaluation
open CategoryTheory CategoryTheory.Functor GroupoidModel
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option backward.defeqAttrib.useBackward true
universe u
variable {C : Grpd.{u,u}} (G : C ⥤ Grpd.{u,u})

theorem sourceId (c : C) (x : G.obj c) : (G.map (𝟙 c)).obj x = x := by
  rw [G.map_id]
  rfl

theorem sourceComp {c d e : C} (f : c ⟶ d) (g : d ⟶ e) (x : G.obj c) :
    (G.map (f ≫ g)).obj x = (G.map g).obj ((G.map f).obj x) := by
  rw [G.map_comp]
  rfl

theorem sourceTransport_id (c : C) (x : G.obj c) :
    (sourceTransport G (𝟙 c)).hom.app x ≫
      (Grothendieck.ι (G ⋙ Grpd.forgetToCat) c).map (eqToHom (sourceId G c x)) =
    𝟙 _ := by
  apply Grothendieck.ext
  · simp [sourceTransport, Grothendieck.ι]
  · simp [sourceTransport, Grothendieck.ι,
      Grpd.forgetToCat, eqToHom_map]

theorem sourceTransport_comp {c d e : C} (f : c ⟶ d) (g : d ⟶ e) (x : G.obj c) :
    (sourceTransport G (f ≫ g)).hom.app x ≫
      (Grothendieck.ι (G ⋙ Grpd.forgetToCat) e).map (eqToHom (sourceComp G f g x)) =
    (sourceTransport G f).hom.app x ≫
      (sourceTransport G g).hom.app ((G.map f).obj x) := by
  apply Grothendieck.ext
  · simp [sourceTransport, Grothendieck.ι]
  · simp [sourceTransport, Grothendieck.ι,
      Grpd.forgetToCat, eqToHom_map]

variable {D : StrictDiagram.{u,u}} (A : FamilyData D) (h : A.Coherence)
variable (R : C ⥤ Datum D.toDiagram) (E : Extend G ⥤ Datum (A.total h).toDiagram)
variable (hE : E ⋙ (A.projection h).functor =
  Grothendieck.forget (G ⋙ Grpd.forgetToCat) ⋙ R)

theorem totalTransport_id (c : C) (x : G.obj c) :
    (totalTransport A h G R E hE (𝟙 c)).hom.app x ≫
      ((component A h G R E hE c).map (eqToHom (sourceId G c x))).matchingArrow =
    𝟙 _ := by
  have hn := (comparison A h G R E hE c).inv.naturality (eqToHom (sourceId G c x))
  dsimp only [Functor.comp_map, Fiber.forget] at hn
  dsimp only [totalTransport, Iso.trans_hom, NatTrans.comp_app,
    isoWhiskerRight_hom, isoWhiskerLeft_hom, whiskerRight_app, whiskerLeft_app,
    Iso.symm_hom]
  rw [Category.assoc, Category.assoc, ← hn]
  rw [← Functor.map_comp_assoc, sourceTransport_id, E.map_id]
  simp

theorem totalTransport_comp {c d e : C} (f : c ⟶ d) (g : d ⟶ e) (x : G.obj c) :
    (totalTransport A h G R E hE (f ≫ g)).hom.app x ≫
      ((component A h G R E hE e).map (eqToHom (sourceComp G f g x))).matchingArrow =
    (totalTransport A h G R E hE f).hom.app x ≫
      (totalTransport A h G R E hE g).hom.app ((G.map f).obj x) := by
  have hn := (comparison A h G R E hE e).inv.naturality (eqToHom (sourceComp G f g x))
  dsimp only [Functor.comp_map, Fiber.forget] at hn
  dsimp only [totalTransport, Iso.trans_hom, NatTrans.comp_app,
    isoWhiskerRight_hom, isoWhiskerLeft_hom, whiskerRight_app, whiskerLeft_app,
    Iso.symm_hom]
  rw [Category.assoc, Category.assoc, ← hn]
  simp only [Category.assoc]
  rw [← Functor.map_comp_assoc, sourceTransport_comp, E.map_comp]
  simp [Category.assoc]

theorem targetId (c : C) (x : G.obj c) :
    Fiber.transport (R.map (𝟙 c)) ((component A h G R E hE c).obj x) =
      (component A h G R E hE c).obj x := by
  rw [R.map_id, Fiber.transport_id]

theorem targetComp {c d e : C} (f : c ⟶ d) (g : d ⟶ e) (x : G.obj c) :
    Fiber.transport (R.map (f ≫ g)) ((component A h G R E hE c).obj x) =
      Fiber.transport (R.map g)
        (Fiber.transport (R.map f) ((component A h G R E hE c).obj x)) := by
  rw [R.map_comp, Fiber.transport_comp]

theorem lift_targetId (c : C) (x : G.obj c) :
    Fiber.lift (R.map (𝟙 c)) ((component A h G R E hE c).obj x) ≫
      eqToHom (congrArg Fiber.datum (targetId G A h R E hE c x)) = 𝟙 _ := by
  exact Fiber.lift_id_cast (R.map_id c) _ (targetId G A h R E hE c x)

theorem lift_targetComp {c d e : C} (f : c ⟶ d) (g : d ⟶ e) (x : G.obj c) :
    Fiber.lift (R.map (f ≫ g)) ((component A h G R E hE c).obj x) ≫
      eqToHom (congrArg Fiber.datum (targetComp G A h R E hE f g x)) =
    Fiber.lift (R.map f) ((component A h G R E hE c).obj x) ≫
      Fiber.lift (R.map g)
        (Fiber.transport (R.map f) ((component A h G R E hE c).obj x)) := by
  exact Fiber.lift_comp_cast (R.map f) (R.map g) (R.map_comp f g) _
    (targetComp G A h R E hE f g x)

/-- Identity coherence of the selected comparison, including endpoint casts. -/
theorem transportComparison_id (c : C) (x : G.obj c) :
    (transportComparison A h G R E hE (𝟙 c)).inv.app x ≫
      (component A h G R E hE c).map (eqToHom (sourceId G c x)) =
    eqToHom (targetId G A h R E hE c x) := by
  apply Fiber.Hom.ext
  apply (cancel_epi (Fiber.lift (R.map (𝟙 c)) ((component A h G R E hE c).obj x))).1
  change Fiber.lift _ _ ≫
      (((transportComparison A h G R E hE (𝟙 c)).inv.app x).matchingArrow ≫
        ((component A h G R E hE c).map (eqToHom (sourceId G c x))).matchingArrow) = _
  rw [← Category.assoc, transportComparison_factor,
    totalTransport_id, Fiber.matchingArrow_eqToHom, lift_targetId]
  rfl

/-- Composition coherence of the chosen comparisons, on every fiber object. -/
theorem transportComparison_comp {c d e : C} (f : c ⟶ d) (g : d ⟶ e) (x : G.obj c) :
    (transportComparison A h G R E hE (f ≫ g)).inv.app x ≫
      (component A h G R E hE e).map (eqToHom (sourceComp G f g x)) =
    eqToHom (targetComp G A h R E hE f g x) ≫
      (Fiber.transportFunctor (R.map g)).map
        ((transportComparison A h G R E hE f).inv.app x) ≫
      (transportComparison A h G R E hE g).inv.app ((G.map f).obj x) := by
  apply Fiber.Hom.ext
  apply (cancel_epi (Fiber.lift (R.map (f ≫ g))
    ((component A h G R E hE c).obj x))).1
  change Fiber.lift _ _ ≫
      (((transportComparison A h G R E hE (f ≫ g)).inv.app x).matchingArrow ≫
        ((component A h G R E hE e).map (eqToHom (sourceComp G f g x))).matchingArrow) =
    Fiber.lift _ _ ≫ ((eqToHom (targetComp G A h R E hE f g x)).matchingArrow ≫
      (((Fiber.transportFunctor (R.map g)).map
        ((transportComparison A h G R E hE f).inv.app x)).matchingArrow ≫
      ((transportComparison A h G R E hE g).inv.app ((G.map f).obj x)).matchingArrow))
  rw [← Category.assoc, transportComparison_factor, totalTransport_comp]
  rw [Fiber.matchingArrow_eqToHom, ← Category.assoc, lift_targetComp]
  change _ = (Fiber.lift (R.map f) _ ≫ Fiber.lift (R.map g) _) ≫
    ((inv (Fiber.lift (R.map g) _) ≫
      ((transportComparison A h G R E hE f).inv.app x).matchingArrow ≫
        Fiber.lift (R.map g) _) ≫
      ((transportComparison A h G R E hE g).inv.app ((G.map f).obj x)).matchingArrow)
  simp only [Category.assoc, IsIso.hom_inv_id_assoc]
  rw [← Category.assoc, transportComparison_factor]
  dsimp only [Functor.comp_obj]
  rw [transportComparison_factor]

end SquareKit.Internal.PathTransport.CechMatching.Comprehension.Evaluation
