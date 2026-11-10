import SquareKit.Internal.PathTransport.CechMatchingComprehensionEquivalence

/-! Constant relative families retain an independent matching datum in the
coefficient diagram. Base matching data remain arbitrary. -/
noncomputable section
namespace SquareKit.Internal.PathTransport.CechMatching.Comprehension.Constant
open CategoryTheory CategoryTheory.Functor
open SquareKit.Internal.PathTransport.GroupoidModel
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option backward.defeqAttrib.useBackward true
universe u v
variable (D E : StrictDiagram.{u,u})

def data : FamilyData D where
  localFamily := (Functor.const D.localCategory).obj E.localCategory
  doubleFamily := (Functor.const D.doubleCategory).obj E.doubleCategory
  tripleFamily := (Functor.const D.tripleCategory).obj E.tripleCategory
  first := { app := fun _ => E.first, naturality := fun {_ _} _ => rfl }
  second := { app := fun _ => E.second, naturality := fun {_ _} _ => rfl }
  diagonal := { app := fun _ => E.diagonal, naturality := fun {_ _} _ => rfl }
  firstSecond := { app := fun _ => E.firstSecond, naturality := fun {_ _} _ => rfl }
  firstThird := { app := fun _ => E.firstThird, naturality := fun {_ _} _ => rfl }
  secondThird := { app := fun _ => E.secondThird, naturality := fun {_ _} _ => rfl }

def fiberFunctor (B C : Grpd.{u,u}) : Extend ((Functor.const B).obj C) ⥤ C where
  obj x := x.fiber
  map f := f.fiber
  map_id _ := rfl
  map_comp f g := by
    change (𝟙 _) ≫ f.fiber ≫ g.fiber = f.fiber ≫ g.fiber
    exact Category.id_comp _

private theorem eqToHom_app_fiber {B C : Grpd.{u,u}} {K : Type u} [Category.{u} K]
    {F G : K ⥤ Extend ((Functor.const B).obj C)} (p : F = G) (x : K) :
    ((eqToHom p).app x).fiber = eqToHom (by cases p; rfl) := by
  cases p
  rfl

variable (h : (data D E).Coherence)

def projection : StrictMap ((data D E).total h) E where
  localMap := fiberFunctor D.localCategory E.localCategory
  doubleMap := fiberFunctor D.doubleCategory E.doubleCategory
  tripleMap := fiberFunctor D.tripleCategory E.tripleCategory
  first := by
    refine CategoryTheory.Functor.hext (fun _ => rfl) ?_
    intro x y f
    apply heq_of_eq
    change E.first.map f.fiber = (𝟙 _) ≫ E.first.map f.fiber
    exact (Category.id_comp _).symm
  second := by
    refine CategoryTheory.Functor.hext (fun _ => rfl) ?_
    intro x y f
    apply heq_of_eq
    change E.second.map f.fiber = (𝟙 _) ≫ E.second.map f.fiber
    exact (Category.id_comp _).symm
  diagonal := by
    refine CategoryTheory.Functor.hext (fun _ => rfl) ?_
    intro x y f
    apply heq_of_eq
    change E.diagonal.map f.fiber = (𝟙 _) ≫ E.diagonal.map f.fiber
    exact (Category.id_comp _).symm
  firstSecond := by
    refine CategoryTheory.Functor.hext (fun _ => rfl) ?_
    intro x y f
    apply heq_of_eq
    change E.firstSecond.map f.fiber = (𝟙 _) ≫ E.firstSecond.map f.fiber
    exact (Category.id_comp _).symm
  firstThird := by
    refine CategoryTheory.Functor.hext (fun _ => rfl) ?_
    intro x y f
    apply heq_of_eq
    change E.firstThird.map f.fiber = (𝟙 _) ≫ E.firstThird.map f.fiber
    exact (Category.id_comp _).symm
  secondThird := by
    refine CategoryTheory.Functor.hext (fun _ => rfl) ?_
    intro x y f
    apply heq_of_eq
    change E.secondThird.map f.fiber = (𝟙 _) ≫ E.secondThird.map f.fiber
    exact (Category.id_comp _).symm

def toDatum {d : Datum D.toDiagram} (x : Fiber (data D E) h d) : Datum E.toDiagram :=
  (projection D E h).mapDatum x.datum

def overlap (d : Datum D.toDiagram) (e : Datum E.toDiagram) :
    (data D E).firstMap.obj (liftLocal (data D E) d e.localObject) ≅
      (data D E).secondMap.obj (liftLocal (data D E) d e.localObject) where
  hom := ⟨d.overlap.hom, e.overlap.hom⟩
  inv := ⟨d.overlap.inv, e.overlap.inv⟩
  hom_inv_id := by
    refine Grothendieck.ext _ _ d.overlap.hom_inv_id ?_
    change eqToHom _ ≫ (eqToHom _ ≫ e.overlap.hom ≫ e.overlap.inv) = 𝟙 _
    simp
  inv_hom_id := by
    refine Grothendieck.ext _ _ d.overlap.inv_hom_id ?_
    change eqToHom _ ≫ (eqToHom _ ≫ e.overlap.inv ≫ e.overlap.hom) = 𝟙 _
    simp

def fromDatum (d : Datum D.toDiagram) (e : Datum E.toDiagram) : Fiber (data D E) h d where
  localFiber := e.localObject
  overlap := overlap D E d e
  base_overlap := rfl
  diagonal := by
    refine Grothendieck.ext _ _ ?_ ?_
    · change D.diagonal.map d.overlap.hom = _
      simp only [eqToHom_app]
      change D.diagonal.map d.overlap.hom =
        (Grothendieck.comp (eqToHom (Functor.congr_obj h.diagonalFirst (liftLocal (data D E) d e.localObject)))
          (eqToHom (Functor.congr_obj h.diagonalSecond.symm (liftLocal (data D E) d e.localObject)))).base
      dsimp only [Grothendieck.comp]
      rw [Grothendieck.base_eqToHom, Grothendieck.base_eqToHom]
      simpa only [StrictDiagram.toDiagram, eqToIso.hom, eqToIso.inv, eqToHom_app] using d.diagonal
    · change eqToHom _ ≫ (𝟙 _ ≫ E.diagonal.map e.overlap.hom) =
        (Grothendieck.comp ((eqToHom h.diagonalFirst).app (liftLocal (data D E) d e.localObject))
          ((eqToHom h.diagonalSecond.symm).app (liftLocal (data D E) d e.localObject))).fiber
      dsimp only [Grothendieck.comp]
      have h1 := eqToHom_app_fiber (B := D.localCategory) (C := E.localCategory)
        h.diagonalFirst (liftLocal (data D E) d e.localObject)
      have h2 := eqToHom_app_fiber (B := D.localCategory) (C := E.localCategory)
        h.diagonalSecond.symm (liftLocal (data D E) d e.localObject)
      rw [h1, h2]
      change (𝟙 _) ≫ (𝟙 _ ≫ E.diagonal.map e.overlap.hom) =
        (𝟙 _) ≫ eqToHom (Functor.congr_obj E.diagonalFirst e.localObject) ≫
          eqToHom (Functor.congr_obj E.diagonalSecond.symm e.localObject)
      simpa only [eqToHom_refl, Category.id_comp, Functor.id_map, StrictDiagram.toDiagram,
        eqToIso.hom, eqToIso.inv, eqToHom_app] using e.diagonal
  cocycle := by
    refine Grothendieck.ext _ _ ?_ ?_
    · change D.firstSecond.map d.overlap.hom ≫
        ((eqToHom h.tripleMiddle).app (liftLocal (data D E) d e.localObject)).base ≫ D.secondThird.map d.overlap.hom =
        ((eqToHom h.tripleFirst).app (liftLocal (data D E) d e.localObject)).base ≫ D.firstThird.map d.overlap.hom ≫
          ((eqToHom h.tripleLast).app (liftLocal (data D E) d e.localObject)).base
      simp only [eqToHom_app, Grothendieck.base_eqToHom]
      simpa only [StrictDiagram.toDiagram, eqToIso.hom, eqToHom_app] using d.cocycle
    · change eqToHom _ ≫ (Grothendieck.comp
        ((data D E).firstSecondMap.map (overlap D E d e).hom)
        (Grothendieck.comp ((eqToHom h.tripleMiddle).app (liftLocal (data D E) d e.localObject))
          ((data D E).secondThirdMap.map (overlap D E d e).hom))).fiber =
        (Grothendieck.comp ((eqToHom h.tripleFirst).app (liftLocal (data D E) d e.localObject))
          (Grothendieck.comp ((data D E).firstThirdMap.map (overlap D E d e).hom)
            ((eqToHom h.tripleLast).app (liftLocal (data D E) d e.localObject)))).fiber
      dsimp only [Grothendieck.comp]
      have h1 := eqToHom_app_fiber (B := D.tripleCategory) (C := E.tripleCategory)
        h.tripleFirst (liftLocal (data D E) d e.localObject)
      have h2 := eqToHom_app_fiber (B := D.tripleCategory) (C := E.tripleCategory)
        h.tripleMiddle (liftLocal (data D E) d e.localObject)
      have h3 := eqToHom_app_fiber (B := D.tripleCategory) (C := E.tripleCategory)
        h.tripleLast (liftLocal (data D E) d e.localObject)
      rw [h1, h2, h3]
      change (𝟙 _) ≫ ((𝟙 _) ≫ (𝟙 _ ≫ E.firstSecond.map e.overlap.hom) ≫
        (𝟙 _ ≫ eqToHom (Functor.congr_obj E.tripleMiddle e.localObject) ≫ (𝟙 _ ≫ E.secondThird.map e.overlap.hom))) =
        (𝟙 _) ≫ eqToHom (Functor.congr_obj E.tripleFirst e.localObject) ≫
          (𝟙 _ ≫ (𝟙 _ ≫ E.firstThird.map e.overlap.hom) ≫
            eqToHom (Functor.congr_obj E.tripleLast e.localObject))
      simpa only [eqToHom_refl, Category.id_comp, Functor.id_map, StrictDiagram.toDiagram,
        eqToIso.hom, eqToHom_app] using e.cocycle

@[simp] theorem toDatum_overlap {d : Datum D.toDiagram} (x : Fiber (data D E) h d) :
    (toDatum D E h x).overlap.hom = x.overlap.hom.fiber := by
  simp only [toDatum, StrictMap.mapDatum, StrictMap.overlap, projection,
    Iso.trans_hom, Iso.symm_hom, Functor.mapIso_hom, eqToIso.inv, eqToIso.hom,
    eqToHom_refl, Category.id_comp, Category.comp_id]
  rfl

@[simp] theorem toDatum_fromDatum (d : Datum D.toDiagram) (e : Datum E.toDiagram) :
    toDatum D E h (fromDatum D E h d e) = e := by
  refine Datum.ext (d := toDatum D E h (fromDatum D E h d e)) (e := e) rfl ?_
  apply heq_of_eq
  apply Iso.ext
  exact toDatum_overlap D E h _

@[simp] theorem fromDatum_toDatum {d : Datum D.toDiagram} (x : Fiber (data D E) h d) :
    fromDatum D E h d (toDatum D E h x) = x := by
  apply Fiber.datum_injective
  refine Datum.ext (d := (fromDatum D E h d (toDatum D E h x)).datum) (e := x.datum) rfl ?_
  apply heq_of_eq
  apply Iso.ext
  refine Grothendieck.ext _ _ x.base_overlap.symm ?_
  change eqToHom _ ≫ (toDatum D E h x).overlap.hom = x.overlap.hom.fiber
  rw [toDatum_overlap]
  exact Category.id_comp _

def toFunctor (d : Datum D.toDiagram) : Fiber (data D E) h d ⥤ Datum E.toDiagram :=
  Fiber.forget ⋙ (projection D E h).functor

@[simp] theorem toFunctor_localArrow {d : Datum D.toDiagram}
    {x y : Fiber (data D E) h d} (f : x ⟶ y) :
    ((toFunctor D E h d).map f).localArrow = f.matchingArrow.localArrow.fiber := rfl

def fromArrow (d : Datum D.toDiagram) {x y : Datum E.toDiagram} (f : x ⟶ y) :
    fromDatum D E h d x ⟶ fromDatum D E h d y where
  matchingArrow := {
    localArrow := ⟨𝟙 d.localObject, f.localArrow⟩
    commutes := by
      refine Grothendieck.ext _ _ ?_ ?_
      · change D.first.map (𝟙 d.localObject) ≫ d.overlap.hom =
          d.overlap.hom ≫ D.second.map (𝟙 d.localObject)
        rw [D.first.map_id, D.second.map_id]
        exact (Category.id_comp _).trans (Category.comp_id _).symm
      · change eqToHom _ ≫ (𝟙 _ ≫ (𝟙 _ ≫ E.first.map f.localArrow) ≫ y.overlap.hom) =
          𝟙 _ ≫ x.overlap.hom ≫ (𝟙 _ ≫ E.second.map f.localArrow)
        simp only [eqToHom_refl, Category.id_comp]
        exact f.commutes }
  vertical := rfl

def fromFunctor (d : Datum D.toDiagram) : Datum E.toDiagram ⥤ Fiber (data D E) h d where
  obj := fromDatum D E h d
  map := fromArrow D E h d
  map_id _ := rfl
  map_comp f g := by
    apply Fiber.Hom.ext
    apply Datum.Hom.ext
    refine Grothendieck.ext _ _ (Category.id_comp _).symm ?_
    change (𝟙 _) ≫ (f.localArrow ≫ g.localArrow) =
      𝟙 _ ≫ f.localArrow ≫ g.localArrow
    rfl

@[simp] theorem from_to (d : Datum D.toDiagram) :
    fromFunctor D E h d ⋙ toFunctor D E h d = 𝟭 _ := by
  refine CategoryTheory.Functor.ext (toDatum_fromDatum D E h d) ?_
  intro x y f
  apply Datum.Hom.ext
  change f.localArrow = (eqToHom (toDatum_fromDatum D E h d x)).localArrow ≫
    f.localArrow ≫ (eqToHom (toDatum_fromDatum D E h d y).symm).localArrow
  simp only [Datum.eqToHom_localArrow, eqToHom_refl]
  exact ((Category.id_comp _).trans (Category.comp_id _)).symm

@[simp] theorem to_from (d : Datum D.toDiagram) :
    toFunctor D E h d ⋙ fromFunctor D E h d = 𝟭 _ := by
  refine CategoryTheory.Functor.ext (fun x => fromDatum_toDatum D E h x) ?_
  intro x y f
  apply Fiber.Hom.ext
  apply Datum.Hom.ext
  change (⟨𝟙 d.localObject, f.matchingArrow.localArrow.fiber⟩ :
    x.datum.localObject ⟶ y.datum.localObject) =
      (eqToHom (fromDatum_toDatum D E h x)).matchingArrow.localArrow ≫
        f.matchingArrow.localArrow ≫
          (eqToHom (fromDatum_toDatum D E h y).symm).matchingArrow.localArrow
  simp only [Fiber.matchingArrow_eqToHom, Datum.eqToHom_localArrow, eqToHom_refl,
    Category.id_comp, Category.comp_id]
  refine Grothendieck.ext _ _ f.vertical.symm ?_
  exact Category.id_comp _

/-- The pointwise comparison is an isomorphism of categories, retaining the
coefficient datum and its chosen arrows exactly. -/
def categoryIso (d : Datum D.toDiagram) : Grpd.of (Fiber (data D E) h d) ≅ Grpd.of (Datum E.toDiagram) where
  hom := toFunctor D E h d
  inv := fromFunctor D E h d
  hom_inv_id := to_from D E h d
  inv_hom_id := from_to D E h d

@[simp] theorem transport_toDatum {d e : Datum D.toDiagram} (f : d ⟶ e)
    (x : Fiber (data D E) h d) :
    toDatum D E h (Fiber.transport f x) = toDatum D E h x := by
  let p := (projection D E h).functor.map (Fiber.lift f x)
  apply Datum.target_eq p (𝟙 (toDatum D E h x))
  · exact Fiber.transport_localFiber f x
  · change HEq (Fiber.lift f x).localArrow.fiber (𝟙 x.localFiber)
    rw [Fiber.lift_fiber]
    exact eqToHom_heq_id_dom _ _ _

/-- Constant coefficients form a constant natural family over all base matching
data, not only over restricted or globally extendible ones. -/
def familyIso : family (data D E) h ≅
    (Functor.const (Datum D.toDiagram)).obj (Grpd.of (Datum E.toDiagram)) :=
  NatIso.ofComponents (categoryIso D E h) (by
    intro d e f
    refine CategoryTheory.Functor.ext (transport_toDatum D E h f) ?_
    intro x y g
    apply Datum.Hom.ext
    change (Fiber.transportMap f g).matchingArrow.localArrow.fiber =
      (eqToHom (transport_toDatum D E h f x)).localArrow ≫
        g.matchingArrow.localArrow.fiber ≫
          (eqToHom (transport_toDatum D E h f y).symm).localArrow
    have hp := congrArg (fun k => ((projection D E h).functor.map k).localArrow)
      (Fiber.lift_naturality f g)
    simp only [Functor.map_comp, Datum.comp_localArrow] at hp
    change g.matchingArrow.localArrow.fiber ≫ (Fiber.lift f y).localArrow.fiber =
      (Fiber.lift f x).localArrow.fiber ≫
        (Fiber.transportMap f g).matchingArrow.localArrow.fiber at hp
    rw [Fiber.lift_fiber, Fiber.lift_fiber] at hp
    rw [← cancel_epi (eqToHom (congrArg Datum.localObject (transport_toDatum D E h f x)).symm)]
    simp only [Datum.eqToHom_localArrow, ← Category.assoc, eqToHom_trans, eqToHom_refl,
      Category.id_comp]
    exact hp.symm)

/-- Changing a presentation by equality transports the family without changing
its selected fiber objects or arrows. -/
def familyIsoOfEq {D : StrictDiagram.{u,u}} {A B : FamilyData D}
    (q : A = B) (ha : A.Coherence) (hb : B.Coherence) : family A ha ≅ family B hb :=
  eqToIso (by subst B; rfl)

theorem familyIsoOfEq_localFiber {D : StrictDiagram.{u,u}} {A B : FamilyData D}
    (q : A = B) (ha : A.Coherence) (hb : B.Coherence) (d : Datum D.toDiagram)
    (x : Fiber A ha d) :
    HEq (((familyIsoOfEq q ha hb).hom.app d).obj x).localFiber x.localFiber := by
  subst B
  rfl

theorem familyIsoOfEq_overlap {D : StrictDiagram.{u,u}} {A B : FamilyData D}
    (q : A = B) (ha : A.Coherence) (hb : B.Coherence) (d : Datum D.toDiagram)
    (x : Fiber A ha d) :
    HEq (((familyIsoOfEq q ha hb).hom.app d).obj x).overlap.hom.fiber x.overlap.hom.fiber := by
  subst B
  rfl

theorem familyIsoOfEq_arrow {D : StrictDiagram.{u,u}} {A B : FamilyData D}
    (q : A = B) (ha : A.Coherence) (hb : B.Coherence) (d : Datum D.toDiagram)
    {x y : Fiber A ha d} (f : x ⟶ y) :
    HEq (((familyIsoOfEq q ha hb).hom.app d).map f).matchingArrow.localArrow.fiber
      f.matchingArrow.localArrow.fiber := by
  subst B
  rfl

/-- A strict natural isomorphism of groupoid families preserves their total
categories and the entire base projection. -/
def totalFamilyEquivalence {B : Type u} [Groupoid.{u} B]
    {F G : B ⥤ Grpd.{u,u}} (i : F ≅ G) : Extend F ≌ Extend G where
  functor := Grothendieck.map (whiskerRight i.hom Grpd.forgetToCat)
  inverse := Grothendieck.map (whiskerRight i.inv Grpd.forgetToCat)
  unitIso := eqToIso (by
    rw [← Grothendieck.map_comp_eq, ← whiskerRight_comp, i.hom_inv_id,
      whiskerRight_id', Grothendieck.map_id_eq])
  counitIso := eqToIso (by
    rw [← Grothendieck.map_comp_eq, ← whiskerRight_comp, i.inv_hom_id,
      whiskerRight_id', Grothendieck.map_id_eq])
  functor_unitIso_comp x := by
    simp only [eqToIso.hom, eqToHom_app, eqToHom_map, eqToHom_trans, eqToHom_refl]

/-- Equality of diagrams transports matching data and every selected arrow. -/
def diagramIsoOfEq {D E : Diagram.{u,u}} (q : D = E) :
    Grpd.of (Datum D) ≅ Grpd.of (Datum E) :=
  eqToIso (congrArg (fun K => Grpd.of (Datum K)) q)

theorem diagramIsoOfEq_local {D E : Diagram.{u,u}} (q : D = E) (x : Datum D) :
    HEq ((diagramIsoOfEq q).hom.obj x).localObject x.localObject := by
  subst E
  rfl

theorem diagramIsoOfEq_overlap {D E : Diagram.{u,u}} (q : D = E) (x : Datum D) :
    HEq ((diagramIsoOfEq q).hom.obj x).overlap.hom x.overlap.hom := by
  subst E
  rfl

theorem diagramIsoOfEq_arrow {D E : Diagram.{u,u}} (q : D = E)
    {x y : Datum D} (f : x ⟶ y) :
    HEq ((diagramIsoOfEq q).hom.map f).localArrow f.localArrow := by
  subst E
  rfl

def equivalenceOfGrpdIso {C D : Grpd.{u,u}} (i : C ≅ D) : C ≌ D where
  functor := i.hom
  inverse := i.inv
  unitIso := eqToIso i.hom_inv_id.symm
  counitIso := eqToIso i.inv_hom_id
  functor_unitIso_comp _ := by
    simp only [eqToIso.hom, eqToHom_app, eqToHom_map, eqToHom_trans, eqToHom_refl]

end SquareKit.Internal.PathTransport.CechMatching.Comprehension.Constant
