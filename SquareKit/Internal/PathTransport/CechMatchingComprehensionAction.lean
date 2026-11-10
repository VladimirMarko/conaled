import SquareKit.Internal.PathTransport.CechMatchingComprehensionFiber
import SquareKit.Internal.PathTransport.CechMatchingComprehensionRebase

/-! Relative matching objects transport along the actual local-family action. -/
noncomputable section
namespace SquareKit.Internal.PathTransport.CechMatching.Comprehension
open CategoryTheory
open SquareKit.Internal.PathTransport.GroupoidModel
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option backward.defeqAttrib.useBackward true
universe u
variable {D : StrictDiagram.{u,u}} {A : FamilyData D} {h : A.Coherence}
namespace Fiber
variable {d e : Datum D.toDiagram}

def transportLocalIso (f : d ⟶ e) (x : Fiber A h d) :
    x.datum.localObject ≅ liftLocal A e ((A.localFamily.map f.localArrow).obj x.localFiber) :=
  (Grothendieck.transportIso x.datum.localObject (asIso f.localArrow)).symm

def transportedDatum (f : d ⟶ e) (x : Fiber A h d) : Datum (A.total h).toDiagram :=
  x.datum.rebase (transportLocalIso f x)

def transportArrow (f : d ⟶ e) (x : Fiber A h d) : x.datum ⟶ transportedDatum f x :=
  x.datum.rebaseArrow (transportLocalIso f x)

theorem transported_projection (f : d ⟶ e) (x : Fiber A h d) :
    (A.projection h).mapDatum (transportedDatum f x) = e := by
  let p := (A.projection h).functor.map (transportArrow f x)
  let q := eqToHom (projection_datum x) ≫ f
  apply Datum.target_eq p q rfl
  apply heq_of_eq
  change f.localArrow = (eqToHom (projection_datum x) ≫ f).localArrow
  simp only [Datum.comp_localArrow, Datum.eqToHom_localArrow, eqToHom_refl,
    Category.id_comp]

def transport (f : d ⟶ e) (x : Fiber A h d) : Fiber A h e :=
  ofDatum (transportedDatum f x) (transported_projection f x)

@[simp] theorem transport_datum (f : d ⟶ e) (x : Fiber A h d) :
    (transport f x).datum = transportedDatum f x := datum_ofDatum _ _

@[simp] theorem transport_localFiber (f : d ⟶ e) (x : Fiber A h d) :
    (transport f x).localFiber = (A.localFamily.map f.localArrow).obj x.localFiber :=
  eq_of_heq (localFiber_ofDatum _ _)

/-- The chosen lift has exactly the supplied local base arrow. -/
def lift (f : d ⟶ e) (x : Fiber A h d) : x.datum ⟶ (transport f x).datum :=
  transportArrow f x ≫ eqToHom (transport_datum f x).symm

@[simp] theorem lift_base (f : d ⟶ e) (x : Fiber A h d) :
    (lift f x).localArrow.base = f.localArrow := by
  simp only [lift, Datum.comp_localArrow, Datum.eqToHom_localArrow]
  change f.localArrow ≫ (eqToHom (congrArg Datum.localObject
    (transport_datum f x).symm)).base = f.localArrow
  rw [Grothendieck.base_eqToHom]
  simp only [eqToHom_refl]
  exact Category.comp_id f.localArrow

/-- Conjugation by the chosen lifts transports vertical matching arrows. -/
def transportMap (f : d ⟶ e) {x y : Fiber A h d} (g : x ⟶ y) :
    transport f x ⟶ transport f y where
  matchingArrow := inv (lift f x) ≫ g.matchingArrow ≫ lift f y
  vertical := by
    change (Datum.localFunctor ⋙ Grothendieck.forget
      (A.localFamily ⋙ Grpd.forgetToCat)).map
      (inv (lift f x) ≫ g.matchingArrow ≫ lift f y) = _
    simp only [Functor.map_comp, Functor.map_inv]
    change inv (lift f x).localArrow.base ≫
      g.matchingArrow.localArrow.base ≫ (lift f y).localArrow.base = _
    rw [lift_base, lift_base, g.vertical]
    exact (congrArg (fun k => inv f.localArrow ≫ k)
      (Category.id_comp f.localArrow)).trans (IsIso.inv_hom_id f.localArrow)

def transportFunctor (f : d ⟶ e) : Fiber A h d ⥤ Fiber A h e where
  obj := transport f
  map := transportMap f
  map_id x := by
    apply Hom.ext
    change inv (lift f x) ≫ 𝟙 x.datum ≫ lift f x = 𝟙 _
    simp
  map_comp g k := by
    apply Hom.ext
    change inv (lift f _) ≫ (g.matchingArrow ≫ k.matchingArrow) ≫ lift f _ =
      (inv (lift f _) ≫ g.matchingArrow ≫ lift f _) ≫
        (inv (lift f _) ≫ k.matchingArrow ≫ lift f _)
    simp

@[simp] theorem lift_fiber (f : d ⟶ e) (x : Fiber A h d) :
    (lift f x).localArrow.fiber = eqToHom (by
      rw [lift_base]
      exact (transport_localFiber f x).symm) := by
  have aux : ∀ (z : Datum (A.total h).toDiagram)
      (q : transportedDatum f x = z), ∃ p,
      (transportArrow f x ≫ eqToHom q).localArrow.fiber = eqToHom p := by
    intro z q
    subst z
    change ∃ p, (Grothendieck.comp (transportArrow f x).localArrow
      (Grothendieck.id (transportedDatum f x).localObject)).fiber = eqToHom p
    refine ⟨?_, ?_⟩
    · change (A.localFamily.map (f.localArrow ≫ 𝟙 _)).obj x.localFiber = _
      rw [Category.comp_id]
      rfl
    · dsimp only [Grothendieck.comp, Grothendieck.id]
      change eqToHom _ ≫ ((A.localFamily ⋙ Grpd.forgetToCat).map _).toFunctor.map (𝟙 _) ≫
        eqToHom _ = _
      simp
  obtain ⟨p, hp⟩ := aux _ (transport_datum f x).symm
  exact hp

private theorem transportLocal_id (x : Fiber A h d) :
    (transportedDatum (𝟙 d) x).localObject = x.datum.localObject := by
  change (⟨d.localObject, (A.localFamily.map (𝟙 d.localObject)).obj x.localFiber⟩ :
    Extend A.localFamily) = ⟨d.localObject, x.localFiber⟩
  rw [A.localFamily.map_id]
  rfl

private theorem transportArrow_id (x : Fiber A h d) :
    (transportArrow (𝟙 d) x).localArrow = eqToHom (transportLocal_id x).symm := by
  refine Grothendieck.ext _ _ ?_ ?_
  · change 𝟙 d.localObject = (eqToHom (transportLocal_id x).symm).base
    rw [Grothendieck.base_eqToHom]
    rfl
  · change eqToHom _ ≫ 𝟙 _ = (eqToHom (transportLocal_id x).symm).fiber
    rw [Grothendieck.fiber_eqToHom]
    simp

@[simp] theorem transport_id (x : Fiber A h d) : transport (𝟙 d) x = x := by
  apply datum_injective
  rw [transport_datum]
  apply Datum.target_eq (transportArrow (𝟙 d) x) (𝟙 x.datum) (transportLocal_id x)
  rw [transportArrow_id]
  simp only [Datum.id_localArrow]
  exact eqToHom_heq_id_dom _ _ _

private theorem transportLocal_comp {k : Datum D.toDiagram}
    (f : d ⟶ e) (g : e ⟶ k) (x : Fiber A h d) :
    (transport (f ≫ g) x).datum.localObject =
      (transport g (transport f x)).datum.localObject := by
  change liftLocal A k _ = liftLocal A k _
  congr 1
  rw [transport_localFiber, transport_localFiber, transport_localFiber]
  change (A.localFamily.map (f.localArrow ≫ g.localArrow)).obj x.localFiber = _
  rw [A.localFamily.map_comp]
  rfl

private theorem lift_local_comp {k : Datum D.toDiagram}
    (f : d ⟶ e) (g : e ⟶ k) (x : Fiber A h d) :
    (lift (f ≫ g) x).localArrow ≫ eqToHom (transportLocal_comp f g x) =
      (lift f x).localArrow ≫ (lift g (transport f x)).localArrow := by
  refine Grothendieck.ext _ _ ?_ ?_
  · change (lift (f ≫ g) x).localArrow.base ≫
      (eqToHom (transportLocal_comp f g x)).base =
        (lift f x).localArrow.base ≫ (lift g (transport f x)).localArrow.base
    rw [Grothendieck.base_eqToHom, lift_base, lift_base, lift_base]
    exact Category.comp_id _
  · change eqToHom _ ≫ (Grothendieck.comp _ _).fiber = (Grothendieck.comp _ _).fiber
    dsimp only [Grothendieck.comp]
    rw [Grothendieck.fiber_eqToHom, lift_fiber, lift_fiber, lift_fiber]
    simp [eqToHom_map]

@[simp] theorem transport_comp {k : Datum D.toDiagram}
    (f : d ⟶ e) (g : e ⟶ k) (x : Fiber A h d) :
    transport (f ≫ g) x = transport g (transport f x) := by
  apply datum_injective
  apply Datum.target_eq (lift (f ≫ g) x) (lift f x ≫ lift g (transport f x))
    (transportLocal_comp f g x)
  apply (comp_eqToHom_heq _ (transportLocal_comp f g x)).symm.trans
  exact heq_of_eq (lift_local_comp f g x)

@[simp] theorem lift_id (x : Fiber A h d) :
    lift (𝟙 d) x = eqToHom (congrArg datum (transport_id x)).symm := by
  apply Datum.Hom.ext
  rw [Datum.eqToHom_localArrow]
  refine Grothendieck.ext _ _ ?_ ?_
  · rw [lift_base, Grothendieck.base_eqToHom]
    rfl
  · rw [Grothendieck.fiber_eqToHom, lift_fiber]
    simp

@[simp] theorem lift_comp {k : Datum D.toDiagram}
    (f : d ⟶ e) (g : e ⟶ k) (x : Fiber A h d) :
    lift (f ≫ g) x ≫ eqToHom (congrArg datum (transport_comp f g x)) =
      lift f x ≫ lift g (transport f x) := by
  apply Datum.Hom.ext
  simp only [Datum.comp_localArrow, Datum.eqToHom_localArrow]
  exact lift_local_comp f g x

@[simp] theorem matchingArrow_eqToHom {x y : Fiber A h d} (q : x = y) :
    (eqToHom q).matchingArrow = eqToHom (congrArg datum q) := by
  subst y
  rfl

@[simp] theorem transportFunctor_id (d : Datum D.toDiagram) :
    transportFunctor (A := A) (h := h) (𝟙 d) = 𝟭 (Fiber A h d) := by
  refine CategoryTheory.Functor.ext (fun x => transport_id x) ?_
  intro x y g
  apply Hom.ext
  change inv (lift (𝟙 d) x) ≫ g.matchingArrow ≫ lift (𝟙 d) y =
    (eqToHom (transport_id x)).matchingArrow ≫ g.matchingArrow ≫
      (eqToHom (transport_id y).symm).matchingArrow
  rw [lift_id, lift_id, matchingArrow_eqToHom, matchingArrow_eqToHom]
  simp

@[simp] theorem transportFunctor_comp {k : Datum D.toDiagram}
    (f : d ⟶ e) (g : e ⟶ k) :
    transportFunctor (A := A) (h := h) (f ≫ g) =
      transportFunctor f ⋙ transportFunctor g := by
  refine CategoryTheory.Functor.ext (fun x => transport_comp f g x) ?_
  intro x y a
  apply Hom.ext
  change inv (lift (f ≫ g) x) ≫ a.matchingArrow ≫ lift (f ≫ g) y =
    (eqToHom (transport_comp f g x)).matchingArrow ≫
      (inv (lift g (transport f x)) ≫
        (inv (lift f x) ≫ a.matchingArrow ≫ lift f y) ≫ lift g (transport f y)) ≫
      (eqToHom (transport_comp f g y).symm).matchingArrow
  rw [matchingArrow_eqToHom, matchingArrow_eqToHom]
  have hx := lift_comp f g x
  have hy := lift_comp f g y
  rw [← cancel_mono (eqToHom (congrArg datum (transport_comp f g y)))]
  simp only [Category.assoc, eqToHom_trans, eqToHom_refl, Category.comp_id]
  rw [← hy]
  have hi := congrArg (fun a => inv a) hx
  simp only [IsIso.inv_comp, inv_eqToHom] at hi
  have hi2 : eqToHom (congrArg datum (transport_comp f g x)) ≫
      inv (lift g (transport f x)) ≫ inv (lift f x) = inv (lift (f ≫ g) x) := by
    rw [← hi]
    simp
  simp only [← Category.assoc] at hi2 ⊢
  rw [hi2]

end Fiber

/-- The relative matching groupoids vary strictly over independent base data. -/
def family {D : StrictDiagram.{u,u}} (A : FamilyData D) (h : A.Coherence) :
    Datum D.toDiagram ⥤ Grpd.{u,u} where
  obj d := Grpd.of (Fiber A h d)
  map f := Fiber.transportFunctor f
  map_id d := Fiber.transportFunctor_id d
  map_comp f g := Fiber.transportFunctor_comp f g

end SquareKit.Internal.PathTransport.CechMatching.Comprehension
