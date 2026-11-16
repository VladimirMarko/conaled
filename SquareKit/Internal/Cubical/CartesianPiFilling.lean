import SquareKit.Internal.Cubical.CartesianPathFilling

/-! Dependent function filling by transporting the generic argument from its target. -/
set_option autoImplicit false
set_option warningAsError true
namespace SquareKit.Cubical.Cartesian
open CategoryTheory
universe u


def restrictedComprehension {Γ : Context.{u}} (A : Family Γ) (φ : Subcontext Γ) :
    restrictContext (φ.reindex (projection A)) ⟶ total (reindex A (restrictInclusion φ)) where
  app _ := TypeCat.ofHom (fun z => ⟨⟨z.val.1,z.property⟩,z.val.2⟩)
  naturality _ _ _ := rfl

def PartialSection.app {Γ : Context.{u}} {A : Family Γ} {B : Family (total A)}
    {φ : Subcontext Γ} (s : PartialSection (pi A B) φ) :
    PartialSection B (φ.reindex (projection A)) :=
  PartialSection.ofRestricted
    (Term.reindex (Cartesian.app (Term.map (piReindex A B (restrictInclusion φ)) s.toRestricted))
      (restrictedComprehension A φ))

theorem PartialSection.app_val {Γ : Context.{u}} {A : Family Γ} {B : Family (total A)}
    {φ : Subcontext Γ} (s : PartialSection (pi A B) φ) (x : (total A).Elements)
    (h : (φ.reindex (projection A)).holds x) :
    s.app.val x h = (s.val ((projection A).mapElements.obj x) h).val (𝟙 _) x.val.2 := rfl

theorem PartialSection.app_reindex {Γ Δ : Context.{u}} {A : Family Γ}
    {B : Family (total A)} {φ : Subcontext Γ} (s : PartialSection (pi A B) φ)
    (σ : Δ ⟶ Γ) :
    ((s.reindex σ).map (piReindex A B σ)).app = s.app.reindex (liftSub A σ) := rfl



namespace OpenBox
variable {Γ Δ E : Context.{u}} {A : Family Γ} {B : Family (total A)}

def applyAlong (p : total (interval Δ) ⟶ Γ) (φ : Subcontext Δ) (r : Term (interval Δ))
    (b : OpenBox (Cartesian.reindex (pi A B) p) φ r) (σ : E ⟶ Δ)
    (v : Term (Cartesian.reindex A (liftSub (interval Δ) σ ≫ p))) :
    OpenBox (Cartesian.reindex B (pair (liftSub (interval Δ) σ ≫ p) v)) (φ.reindex σ) (Term.reindex r σ) where
  tube :=
    (((b.tube.reindex (liftSub (interval Δ) σ)).map
      (piReindex A B (liftSub (interval Δ) σ ≫ p))).app).reindex (pair (𝟙 _) v)
  base :=
    Term.reindex (Cartesian.app (Term.map (piReindex A B (σ ≫ graph r ≫ p))
      (Term.reindex b.base σ))) (pair (𝟙 _) (Term.reindex v (graph (Term.reindex r σ))))
  boundary x h := by
    change ((b.tube.val ((graph r).mapElements.obj (σ.mapElements.obj x)) h).val
      (𝟙 _) (v.val ((graph (Term.reindex r σ)).mapElements.obj x))) =
      ((b.base.val (σ.mapElements.obj x)).val (𝟙 _) _)
    exact congrArg (fun f => f.val (𝟙 _) (v.val ((graph (Term.reindex r σ)).mapElements.obj x))) (b.boundary (σ.mapElements.obj x) h)

theorem applyAlong_reindex (p : total (interval Δ) ⟶ Γ) (φ : Subcontext Δ) (r : Term (interval Δ))
    (b : OpenBox (Cartesian.reindex (pi A B) p) φ r) (σ : E ⟶ Δ)
    (v : Term (Cartesian.reindex A (liftSub (interval Δ) σ ≫ p)))
    {K : Context.{u}} (τ : K ⟶ E) :
    (applyAlong p φ r b σ v).reindex τ =
      applyAlong p φ r b (τ ≫ σ) (Term.reindex v (liftSub (interval E) τ)) := rfl

end OpenBox

namespace FunctionFilling
variable {Γ Δ : Context.{u}} {A : Family Γ} {B : Family (total A)}
abbrev Args (A : Family Γ) (p : total (interval Δ) ⟶ Γ) : Context := total (reindex A p)
def argumentProjection (p : total (interval Δ) ⟶ Γ) : Args A p ⟶ Δ :=
  projection (reindex A p) ≫ projection (interval Δ)
def target (p : total (interval Δ) ⟶ Γ) : Term (interval (Args A p)) :=
  Term.reindex (generic (interval Δ)) (projection (reindex A p))
def argumentPath (p : total (interval Δ) ⟶ Γ) : total (interval (Args A p)) ⟶ Γ :=
  intervalSub (argumentProjection (A := A) p) ≫ p

def argumentBox (p : total (interval Δ) ⟶ Γ) :
    OpenBox (reindex A (argumentPath (A := A) p)) Subcontext.bot (target (A := A) p) where
  tube := ⟨fun _ h => h.elim, fun _ h => h.elim⟩
  base := generic (reindex A p)
  boundary _ h := h.elim

def argument (F : Filling A) (p : total (interval Δ) ⟶ Γ) :
    Term (reindex A (argumentPath (A := A) p)) :=
  F.fill (argumentPath (A := A) p) Subcontext.bot (target (A := A) p) (argumentBox p)

theorem argument_target (F : Filling A) (hF : F.Lawful) (p : total (interval Δ) ⟶ Γ) :
    Term.reindex (argument F p) (graph (target (A := A) p)) = generic (reindex A p) :=
  (hF.fills _ _ _ _).1

def bodyAlong (G : Filling B) (p : total (interval Δ) ⟶ Γ) (φ : Subcontext Δ)
    (r : Term (interval Δ)) (b : OpenBox (reindex (pi A B) p) φ r)
    (v : Term (reindex A (argumentPath (A := A) p)))
    (hv : Term.reindex v (graph (target (A := A) p)) = generic (reindex A p)) :
    Term (reindex B (liftSub A p)) :=
  Term.convert (congrArg (fun σ => reindex B σ)
    (congrArg (pair (projection (reindex A p) ≫ p)) hv))
    (G.comp (pair (argumentPath (A := A) p) v) (φ.reindex (argumentProjection p))
      (Term.reindex r (argumentProjection p)) (target (A := A) p)
      (b.applyAlong p φ r (argumentProjection p) v))

def body (F : Filling A) (hF : F.Lawful) (G : Filling B)
    (p : total (interval Δ) ⟶ Γ) (φ : Subcontext Δ) (r : Term (interval Δ))
    (b : OpenBox (reindex (pi A B) p) φ r) : Term (reindex B (liftSub A p)) :=
  bodyAlong G p φ r b (argument F p) (argument_target F hF p)

def fill (F : Filling A) (hF : F.Lawful) (G : Filling B)
    (p : total (interval Δ) ⟶ Γ) (φ : Subcontext Δ) (r : Term (interval Δ))
    (b : OpenBox (reindex (pi A B) p) φ r) : Term (reindex (pi A B) p) :=
  Term.map (piReindexIso A B p).inv (lam (body F hF G p φ r b))

theorem fill_normalize (F : Filling A) (hF : F.Lawful) (G : Filling B)
    (p : total (interval Δ) ⟶ Γ) (φ : Subcontext Δ) (r : Term (interval Δ))
    (b : OpenBox (reindex (pi A B) p) φ r) :
    Term.map (piReindex A B p) (fill F hF G p φ r b) = lam (body F hF G p φ r b) :=
  Term.map_iso_roundtrip (piReindexIso A B p).symm _

theorem body_tube (F : Filling A) (hF : F.Lawful) (G : Filling B) (hG : G.Lawful)
    (p : total (interval Δ) ⟶ Γ) (φ : Subcontext Δ) (r : Term (interval Δ))
    (b : OpenBox (reindex (pi A B) p) φ r) (z : (Args A p).Elements)
    (hz : φ.holds ((argumentProjection p).mapElements.obj z)) :
    (body F hF G p φ r b).val z =
      (b.tube.val ((projection (reindex A p)).mapElements.obj z) hz).val (𝟙 _) z.val.2 := by
  have hc := Filling.comp_tube hG (pair (argumentPath p) (argument F p))
    (φ.reindex (argumentProjection p)) (Term.reindex r (argumentProjection p)) (target p)
    (b.applyAlong p φ r (argumentProjection p) (argument F p)) z hz
  have ha := congrArg (fun t => t.val z) (argument_target F hF p)
  apply eq_of_heq
  apply (Term.convert_val_heq _ _ z).trans
  apply (heq_of_eq hc).trans
  change HEq ((b.tube.val ((projection (reindex A p)).mapElements.obj z) hz).val
    (𝟙 _) ((Term.reindex (argument F p) (graph (target p))).val z)) _
  rw [ha]
  rfl

theorem body_cap (F : Filling A) (hF : F.Lawful) (G : Filling B) (hG : G.Lawful)
    (p : total (interval Δ) ⟶ Γ) (φ : Subcontext Δ) (r : Term (interval Δ))
    (b : OpenBox (reindex (pi A B) p) φ r) (x : Δ.Elements)
    (a : A.obj ((graph r ≫ p).mapElements.obj x)) :
    (body F hF G p φ r b).val (extendObj (reindex A p) ((graph r).mapElements.obj x) a) =
      (b.base.val x).val (𝟙 _) a := by
  let z := extendObj (reindex A p) ((graph r).mapElements.obj x) a
  have hc := Filling.comp_diagonal hG (pair (argumentPath p) (argument F p))
    (φ.reindex (argumentProjection p)) (Term.reindex r (argumentProjection p)) (target p)
    (b.applyAlong p φ r (argumentProjection p) (argument F p)) z rfl
  have ha := congrArg (fun t => t.val z) (argument_target F hF p)
  apply eq_of_heq
  apply (Term.convert_val_heq _ _ z).trans
  apply hc.trans
  change HEq ((b.base.val x).val (𝟙 _)
    ((Term.reindex (argument F p) (graph (target p))).val z)) _
  rw [ha]
  rfl

set_option backward.isDefEq.respectTransparency false in
theorem fill_tube (F : Filling A) (hF : F.Lawful) (G : Filling B) (hG : G.Lawful)
    (p : total (interval Δ) ⟶ Γ) (φ : Subcontext Δ) (r : Term (interval Δ))
    (b : OpenBox (reindex (pi A B) p) φ r) (x : (total (interval Δ)).Elements)
    (hx : (φ.reindex (projection (interval Δ))).holds x) :
    (fill F hF G p φ r b).val x = b.tube.val x hx := by
  apply ((piReindexIso A B p).app x).toEquiv.injective
  change (Term.map (piReindex A B p) (fill F hF G p φ r b)).val x = _
  rw [fill_normalize]
  apply PiElement.ext
  intro y f a
  have hy := (φ.reindex (projection (interval Δ))).natural f hx
  have hp := congrArg (fun q => q.val (𝟙 _) a) (b.tube.natural f hx)
  change (b.tube.val x hx).val (p.mapElements.map f ≫ 𝟙 _) a =
    (b.tube.val y hy).val (𝟙 _) a at hp
  change (body F hF G p φ r b).val (extendObj (reindex A p) y a) =
    (b.tube.val x hx).val (p.mapElements.map f) a
  apply (body_tube F hF G hG p φ r b (extendObj (reindex A p) y a) hy).trans
  change (b.tube.val y hy).val (𝟙 _) a = (b.tube.val x hx).val (p.mapElements.map f) a
  simpa only [Category.comp_id] using hp.symm

set_option backward.isDefEq.respectTransparency false in
theorem fill_cap (F : Filling A) (hF : F.Lawful) (G : Filling B) (hG : G.Lawful)
    (p : total (interval Δ) ⟶ Γ) (φ : Subcontext Δ) (r : Term (interval Δ))
    (b : OpenBox (reindex (pi A B) p) φ r) :
    Term.reindex (fill F hF G p φ r b) (graph r) = b.base := by
  apply Term.map_injective_of_iso (piReindexIso A B (graph r ≫ p))
  have hn := congrArg (fun s => Term.map
    (piReindex (reindex A p) (reindex B (liftSub A p)) (graph r))
      (Term.reindex s (graph r))) (fill_normalize F hF G p φ r b)
  apply hn.trans
  apply Term.ext
  intro x
  apply PiElement.ext
  intro y f a
  have hp := congrArg (fun q => q.val (𝟙 _) a) (b.base.property f)
  change (b.base.val x).val ((graph r ≫ p).mapElements.map f ≫ 𝟙 _) a =
    (b.base.val y).val (𝟙 _) a at hp
  change (body F hF G p φ r b).val
    (extendObj (reindex A p) ((graph r).mapElements.obj y) a) =
    (b.base.val x).val ((graph r ≫ p).mapElements.map f) a
  exact (body_cap F hF G hG p φ r b y a).trans
    ((by simpa only [Category.comp_id] using hp) : _ = _).symm

theorem argument_uniform (F : Filling A) (hF : F.Lawful)
    (p : total (interval Δ) ⟶ Γ) {Θ : Context.{u}} (σ : Θ ⟶ Δ) :
    argument F (intervalSub σ ≫ p) =
      Term.reindex (argument F p)
        (intervalSub (liftSub (reindex A p) (intervalSub σ))) :=
  hF.uniform (argumentPath p) Subcontext.bot (target p) (argumentBox p)
    (liftSub (reindex A p) (intervalSub σ))

theorem bodyAlong_uniform (G : Filling B) (hG : G.Lawful)
    (p : total (interval Δ) ⟶ Γ) (φ : Subcontext Δ) (r : Term (interval Δ))
    (b : OpenBox (reindex (pi A B) p) φ r)
    (v : Term (reindex A (argumentPath (A := A) p)))
    (hv : Term.reindex v (graph (target p)) = generic (reindex A p))
    {Θ : Context.{u}} (σ : Θ ⟶ Δ) :
    bodyAlong G (intervalSub σ ≫ p) (φ.reindex σ) (Term.reindex r σ) (b.reindex σ)
      (Term.reindex v (intervalSub (liftSub (reindex A p) (intervalSub σ))))
      (congrArg (fun t => Term.reindex t (liftSub (reindex A p) (intervalSub σ))) hv) =
      Term.reindex (bodyAlong G p φ r b v hv) (liftSub (reindex A p) (intervalSub σ)) := by
  let τ := liftSub (reindex A p) (intervalSub σ)
  have h := hG.uniform (pair (argumentPath p) v) (φ.reindex (argumentProjection p))
    (Term.reindex r (argumentProjection p))
    (b.applyAlong p φ r (argumentProjection p) v) τ
  have he := congrArg (fun t => Term.reindex t (graph (target (A := A) (intervalSub σ ≫ p)))) h
  apply Term.ext
  intro x
  apply eq_of_heq
  apply (Term.convert_val_heq _ _ x).trans
  apply HEq.trans _ (Term.convert_val_heq _ _ (τ.mapElements.obj x)).symm
  exact heq_of_eq (congrArg (fun t => t.val x) he)

theorem body_uniform (F : Filling A) (hF : F.Lawful) (G : Filling B) (hG : G.Lawful)
    (p : total (interval Δ) ⟶ Γ) (φ : Subcontext Δ) (r : Term (interval Δ))
    (b : OpenBox (reindex (pi A B) p) φ r) {Θ : Context.{u}} (σ : Θ ⟶ Δ) :
    body F hF G (intervalSub σ ≫ p) (φ.reindex σ) (Term.reindex r σ) (b.reindex σ) =
      Term.reindex (body F hF G p φ r b) (liftSub (reindex A p) (intervalSub σ)) := by
  let p' := intervalSub σ ≫ p
  let τ := liftSub (reindex A p) (intervalSub σ)
  let k : {v : Term (reindex A (argumentPath (A := A) p')) //
      Term.reindex v (graph (target p')) = generic (reindex A p')} →
      Term (reindex B (liftSub A p')) :=
    fun v => bodyAlong G p' (φ.reindex σ) (Term.reindex r σ) (b.reindex σ) v.val v.property
  have he : (⟨argument F p',argument_target F hF p'⟩ :
      {v : Term (reindex A (argumentPath (A := A) p')) //
        Term.reindex v (graph (target p')) = generic (reindex A p')}) =
      ⟨Term.reindex (argument F p) (intervalSub τ),
        congrArg (fun t => Term.reindex t τ) (argument_target F hF p)⟩ :=
    Subtype.ext (argument_uniform F hF p σ)
  exact (congrArg k he).trans (bodyAlong_uniform G hG p φ r b _ _ σ)

theorem fill_uniform (F : Filling A) (hF : F.Lawful) (G : Filling B) (hG : G.Lawful)
    (p : total (interval Δ) ⟶ Γ) (φ : Subcontext Δ) (r : Term (interval Δ))
    (b : OpenBox (reindex (pi A B) p) φ r) {Θ : Context.{u}} (σ : Θ ⟶ Δ) :
    fill F hF G (intervalSub σ ≫ p) (φ.reindex σ) (Term.reindex r σ) (b.reindex σ) =
      Term.reindex (fill F hF G p φ r b) (intervalSub σ) := by
  apply Term.map_injective_of_iso (piReindexIso A B (intervalSub σ ≫ p))
  have hn := congrArg (fun s => Term.map
    (piReindex (reindex A p) (reindex B (liftSub A p)) (intervalSub σ))
      (Term.reindex s (intervalSub σ))) (fill_normalize F hF G p φ r b)
  exact (fill_normalize F hF G _ _ _ _).trans
    ((congrArg lam (body_uniform F hF G hG p φ r b σ)).trans hn.symm)

end FunctionFilling
def piFilling {Γ : Context.{u}} {A : Family Γ} {B : Family (total A)}
    (F : Filling A) (hF : F.Lawful) (G : Filling B) : Filling (pi A B) where
  fill := FunctionFilling.fill F hF G

theorem piFilling_lawful {Γ : Context.{u}} {A : Family Γ} {B : Family (total A)}
    (F : Filling A) (hF : F.Lawful) (G : Filling B) (hG : G.Lawful) :
    (piFilling F hF G).Lawful where
  fills p φ r b := ⟨FunctionFilling.fill_cap F hF G hG p φ r b,
    FunctionFilling.fill_tube F hF G hG p φ r b⟩
  uniform p φ r b σ := FunctionFilling.fill_uniform F hF G hG p φ r b σ

end SquareKit.Cubical.Cartesian
