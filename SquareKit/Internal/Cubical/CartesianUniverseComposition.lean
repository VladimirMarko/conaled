import SquareKit.Internal.Cubical.CartesianIntervalTransport
import SquareKit.Internal.Cubical.CartesianRelativeExtension
import SquareKit.Internal.Cubical.CartesianSmallFamilyClassification
import SquareKit.Internal.Cubical.CartesianDependentFilling

/-! Filling the universal decoding family over the larger code context, by
small represented charts. The lift changes the native interface universe only. -/
set_option autoImplicit false
set_option warningAsError true
namespace SquareKit.Cubical.Cartesian
open CategoryTheory
universe u

namespace SmallUniverse

def liftedDecode {Ξ : Context.{u+1}} (a : Ξ ⟶ smallFamilyCodes.{u}) : Family Ξ :=
  a.mapElements ⋙ universalDecode ⋙ uliftFunctor.{u+1,u}

def chartFace {Γ : Context.{u}} {Δ : Context.{u+1}}
    (φ : Subcontext Δ) (σ : raisedContext Γ ⟶ Δ) : Subcontext Γ where
  Holds x := φ.Holds ((raisedElements Γ ⋙ σ.mapElements).obj x)
  natural f hx := φ.natural ((raisedElements Γ ⋙ σ.mapElements).map f) hx

def chartInterval {Γ : Context.{u}} {Δ : Context.{u+1}} (σ : raisedContext Γ ⟶ Δ) :
    raisedContext (total (interval Γ)) ⟶ total (interval Δ) where
  app I := TypeCat.ofHom (fun x => ⟨σ.app I ⟨x.down.1⟩,⟨x.down.2.down⟩⟩)
  naturality I J f := by
    apply ConcreteCategory.hom_ext
    intro x
    apply Sigma.ext
    · exact σ.naturality_apply f ⟨x.down.1⟩
    · rfl

def chartSource {Γ : Context.{u}} {Δ : Context.{u+1}} (σ : raisedContext Γ ⟶ Δ)
    (r : Term (interval Δ)) : Term (interval Γ) where
  val x := ⟨(r.val ((raisedElements Γ ⋙ σ.mapElements).obj x)).down⟩
  property {x y} f := by
    have hr := r.property ((raisedElements Γ ⋙ σ.mapElements).map f)
    have hh := congrArg (fun z : ULift.{u+1} (Cube.Hom y.obj.unop ⟨1⟩) => z.down) hr
    exact congrArg (fun z => (ULift.up z : ULift.{u} (Cube.Hom y.obj.unop ⟨1⟩))) hh

def raisedIntervalIso (Γ : Context.{u}) :
    raisedContext (total (interval Γ)) ≅ total (interval (raisedContext Γ)) where
  hom := chartInterval (𝟙 (raisedContext Γ))
  inv := {
    app := fun _ => TypeCat.ofHom (fun x => ⟨⟨x.1.down,⟨x.2.down⟩⟩⟩)
    naturality := fun _ _ _ => rfl }
  hom_inv_id := rfl
  inv_hom_id := rfl

namespace NativeDecode
variable {Γ Θ : Context.{u}} {Ξ : Context.{u+1}}

def pullTerm {a : Ξ ⟶ smallFamilyCodes.{u}} (σ : raisedContext Γ ⟶ Ξ)
    (t : Term (liftedDecode a)) : Term (Cartesian.decode (σ ≫ a)) where
  val x := (t.val ((raisedElements Γ ⋙ σ.mapElements).obj x)).down
  property f := congrArg ULift.down (t.property ((raisedElements Γ ⋙ σ.mapElements).map f))

def pullPartial {a : Ξ ⟶ smallFamilyCodes.{u}} {φ : Subcontext Ξ}
    (σ : raisedContext Γ ⟶ Ξ) (t : PartialSection (liftedDecode a) φ) :
    PartialSection (Cartesian.decode (σ ≫ a)) (chartFace φ σ) where
  val x hx := (t.val ((raisedElements Γ ⋙ σ.mapElements).obj x) hx).down
  natural f hx := congrArg ULift.down
    (t.natural ((raisedElements Γ ⋙ σ.mapElements).map f) hx)

variable {φ : Subcontext Ξ} {r : Term (interval Ξ)}
    (a : total (interval Ξ) ⟶ smallFamilyCodes.{u}) (b : OpenBox (liftedDecode a) φ r)

def chartBox (σ : raisedContext Γ ⟶ Ξ) :
    OpenBox (Cartesian.decode (chartInterval σ ≫ a)) (chartFace φ σ) (chartSource σ r) where
  base := pullTerm (a := graph r ≫ a) σ b.base
  tube := pullPartial (chartInterval σ) b.tube
  boundary x hx := congrArg ULift.down (b.boundary ((raisedElements Γ ⋙ σ.mapElements).obj x) hx)

theorem chartBox_reindex (σ : raisedContext Γ ⟶ Ξ) (τ : Θ ⟶ Γ) :
    (chartBox a b σ).reindex τ = chartBox a b (raisedSub τ ≫ σ) := rfl

private def selectedFill (L : LocalFamily (total (interval Γ))) (ψ : Subcontext Γ)
    (s : Term (interval Γ)) (c : OpenBox L.family ψ s) : Term L.family :=
  L.toFilling.fill (𝟙 _) ψ s c

private theorem selectedFill_reindex (L : LocalFamily (total (interval Γ))) (ψ : Subcontext Γ)
    (s : Term (interval Γ)) (c : OpenBox L.family ψ s) (τ : Θ ⟶ Γ) :
    Term.reindex (selectedFill L ψ s c) (intervalSub τ) =
      selectedFill (L.reindex (intervalSub τ)) (ψ.reindex τ) (Term.reindex s τ) (c.reindex τ) :=
  (L.toFilling_lawful.uniform (𝟙 _) ψ s c τ).symm

private theorem selectedFill_congr {L M : LocalFamily (total (interval Γ))}
    (h : L = M) (ψ : Subcontext Γ) (s : Term (interval Γ))
    (c : OpenBox L.family ψ s) (d : OpenBox M.family ψ s)
    (hc : HEq c d) : HEq (selectedFill L ψ s c) (selectedFill M ψ s d) := by
  cases h
  cases hc
  rfl

def chartFilled (σ : raisedContext Γ ⟶ Ξ) :
    Term (Cartesian.decode (chartInterval σ ≫ a)) :=
  selectedFill (decodedLocalFamily (chartInterval σ ≫ a)) (chartFace φ σ)
    (chartSource σ r) (chartBox a b σ)

theorem chartFilled_fills (σ : raisedContext Γ ⟶ Ξ) :
    (chartBox a b σ).Fills (chartFilled a b σ) :=
  (decodedLocalFamily (chartInterval σ ≫ a)).toFilling_lawful.fills _ _ _ _

theorem chartFilled_reindex (σ : raisedContext Γ ⟶ Ξ) (τ : Θ ⟶ Γ) :
    Term.reindex (chartFilled a b σ) (intervalSub τ) =
      chartFilled a b (raisedSub τ ≫ σ) :=
  (selectedFill_reindex _ _ _ _ τ).trans (eq_of_heq
    (selectedFill_congr (decodedLocalFamily_reindex (chartInterval σ ≫ a) (intervalSub τ)).symm
      (chartFace φ (raisedSub τ ≫ σ)) (chartSource (raisedSub τ ≫ σ) r) _ _ HEq.rfl))

/-- Raising a small represented chart has the same cube points as the native
represented chart at the larger universe level. -/
def representedRaise (I : Cube) : raisedContext (representable.{u} I) ⟶ representable.{u+1} I where
  app _ := TypeCat.ofHom (fun x => ⟨x.down.down⟩)
  naturality _ _ _ := rfl

def lowerIntervalElements (I : Cube) :
    (total (interval (representable.{u+1} I))).Elements ⥤
      (total (interval (representable.{u} I))).Elements where
  obj x := (total (interval (representable.{u} I))).elementsMk x.obj
    ⟨⟨x.val.1.down⟩,⟨x.val.2.down⟩⟩
  map {_x y} f := Functor.Elements.homMk f.hom
    (congrArg (fun z : (total (interval (representable.{u+1} I))).obj y.obj =>
      (⟨⟨z.1.down⟩,⟨z.2.down⟩⟩ :
        (total (interval (representable.{u} I))).obj y.obj)) f.map_val)
  map_id _ := rfl
  map_comp _ _ := rfl

def raiseRepresentedTerm {I : Cube}
    (c : total (interval (representable.{u+1} I)) ⟶ smallFamilyCodes.{u})
    (t : Term (Cartesian.decode (chartInterval (representedRaise I) ≫ c))) :
    Term (liftedDecode c) where
  val x := ⟨t.val ((lowerIntervalElements I).obj x)⟩
  property f := congrArg ULift.up (t.property ((lowerIntervalElements I).map f))

def fillRepresented {I : Cube}
    (c : total (interval (representable.{u+1} I)) ⟶ smallFamilyCodes.{u})
    {ψ : Subcontext (representable.{u+1} I)} {s : Term (interval (representable.{u+1} I))}
    (d : OpenBox (liftedDecode c) ψ s) :
    Term (liftedDecode c) :=
  raiseRepresentedTerm c (chartFilled c d (representedRaise I))

theorem fillRepresented_fills {I : Cube}
    (c : total (interval (representable.{u+1} I)) ⟶ smallFamilyCodes.{u})
    {ψ : Subcontext (representable.{u+1} I)} {s : Term (interval (representable.{u+1} I))}
    (d : OpenBox (liftedDecode c) ψ s) :
    d.Fills (fillRepresented c d) := by
  constructor
  · apply Term.ext
    intro x
    exact congrArg (fun t => ULift.up (t.val ((representable.{u} I).elementsMk x.obj ⟨x.val.down⟩)))
      (chartFilled_fills c d (representedRaise I)).1
  · intro x hx
    exact congrArg ULift.up ((chartFilled_fills c d (representedRaise I)).2
      ((lowerIntervalElements I).obj x) hx)

theorem fillRepresented_reindex {I J : Cube}
    (c : total (interval (representable.{u+1} I)) ⟶ smallFamilyCodes.{u})
    {ψ : Subcontext (representable.{u+1} I)} {s : Term (interval (representable.{u+1} I))}
    (d : OpenBox (liftedDecode c) ψ s) (f : J ⟶ I) :
    Term.reindex (fillRepresented c d) (intervalSub (representableMap f)) =
      fillRepresented (intervalSub (representableMap f) ≫ c)
        (d.reindex (representableMap f)) := by
  apply Term.ext
  intro x
  exact congrArg (fun t => ULift.up (t.val ((lowerIntervalElements J).obj x)))
    (chartFilled_reindex c d (representedRaise I) (representableMap f))

def localFilling {Ω : Context.{u+1}} (c : Ω ⟶ smallFamilyCodes.{u}) :
    LocalFilling (liftedDecode c) where
  fill p _ _ d := fillRepresented (p ≫ c) d

theorem localFilling_lawful {Ω : Context.{u+1}} (c : Ω ⟶ smallFamilyCodes.{u}) :
    (localFilling c).Lawful where
  fills p _ _ d := fillRepresented_fills (p ≫ c) d
  uniform p _ _ d f := (fillRepresented_reindex (p ≫ c) d f).symm

def filling {Ω : Context.{u+1}} (c : Ω ⟶ smallFamilyCodes.{u}) :
    Filling (liftedDecode c) := (localFilling c).toFilling (localFilling_lawful c)

theorem filling_lawful {Ω : Context.{u+1}} (c : Ω ⟶ smallFamilyCodes.{u}) :
    (filling c).Lawful := (localFilling c).toFilling_lawful (localFilling_lawful c)


theorem filling_reindex {Ω Λ : Context.{u+1}} (c : Ω ⟶ smallFamilyCodes.{u}) (σ : Λ ⟶ Ω) :
    (filling c).reindex σ = filling (σ ≫ c) := rfl

end NativeDecode
end SmallUniverse
namespace Raising

def lowerElements (Γ : Context.{u}) : (raisedContext Γ).Elements ⥤ Γ.Elements where
  obj x := Γ.elementsMk x.obj x.val.down
  map f := Functor.Elements.homMk f.hom (congrArg ULift.down f.map_val)
  map_id _ := rfl
  map_comp _ _ := rfl

def family {Γ : Context.{u}} (A : Family Γ) : Family (raisedContext Γ) where
  obj x := ULift.{u+1} (A.obj ((lowerElements Γ).obj x))
  map f := TypeCat.ofHom (fun a => ⟨A.map ((lowerElements Γ).map f) a.down⟩)
  map_id x := by
    apply ConcreteCategory.hom_ext
    intro a
    exact congrArg ULift.up (ConcreteCategory.congr_hom (A.map_id _) a.down)
  map_comp f g := by
    apply ConcreteCategory.hom_ext
    intro a
    exact congrArg ULift.up (ConcreteCategory.congr_hom (A.map_comp ((lowerElements Γ).map f) ((lowerElements Γ).map g)) a.down)

def raiseTerm {Γ : Context.{u}} {A : Family Γ} (a : Term A) : Term (family A) where
  val x := ⟨a.val ((lowerElements Γ).obj x)⟩
  property f := congrArg ULift.up (a.property ((lowerElements Γ).map f))

def lowerTerm {Γ : Context.{u}} {A : Family Γ} (a : Term (family A)) : Term A where
  val x := (a.val ((raisedElements Γ).obj x)).down
  property f := congrArg ULift.down (a.property ((raisedElements Γ).map f))

theorem lower_raise {Γ : Context.{u}} {A : Family Γ} (a : Term A) :
    lowerTerm (raiseTerm a) = a := rfl

theorem raise_lower {Γ : Context.{u}} {A : Family Γ} (a : Term (family A)) :
    raiseTerm (lowerTerm a) = a := rfl

def map {Γ : Context.{u}} {A B : Family Γ} (f : A ⟶ B) : family A ⟶ family B where
  app x := TypeCat.ofHom (fun a => ⟨f.app ((lowerElements Γ).obj x) a.down⟩)
  naturality x y g := by
    apply ConcreteCategory.hom_ext
    intro a
    exact congrArg ULift.up (ConcreteCategory.congr_hom (f.naturality ((lowerElements Γ).map g)) a.down)

def lowerMap {Γ : Context.{u}} {A B : Family Γ} (f : family A ⟶ family B) : A ⟶ B where
  app x := TypeCat.ofHom (fun a => (f.app ((raisedElements Γ).obj x) ⟨a⟩).down)
  naturality x y g := by
    apply ConcreteCategory.hom_ext
    intro a
    exact congrArg ULift.down (ConcreteCategory.congr_hom (f.naturality ((raisedElements Γ).map g)) ⟨a⟩)

def totalIso {Γ : Context.{u}} (A : Family Γ) :
    raisedContext (total A) ≅ total (family A) where
  hom :=
    { app := fun _ => TypeCat.ofHom (fun x => ⟨⟨x.down.1⟩,⟨x.down.2⟩⟩)
      naturality := fun _ _ _ => rfl }
  inv :=
    { app := fun _ => TypeCat.ofHom (fun x => ⟨⟨x.1.down,x.2.down⟩⟩)
      naturality := fun _ _ _ => rfl }
  hom_inv_id := rfl
  inv_hom_id := rfl

def lowerPath {Γ : Context.{u}} {A : Family Γ} {a b : Term (family A)}
    (p : Term (homogeneousPath (family A) a b)) :
    Term (homogeneousPath A (lowerTerm a) (lowerTerm b)) :=
  pathLam (lowerTerm (Term.reindex (pathApp p) (SmallUniverse.raisedIntervalIso Γ).hom))
    (congrArg lowerTerm (pathApp_zero p)) (congrArg lowerTerm (pathApp_one p))

def raisePath {Γ : Context.{u}} {A : Family Γ} {a b : Term A}
    (p : Term (homogeneousPath A a b)) :
    Term (homogeneousPath (family A) (raiseTerm a) (raiseTerm b)) :=
  pathLam (Term.reindex (raiseTerm (pathApp p)) (SmallUniverse.raisedIntervalIso Γ).inv)
    (congrArg raiseTerm (pathApp_zero p)) (congrArg raiseTerm (pathApp_one p))

theorem lower_raise_path {Γ : Context.{u}} {A : Family Γ} {a b : Term A}
    (p : Term (homogeneousPath A a b)) : lowerPath (raisePath p) = p :=
  pathLam_app p

theorem raise_lower_path {Γ : Context.{u}} {A : Family Γ} {a b : Term (family A)}
    (p : Term (homogeneousPath (family A) a b)) : raisePath (lowerPath p) = p :=
  pathLam_app p

def raisePathElement {Γ : Context.{u}} {A : Family Γ} {a b : Term A}
    {x : (raisedContext Γ).Elements}
    (p : (homogeneousPath A a b).obj ((lowerElements Γ).obj x)) :
    (homogeneousPath (family A) (raiseTerm a) (raiseTerm b)).obj x :=
  ⟨{ val := fun f i => ⟨p.val.val ((lowerElements Γ).map f) ⟨i.down⟩⟩
     naturality := fun f g i => congrArg ULift.up
       (p.val.naturality ((lowerElements Γ).map f) ((lowerElements Γ).map g) ⟨i.down⟩) },
   fun f => ⟨congrArg ULift.up (p.property ((lowerElements Γ).map f)).1,
     congrArg ULift.up (p.property ((lowerElements Γ).map f)).2⟩⟩

def lowerPathElement {Γ : Context.{u}} {A : Family Γ} {a b : Term A}
    {x : (raisedContext Γ).Elements}
    (p : (homogeneousPath (family A) (raiseTerm a) (raiseTerm b)).obj x) :
    (homogeneousPath A a b).obj ((lowerElements Γ).obj x) :=
  ⟨{ val := fun f i => (p.val.val ((raisedElements Γ).map f) ⟨i.down⟩).down
     naturality := fun f g i => congrArg ULift.down
       (p.val.naturality ((raisedElements Γ).map f) ((raisedElements Γ).map g) ⟨i.down⟩) },
   fun f => ⟨congrArg ULift.down (p.property ((raisedElements Γ).map f)).1,
     congrArg ULift.down (p.property ((raisedElements Γ).map f)).2⟩⟩

def pathIso {Γ : Context.{u}} {A : Family Γ} (a b : Term A) :
    family (homogeneousPath A a b) ≅
      homogeneousPath (family A) (raiseTerm a) (raiseTerm b) :=
  NatIso.ofComponents (fun _ =>
    { hom := TypeCat.ofHom (fun p => raisePathElement p.down)
      inv := TypeCat.ofHom (fun p => ⟨lowerPathElement p⟩)
      hom_inv_id := by
        apply ConcreteCategory.hom_ext
        intro p
        apply congrArg ULift.up
        apply Subtype.ext
        apply PiElement.ext
        intro y f i
        rfl
      inv_hom_id := by
        apply ConcreteCategory.hom_ext
        intro p
        apply Subtype.ext
        apply PiElement.ext
        intro y f i
        rfl }) (by intro x y f; rfl)

def iso {Γ : Context.{u}} {A B : Family Γ} (e : A ≅ B) : family A ≅ family B where
  hom := map e.hom
  inv := map e.inv
  hom_inv_id := by
    ext x a
    exact congrArg ULift.up (e.hom_inv_id_app_apply ((lowerElements Γ).obj x) a.down)
  inv_hom_id := by
    ext x a
    exact congrArg ULift.up (e.inv_hom_id_app_apply ((lowerElements Γ).obj x) a.down)

end Raising
namespace SmallUniverse

theorem liftedDecode_raised {Γ : Context.{u}} (a : raisedContext Γ ⟶ smallFamilyCodes.{u}) :
    liftedDecode a = Raising.family (Cartesian.decode a) := rfl

def liftedDecodeCodeIso {Γ : Context.{u}} (A : LocalFamily Γ) :
    liftedDecode A.code ≅ Raising.family A.family := Raising.iso A.decodeCodeIso

end SmallUniverse
namespace Raising

def lowerContractible {Γ : Context.{u}} {A : Family Γ}
    (c : Contractible (family A)) : Contractible A :=
  Contractible.ofContraction (lowerTerm c.center)
    (lowerPath (A := reindex A (projection A))
      (homogeneousReindex c.toContraction (totalIso A).hom))

def sigmaIso {Γ : Context.{u}} (A : Family Γ) (B : Family (total A)) :
    family (sigma A B) ≅ sigma (family A) (reindex (family B) (totalIso A).inv) :=
  NatIso.ofComponents (fun _ =>
    { hom := TypeCat.ofHom (fun z => ⟨⟨z.down.1⟩,⟨z.down.2⟩⟩)
      inv := TypeCat.ofHom (fun z => ⟨⟨z.1.down,z.2.down⟩⟩)
      hom_inv_id := rfl
      inv_hom_id := rfl }) (by intro x y f; rfl)

def fiberIso {Γ : Context.{u}} {A B : Family Γ} (f : A ⟶ B) (b : Term B) :
    family (Homotopy.fiber f b) ≅ Homotopy.fiber (map f) (raiseTerm b) :=
  sigmaIso A _ ≪≫ Homotopy.sigmaSecondIso _
    (Functor.isoWhiskerLeft (totalIso A).inv.mapElements
      (pathIso (Term.map (Functor.whiskerLeft (projection A).mapElements f) (generic A))
        (Term.reindex b (projection A))) ≪≫
      pathReindexIso _ _ _ (totalIso A).inv)

def lowerEquivalence {Γ : Context.{u}} {A B : Family Γ} {f : A ⟶ B}
    (E : HomotopyEquivalence (map f)) : HomotopyEquivalence f where
  fibers := lowerContractible (Contractible.map
    (fiberIso (Functor.whiskerLeft (projection B).mapElements f) (generic B)).symm
    (Contractible.map (Homotopy.fiberReindexIso (Functor.whiskerLeft (projection (family B)).mapElements (map f))
      (generic (family B)) (totalIso B).hom) (E.fibers.reindex (totalIso B).hom)))

theorem lowerMap_reindex {Γ Δ : Context.{u}} {A B : Family Γ}
    (f : family A ⟶ family B) (σ : Δ ⟶ Γ) :
    lowerMap (A := reindex A σ) (B := reindex B σ)
      (Functor.whiskerLeft (raisedSub σ).mapElements f) =
      Functor.whiskerLeft σ.mapElements (lowerMap f) := rfl


end Raising


theorem Contractible.reindex_map_comp {Γ Δ Θ : Context.{u}} {A : Family Γ}
    (c : Contractible A) (σ : Δ ⟶ Γ) {B : Family Δ} (e : Cartesian.reindex A σ ≅ B)
    (τ : Θ ⟶ Δ) {C : Family Θ} (d : Cartesian.reindex B τ ≅ C) :
    Contractible.map d ((Contractible.map e (c.reindex σ)).reindex τ) =
      Contractible.map (Functor.isoWhiskerLeft τ.mapElements e ≪≫ d) (c.reindex (τ ≫ σ)) := by
  apply Contractible.ext rfl
  intro x a y f r
  rfl

namespace Raising

theorem lowerContractible_reindex {Γ Δ : Context.{u}} {A : Family Γ}
    (c : Contractible (family A)) (σ : Δ ⟶ Γ) :
    lowerContractible (A := reindex A σ) (c.reindex (raisedSub σ)) =
      (lowerContractible c).reindex σ := by
  apply Contractible.ext rfl
  intro x a y f r
  rfl

theorem lowerContractible_map {Γ : Context.{u}} {A B : Family Γ}
    (c : Contractible (family A)) (e : A ≅ B) :
    lowerContractible (Contractible.map (iso e) c) = Contractible.map e (lowerContractible c) := by
  apply Contractible.ext
  · apply Term.ext
    intro x
    rfl
  · intro x a y f r
    let y' := (raisedContext Γ).elementsMk y.obj ⟨y.val⟩
    change e.hom.app y ((c.contraction y' ⟨e.inv.app y (B.map f a)⟩).val.val (𝟙 y') ⟨r.down⟩).down =
      e.hom.app y ((c.contraction y' ⟨A.map f (e.inv.app x a)⟩).val.val (𝟙 y') ⟨r.down⟩).down
    exact congrArg (fun v => e.hom.app y ((c.contraction y' ⟨v⟩).val.val (𝟙 y') ⟨r.down⟩).down)
      (e.inv.naturality_apply f a)
/-- The comparison of whole generic fibers packages both representation changes. -/
def lowerFiberIso {Γ : Context.{u}} {A B : Family Γ} (f : A ⟶ B) :
    reindex (Homotopy.fiber (Functor.whiskerLeft (projection (family B)).mapElements (map f))
      (generic (family B))) (totalIso B).hom ≅
    family (Homotopy.fiber (Functor.whiskerLeft (projection B).mapElements f) (generic B)) :=
  Homotopy.fiberReindexIso (Functor.whiskerLeft (projection (family B)).mapElements (map f))
    (generic (family B)) (totalIso B).hom ≪≫
      (fiberIso (Functor.whiskerLeft (projection B).mapElements f) (generic B)).symm

theorem fiberIso_reindex {Γ Δ : Context.{u}} {A B : Family Γ}
    (f : A ⟶ B) (b : Term B) (σ : Δ ⟶ Γ) :
    Functor.isoWhiskerLeft (raisedSub σ).mapElements (fiberIso f b) ≪≫
      Homotopy.fiberReindexIso (map f) (raiseTerm b) (raisedSub σ) =
    iso (Homotopy.fiberReindexIso f b σ) ≪≫
      fiberIso (Functor.whiskerLeft σ.mapElements f) (Term.reindex b σ) := by
  apply Iso.ext
  apply NatTrans.ext
  funext x
  apply ConcreteCategory.hom_ext
  intro z
  apply Sigma.ext
  · rfl
  · apply heq_of_eq
    apply Subtype.ext
    apply PiElement.ext
    intro y g i
    rfl

private theorem inverse_square {C : Type*} [Category C] {A B D E : C}
    (i : A ≅ B) (k : B ≅ E) (j : A ≅ D) (l : D ≅ E)
    (h : i ≪≫ k = j ≪≫ l) : i.symm ≪≫ j = k ≪≫ l.symm := by
  apply Iso.ext
  apply (cancel_epi i.hom).mp
  apply (cancel_mono l.hom).mp
  simpa only [Iso.trans_hom, Iso.symm_hom, Category.assoc, Iso.hom_inv_id_assoc,
    Iso.inv_hom_id, Category.comp_id] using (congrArg Iso.hom h).symm

theorem fiberIso_reindex_inv {Γ Δ : Context.{u}} {A B : Family Γ}
    (f : A ⟶ B) (b : Term B) (σ : Δ ⟶ Γ) :
    (Functor.isoWhiskerLeft (raisedSub σ).mapElements (fiberIso f b)).symm ≪≫
      iso (Homotopy.fiberReindexIso f b σ) =
    Homotopy.fiberReindexIso (map f) (raiseTerm b) (raisedSub σ) ≪≫
      (fiberIso (Functor.whiskerLeft σ.mapElements f) (Term.reindex b σ)).symm :=
  inverse_square _ _ _ _ (fiberIso_reindex f b σ)

theorem lowerFiberIso_reindex {Γ Δ : Context.{u}} {A B : Family Γ}
    (f : A ⟶ B) (σ : Δ ⟶ Γ) :
    Functor.isoWhiskerLeft (totalIso (reindex B σ)).hom.mapElements
      (genericFiberReindexIso (map f) (raisedSub σ)) ≪≫
      lowerFiberIso (Functor.whiskerLeft σ.mapElements f) =
    Functor.isoWhiskerLeft (raisedSub (liftSub B σ)).mapElements (lowerFiberIso f) ≪≫
      iso (genericFiberReindexIso f σ) := by
  apply Iso.ext
  let F := Functor.whiskerLeft (projection (family B)).mapElements (map f)
  let p := generic (family B)
  let Q := Functor.isoWhiskerLeft (raisedSub (liftSub B σ)).mapElements
    (Homotopy.fiberReindexIso F p (totalIso B).hom)
  let J := fiberIso (Functor.whiskerLeft (projection (reindex B σ)).mapElements
    (Functor.whiskerLeft σ.mapElements f)) (generic (reindex B σ))
  have hP := (Homotopy.fiberReindexIso_comp F p (liftSub (family B) (raisedSub σ))
    (totalIso (reindex B σ)).hom).trans
      (Homotopy.fiberReindexIso_comp F p (totalIso B).hom (raisedSub (liftSub B σ))).symm
  have h := fiberIso_reindex_inv (Functor.whiskerLeft (projection B).mapElements f)
    (generic B) (liftSub B σ)
  exact (congrArg (fun e => e ≫ J.inv) (congrArg Iso.hom hP)).trans
    (congrArg (fun e => Q.hom ≫ e) (congrArg Iso.hom h).symm)


theorem lowerEquivalence_fibers {Γ : Context.{u}} {A B : Family Γ} {f : A ⟶ B}
    (E : HomotopyEquivalence (map f)) :
    (lowerEquivalence (f := f) E).fibers =
    lowerContractible (Contractible.map (lowerFiberIso f) (E.fibers.reindex (totalIso B).hom)) := rfl

theorem lowerEquivalence_reindex {Γ Δ : Context.{u}} {A B : Family Γ} {f : A ⟶ B}
    (E : HomotopyEquivalence (map f)) (σ : Δ ⟶ Γ) :
    lowerEquivalence (f := Functor.whiskerLeft σ.mapElements f) (E.reindex (raisedSub σ)) =
      (lowerEquivalence (f := f) E).reindex σ := by
  apply congrArg HomotopyEquivalence.mk
  let C := Homotopy.fiber (Functor.whiskerLeft (projection (reindex B σ)).mapElements
    (Functor.whiskerLeft σ.mapElements f)) (generic (reindex B σ))
  let c := Contractible.map (lowerFiberIso f) (E.fibers.reindex (totalIso B).hom)
  have hL := (lowerEquivalence_fibers (f := Functor.whiskerLeft σ.mapElements f)
    (E.reindex (raisedSub σ))).trans
      (congrArg (lowerContractible (A := C)) (E.fibers.reindex_map_comp
        (liftSub (family B) (raisedSub σ)) (genericFiberReindexIso (map f) (raisedSub σ))
        (totalIso (reindex B σ)).hom (lowerFiberIso (Functor.whiskerLeft σ.mapElements f))))
  have hR := (congrArg (fun d => Contractible.map (genericFiberReindexIso f σ) (d.reindex (liftSub B σ)))
      (lowerEquivalence_fibers E)).trans
    ((congrArg (Contractible.map (genericFiberReindexIso f σ))
      (lowerContractible_reindex c (liftSub B σ)).symm).trans
    ((lowerContractible_map
      (A := reindex (Homotopy.fiber (Functor.whiskerLeft (projection B).mapElements f) (generic B))
        (liftSub B σ)) (B := C) (c.reindex (raisedSub (liftSub B σ)))
      (genericFiberReindexIso f σ)).symm.trans
      (congrArg (lowerContractible (A := C)) (E.fibers.reindex_map_comp
        (totalIso B).hom (lowerFiberIso f) (raisedSub (liftSub B σ))
        (iso (genericFiberReindexIso f σ))))))
  exact hL.trans ((congrArg (fun e => lowerContractible (A := C)
    (Contractible.map e (E.fibers.reindex (raisedSub (liftSub B σ) ≫ (totalIso B).hom))))
      (lowerFiberIso_reindex f σ)).trans hR.symm)

end Raising

theorem HomotopyEquivalence.reindex_comp {Γ Δ Θ : Context.{u}} {A B : Family Γ}
    {f : A ⟶ B} (E : HomotopyEquivalence f) (σ : Δ ⟶ Γ) (τ : Θ ⟶ Δ) :
    (E.reindex σ).reindex τ = E.reindex (τ ≫ σ) := by
  apply congrArg (HomotopyEquivalence.mk (f := Functor.whiskerLeft (τ ≫ σ).mapElements f))
  change Contractible.map _ ((Contractible.map _ (E.fibers.reindex _)).reindex _) = _
  refine (Contractible.reindex_map_comp E.fibers (liftSub B σ)
    (Homotopy.fiberReindexIso _ _ (liftSub B σ)) (liftSub (Cartesian.reindex B σ) τ)
    (Homotopy.fiberReindexIso _ _ (liftSub (Cartesian.reindex B σ) τ))).trans ?_
  exact congrArg (fun i => Contractible.map i (E.fibers.reindex (liftSub B (τ ≫ σ))))
    (Homotopy.fiberReindexIso_comp (Functor.whiskerLeft (projection B).mapElements f)
      (generic B) (liftSub B σ) (liftSub (Cartesian.reindex B σ) τ))


theorem HomotopyEquivalence.reindex_heq {Γ Δ : Context.{u}} {A B : Family Γ}
    {f : A ⟶ B} (E : HomotopyEquivalence f) (σ τ : Δ ⟶ Γ) (h : σ = τ) :
    HEq (E.reindex σ) (E.reindex τ) := by cases h; rfl

namespace HomotopyEquivalence

def castMap {Γ : Context.{u}} {A B : Family Γ} (f : A ⟶ B)
    (A' B' : Family Γ) (hA : A = A') (hB : B = B') : A' ⟶ B' :=
  eqToHom hA.symm ≫ f ≫ eqToHom hB

def castFamilies {Γ : Context.{u}} {A B : Family Γ} {f : A ⟶ B}
    (E : HomotopyEquivalence f) (A' B' : Family Γ) (hA : A = A') (hB : B = B') :
    HomotopyEquivalence (castMap f A' B' hA hB) := by
  subst A'; subst B'; exact E

theorem castFamilies_reindex_comp {Γ Δ Θ : Context.{u}} {A B : Family Γ}
    {f : A ⟶ B} (E : HomotopyEquivalence f) (ρ : Δ ⟶ Γ) (σ : Θ ⟶ Δ)
    (τ : Θ ⟶ Γ) (h : σ ≫ ρ = τ)
    (A' B' : Family Δ) (hA : Cartesian.reindex A ρ = A')
    (hB : Cartesian.reindex B ρ = B')
    (hA' : Cartesian.reindex A τ = Cartesian.reindex A' σ)
    (hB' : Cartesian.reindex B τ = Cartesian.reindex B' σ) :
    HEq (((E.reindex ρ).castFamilies A' B' hA hB).reindex σ)
      ((E.reindex τ).castFamilies (Cartesian.reindex A' σ) (Cartesian.reindex B' σ) hA' hB') := by
  subst τ
  subst A'; subst B'
  exact heq_of_eq (E.reindex_comp ρ σ)

end HomotopyEquivalence

namespace UniversalTransport
structure Line (I : Cubeᵒᵖ) where
  val : ∀ {J : Cubeᵒᵖ}, (I ⟶ J) → Cube.Hom J.unop ⟨1⟩ → SmallFamilyCode.{u} J.unop
  naturality : ∀ {J K : Cubeᵒᵖ} (f : I ⟶ J) (g : J ⟶ K) (r : Cube.Hom J.unop ⟨1⟩),
    smallFamilyCodes.map g (val f r) = val (f ≫ g) (Cube.comp g.unop r)
@[ext] theorem Line.ext {I : Cubeᵒᵖ} {p q : Line.{u} I}
    (h : ∀ {J} (f : I ⟶ J) r, p.val f r = q.val f r) : p = q := by
  cases p; cases q; congr; funext J f r; exact h f r

def Line.restrict {I J : Cubeᵒᵖ} (f : I ⟶ J) (p : Line.{u} I) : Line.{u} J where
  val g r := p.val (f ≫ g) r
  naturality g h r := by simpa only [Category.assoc] using p.naturality (f ≫ g) h r

def parameters : Context.{u+1} where
  obj I := Line.{u} I × Cube.Hom I.unop ⟨1⟩ × Cube.Hom I.unop ⟨1⟩
  map f := TypeCat.ofHom (fun p => ⟨p.1.restrict f, Cube.comp f.unop p.2.1, Cube.comp f.unop p.2.2⟩)
  map_id I := by
    apply ConcreteCategory.hom_ext
    intro p
    apply Prod.ext
    · apply Line.ext; intro J f r
      change p.1.val ((𝟙 I) ≫ f) r = p.1.val f r
      rw [Category.id_comp]
    · change (Cube.comp (𝟙 I.unop) p.2.1, Cube.comp (𝟙 I.unop) p.2.2) = p.2
      exact Prod.ext (@Category.id_comp Cube _ I.unop ⟨1⟩ p.2.1) (@Category.id_comp Cube _ I.unop ⟨1⟩ p.2.2)
  map_comp f g := by
    apply ConcreteCategory.hom_ext
    intro p
    apply Prod.ext
    · apply Line.ext; intro J h r
      change p.1.val ((f ≫ g) ≫ h) r = p.1.val (f ≫ g ≫ h) r
      rw [Category.assoc]
    · change (Cube.comp (Cube.comp g.unop f.unop) p.2.1,
        Cube.comp (Cube.comp g.unop f.unop) p.2.2) = _
      exact Prod.ext (@Category.assoc Cube _ _ _ _ _ g.unop f.unop p.2.1)
        (@Category.assoc Cube _ _ _ _ _ g.unop f.unop p.2.2)

def source : Term (interval parameters.{u}) where
  val x := ⟨x.val.2.1⟩
  property f := congrArg ULift.up (congrArg (fun z => z.2.1) f.map_val)

def target : Term (interval parameters.{u}) where
  val x := ⟨x.val.2.2⟩
  property f := congrArg ULift.up (congrArg (fun z => z.2.2) f.map_val)

def evaluation : total (interval parameters.{u}) ⟶ smallFamilyCodes.{u} where
  app I := TypeCat.ofHom (fun x => x.1.1.val (𝟙 I) x.2.down)
  naturality I J f := by
    apply ConcreteCategory.hom_ext
    intro x
    change x.1.1.val (f ≫ 𝟙 J) (Cube.comp f.unop x.2.down) =
      smallFamilyCodes.map f (x.1.1.val (𝟙 I) x.2.down)
    have h := (x.1.1.naturality (𝟙 I) f x.2.down).symm
    change x.1.1.val ((𝟙 I) ≫ f) (Cube.comp f.unop x.2.down) =
      smallFamilyCodes.map f (x.1.1.val (𝟙 I) x.2.down) at h
    simpa only [Category.id_comp, Category.comp_id] using h

noncomputable def equivalence : HomotopyEquivalence
    (IntervalTransport.map (SmallUniverse.NativeDecode.filling evaluation) source target) :=
  IntervalTransport.equivalence (SmallUniverse.NativeDecode.filling evaluation)
    (SmallUniverse.NativeDecode.filling_lawful evaluation) source target

def classify {Γ : Context.{u+1}} (a : total (interval Γ) ⟶ smallFamilyCodes.{u})
    (r s : Term (interval Γ)) : Γ ⟶ parameters.{u} where
  app I := TypeCat.ofHom (fun x =>
    ⟨{ val := fun {J} f i => a.app J ⟨Γ.map f x,⟨i⟩⟩
       naturality := fun {J K} f g i => by
         have h := (a.naturality_apply g ⟨Γ.map f x,⟨i⟩⟩).symm
         exact h.trans (congrArg (fun y => a.app K ⟨y,⟨Cube.comp g.unop i⟩⟩)
           (ConcreteCategory.congr_hom (Γ.map_comp f g) x).symm) },
      (r.val (Γ.elementsMk I x)).down, (s.val (Γ.elementsMk I x)).down⟩)
  naturality I J f := by
    apply ConcreteCategory.hom_ext
    intro x
    apply Prod.ext
    · apply Line.ext
      intro K g i
      exact congrArg (fun y => a.app K ⟨y,⟨i⟩⟩)
        (ConcreteCategory.congr_hom (Γ.map_comp f g) x).symm
    · let k : Γ.elementsMk I x ⟶ Γ.elementsMk J (Γ.map f x) := Functor.Elements.homMk f rfl
      exact Prod.ext
        (congrArg ULift.down (r.property k)).symm
        (congrArg ULift.down (s.property k)).symm
theorem classify_reindex {Γ Δ : Context.{u+1}}
    (a : total (interval Γ) ⟶ smallFamilyCodes.{u}) (r s : Term (interval Γ)) (σ : Δ ⟶ Γ) :
    classify (intervalSub σ ≫ a) (Term.reindex r σ) (Term.reindex s σ) = σ ≫ classify a r s := by
  apply NatTrans.ext
  funext I
  apply ConcreteCategory.hom_ext
  intro x
  apply Prod.ext
  · apply Line.ext
    intro J f i
    exact congrArg (fun y => a.app J ⟨y,⟨i⟩⟩) (σ.naturality_apply f x)
  · rfl

theorem classify_source {Γ : Context.{u+1}}
    (a : total (interval Γ) ⟶ smallFamilyCodes.{u}) (r s : Term (interval Γ)) :
    Term.reindex source (classify a r s) = r := rfl

theorem classify_target {Γ : Context.{u+1}}
    (a : total (interval Γ) ⟶ smallFamilyCodes.{u}) (r s : Term (interval Γ)) :
    Term.reindex target (classify a r s) = s := rfl

theorem classify_evaluation {Γ : Context.{u+1}}
    (a : total (interval Γ) ⟶ smallFamilyCodes.{u}) (r s : Term (interval Γ)) :
    intervalSub (classify a r s) ≫ evaluation = a := by
  apply NatTrans.ext
  funext I
  apply ConcreteCategory.hom_ext
  intro x
  change a.app I ⟨Γ.map (𝟙 I) x.1,x.2⟩ = a.app I x
  exact congrArg (fun y => a.app I ⟨y,x.2⟩)
    (ConcreteCategory.congr_hom (Γ.map_id I) x.1)

theorem classify_source_code {Γ : Context.{u+1}}
    (a : total (interval Γ) ⟶ smallFamilyCodes.{u}) (r s : Term (interval Γ)) :
    classify a r s ≫ graph source ≫ evaluation = graph r ≫ a :=
  congrArg (fun k => graph r ≫ k) (classify_evaluation a r s)

theorem classify_target_code {Γ : Context.{u+1}}
    (a : total (interval Γ) ⟶ smallFamilyCodes.{u}) (r s : Term (interval Γ)) :
    classify a r s ≫ graph target ≫ evaluation = graph s ≫ a :=
  congrArg (fun k => graph s ≫ k) (classify_evaluation a r s)

noncomputable def selectedEquivalence {Γ : Context.{u+1}}
    (a : total (interval Γ) ⟶ smallFamilyCodes.{u}) (r s : Term (interval Γ)) :=
  equivalence.reindex (classify a r s)

theorem selectedEquivalence_reindex {Γ Δ : Context.{u+1}}
    (a : total (interval Γ) ⟶ smallFamilyCodes.{u}) (r s : Term (interval Γ)) (σ : Δ ⟶ Γ) :
    HEq ((selectedEquivalence a r s).reindex σ)
      (selectedEquivalence (intervalSub σ ≫ a) (Term.reindex r σ) (Term.reindex s σ)) := by
  exact (heq_of_eq (equivalence.reindex_comp (classify a r s) σ)).trans
    (equivalence.reindex_heq _ _ (classify_reindex a r s σ).symm)

def selectedMap {Γ : Context.{u+1}}
    (a : total (interval Γ) ⟶ smallFamilyCodes.{u}) (r s : Term (interval Γ)) :
    SmallUniverse.liftedDecode (graph r ≫ a) ⟶ SmallUniverse.liftedDecode (graph s ≫ a) :=
  HomotopyEquivalence.castMap
    (Functor.whiskerLeft (classify a r s).mapElements
      (IntervalTransport.map (SmallUniverse.NativeDecode.filling evaluation) source target))
    _ _ (congrArg SmallUniverse.liftedDecode (classify_source_code a r s))
      (congrArg SmallUniverse.liftedDecode (classify_target_code a r s))

noncomputable def normalizedEquivalence {Γ : Context.{u+1}}
    (a : total (interval Γ) ⟶ smallFamilyCodes.{u}) (r s : Term (interval Γ)) :
    HomotopyEquivalence (selectedMap a r s) :=
  (selectedEquivalence a r s).castFamilies _ _
    (congrArg SmallUniverse.liftedDecode (classify_source_code a r s))
    (congrArg SmallUniverse.liftedDecode (classify_target_code a r s))

theorem normalizedEquivalence_reindex {Γ Δ : Context.{u+1}}
    (a : total (interval Γ) ⟶ smallFamilyCodes.{u}) (r s : Term (interval Γ)) (σ : Δ ⟶ Γ) :
    HEq ((normalizedEquivalence a r s).reindex σ)
      (normalizedEquivalence (intervalSub σ ≫ a) (Term.reindex r σ) (Term.reindex s σ)) := by
  exact equivalence.castFamilies_reindex_comp (classify a r s) σ
    (classify (intervalSub σ ≫ a) (Term.reindex r σ) (Term.reindex s σ))
    (classify_reindex a r s σ).symm _ _ _ _ _ _

theorem actualMap_cast {Γ : Context.{u+1}}
    (a b : total (interval Γ) ⟶ smallFamilyCodes.{u}) (h : a = b) (r s : Term (interval Γ)) :
    HomotopyEquivalence.castMap (IntervalTransport.map (SmallUniverse.NativeDecode.filling a) r s)
      (SmallUniverse.liftedDecode (graph r ≫ b)) (SmallUniverse.liftedDecode (graph s ≫ b))
      (congrArg (fun k => SmallUniverse.liftedDecode (graph r ≫ k)) h)
      (congrArg (fun k => SmallUniverse.liftedDecode (graph s ≫ k)) h) =
      IntervalTransport.map (SmallUniverse.NativeDecode.filling b) r s := by
  subst b; rfl

theorem selectedMap_eq {Γ : Context.{u+1}}
    (a : total (interval Γ) ⟶ smallFamilyCodes.{u}) (r s : Term (interval Γ)) :
    selectedMap a r s = IntervalTransport.map (SmallUniverse.NativeDecode.filling a) r s := by
  have h := IntervalTransport.map_reindex (SmallUniverse.NativeDecode.filling evaluation)
    (SmallUniverse.NativeDecode.filling_lawful evaluation) source target (classify a r s)
  exact (congrArg (fun f => HomotopyEquivalence.castMap f
    (SmallUniverse.liftedDecode (graph r ≫ a)) (SmallUniverse.liftedDecode (graph s ≫ a))
    (congrArg SmallUniverse.liftedDecode (classify_source_code a r s))
    (congrArg SmallUniverse.liftedDecode (classify_target_code a r s))) h.symm).trans
      (actualMap_cast _ a (classify_evaluation a r s) r s)

theorem selectedMap_diagonal {Γ : Context.{u+1}}
    (a : total (interval Γ) ⟶ smallFamilyCodes.{u}) (r : Term (interval Γ)) :
    selectedMap a r r = 𝟙 _ :=
  (selectedMap_eq a r r).trans
    (IntervalTransport.map_diagonal _ (SmallUniverse.NativeDecode.filling_lawful a) r)

def raiseInterval {Γ : Context.{u}} (r : Term (interval Γ)) : Term (interval (raisedContext Γ)) where
  val x := ⟨(r.val ((Raising.lowerElements Γ).obj x)).down⟩
  property {_x y} f := congrArg (fun z : ULift.{u} (Cube.Hom y.obj.unop ⟨1⟩) =>
    (ULift.up z.down : ULift.{u+1} (Cube.Hom y.obj.unop ⟨1⟩)))
      (r.property ((Raising.lowerElements Γ).map f))

def smallLine {Γ : Context.{u}}
    (a : raisedContext (total (interval Γ)) ⟶ smallFamilyCodes.{u}) :
    total (interval (raisedContext Γ)) ⟶ smallFamilyCodes.{u} :=
  (SmallUniverse.raisedIntervalIso Γ).inv ≫ a

def smallMap {Γ : Context.{u}}
    (a : raisedContext (total (interval Γ)) ⟶ smallFamilyCodes.{u}) (r s : Term (interval Γ)) :
    decode (raisedSub (graph r) ≫ a) ⟶ decode (raisedSub (graph s) ≫ a) :=
  Raising.lowerMap (selectedMap (smallLine a) (raiseInterval r) (raiseInterval s))

noncomputable def smallEquivalence {Γ : Context.{u}}
    (a : raisedContext (total (interval Γ)) ⟶ smallFamilyCodes.{u}) (r s : Term (interval Γ)) :
    HomotopyEquivalence (smallMap a r s) :=
  Raising.lowerEquivalence (normalizedEquivalence (smallLine a) (raiseInterval r) (raiseInterval s))

theorem smallMap_diagonal {Γ : Context.{u}}
    (a : raisedContext (total (interval Γ)) ⟶ smallFamilyCodes.{u}) (r : Term (interval Γ)) :
    smallMap a r r = 𝟙 _ :=
  congrArg (Raising.lowerMap (A := decode (raisedSub (graph r) ≫ a))
    (B := decode (raisedSub (graph r) ≫ a))) (selectedMap_diagonal (smallLine a) (raiseInterval r))

theorem selectedMap_reindex {Γ Δ : Context.{u+1}}
    (a : total (interval Γ) ⟶ smallFamilyCodes.{u}) (r s : Term (interval Γ)) (σ : Δ ⟶ Γ) :
    selectedMap (intervalSub σ ≫ a) (Term.reindex r σ) (Term.reindex s σ) =
      Functor.whiskerLeft σ.mapElements (selectedMap a r s) := by
  exact (selectedMap_eq (intervalSub σ ≫ a) (Term.reindex r σ) (Term.reindex s σ)).trans
    ((IntervalTransport.map_reindex _ (SmallUniverse.NativeDecode.filling_lawful a) r s σ).trans
      (congrArg (Functor.whiskerLeft σ.mapElements) (selectedMap_eq a r s).symm))

theorem smallMap_reindex {Γ Δ : Context.{u}}
    (a : raisedContext (total (interval Γ)) ⟶ smallFamilyCodes.{u}) (r s : Term (interval Γ))
    (σ : Δ ⟶ Γ) :
    smallMap (raisedSub (intervalSub σ) ≫ a) (Term.reindex r σ) (Term.reindex s σ) =
      Functor.whiskerLeft σ.mapElements (smallMap a r s) :=
  congrArg (Raising.lowerMap (A := reindex (decode (raisedSub (graph r) ≫ a)) σ)
    (B := reindex (decode (raisedSub (graph s) ≫ a)) σ))
    (selectedMap_reindex (smallLine a) (raiseInterval r) (raiseInterval s) (raisedSub σ))

theorem lowerEquivalence_heq {Γ : Context.{u}} {A B : Family Γ} {f g : A ⟶ B}
    (E : HomotopyEquivalence (Raising.map f)) (F : HomotopyEquivalence (Raising.map g))
    (h : f = g) (hE : HEq E F) : HEq (Raising.lowerEquivalence E) (Raising.lowerEquivalence F) := by
  subst g
  cases eq_of_heq hE
  rfl

theorem smallEquivalence_reindex {Γ Δ : Context.{u}}
    (a : raisedContext (total (interval Γ)) ⟶ smallFamilyCodes.{u}) (r s : Term (interval Γ))
    (σ : Δ ⟶ Γ) :
    HEq ((smallEquivalence a r s).reindex σ)
      (smallEquivalence (raisedSub (intervalSub σ) ≫ a) (Term.reindex r σ) (Term.reindex s σ)) := by
  exact (heq_of_eq (Raising.lowerEquivalence_reindex
    (f := smallMap a r s) (normalizedEquivalence (smallLine a) (raiseInterval r) (raiseInterval s)) σ).symm).trans
    (lowerEquivalence_heq _ _ (smallMap_reindex a r s σ).symm
      (normalizedEquivalence_reindex (smallLine a) (raiseInterval r) (raiseInterval s) (raisedSub σ)))

end UniversalTransport

namespace SmallUniverse
def lowerChartMap {Γ : Context.{u}} {Ξ : Context.{u+1}}
    (a b : Ξ ⟶ smallFamilyCodes.{u}) (σ : raisedContext Γ ⟶ Ξ)
    (f : liftedDecode a ⟶ liftedDecode b) :
    decode (σ ≫ a) ⟶ decode (σ ≫ b) :=
  Raising.lowerMap (Functor.whiskerLeft σ.mapElements f)

def lowerChartEquivalence {Γ : Context.{u}} {Ξ : Context.{u+1}}
    (a b : Ξ ⟶ smallFamilyCodes.{u}) (σ : raisedContext Γ ⟶ Ξ)
    (f : liftedDecode a ⟶ liftedDecode b) (E : HomotopyEquivalence f) :
    HomotopyEquivalence (lowerChartMap a b σ f) :=
  Raising.lowerEquivalence (E.reindex σ)

theorem lowerChartMap_reindex {Γ Θ : Context.{u}} {Ξ : Context.{u+1}}
    (a b : Ξ ⟶ smallFamilyCodes.{u}) (σ : raisedContext Γ ⟶ Ξ)
    (f : liftedDecode a ⟶ liftedDecode b) (τ : Θ ⟶ Γ) :
    lowerChartMap a b (raisedSub τ ≫ σ) f =
      Functor.whiskerLeft τ.mapElements (lowerChartMap a b σ f) := rfl
theorem lowerChartEquivalence_reindex {Γ Θ : Context.{u}} {Ξ : Context.{u+1}}
    (a b : Ξ ⟶ smallFamilyCodes.{u}) (σ : raisedContext Γ ⟶ Ξ)
    (f : liftedDecode a ⟶ liftedDecode b) (E : HomotopyEquivalence f) (τ : Θ ⟶ Γ) :
    lowerChartEquivalence a b (raisedSub τ ≫ σ) f E =
      (lowerChartEquivalence a b σ f E).reindex τ := by
  have h := E.reindex_comp σ (raisedSub τ)
  exact (congrArg (fun e => Raising.lowerEquivalence
    (f := Functor.whiskerLeft τ.mapElements (lowerChartMap a b σ f)) e) h.symm).trans
      (Raising.lowerEquivalence_reindex (f := lowerChartMap a b σ f) (E.reindex σ) τ)

end SmallUniverse

end SquareKit.Cubical.Cartesian

namespace SquareKit.Cubical.Cartesian.SmallUniverse.NativeUnivalence
open CategoryTheory
universe u
variable {Ξ : Context.{u+1}}
/-- A small represented chart reaches any element of a larger context. -/
def chart {Γ : Context.{u+1}} (x : Γ.Elements) :
    raisedContext (representable.{u} x.obj.unop) ⟶ Γ where
  app J := TypeCat.ofHom (fun f => Γ.map f.down.down.op x.val)
  naturality J K f := by
    apply ConcreteCategory.hom_ext
    intro g
    exact ConcreteCategory.congr_hom (Γ.map_comp g.down.down.op f) x.val

theorem chart_substitution {Γ Δ : Context.{u+1}} (σ : Δ ⟶ Γ) (x : Δ.Elements) :
    chart (σ.mapElements.obj x) = chart x ≫ σ := by
  ext I f
  exact (σ.naturality_apply f.down.down.op x.val).symm

theorem chart_restrict {Γ : Context.{u+1}} {x y : Γ.Elements} (f : x ⟶ y) :
    raisedSub (representableMap.{u} f.hom.unop) ≫ chart x = chart y := by
  ext I g
  change Γ.map (g.down.down ≫ f.hom.unop).op x.val = Γ.map g.down.down.op y.val
  exact (ConcreteCategory.congr_hom (Γ.map_comp f.hom g.down.down.op) x.val).trans
    (congrArg (fun z => Γ.map g.down.down.op z) f.map_val)

/-- Generic evaluation of the small represented chart recovers the large point. -/
theorem chart_generic (x : Ξ.Elements) : (chart x).app x.obj ⟨⟨𝟙 x.obj.unop⟩⟩ = x.val :=
  ConcreteCategory.congr_hom (Ξ.map_id x.obj) x.val

end SquareKit.Cubical.Cartesian.SmallUniverse.NativeUnivalence
