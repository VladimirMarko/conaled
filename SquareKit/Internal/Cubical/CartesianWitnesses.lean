import SquareKit.Internal.Cubical.CartesianPaths
import SquareKit.Internal.Cubical.SelectedInverse

/-! Actual target fibers and chosen contractions under Cartesian restriction. -/
set_option autoImplicit false
set_option warningAsError true
namespace SquareKit.Cubical.Cartesian
open CategoryTheory
universe u

abbrev intervalCoefficient {Γ : Context.{u}} (A : Family Γ) :
    Family (total (interval Γ)) := (projection (interval Γ)).mapElements ⋙ A

/-- A homogeneous path retains all Cartesian generalized evaluations. -/
abbrev PathBetween {Γ : Context.{u}} (A : Family Γ) (x : Γ.Elements) (a b : A.obj x) :=
  { p : PiElement (interval Γ) (intervalCoefficient A) x // ∀ {y} (f : x ⟶ y),
    p.val f ⟨Cube.endpoint y.obj.unop false⟩ = A.map f a ∧
    p.val f ⟨Cube.endpoint y.obj.unop true⟩ = A.map f b }

/-- A selected contraction covers every target point and is coherent in all substitutions. -/
structure Contractible {Γ : Context.{u}} (A : Family Γ) where
  center : Term A
  contraction : ∀ (x : Γ.Elements) (a : A.obj x), PathBetween A x (center.val x) a
  naturality : ∀ {x y z : Γ.Elements} (f : x ⟶ y) (g : y ⟶ z) (a : A.obj x)
    (r : (interval Γ).obj z),
    (contraction x a).val.val (f ≫ g) r = (contraction y (A.map f a)).val.val g r

@[ext] theorem Contractible.ext {Γ : Context.{u}} {A : Family Γ} {c d : Contractible A}
    (hc : c.center = d.center)
    (hp : ∀ (x : Γ.Elements) (a : A.obj x) {y : Γ.Elements} (f : x ⟶ y) r,
      (c.contraction x a).val.val f r = (d.contraction x a).val.val f r) : c = d := by
  cases c with
  | mk cc cp cn =>
    cases d with
    | mk dc dp dn =>
      dsimp at hc
      cases hc
      congr
      funext x a
      apply Subtype.ext
      apply PiElement.ext
      exact hp x a

/-- Transport a whole contraction, including its interior, through a family isomorphism. -/
def Contractible.map {Γ : Context.{u}} {A B : Family Γ} (e : A ≅ B)
    (c : Contractible A) : Contractible B where
  center := Term.map e.hom c.center
  contraction x b := ⟨{
    val := fun {y} f r => e.hom.app y ((c.contraction x (e.inv.app x b)).val.val f r)
    naturality := fun {y z} f g r => by
      change B.map g (e.hom.app y _) = e.hom.app z _
      exact (e.hom.naturality_apply g _).symm.trans
        (congrArg (e.hom.app z) ((c.contraction x (e.inv.app x b)).val.naturality f g r))
    }, fun {y} f => by
      constructor
      · change e.hom.app y _ = B.map f (e.hom.app x (c.center.val x))
        rw [((c.contraction x (e.inv.app x b)).property f).1, e.hom.naturality_apply]
      · change e.hom.app y _ = B.map f b
        rw [((c.contraction x (e.inv.app x b)).property f).2, e.hom.naturality_apply]
        exact congrArg (B.map f) (congrArg (fun k => k b) (e.inv_hom_id_app x))⟩
  naturality f g b r := by
    change e.hom.app _ _ = e.hom.app _ _
    apply congrArg
    rw [c.naturality]
    rw [e.inv.naturality_apply]

private theorem source_contraction_comp {Γ : Presheaf.Context.{u}} {A : Presheaf.Family Γ}
    (c : Presheaf.HomotopyContractible A) {x y z : Γ.Elements}
    (a : A.obj x) (f : x ⟶ y) (g : y ⟶ z)
    (r : (Presheaf.interval Γ).obj z) :
    (c.contraction.val (Presheaf.extendObj A x a)).val.val (Presheaf.extendHom A (f ≫ g) a) r =
      (c.contraction.val (Presheaf.extendObj A x a)).val.val
        (Presheaf.extendHom A f a ≫ Presheaf.extendHom A g (A.map f a)) r := by
  have evalAlong (k : x ⟶ z) {a' : A.obj z} (ha : A.map k a = a') :
      (c.contraction.val (Presheaf.extendObj A x a)).val.val (Presheaf.extendAlong A k ha) r =
        (c.contraction.val (Presheaf.extendObj A x a)).val.val (Presheaf.extendHom A k a) r := by
    subst a'
    rfl
  exact (evalAlong (f ≫ g) (a' := A.map g (A.map f a)) (congrArg (fun k => k a) (A.map_comp f g))).symm

/-- Source contractions evaluate to coherent target paths for all target points. -/
def restrictContractible {Γ : Presheaf.Context.{u}} {A : Presheaf.Family Γ}
    (c : Presheaf.HomotopyContractible A) : Contractible (restrictFamily A) where
  center := restrictTerm c.center
  contraction x a := ⟨{
    val := fun {y} f r => (c.contraction.val (Presheaf.extendObj A ((elements Γ).obj x) a)).val.val
      (Presheaf.extendHom A ((elements Γ).map f) a) ⟨inclusion.map r.down⟩
    naturality := fun {y z} f g r => by
      have h := (c.contraction.val (Presheaf.extendObj A ((elements Γ).obj x) a)).val.naturality
        (Presheaf.extendHom A ((elements Γ).map f) a)
        (Presheaf.extendHom A ((elements Γ).map g) (A.map ((elements Γ).map f) a))
        ⟨inclusion.map r.down⟩
      -- Coefficients are homogeneous, so dimension comparison only changes the argument.
      change A.map ((elements Γ).map g) _ = _ at h ⊢
      let p := c.contraction.val (Presheaf.extendObj A ((elements Γ).obj x) a)
      change A.map ((elements Γ).map g)
        (p.val.val (Presheaf.extendHom A ((elements Γ).map f) a) ⟨inclusion.map r.down⟩) =
        p.val.val (Presheaf.extendHom A ((elements Γ).map (f ≫ g)) a)
          ⟨inclusion.map (Cube.comp g.hom.unop r.down)⟩
      have hd : inclusion.map (Cube.comp g.hom.unop r.down) =
          SquareKit.Cubical.Cube.comp (inclusion.map g.hom.unop) (inclusion.map r.down) :=
        inclusion.map_comp g.hom.unop r.down
      rw [hd]
      change A.map ((elements Γ).map g)
        (p.val.val (Presheaf.extendHom A ((elements Γ).map f) a) ⟨inclusion.map r.down⟩) =
        p.val.val (Presheaf.extendHom A ((elements Γ).map f) a ≫
          Presheaf.extendHom A ((elements Γ).map g) (A.map ((elements Γ).map f) a))
          ⟨SquareKit.Cubical.Cube.comp (inclusion.map g.hom.unop) (inclusion.map r.down)⟩ at h
      have evalAlong {w : Γ.Elements} (k : (elements Γ).obj x ⟶ w)
          {a' : A.obj w} (ha : A.map k a = a') (s : (Presheaf.interval Γ).obj w) :
          p.val.val (Presheaf.extendAlong A k ha) s =
            p.val.val (Presheaf.extendHom A k a) s := by
        subst a'
        rfl
      have ha : A.map ((elements Γ).map f ≫ (elements Γ).map g) a =
          A.map ((elements Γ).map g) (A.map ((elements Γ).map f) a) :=
        congrArg (fun k => k a) (A.map_comp ((elements Γ).map f) ((elements Γ).map g))
      have hp := evalAlong ((elements Γ).map f ≫ (elements Γ).map g) ha
        (ULift.up (SquareKit.Cubical.Cube.comp (inclusion.map g.hom.unop) (inclusion.map r.down)))
      rw [(elements Γ).map_comp]
      exact h.trans hp

    }, fun {y} f => by
      have h := (c.contraction.val (Presheaf.extendObj A ((elements Γ).obj x) a)).property
        (Presheaf.extendHom A ((elements Γ).map f) a)
      constructor
      · exact h.1.trans (c.center.property ((elements Γ).map f)).symm
      · exact h.2⟩
  naturality {x y z} f g a r := by
    have h := congrArg
      (fun p => p.val.val (Presheaf.extendHom A ((elements Γ).map g) (A.map ((elements Γ).map f) a))
        (ULift.up (inclusion.map r.down)))
      (c.contraction.property (Presheaf.extendHom A ((elements Γ).map f) a))
    change (c.contraction.val (Presheaf.extendObj A ((elements Γ).obj x) a)).val.val
      (Presheaf.extendHom A ((elements Γ).map (f ≫ g)) a) ⟨inclusion.map r.down⟩ = _
    rw [(elements Γ).map_comp]
    exact (source_contraction_comp c a ((elements Γ).map f) ((elements Γ).map g)
      ⟨inclusion.map r.down⟩).trans h


/-- A target dependent pair with an actual target path as its second component. -/
def sigmaPath {Γ : Presheaf.Context.{u}} (A : Presheaf.Family Γ)
    (B : Presheaf.Family (Presheaf.total (Presheaf.interval (Presheaf.total A))))
    (a₀ : Presheaf.Term (Presheaf.reindex B (Presheaf.endpointSub (Presheaf.total A) false)))
    (a₁ : Presheaf.Term (Presheaf.reindex B (Presheaf.endpointSub (Presheaf.total A) true))) :
    Family (restrict Γ) :=
  sigma (restrictFamily A) ((totalComparison A).inv.mapElements ⋙ relativePath B a₀ a₁)

def sigmaPathEquiv {Γ : Presheaf.Context.{u}} (A : Presheaf.Family Γ)
    (B : Presheaf.Family (Presheaf.total (Presheaf.interval (Presheaf.total A))))
    (a₀ : Presheaf.Term (Presheaf.reindex B (Presheaf.endpointSub (Presheaf.total A) false)))
    (a₁ : Presheaf.Term (Presheaf.reindex B (Presheaf.endpointSub (Presheaf.total A) true)))
    (x : (restrict Γ).Elements) :
    (restrictFamily (Presheaf.sigma A (Presheaf.path B a₀ a₁))).obj x ≃
      (sigmaPath A B a₀ a₁).obj x where
  toFun z := ⟨z.1, pathEquiv B a₀ a₁ _ z.2⟩
  invFun z := ⟨z.1, (pathEquiv B a₀ a₁ _).symm z.2⟩
  left_inv z := by
    cases z with
    | mk a p => exact congrArg (Sigma.mk a) ((pathEquiv B a₀ a₁ ((restrict (Presheaf.total A)).elementsMk x.obj ⟨x.val, a⟩)).left_inv p)
  right_inv z := by
    cases z with
    | mk a p => exact congrArg (Sigma.mk a) ((pathEquiv B a₀ a₁ ((restrict (Presheaf.total A)).elementsMk x.obj ⟨x.val, a⟩)).right_inv p)

def sigmaPathIso {Γ : Presheaf.Context.{u}} (A : Presheaf.Family Γ)
    (B : Presheaf.Family (Presheaf.total (Presheaf.interval (Presheaf.total A))))
    (a₀ : Presheaf.Term (Presheaf.reindex B (Presheaf.endpointSub (Presheaf.total A) false)))
    (a₁ : Presheaf.Term (Presheaf.reindex B (Presheaf.endpointSub (Presheaf.total A) true))) :
    restrictFamily (Presheaf.sigma A (Presheaf.path B a₀ a₁)) ≅ sigmaPath A B a₀ a₁ :=
  NatIso.ofComponents (fun x => (sigmaPathEquiv A B a₀ a₁ x).toIso) (fun {x y} f => by
    apply ConcreteCategory.hom_ext
    intro z
    apply Sigma.ext
    · rfl
    apply heq_of_eq
    apply Subtype.ext
    apply PiElement.ext
    intro w g r
    change z.2.val.val _ _ = z.2.val.val _ _
    congr 2
    apply Functor.Elements.Hom.ext
    exact (inclusion.op.map_comp f.hom g.hom).symm)


/-- The Cartesian fiber has an input and a Cartesian path from its image to `b`. -/
def homotopyFiber {Γ : Presheaf.Context.{u}} {A B : Presheaf.Family Γ}
    (f : A ⟶ B) (b : Presheaf.Term B) : Family (restrict Γ) :=
  sigmaPath A
    (Presheaf.reindex (Presheaf.reindex B (Presheaf.projection A))
      (Presheaf.projection (Presheaf.interval (Presheaf.total A))))
    (Presheaf.Term.map (Functor.whiskerLeft (Presheaf.projection A).mapElements f) (Presheaf.generic A))
    (b.reindex (Presheaf.projection A))

def fiberIso {Γ : Presheaf.Context.{u}} {A B : Presheaf.Family Γ}
    (f : A ⟶ B) (b : Presheaf.Term B) :
    restrictFamily (Presheaf.homotopyFiber f b) ≅ homotopyFiber f b :=
  sigmaPathIso A _ _ _

abbrev genericFiber {Γ : Presheaf.Context.{u}} {A B : Presheaf.Family Γ} (f : A ⟶ B) :=
  homotopyFiber (Functor.whiskerLeft (Presheaf.projection B).mapElements f) (Presheaf.generic B)

/-- Full target equivalence data, with an actual contraction of every generic target fiber. -/
structure Equivalence {Γ : Presheaf.Context.{u}} {A B : Presheaf.Family Γ} (f : A ⟶ B) where
  fibers : Contractible (genericFiber f)

def restrictEquivalence {Γ : Presheaf.Context.{u}} {A B : Presheaf.Family Γ}
    {f : A ⟶ B} (E : Presheaf.HomotopyEquivalence f) : Equivalence f where
  fibers := (restrictContractible E.fibers).map (fiberIso _ _)

/-- The target inverse is selected by the actual target fiber center. -/
def Equivalence.selectedInverse {Γ : Presheaf.Context.{u}} {A B : Presheaf.Family Γ}
    {f : A ⟶ B} (E : Equivalence f) : restrictFamily B ⟶ restrictFamily A where
  app x := TypeCat.ofHom (fun b => (E.fibers.center.val
    ((restrict (Presheaf.total B)).elementsMk x.obj ⟨x.val,b⟩)).1)
  naturality x y g := by
    apply ConcreteCategory.hom_ext
    intro b
    let k : (restrict (Presheaf.total B)).elementsMk x.obj ⟨x.val,b⟩ ⟶
        (restrict (Presheaf.total B)).elementsMk y.obj ⟨y.val, (restrictFamily B).map g b⟩ :=
      Functor.Elements.homMk g.hom (Presheaf.totalMap_hom B ((elements Γ).map g) b)
    exact (congrArg Sigma.fst (E.fibers.center.property k)).symm


@[simp] theorem restrict_selectedInverse {Γ : Presheaf.Context.{u}} {A B : Presheaf.Family Γ}
    {f : A ⟶ B} (E : Presheaf.HomotopyEquivalence f) :
    (restrictEquivalence E).selectedInverse = restrictFamilyMap E.selectedInverse := rfl


/-- Restriction recovers the entire source contraction, not just its center. -/
theorem restrictContractible_injective {Γ : Presheaf.Context.{u}} {A : Presheaf.Family Γ} :
    Function.Injective (restrictContractible (A := A)) := by
  intro c d h
  have hc : c.center = d.center := restrictTerm_injective (congrArg Contractible.center h)
  cases c with
  | mk cc cp =>
    cases d with
    | mk dc dp =>
      dsimp at hc
      cases hc
      congr
      apply Presheaf.Term.ext
      intro x
      apply Subtype.ext
      apply (Presheaf.intervalProductEquiv _ x).injective
      rcases x with @⟨⟨⟨n⟩⟩, γ, a⟩
      let y := (restrict Γ).elementsMk (.op ⟨n⟩) γ
      exact congrArg (fun c => (c.contraction y a).val.val (freshBaseHom y)
        (ULift.up (Cube.fresh y.obj.unop))) h


@[simp] theorem Contractible.map_inverse {Γ : Context.{u}} {A B : Family Γ}
    (e : A ≅ B) (c : Contractible A) : (c.map e).map e.symm = c := by
  apply Contractible.ext
  · apply Term.ext
    intro x
    exact congrArg (fun k => k (c.center.val x)) (e.hom_inv_id_app x)
  · intro x a y f r
    change e.inv.app y (e.hom.app y ((c.contraction x (e.inv.app x (e.hom.app x a))).val.val f r)) = _
    have hx := congrArg (fun k => k a) (e.hom_inv_id_app x)
    have hy := congrArg (fun k => k ((c.contraction x a).val.val f r)) (e.hom_inv_id_app y)
    change e.inv.app x (e.hom.app x a) = a at hx
    rw [hx]
    exact hy

theorem Contractible.map_injective {Γ : Context.{u}} {A B : Family Γ} (e : A ≅ B) :
    Function.Injective (Contractible.map e) := by
  intro c d h
  have h' := congrArg (Contractible.map e.symm) h
  simpa using h'

/-- Complete source equivalence records are recoverable from their target images. -/
theorem restrictEquivalence_injective {Γ : Presheaf.Context.{u}} {A B : Presheaf.Family Γ}
    {f : A ⟶ B} : Function.Injective (restrictEquivalence (f := f)) := by
  intro E D h
  have hf := congrArg Equivalence.fibers h
  have hc := restrictContractible_injective ((Contractible.map_injective (fiberIso _ _)) hf)
  cases E
  cases D
  cases hc
  rfl


def sourceZero (I : SquareKit.Cubical.Cube) : SquareKit.Cubical.Cube.Hom I ⟨0⟩ :=
  SquareKit.Cubical.Cube.ofRaw (fun i => Fin.elim0 i)

theorem sourceZero_unique {I : SquareKit.Cubical.Cube} (f : SquareKit.Cubical.Cube.Hom I ⟨0⟩) :
    f = sourceZero I := by
  refine Quotient.inductionOn f ?_
  intro f
  exact Quotient.sound (fun i => Fin.elim0 i)

def closedRootHom {Γ : Presheaf.Context.{u}} (hΓ : ∀ I, Subsingleton (Γ.obj I))
    (root : Γ.obj (.op ⟨0⟩)) (x : Γ.Elements) : Γ.elementsMk (.op ⟨0⟩) root ⟶ x :=
  Functor.Elements.homMk (Quiver.Hom.op (sourceZero x.obj.unop)) ((hΓ x.obj).elim _ _)

/-- Closed sections of a restricted family lift because the zero cube represents the context. -/
def recoverClosedTerm {Γ : Presheaf.Context.{u}} {A : Presheaf.Family Γ}
    (hΓ : ∀ I, Subsingleton (Γ.obj I)) (root : Γ.obj (.op ⟨0⟩))
    (s : Term (restrictFamily A)) : Presheaf.Term A where
  val x := A.map (closedRootHom hΓ root x)
    (s.val ((restrict Γ).elementsMk (.op ⟨0⟩) root))
  property {x y} f := by
    have h : closedRootHom hΓ root x ≫ f = closedRootHom hΓ root y := by
      apply Functor.Elements.Hom.ext
      exact congrArg Quiver.Hom.op (sourceZero_unique (f.hom.unop ≫ sourceZero x.obj.unop))
    exact (congrArg (fun k => k (s.val ((restrict Γ).elementsMk (.op ⟨0⟩) root)))
      (A.map_comp (closedRootHom hΓ root x) f)).symm.trans
      (congrArg (fun k => A.map k (s.val ((restrict Γ).elementsMk (.op ⟨0⟩) root))) h)

/-- Actual target homogeneous paths, independent of a source presentation. -/
abbrev HomogeneousPathElement {Γ : Context.{u}} (A : Family Γ) (a b : Term A) (x : Γ.Elements) :=
  {p : PiElement (interval Γ) (intervalCoefficient A) x // ∀ {y} (f : x ⟶ y),
    p.val f ⟨Cube.endpoint y.obj.unop false⟩ = a.val y ∧
    p.val f ⟨Cube.endpoint y.obj.unop true⟩ = b.val y}

def homogeneousPath {Γ : Context.{u}} (A : Family Γ) (a b : Term A) : Family Γ where
  obj x := HomogeneousPathElement A a b x
  map f := TypeCat.ofHom (fun p => ⟨p.val.restrict f, fun g => p.property (f ≫ g)⟩)
  map_id x := by
    apply ConcreteCategory.hom_ext
    intro p
    apply Subtype.ext
    apply PiElement.ext
    intro y f r
    simp [PiElement.restrict]
  map_comp f g := by
    apply ConcreteCategory.hom_ext
    intro p
    apply Subtype.ext
    apply PiElement.ext
    intro z h r
    simp [PiElement.restrict]

def homogeneousIso {Γ : Presheaf.Context.{u}} (A : Presheaf.Family Γ) (a b : Presheaf.Term A) :
    restrictFamily (Presheaf.homogeneousPath A a b) ≅
      homogeneousPath (restrictFamily A) (restrictTerm a) (restrictTerm b) :=
  pathIso (Presheaf.reindex A (Presheaf.projection (Presheaf.interval Γ))) a b

def homogeneousTerm {Γ : Presheaf.Context.{u}} {A : Presheaf.Family Γ} {a b : Presheaf.Term A}
    (p : Presheaf.Term (Presheaf.homogeneousPath A a b)) :
    Term (homogeneousPath (restrictFamily A) (restrictTerm a) (restrictTerm b)) :=
  Term.map (homogeneousIso A a b).hom (restrictTerm p)

def homogeneousMap {Γ : Context.{u}} {A B : Family Γ} (f : A ⟶ B) (a b : Term A) :
    homogeneousPath A a b ⟶ homogeneousPath B (Term.map f a) (Term.map f b) where
  app _x := TypeCat.ofHom (fun p => ⟨{
    val := fun {y} g r => f.app y (p.val.val g r)
    naturality := fun {_y z} g k r => (f.naturality_apply k _).symm.trans
      (congrArg (f.app z) (p.val.naturality g k r))
    }, fun g => ⟨congrArg (f.app _) (p.property g).1, congrArg (f.app _) (p.property g).2⟩⟩)
  naturality _ _ _ := rfl

def homogeneousIsoMap {Γ : Context.{u}} {A B : Family Γ} (e : A ≅ B) (a b : Term A) :
    homogeneousPath A a b ≅ homogeneousPath B (Term.map e.hom a) (Term.map e.hom b) where
  hom := homogeneousMap e.hom a b
  inv := {
    app := fun x => TypeCat.ofHom (fun p => ⟨{
      val := fun {y} g r => e.inv.app y (p.val.val g r)
      naturality := fun {_y z} g k r => (e.inv.naturality_apply k _).symm.trans
        (congrArg (e.inv.app z) (p.val.naturality g k r)) }, fun {y} g => by
          constructor
          · exact (congrArg (e.inv.app y) (p.property g).1).trans
              (congrArg (fun k => k (a.val y)) (e.hom_inv_id_app y))
          · exact (congrArg (e.inv.app y) (p.property g).2).trans
              (congrArg (fun k => k (b.val y)) (e.hom_inv_id_app y))⟩)
    naturality := fun _ _ _ => rfl }
  hom_inv_id := by
    ext x p
    apply Subtype.ext
    apply PiElement.ext
    intro y g r
    exact congrArg (fun k => k (p.val.val g r)) (e.hom_inv_id_app y)
  inv_hom_id := by
    ext x p
    apply Subtype.ext
    apply PiElement.ext
    intro y g r
    exact congrArg (fun k => k (p.val.val g r)) (e.inv_hom_id_app y)

/-- Iteration gives a genuine target two-path, with both coefficients compared. -/
def twoPathIso {Γ : Presheaf.Context.{u}} (A : Presheaf.Family Γ) (a b : Presheaf.Term A)
    (p q : Presheaf.Term (Presheaf.homogeneousPath A a b)) :
    restrictFamily (Presheaf.homogeneousPath (Presheaf.homogeneousPath A a b) p q) ≅
      homogeneousPath (homogeneousPath (restrictFamily A) (restrictTerm a) (restrictTerm b))
        (homogeneousTerm p) (homogeneousTerm q) :=
  homogeneousIso _ p q ≪≫ homogeneousIsoMap (homogeneousIso A a b) (restrictTerm p) (restrictTerm q)

variable {Γ : Presheaf.Context.{u}} {A B : Presheaf.Family Γ} {f : A ⟶ B}
/-- Every evaluation of the selected right homotopy comes from the target center path. -/
theorem restrict_selectedRight (E : Presheaf.HomotopyEquivalence f)
    (x : (restrict (Presheaf.total B)).Elements)
    (r : ULift (Cube.Hom x.obj.unop ⟨1⟩)) :
    (((restrictEquivalence E).fibers.center.val x).2).val.val (𝟙 _) r =
      ((E.selectedRight.val ((elements _).obj x)).val).val (𝟙 _)
        ⟨inclusion.map r.down⟩ := rfl
variable {Γ : Presheaf.Context.{u}} {A B : Presheaf.Family Γ} {f : A ⟶ B}
/-- Whole contraction values commute with the genuine fiber comparison. -/
theorem restrict_contraction (E : Presheaf.HomotopyEquivalence f)
    (x : (restrict (Presheaf.total B)).Elements)
    (a : (restrictFamily (Presheaf.homotopyFiber (Functor.whiskerLeft (Presheaf.projection B).mapElements f) (Presheaf.generic B))).obj x)
    {y : (restrict (Presheaf.total B)).Elements} (g : x ⟶ y)
    (r : (interval (restrict (Presheaf.total B))).obj y) :
    ((restrictEquivalence E).fibers.contraction x ((fiberIso _ _).hom.app x a)).val.val g r =
      (fiberIso _ _).hom.app y (((restrictContractible E.fibers).contraction x a).val.val g r) := by
  change (fiberIso _ _).hom.app y
    (((restrictContractible E.fibers).contraction x
      ((fiberIso _ _).inv.app x ((fiberIso _ _).hom.app x a))).val.val g r) = _
  have h := congrArg (fun k => k a) ((fiberIso (Functor.whiskerLeft (Presheaf.projection B).mapElements f)
    (Presheaf.generic B)).hom_inv_id_app x)
  change (fiberIso _ _).inv.app x ((fiberIso _ _).hom.app x a) = a at h
  rw [h]
variable {Γ : Presheaf.Context.{u}} {A B : Presheaf.Family Γ} {f : A ⟶ B}
def leftBase (f : A ⟶ B) (x : (restrict (Presheaf.total A)).Elements) :
    (restrict (Presheaf.total B)).Elements :=
  (restrict (Presheaf.total B)).elementsMk x.obj
    ⟨x.val.1, f.app (Γ.elementsMk (inclusion.op.obj x.obj) x.val.1) x.val.2⟩
def reflexiveFiberPoint (f : A ⟶ B) (x : (restrict (Presheaf.total A)).Elements) :
    (restrictFamily (Presheaf.homotopyFiber (Functor.whiskerLeft (Presheaf.projection B).mapElements f) (Presheaf.generic B))).obj (leftBase f x) :=
  (Presheaf.genericFiberIntro f
    (Presheaf.pair (Presheaf.projection A)
      (Presheaf.Term.map (Functor.whiskerLeft (Presheaf.projection A).mapElements f) (Presheaf.generic A)))
    (Presheaf.generic A)
    (Presheaf.homogeneousRefl (Presheaf.Term.map
      (Functor.whiskerLeft (Presheaf.projection A).mapElements f) (Presheaf.generic A)))).val
      ((elements _).obj x)
/-- The selected left path is obtained by contracting the actual reflexive fiber point. -/
theorem restrict_selectedLeft (E : Presheaf.HomotopyEquivalence f)
    (x : (restrict (Presheaf.total A)).Elements)
    (r : ULift (Cube.Hom x.obj.unop ⟨1⟩)) :
    (((restrictEquivalence E).fibers.contraction (leftBase f x)
      ((fiberIso _ _).hom.app _ (reflexiveFiberPoint f x))).val.val (𝟙 _) r).1 =
      (E.selectedLeft.val ((elements _).obj x)).val.val (𝟙 _) ⟨inclusion.map r.down⟩ := by
  refine (congrArg Sigma.fst (restrict_contraction E (leftBase f x) (reflexiveFiberPoint f x) (𝟙 _) r)).trans ?_
  let C := Presheaf.homotopyFiber (Functor.whiskerLeft (Presheaf.projection B).mapElements f) (Presheaf.generic B)
  change ((E.fibers.contraction.val (Presheaf.extendObj C ((elements (Presheaf.total B)).obj (leftBase f x))
    (reflexiveFiberPoint f x))).val.val
      (Presheaf.extendHom C ((elements (Presheaf.total B)).map (𝟙 (leftBase f x))) (reflexiveFiberPoint f x))
      ⟨inclusion.map r.down⟩).1 = _
  rw [(elements _).map_id]
  let sx := (elements (Presheaf.total B)).obj (leftBase f x)
  let a := reflexiveFiberPoint f x
  let p := E.fibers.contraction.val (Presheaf.extendObj C sx a)
  have evalAlong {a' : C.obj sx} (h : C.map (𝟙 sx) a = a') :
      (p.val.val (Presheaf.extendAlong C (𝟙 sx) h) ⟨inclusion.map r.down⟩).1 =
        (p.val.val (Presheaf.extendHom C (𝟙 sx) a) ⟨inclusion.map r.down⟩).1 := by
    subst a'
    rfl
  exact (evalAlong (a' := a) (congrArg (fun k => k a) (C.map_id sx))).symm
def Contractible.reindex {Γ Δ : Context.{u}} {A : Family Γ}
    (c : Contractible A) (τ : Δ ⟶ Γ) : Contractible (τ.mapElements ⋙ A) where
  center := {
    val := fun x => c.center.val (τ.mapElements.obj x)
    property := fun f => c.center.property (τ.mapElements.map f) }
  contraction x a := ⟨{
    val := fun f r => (c.contraction (τ.mapElements.obj x) a).val.val (τ.mapElements.map f) r
    naturality := fun f g r => (c.contraction (τ.mapElements.obj x) a).val.naturality
      (τ.mapElements.map f) (τ.mapElements.map g) r },
    fun f => (c.contraction (τ.mapElements.obj x) a).property (τ.mapElements.map f)⟩
  naturality f g a r := c.naturality (τ.mapElements.map f) (τ.mapElements.map g) a r

/-- Both paths of iterated base change preserve the whole center/contraction record. -/
theorem Contractible.reindex_comp {Γ Δ Θ : Context.{u}} {A : Family Γ}
    (c : Contractible A) (τ : Δ ⟶ Γ) (σ : Θ ⟶ Δ) :
    (c.reindex τ).reindex σ = c.reindex (σ ≫ τ) := rfl

/-- Two successively forgotten interval coordinates exercise nonidentity base changes. -/
theorem Contractible.forget_two_intervals {Γ : Context.{u}} {A : Family Γ} (c : Contractible A) :
    (c.reindex (projection (interval Γ))).reindex (projection (interval (total (interval Γ)))) =
      c.reindex (projection (interval (total (interval Γ))) ≫ projection (interval Γ)) := rfl
end SquareKit.Cubical.Cartesian
