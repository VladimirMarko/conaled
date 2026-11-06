import SquareKit.Internal.Cubical.Paths

/-! Natural generalized cubes and the connection contraction. The values include
all restrictions; arbitrary set functions on interval values would not suffice. -/
namespace SquareKit.Cubical.Presheaf
open CategoryTheory
universe u

/-- A generalized n-cube is coherent in every future cube substitution. -/
structure CubeElement (X : Context.{u}) (n : ℕ) (I : Cubeᵒᵖ) where
  val : ∀ {J : Cubeᵒᵖ}, (I ⟶ J) → (Fin n → Cube.Hom J.unop ⟨1⟩) → X.obj J
  naturality : ∀ {J K : Cubeᵒᵖ} (f : I ⟶ J) (g : J ⟶ K)
      (r : Fin n → Cube.Hom J.unop ⟨1⟩),
    X.map g (val f r) = val (f ≫ g) (fun k => Cube.comp g.unop (r k))

@[ext] theorem CubeElement.ext {X : Context.{u}} {n : ℕ} {I : Cubeᵒᵖ}
    {p q : CubeElement X n I}
    (h : ∀ {J} (f : I ⟶ J) r, p.val f r = q.val f r) : p = q := by
  cases p
  cases q
  congr
  funext J f r
  exact h f r

def CubeElement.restrict {X : Context.{u}} {n : ℕ} {I J : Cubeᵒᵖ}
    (f : I ⟶ J) (p : CubeElement X n I) : CubeElement X n J where
  val g r := p.val (f ≫ g) r
  naturality g h r := by simpa only [Category.assoc] using p.naturality (f ≫ g) h r

/-- The exponential by n copies of the represented interval. -/
def cubes (X : Context.{u}) (n : ℕ) : Context.{u} where
  obj I := CubeElement X n I
  map f := TypeCat.ofHom (CubeElement.restrict f)
  map_id I := by
    apply ConcreteCategory.hom_ext
    intro p
    apply CubeElement.ext
    intro J f r
    simp [CubeElement.restrict]
  map_comp f g := by
    apply ConcreteCategory.hom_ext
    intro p
    apply CubeElement.ext
    intro J h r
    simp [CubeElement.restrict]

def cubeOrigin (X : Context.{u}) (n : ℕ) : cubes X n ⟶ X where
  app I := TypeCat.ofHom (fun p => p.val (𝟙 I) (fun _ => Cube.endpoint I.unop false))
  naturality I J f := by
    apply ConcreteCategory.hom_ext
    intro p
    have h := p.naturality (𝟙 I) f (fun _ => Cube.endpoint I.unop false)
    change p.val (f ≫ 𝟙 J) (fun _ => Cube.endpoint J.unop false) =
      X.map f (p.val (𝟙 I) (fun _ => Cube.endpoint I.unop false))
    simpa only [Category.comp_id, Category.id_comp, Cube.comp_endpoint] using h.symm

def constantCube (X : Context.{u}) (n : ℕ) : X ⟶ cubes X n where
  app I := TypeCat.ofHom (fun x => {
    val := fun f _ => X.map f x
    naturality := fun f g _ => by simp })
  naturality I J f := by
    apply ConcreteCategory.hom_ext
    intro x
    apply CubeElement.ext
    intro K g r
    exact (congrArg (fun h => h x) (X.map_comp f g)).symm

@[simp] theorem constantCube_origin (X : Context.{u}) (n : ℕ) :
    constantCube X n ≫ cubeOrigin X n = 𝟙 X := by
  ext I x
  exact congrArg (fun f => f x) (X.map_id I)

/-- Scale each source coordinate by the path coordinate, using De Morgan meet. -/
def contractCube (X : Context.{u}) (n : ℕ) : total (interval (cubes X n)) ⟶ cubes X n where
  app I := TypeCat.ofHom (fun z => {
    val := fun f r => z.1.val f (fun k => Cube.meet (r k) (Cube.comp f.unop z.2.down))
    naturality := by
      intro J K f g r
      have h := z.1.naturality f g
        (fun k => Cube.meet (r k) (Cube.comp f.unop z.2.down))
      refine h.trans ?_
      apply congrArg (z.1.val (f ≫ g))
      funext k
      exact (Cube.comp_meet g.unop _ _).trans
        (congrArg (Cube.meet (Cube.comp g.unop (r k)))
          (@Category.assoc Cube _ _ _ _ _ g.unop f.unop z.2.down).symm) })
  naturality I J f := by
    apply ConcreteCategory.hom_ext
    intro z
    apply CubeElement.ext
    intro K g r
    change z.1.val (f ≫ g) (fun k => Cube.meet (r k) (Cube.comp g.unop
      (Cube.comp f.unop z.2.down))) =
        z.1.val (f ≫ g) (fun k => Cube.meet (r k) (Cube.comp (f ≫ g).unop z.2.down))
    apply congrArg (z.1.val (f ≫ g))
    funext k
    exact congrArg (Cube.meet (r k))
      (@Category.assoc Cube _ _ _ _ _ g.unop f.unop z.2.down).symm

/-- The zero endpoint is the constant cube at the source cube's origin. -/
theorem contractCube_zero (X : Context.{u}) (n : ℕ) :
    endpointSub (cubes X n) false ≫ contractCube X n = cubeOrigin X n ≫ constantCube X n := by
  ext I p
  apply CubeElement.ext
  intro J f r
  change p.val f (fun k => Cube.meet (r k) (Cube.comp f.unop (Cube.endpoint I.unop false))) =
    X.map f (p.val (𝟙 I) (fun _ => Cube.endpoint I.unop false))
  simpa using (p.naturality (𝟙 I) f (fun _ => Cube.endpoint I.unop false)).symm

/-- The one endpoint retains the whole generalized cube. -/
theorem contractCube_one (X : Context.{u}) (n : ℕ) :
    endpointSub (cubes X n) true ≫ contractCube X n = 𝟙 (cubes X n) := by
  ext I p
  apply CubeElement.ext
  intro J f r
  change p.val f (fun k => Cube.meet (r k) (Cube.comp f.unop (Cube.endpoint I.unop true))) =
    p.val f r
  simp

/-- Natural transformations are sections of the pulled-back codomain. -/
def transformationTerm {Γ X : Context.{u}} (f : Γ ⟶ X) : Term (Functor.Elements.π Γ ⋙ X) where
  val x := f.app x.obj x.val
  property {x y} g := by
    have h := f.naturality_apply g.hom x.val
    exact h.symm.trans (congrArg (f.app _) g.map_val)

/-- Apply the outer interval argument of a successor cube. -/
def CubeElement.apply {X : Context.{u}} {n : ℕ} {I : Cubeᵒᵖ}
    (p : CubeElement X (n+1) I) (r : Cube.Hom I.unop ⟨1⟩) : CubeElement X n I where
  val f rs := p.val f (Fin.cases (Cube.comp f.unop r) rs)
  naturality f g rs := by
    refine (p.naturality f g _).trans ?_
    apply congrArg (p.val (f ≫ g))
    funext k
    refine Fin.cases ?_ (fun _ => rfl) k
    exact (@Category.assoc Cube _ _ _ _ _ g.unop f.unop r).symm

theorem CubeElement.apply_restrict {X : Context.{u}} {n : ℕ} {I J : Cubeᵒᵖ}
    (p : CubeElement X (n+1) I) (r : Cube.Hom I.unop ⟨1⟩) (f : I ⟶ J) :
    (p.apply r).restrict f = (p.restrict f).apply (Cube.comp f.unop r) := by
  apply CubeElement.ext
  intro K g rs
  change p.val (f ≫ g) (Fin.cases (Cube.comp (f ≫ g).unop r) rs) =
    p.val (f ≫ g) (Fin.cases (Cube.comp g.unop (Cube.comp f.unop r)) rs)
  apply congrArg (p.val (f ≫ g))
  funext k
  exact Fin.cases (@Category.assoc Cube _ _ _ _ _ g.unop f.unop r) (fun _ => rfl) k

/-- Currying identifies the successor construction with an interval function. -/
def cubeCurry (X : Context.{u}) (n : ℕ) : cubes X (n+1) ⟶ cubes (cubes X n) 1 where
  app I := TypeCat.ofHom (fun p => {
    val := fun f r => (p.restrict f).apply (r 0)
    naturality := by
      intro J K f g r
      apply CubeElement.ext
      intro L h rs
      change p.val (f ≫ (g ≫ h)) (Fin.cases (Cube.comp (g ≫ h).unop (r 0)) rs) =
        p.val ((f ≫ g) ≫ h) (Fin.cases (Cube.comp h.unop (Cube.comp g.unop (r 0))) rs)
      rw [Category.assoc]
      apply congrArg (p.val (f ≫ (g ≫ h)))
      funext k
      refine Fin.cases ?_ (fun _ => rfl) k
      exact @Category.assoc Cube _ _ _ _ _ h.unop g.unop (r 0) })
  naturality I J f := by
    apply ConcreteCategory.hom_ext
    intro p
    apply CubeElement.ext
    intro K g r
    apply CubeElement.ext
    intro L h rs
    exact congrArg (fun k => p.val k _) (Category.assoc f g h).symm

def cubeUncurry (X : Context.{u}) (n : ℕ) : cubes (cubes X n) 1 ⟶ cubes X (n+1) where
  app I := TypeCat.ofHom (fun p => {
    val := fun f r => (p.val f (fun _ => r 0)).val (𝟙 _) (fun k => r k.succ)
    naturality := by
      intro J K f g r
      have hi := (p.val f (fun _ => r 0)).naturality (𝟙 _) g (fun k => r k.succ)
      have ho := congrArg (fun q : CubeElement X n K =>
        q.val (𝟙 _) (fun k => Cube.comp g.unop (r k.succ)))
        (p.naturality f g (fun _ => r 0))
      change (p.val f (fun _ => r 0)).val (g ≫ 𝟙 _) _ = _ at ho
      rw [Category.id_comp] at hi
      rw [Category.comp_id] at ho
      exact hi.trans ho })
  naturality I J f := by
    apply ConcreteCategory.hom_ext
    intro p
    apply CubeElement.ext
    intro K g r
    rfl

@[simp] theorem cubeCurry_uncurry (X : Context.{u}) (n : ℕ) :
    cubeCurry X n ≫ cubeUncurry X n = 𝟙 (cubes X (n+1)) := by
  ext I p
  apply CubeElement.ext
  intro J f r
  change p.val (f ≫ 𝟙 J) (Fin.cases (Cube.comp (𝟙 J).unop (r 0)) (fun k => r k.succ)) = p.val f r
  rw [Category.comp_id]
  have he : Cube.comp (𝟙 J).unop (r 0) = r 0 := @Category.id_comp Cube _ _ _ _
  rw [he]
  apply congrArg (p.val f)
  funext k
  exact Fin.cases rfl (fun _ => rfl) k

@[simp] theorem cubeUncurry_curry (X : Context.{u}) (n : ℕ) :
    cubeUncurry X n ≫ cubeCurry X n = 𝟙 (cubes (cubes X n) 1) := by
  ext I p
  apply CubeElement.ext
  intro J f r
  apply CubeElement.ext
  intro K g rs
  have h := congrArg (fun q : CubeElement X n K => q.val (𝟙 _) rs) (p.naturality f g r)
  change (p.val f r).val (g ≫ 𝟙 _) rs =
    (p.val (f ≫ g) (fun k => Cube.comp g.unop (r k))).val (𝟙 _) rs at h
  change (p.val (f ≫ g) (fun _ => Cube.comp g.unop (r 0))).val (𝟙 _) rs = (p.val f r).val g rs
  have hr : (fun _ : Fin 1 => Cube.comp g.unop (r 0)) =
      (fun k => Cube.comp g.unop (r k)) := by
    funext k
    rw [Fin.eq_zero k]
  rw [hr]
  simpa only [Category.comp_id] using h.symm

/-- Zero-dimensional cubes are precisely their values in X. -/
theorem cubeOrigin_constant_zero (X : Context.{u}) :
    cubeOrigin X 0 ≫ constantCube X 0 = 𝟙 (cubes X 0) := by
  ext I p
  apply CubeElement.ext
  intro J f r
  have h := p.naturality (𝟙 I) f (fun k => Fin.elim0 k)
  change X.map f (p.val (𝟙 I) (fun _ => Cube.endpoint I.unop false)) = p.val f r
  have h₁ : (fun k : Fin 0 => Fin.elim0 k) = (fun _ => Cube.endpoint I.unop false) :=
    Subsingleton.elim _ _
  have h₂ : (fun _ : Fin 0 => Cube.comp f.unop (Cube.endpoint I.unop false)) = r := Subsingleton.elim _ _
  simpa only [Category.id_comp, h₁, h₂] using h

/-- Interval abstraction realizes the exponential universal property. -/
def cubeLam {Γ X : Context.{u}} (t : total (interval Γ) ⟶ X) : Γ ⟶ cubes X 1 where
  app I := TypeCat.ofHom (fun x => {
    val := fun {J} f r => t.app J ⟨Γ.map f x, ⟨r 0⟩⟩
    naturality := by
      intro J K f g r
      have h := t.naturality_apply g ⟨Γ.map f x, ⟨r 0⟩⟩
      change t.app K ⟨Γ.map g (Γ.map f x), ⟨Cube.comp g.unop (r 0)⟩⟩ =
        X.map g (t.app J ⟨Γ.map f x, ⟨r 0⟩⟩) at h
      rw [Γ.map_comp]
      exact h.symm })
  naturality I J f := by
    apply ConcreteCategory.hom_ext
    intro x
    apply CubeElement.ext
    intro K g r
    change t.app K ⟨Γ.map g (Γ.map f x), ⟨r 0⟩⟩ = t.app K ⟨Γ.map (f ≫ g) x, ⟨r 0⟩⟩
    rw [Γ.map_comp]
    rfl

def cubeApp {Γ X : Context.{u}} (p : Γ ⟶ cubes X 1) : total (interval Γ) ⟶ X where
  app I := TypeCat.ofHom (fun z => (p.app I z.1).val (𝟙 I) (fun _ => z.2.down))
  naturality I J f := by
    apply ConcreteCategory.hom_ext
    intro z
    have hp := congrArg (fun q : CubeElement X 1 J => q.val (𝟙 J)
      (fun _ => Cube.comp f.unop z.2.down)) (p.naturality_apply f z.1)
    have hc := (p.app I z.1).naturality (𝟙 I) f (fun _ => z.2.down)
    change (p.app J (Γ.map f z.1)).val (𝟙 J) (fun _ => Cube.comp f.unop z.2.down) =
      (p.app I z.1).val (f ≫ 𝟙 J) (fun _ => Cube.comp f.unop z.2.down) at hp
    rw [Category.comp_id] at hp
    rw [Category.id_comp] at hc
    exact hp.trans hc.symm

@[simp] theorem cubeApp_lam {Γ X : Context.{u}} (t : total (interval Γ) ⟶ X) :
    cubeApp (cubeLam t) = t := by
  ext I z
  change t.app I ⟨Γ.map (𝟙 I) z.1, ⟨z.2.down⟩⟩ = t.app I z
  rw [Γ.map_id]
  rfl

@[simp] theorem cubeLam_app {Γ X : Context.{u}} (p : Γ ⟶ cubes X 1) :
    cubeLam (cubeApp p) = p := by
  ext I x
  apply CubeElement.ext
  intro J f r
  have h := congrArg (fun q : CubeElement X 1 J => q.val (𝟙 J) r) (p.naturality_apply f x)
  change (p.app J (Γ.map f x)).val (𝟙 J) r = (p.app I x).val (f ≫ 𝟙 J) r at h
  change (p.app J (Γ.map f x)).val (𝟙 J) (fun _ => r 0) = (p.app I x).val f r
  have hr : (fun _ : Fin 1 => r 0) = r := by funext k; rw [Fin.eq_zero k]
  rw [hr]
  simpa only [Category.comp_id] using h

/-- The source function object maps into the constructed dependent product. -/
def cubePi (Γ X : Context.{u}) : Functor.Elements.π Γ ⋙ cubes X 1 ⟶
    pi (interval Γ) (Functor.Elements.π (total (interval Γ)) ⋙ X) where
  app _ := TypeCat.ofHom (fun p => {
    val := fun f a => p.val f.hom (fun _ => a.down)
    naturality := fun f g a => p.naturality f.hom g.hom (fun _ => a.down) })
  naturality _ _ _ := rfl

/-- Source interval abstraction agrees with dependent-product abstraction. -/
theorem cubeLam_pi {Γ X : Context.{u}} (t : total (interval Γ) ⟶ X) :
    Term.map (cubePi Γ X) (transformationTerm (cubeLam t)) =
      lam (A := interval Γ) (transformationTerm t) := by
  apply Term.ext
  intro x
  apply PiElement.ext
  intro y f a
  change t.app y.obj ⟨Γ.map f.hom x.val, a⟩ = t.app y.obj ⟨y.val,a⟩
  rw [f.map_val]

theorem cubeApp_pi {Γ X : Context.{u}} (p : Γ ⟶ cubes X 1) :
    app (Term.map (cubePi Γ X) (transformationTerm p)) =
      transformationTerm (cubeApp p) := rfl

/-- This is the successor equation in the archived `contract-cube` derivation. -/
theorem contractCube_apply (X : Context.{u}) (n : ℕ) {I : Cubeᵒᵖ}
    (c : CubeElement X (n+1) I) (j i : Cube.Hom I.unop ⟨1⟩) :
    ((contractCube X (n+1)).app I ⟨c, ⟨j⟩⟩).apply i =
      (contractCube X n).app I ⟨c.apply (Cube.meet i j), ⟨j⟩⟩ := by
  apply CubeElement.ext
  intro J f r
  change c.val f (fun k => Cube.meet (Fin.cases (Cube.comp f.unop i) r k) (Cube.comp f.unop j)) =
    c.val f (Fin.cases (Cube.comp f.unop (Cube.meet i j))
      (fun k => Cube.meet (r k) (Cube.comp f.unop j)))
  apply congrArg (c.val f)
  funext k
  refine Fin.cases ?_ (fun _ => rfl) k
  exact (Cube.comp_meet f.unop i j).symm

/-- At dimension zero, contraction is the constant reflexivity path. -/
theorem contractCube_dimension_zero (X : Context.{u}) {I : Cubeᵒᵖ}
    (c : CubeElement X 0 I) (j : Cube.Hom I.unop ⟨1⟩) :
    (contractCube X 0).app I ⟨c, ⟨j⟩⟩ = c := by
  apply CubeElement.ext
  intro J f r
  apply congrArg (c.val f)
  exact Subsingleton.elim _ _

def cubeZeroIso (X : Context.{u}) : cubes X 0 ≅ X where
  hom := cubeOrigin X 0
  inv := constantCube X 0
  hom_inv_id := cubeOrigin_constant_zero X
  inv_hom_id := constantCube_origin X 0

def cubeSuccessorIso (X : Context.{u}) (n : ℕ) : cubes X (n+1) ≅ cubes (cubes X n) 1 where
  hom := cubeCurry X n
  inv := cubeUncurry X n
  hom_inv_id := cubeCurry_uncurry X n
  inv_hom_id := cubeUncurry_curry X n

theorem cubeOrigin_successor (X : Context.{u}) (n : ℕ) {I : Cubeᵒᵖ}
    (c : CubeElement X (n+1) I) :
    (cubeOrigin X (n+1)).app I c =
      (cubeOrigin X n).app I (c.apply (Cube.endpoint I.unop false)) := by
  change c.val (𝟙 I) (fun _ => Cube.endpoint I.unop false) =
    c.val (𝟙 I) (Fin.cases (Cube.comp (𝟙 I).unop (Cube.endpoint I.unop false))
      (fun _ => Cube.endpoint I.unop false))
  rw [Cube.comp_endpoint]
  apply congrArg (c.val (𝟙 I))
  funext k
  exact Fin.cases rfl (fun _ => rfl) k

theorem constantCube_successor (X : Context.{u}) (n : ℕ) {I : Cubeᵒᵖ}
    (x : X.obj I) (i : Cube.Hom I.unop ⟨1⟩) :
    ((constantCube X (n+1)).app I x).apply i = (constantCube X n).app I x := rfl

/-- The contraction is an inhabitant of the constructed Path family. -/
def cubeContraction (X : Context.{u}) (n : ℕ) :
    Term (path (Functor.Elements.π (total (interval (cubes X n))) ⋙ cubes X n)
      (transformationTerm (cubeOrigin X n ≫ constantCube X n))
      (transformationTerm (𝟙 (cubes X n)))) :=
  pathLam (transformationTerm (contractCube X n))
    (congrArg transformationTerm (contractCube_zero X n))
    (congrArg transformationTerm (contractCube_one X n))

end SquareKit.Cubical.Presheaf
