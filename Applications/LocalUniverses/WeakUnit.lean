module

public import Mathlib.CategoryTheory.CodiscreteCategory
public import Mathlib.CategoryTheory.Functor.Currying
public import Mathlib.CategoryTheory.Groupoid

/-! Actual selected lift data and the conjugation construction for a weak unit. -/
@[expose] public section

set_option autoImplicit false
set_option warningAsError true

namespace LocalUniverses.WeakUnit
open CategoryTheory
open scoped CategoryTheory.Prod
universe u v u₁ v₁ u₂ v₂ u₃ v₃

abbrev I := Codiscrete Bool
abbrev zero : I := ⟨false⟩
abbrev one : I := ⟨true⟩

instance : Groupoid I where
  inv _ := ()

variable {Γ : Type u} [Groupoid.{v} Γ]
variable {E : Type u₁} [Groupoid.{v₁} E] {V : Type u₂} [Groupoid.{v₂} V]

def constructor (Γ : Type u) [Category.{v} Γ] : Γ ⥤ Γ × I where
  obj x := (x, zero)
  map f := f ×ₘ 𝟙 zero

/-- Transport a whole functor along selected object isomorphisms. -/
def conjugate {C : Type*} [Category* C] (F : C ⥤ E)
    (obj : C → E) (lift : ∀ x, F.obj x ≅ obj x) : C ⥤ E where
  obj := obj
  map {x y} f := (lift x).inv ≫ F.map f ≫ (lift y).hom
  map_id x := by simp
  map_comp f g := by simp

/-- A chosen lift has an actual target; equality over the target is explicit. -/
structure Lift (p : E ⥤ V) (e : E) (v : V) where
  target : E
  over : p.obj target = v
  arrow : e ≅ target

def identityLift (p : E ⥤ V) (e : E) : Lift p e (p.obj e) where
  target := e
  over := rfl
  arrow := Iso.refl e

/-- Identity normalization is separate from the deliberately absent composition law. -/
structure NormalizedLifts (p : E ⥤ V) where
  lift : ∀ (e : E) (v : V) (_f : p.obj e ⟶ v), Lift p e v
  image : ∀ e v f, p.map (lift e v f).arrow.hom ≫ eqToHom (lift e v f).over = f
  identity : ∀ e, lift e (p.obj e) (𝟙 _) = identityLift p e

variable (p : E ⥤ V) (L : NormalizedLifts p)
variable (c : Γ × I ⥤ V) (d : Γ ⥤ E) (h : d ⋙ p = constructor Γ ⋙ c)

include h in
theorem branchEq (x : Γ) : p.obj (d.obj x) = c.obj (x,zero) :=
  congrArg (fun F : Γ ⥤ V => F.obj x) h

def outgoing (x : Γ) : p.obj (d.obj x) ⟶ c.obj (x,one) :=
  eqToHom (branchEq p c d h x) ≫ c.map (𝟙 x ×ₘ (Codiscrete.iso zero one).hom)

def selected (x : Γ) := L.lift (d.obj x) (c.obj (x,one)) (outgoing p c d h x)

def directObj (x : Γ × I) : E :=
  match x.2.as with
  | false => d.obj x.1
  | true => (selected p L c d h x.1).target

def directIso (x : Γ × I) : d.obj x.1 ≅ directObj p L c d h x :=
  match x with
  | (_, ⟨false⟩) => Iso.refl _
  | (x, ⟨true⟩) => (selected p L c d h x).arrow

def direct : Γ × I ⥤ E :=
  conjugate ((CategoryTheory.Prod.fst Γ I) ⋙ d) (directObj p L c d h)
    (directIso p L c d h)

@[simp] theorem directObj_zero (x : Γ) : directObj p L c d h (x,zero) = d.obj x := rfl
@[simp] theorem directIso_zero (x : Γ) : directIso p L c d h (x,zero) = Iso.refl _ := rfl

theorem direct_beta : constructor Γ ⋙ direct p L c d h = d := by
  apply Functor.ext (F := constructor Γ ⋙ direct p L c d h) (G := d) (fun _ => rfl)

theorem directOver (x : Γ × I) : p.obj (directObj p L c d h x) = c.obj x := by
  rcases x with ⟨x,⟨i⟩⟩
  cases i
  · exact branchEq p c d h x
  · exact (selected p L c d h x).over

def leg (x : Γ × I) : (x.1,zero) ⟶ x := 𝟙 x.1 ×ₘ (Codiscrete.iso zero x.2).hom

theorem leg_natural {x y : Γ × I} (f : x ⟶ y) :
    (f.1 ×ₘ 𝟙 zero) ≫ leg y = leg x ≫ f := by
  apply CategoryTheory.Prod.hom_ext
  · simp [leg]
  · exact Subsingleton.elim _ _

theorem directIso_image (x : Γ × I) :
    p.map (directIso p L c d h x).hom ≫ eqToHom (directOver p L c d h x) =
      eqToHom (branchEq p c d h x.1) ≫ c.map (leg x) := by
  rcases x with ⟨x,⟨i⟩⟩
  cases i
  · have hi : leg (x,zero) = 𝟙 (x,zero) := by rfl
    change p.map (𝟙 (d.obj x)) ≫ eqToHom _ = eqToHom _ ≫ c.map (leg (x,zero))
    rw [hi]
    simp only [Functor.map_id, Category.id_comp, Category.comp_id]
  · exact L.image _ _ _

theorem branch_map {x y : Γ} (f : x ⟶ y) :
    p.map (d.map f) ≫ eqToHom (branchEq p c d h y) =
      eqToHom (branchEq p c d h x) ≫ c.map (f ×ₘ 𝟙 zero) := by
  have hh := Functor.congr_hom h f
  change p.map (d.map f) = eqToHom (branchEq p c d h x) ≫
    c.map (f ×ₘ 𝟙 zero) ≫ eqToHom (branchEq p c d h y).symm at hh
  simpa [Category.assoc] using congrArg
    (fun k => k ≫ eqToHom (branchEq p c d h y)) hh

theorem direct_projection : direct p L c d h ⋙ p = c := by
  refine Functor.ext (F := direct p L c d h ⋙ p) (G := c)
    (directOver p L c d h) ?_
  intro x y f
  change p.map ((directIso p L c d h x).inv ≫ d.map f.1 ≫
    (directIso p L c d h y).hom) =
      eqToHom (directOver p L c d h x) ≫ c.map f ≫ eqToHom (directOver p L c d h y).symm
  apply (cancel_mono (eqToHom (directOver p L c d h y))).1
  simp only [Functor.map_comp, Category.assoc]
  rw [directIso_image p L c d h y]
  rw [← Category.assoc (p.map (d.map f.1)), branch_map p c d h f.1]
  rw [Category.assoc, ← c.map_comp, leg_natural, c.map_comp]
  rw [← Category.assoc (eqToHom (branchEq p c d h x.1)), ← directIso_image p L c d h x]
  simp

variable {Δ : Type u₃} [Groupoid.{v₃} Δ]

theorem constructor_natural (σ : Δ ⥤ Γ) :
    constructor Δ ⋙ σ.prod (𝟭 I) = σ ⋙ constructor Γ := by
  rfl

include h in
theorem reindexBranch (σ : Δ ⥤ Γ) :
    (σ ⋙ d) ⋙ p = constructor Δ ⋙ (σ.prod (𝟭 I) ⋙ c) := by
  calc
    _ = σ ⋙ (d ⋙ p) := rfl
    _ = σ ⋙ (constructor Γ ⋙ c) := congrArg (fun F => σ ⋙ F) h
    _ = _ := by rw [← Functor.assoc, ← constructor_natural]; rfl

theorem outgoing_substitution (σ : Δ ⥤ Γ) (x : Δ) :
    outgoing p (σ.prod (𝟭 I) ⋙ c) (σ ⋙ d) (reindexBranch p c d h σ) x =
      outgoing p c d h (σ.obj x) := by
  change eqToHom _ ≫ c.map (σ.map (𝟙 x) ×ₘ (Codiscrete.iso zero one).hom) = _
  rw [σ.map_id]
  rfl

theorem selected_substitution (σ : Δ ⥤ Γ) (x : Δ) :
    selected p L (σ.prod (𝟭 I) ⋙ c) (σ ⋙ d) (reindexBranch p c d h σ) x =
      selected p L c d h (σ.obj x) := by
  unfold selected
  rw [outgoing_substitution]
  rfl

theorem direct_substitution (σ : Δ ⥤ Γ) :
    direct p L (σ.prod (𝟭 I) ⋙ c) (σ ⋙ d) (reindexBranch p c d h σ) =
      σ.prod (𝟭 I) ⋙ direct p L c d h := by
  apply Functor.hext
  · rintro ⟨x,⟨i⟩⟩
    cases i
    · rfl
    · exact congrArg Lift.target (selected_substitution p L c d h σ x)
  · rintro ⟨x,⟨i⟩⟩ ⟨y,⟨j⟩⟩ f
    change ((directIso p L (σ.prod (𝟭 I) ⋙ c) (σ ⋙ d) _ (x,⟨i⟩)).inv ≫
      d.map (σ.map f.1) ≫ (directIso p L (σ.prod (𝟭 I) ⋙ c) (σ ⋙ d) _ (y,⟨j⟩)).hom) ≍
      ((directIso p L c d h (σ.obj x,⟨i⟩)).inv ≫ d.map (σ.map f.1) ≫
      (directIso p L c d h (σ.obj y,⟨j⟩)).hom)
    cases i <;> cases j <;> dsimp only [directIso, directObj, Functor.comp_obj]
    all_goals try rw [selected_substitution p L c d h σ x]
    all_goals try rw [selected_substitution p L c d h σ y]
    all_goals rfl

/-- Natural transformations into a groupoid are invertible componentwise. -/
@[instance_reducible] noncomputable def functorGroupoid : Groupoid (I ⥤ V) :=
  Groupoid.ofIsIso (fun f => NatIso.isIso_of_isIso_app f)

/-- Strict equality over the constructor, rather than an isomorphism. -/
@[ext] structure Parameter (p : E ⥤ V) where
  motive : I ⥤ V
  branch : E
  over : p.obj branch = motive.obj zero

namespace Parameter
variable {p}
@[ext] structure Hom (a b : Parameter p) where
  motive : a.motive ⟶ b.motive
  branch : a.branch ⟶ b.branch
  over : p.map branch ≫ eqToHom b.over = eqToHom a.over ≫ motive.app zero

instance : Category (Parameter p) where
  Hom := Hom
  id a := ⟨𝟙 a.motive, 𝟙 a.branch, by simp⟩
  comp f g := ⟨f.motive ≫ g.motive, f.branch ≫ g.branch, by
    simp only [Functor.map_comp, NatTrans.comp_app, Category.assoc]
    rw [g.over, ← Category.assoc, f.over]
    simp [Category.assoc]⟩
  id_comp f := by apply Hom.ext <;> simp
  comp_id f := by apply Hom.ext <;> simp
  assoc f g k := by apply Hom.ext <;> simp [Category.assoc]

@[simp] theorem id_motive (a : Parameter p) : (𝟙 a : a ⟶ a).motive = 𝟙 a.motive := rfl
@[simp] theorem id_branch (a : Parameter p) : (𝟙 a : a ⟶ a).branch = 𝟙 a.branch := rfl
@[simp] theorem comp_motive {a b z : Parameter p} (f : a ⟶ b) (g : b ⟶ z) :
    (f ≫ g).motive = f.motive ≫ g.motive := rfl
@[simp] theorem comp_branch {a b z : Parameter p} (f : a ⟶ b) (g : b ⟶ z) :
    (f ≫ g).branch = f.branch ≫ g.branch := rfl

noncomputable def inverse {a b : Parameter p} (f : a ⟶ b) : b ⟶ a where
  motive := (NatIso.ofComponents (fun i => asIso (f.motive.app i))
    (fun k => f.motive.naturality k)).inv
  branch := inv f.branch
  over := by
    apply (cancel_mono (f.motive.app zero)).1
    apply (cancel_epi (p.map f.branch)).1
    simp only [Category.assoc]
    rw [← Category.assoc (p.map f.branch), ← p.map_comp]
    simp only [IsIso.hom_inv_id, Functor.map_id, Category.id_comp]
    change eqToHom a.over ≫ f.motive.app zero =
      p.map f.branch ≫ eqToHom b.over ≫ inv (f.motive.app zero) ≫ f.motive.app zero
    simpa using f.over.symm

noncomputable instance : Groupoid (Parameter p) where
  inv := inverse
  inv_comp f := by
    apply Hom.ext
    · ext i; simp [inverse]
    · simp [inverse]
  comp_inv f := by
    apply Hom.ext
    · ext i; simp [inverse]
    · simp [inverse]

def motiveFunctor : Parameter p ⥤ I ⥤ V where
  obj a := a.motive
  map f := f.motive

def branchFunctor : Parameter p ⥤ E where
  obj a := a.branch
  map f := f.branch

def evaluation : Parameter p × I ⥤ V := Functor.uncurry.obj (motiveFunctor (p := p))

theorem genericBranch : branchFunctor (p := p) ⋙ p = constructor (Parameter p) ⋙ evaluation := by
  refine Functor.ext (fun a => a.over) ?_
  intro a b f
  change p.map f.branch = eqToHom a.over ≫
    (f.motive.app zero ≫ b.motive.map (𝟙 zero)) ≫ eqToHom b.over.symm
  apply (cancel_mono (eqToHom b.over)).1
  simpa using f.over

theorem functor_ext {C : Type*} [Category* C] {F G : C ⥤ Parameter p}
    (hm : F ⋙ motiveFunctor = G ⋙ motiveFunctor)
    (hb : F ⋙ branchFunctor = G ⋙ branchFunctor) : F = G := by
  let ho : ∀ x, F.obj x = G.obj x := fun x => Parameter.ext
    (congrArg (fun K : C ⥤ I ⥤ V => K.obj x) hm)
    (congrArg (fun K : C ⥤ E => K.obj x) hb)
  refine Functor.ext ho ?_
  intro x y f
  apply Hom.ext
  · have hh := Functor.congr_hom hm f
    change (F.map f).motive = _ at hh
    change (F.map f).motive = motiveFunctor.map (eqToHom (ho x) ≫ G.map f ≫ eqToHom (ho y).symm)
    rw [Functor.map_comp, Functor.map_comp, eqToHom_map, eqToHom_map]
    exact hh
  · have hh := Functor.congr_hom hb f
    change (F.map f).branch = _ at hh
    change (F.map f).branch = branchFunctor.map (eqToHom (ho x) ≫ G.map f ≫ eqToHom (ho y).symm)
    rw [Functor.map_comp, Functor.map_comp, eqToHom_map, eqToHom_map]
    exact hh

end Parameter

def name : Γ ⥤ Parameter p where
  obj x := ⟨(Functor.curry.obj c).obj x, d.obj x, branchEq p c d h x⟩
  map f := ⟨(Functor.curry.obj c).map f, d.map f, branch_map p c d h f⟩
  map_id x := by apply Parameter.Hom.ext <;> simp
  map_comp f g := by apply Parameter.Hom.ext <;> simp

theorem name_branch : name p c d h ⋙ Parameter.branchFunctor = d := rfl

theorem name_motive : (name p c d h).prod (𝟭 I) ⋙ Parameter.evaluation = c := by
  exact Functor.uncurry_obj_curry_obj c

theorem name_evaluation (n : Γ ⥤ Parameter p) :
    name p (n.prod (𝟭 I) ⋙ Parameter.evaluation) (n ⋙ Parameter.branchFunctor)
      (reindexBranch p Parameter.evaluation Parameter.branchFunctor Parameter.genericBranch n) = n := by
  apply Parameter.functor_ext
  · exact Functor.curry_obj_uncurry_obj (n ⋙ Parameter.motiveFunctor)
  · rfl

theorem curry_substitution (σ : Δ ⥤ Γ) :
    Functor.curry.obj (σ.prod (𝟭 I) ⋙ c) = σ ⋙ Functor.curry.obj c := by
  refine Functor.ext (fun x => ?_) ?_
  · refine Functor.ext (F := (Functor.curry.obj (σ.prod (𝟭 I) ⋙ c)).obj x)
      (G := (Functor.curry.obj c).obj (σ.obj x)) (fun _ => rfl) ?_
    intro i j f
    change c.map (σ.map (𝟙 x) ×ₘ f) = _
    simp
  · intro x y f
    ext i
    simp [Functor.curry, Functor.curryObj, eqToHom_app]

theorem name_substitution (σ : Δ ⥤ Γ) :
    name p (σ.prod (𝟭 I) ⋙ c) (σ ⋙ d) (reindexBranch p c d h σ) = σ ⋙ name p c d h := by
  apply Parameter.functor_ext
  · exact curry_substitution c σ
  · rfl

noncomputable def generic : Parameter p × I ⥤ E :=
  direct p L Parameter.evaluation Parameter.branchFunctor Parameter.genericBranch

theorem generic_beta : constructor (Parameter p) ⋙ generic p L = Parameter.branchFunctor :=
  direct_beta p L _ _ _

theorem generic_projection : generic p L ⋙ p = Parameter.evaluation :=
  direct_projection p L _ _ _


theorem instantiated_agreement :
    (name p c d h).prod (𝟭 I) ⋙ generic p L = direct p L c d h := by
  have hs := direct_substitution p L Parameter.evaluation Parameter.branchFunctor
    Parameter.genericBranch (name p c d h)
  simp only [name_motive, name_branch] at hs
  exact hs.symm

/-- The parameter route instantiates the constructed generic filler. -/
noncomputable def parameterEliminator : Γ × I ⥤ E :=
  (name p c d h).prod (𝟭 I) ⋙ generic p L

theorem parameter_substitution (σ : Δ ⥤ Γ) :
    parameterEliminator p L (σ.prod (𝟭 I) ⋙ c) (σ ⋙ d) (reindexBranch p c d h σ) =
      σ.prod (𝟭 I) ⋙ parameterEliminator p L c d h := by
  unfold parameterEliminator
  rw [name_substitution p c d h σ]
  rfl

theorem parameter_beta : constructor Γ ⋙ parameterEliminator p L c d h = d := by
  change constructor Γ ⋙ (name p c d h).prod (𝟭 I) ⋙ generic p L = d
  rw [← Functor.assoc, constructor_natural, Functor.assoc, generic_beta, name_branch]

theorem parameter_projection : parameterEliminator p L c d h ⋙ p = c := by
  change ((name p c d h).prod (𝟭 I) ⋙ generic p L) ⋙ p = c
  rw [Functor.assoc, generic_projection, name_motive]

/-- Native input data; the branch condition is equality of functors. -/
@[ext] structure Family (Γ : Type u) [Groupoid.{v} Γ] (p : E ⥤ V) where
  motive : Γ × I ⥤ V
  branch : Γ ⥤ E
  equation : branch ⋙ p = constructor Γ ⋙ motive

def represent (a : Family Γ p) : Γ ⥤ Parameter p := name p a.motive a.branch a.equation

def realize (n : Γ ⥤ Parameter p) : Family Γ p where
  motive := n.prod (𝟭 I) ⋙ Parameter.evaluation
  branch := n ⋙ Parameter.branchFunctor
  equation := reindexBranch p _ _ Parameter.genericBranch n

theorem realize_represent (a : Family Γ p) : realize p (represent p a) = a := by
  apply Family.ext
  · exact name_motive p a.motive a.branch a.equation
  · rfl

theorem represent_realize (n : Γ ⥤ Parameter p) : represent p (realize p n) = n :=
  name_evaluation p n

def representation : Family Γ p ≃ (Γ ⥤ Parameter p) where
  toFun := represent p
  invFun := realize p
  left_inv := realize_represent p
  right_inv := represent_realize p

universe u₄ v₄
variable {Θ : Type u₄} [Groupoid.{v₄} Θ]

theorem direct_composite_substitution (σ : Δ ⥤ Γ) (τ : Θ ⥤ Δ) :
    direct p L ((τ ⋙ σ).prod (𝟭 I) ⋙ c) ((τ ⋙ σ) ⋙ d)
      (reindexBranch p c d h (τ ⋙ σ)) =
    τ.prod (𝟭 I) ⋙ σ.prod (𝟭 I) ⋙ direct p L c d h := by
  exact direct_substitution p L c d h (τ ⋙ σ)

theorem parameter_composite_substitution (σ : Δ ⥤ Γ) (τ : Θ ⥤ Δ) :
    parameterEliminator p L ((τ ⋙ σ).prod (𝟭 I) ⋙ c) ((τ ⋙ σ) ⋙ d)
      (reindexBranch p c d h (τ ⋙ σ)) =
    τ.prod (𝟭 I) ⋙ σ.prod (𝟭 I) ⋙ parameterEliminator p L c d h :=
  parameter_substitution p L c d h (τ ⋙ σ)

end LocalUniverses.WeakUnit
