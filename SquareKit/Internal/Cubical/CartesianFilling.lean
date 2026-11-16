import SquareKit.Internal.Cubical.CartesianPaths

/-! Variable-source filling in Cartesian presheaves. Tubes are arbitrary
subobjects; finite dimension formulas give the promised cofibrations. -/
set_option autoImplicit false
set_option warningAsError true
namespace SquareKit.Cubical.Cartesian
open CategoryTheory
universe u

inductive Face (n : ℕ) where
  | bot
  | top
  | eq (r s : Dim n)
  | meet (p q : Face n)
  | join (p q : Face n)

namespace Face
variable {n m k : ℕ}
def subst (f : Fin n → Dim m) : Face n → Face m
  | .bot => .bot
  | .top => .top
  | .eq r s => .eq (r.subst f) (s.subst f)
  | .meet p q => .meet (p.subst f) (q.subst f)
  | .join p q => .join (p.subst f) (q.subst f)

def Holds : Face n → Prop
  | .bot => False
  | .top => True
  | .eq r s => r = s
  | .meet p q => p.Holds ∧ q.Holds
  | .join p q => p.Holds ∨ q.Holds

theorem holds_subst (f : Fin n → Dim m) (p : Face n) (h : p.Holds) :
    (p.subst f).Holds := by
  induction p with
  | bot => exact h.elim
  | top => trivial
  | eq r s => exact congrArg (Dim.subst f) h
  | meet p q hp hq => exact ⟨hp h.1, hq h.2⟩
  | join p q hp hq => exact h.elim (fun h => Or.inl (hp h)) (fun h => Or.inr (hq h))

@[simp] theorem subst_id (p : Face n) : p.subst Dim.var = p := by
  induction p <;> simp_all [subst]
@[simp] theorem subst_comp (p : Face n) (f : Fin n → Dim m) (g : Fin m → Dim k) :
    (p.subst f).subst g = p.subst (fun i => (f i).subst g) := by
  induction p <;> simp_all [subst, Dim.subst_subst]
end Face

/-- Membership is stable under every generalized substitution. -/
structure Subcontext (Γ : Context.{u}) where
  holds : Γ.Elements → Prop
  natural : ∀ {x y : Γ.Elements} (_f : x ⟶ y), holds x → holds y

def Subcontext.reindex {Γ Δ : Context.{u}} (φ : Subcontext Γ) (σ : Δ ⟶ Γ) : Subcontext Δ where
  holds x := φ.holds (σ.mapElements.obj x)
  natural f := φ.natural (σ.mapElements.map f)

/-- A locally finite positive formula in dimension equations. -/
structure Cofibration (Γ : Context.{u}) extends Subcontext Γ where
  localFormula : ∀ x : Γ.Elements, ∃ p : Face x.obj.unop.dimension,
    ∀ {y : Γ.Elements} (f : x ⟶ y), holds y ↔ (p.subst f.hom.unop).Holds

def Cofibration.reindex {Γ Δ : Context.{u}} (φ : Cofibration Γ) (σ : Δ ⟶ Γ) :
    Cofibration Δ where
  toSubcontext := φ.toSubcontext.reindex σ
  localFormula x := by
    obtain ⟨p, hp⟩ := φ.localFormula (σ.mapElements.obj x)
    exact ⟨p, fun f => hp (σ.mapElements.map f)⟩

def representable (I : Cube) : Context.{u} where
  obj J := ULift.{u} (J.unop ⟶ I)
  map f := TypeCat.ofHom (fun g => ⟨f.unop ≫ g.down⟩)
  map_id _ := by ext g; exact Category.id_comp g.down
  map_comp _ _ := by ext g; exact Category.assoc _ _ _

def Face.cofibration {I : Cube} (p : Face I.dimension) : Cofibration (representable.{u} I) where
  holds x := (p.subst x.val.down).Holds
  natural f h := by
    have hh := Face.holds_subst f.hom.unop (p.subst _) h
    rw [Face.subst_comp] at hh
    have hf := congrArg ULift.down f.map_val
    change Cube.comp f.hom.unop _ = _ at hf
    rw [← hf]
    exact hh
  localFormula x := ⟨p.subst x.val.down, fun f => by
    rw [Face.subst_comp]
    have hf := congrArg ULift.down f.map_val
    change Cube.comp f.hom.unop _ = _ at hf
    rw [← hf]
    rfl⟩

abbrev constantFamily (Γ : Context.{u}) (S : Type u) : Family Γ :=
  (Functor.const Γ.Elements).obj S
abbrev reindex {Γ Δ : Context.{u}} (A : Family Γ) (σ : Δ ⟶ Γ) := σ.mapElements ⋙ A

def graph {Γ : Context.{u}} (r : Term (interval Γ)) : Γ ⟶ total (interval Γ) where
  app I := TypeCat.ofHom (fun γ => ⟨γ, r.val (Γ.elementsMk I γ)⟩)
  naturality I J f := by
    apply ConcreteCategory.hom_ext
    intro γ
    let h : Γ.elementsMk I γ ⟶ Γ.elementsMk J (Γ.map f γ) :=
      Functor.Elements.homMk f rfl
    change (⟨Γ.map f γ, r.val _⟩ : (total (interval Γ)).obj J) =
      ⟨Γ.map f γ, (interval Γ).map h (r.val _)⟩
    exact (congrArg (fun a => Sigma.mk (Γ.map f γ) a) (r.property h)).symm

def intervalSub {Γ Δ : Context.{u}} (σ : Δ ⟶ Γ) : total (interval Δ) ⟶ total (interval Γ) where
  app I := TypeCat.ofHom (fun z => ⟨σ.app I z.1, z.2⟩)
  naturality I J f := by
    apply ConcreteCategory.hom_ext
    intro z
    change (⟨σ.app J (Δ.map f z.1), ULift.up (Cube.comp f.unop z.2.down)⟩ :
      (total (interval Γ)).obj J) = ⟨Γ.map f (σ.app I z.1),
        ULift.up (Cube.comp f.unop z.2.down)⟩
    exact congrArg (fun a => Sigma.mk a (ULift.up (Cube.comp f.unop z.2.down)))
      (σ.naturality_apply f z.1)


structure PartialSection {Γ : Context.{u}} (A : Family Γ) (φ : Subcontext Γ) where
  val : ∀ x, φ.holds x → A.obj x
  natural : ∀ {x y : Γ.Elements} (f : x ⟶ y) (h : φ.holds x),
    A.map f (val x h) = val y (φ.natural f h)

def PartialSection.reindex {Γ Δ : Context.{u}} {A : Family Γ} {φ : Subcontext Γ}
    (t : PartialSection A φ) (σ : Δ ⟶ Γ) :
    PartialSection (reindex A σ) (φ.reindex σ) where
  val x h := t.val (σ.mapElements.obj x) h
  natural f h := t.natural (σ.mapElements.map f) h

structure OpenBox {Γ : Context.{u}} (A : Family (total (interval Γ)))
    (φ : Subcontext Γ) (r : Term (interval Γ)) where
  tube : PartialSection A (φ.reindex (projection (interval Γ)))
  base : Term (reindex A (graph r))
  boundary : ∀ x h, tube.val (extendObj (interval Γ) x (r.val x)) h = base.val x

def OpenBox.Fills {Γ : Context.{u}} {A : Family (total (interval Γ))}
    {φ : Subcontext Γ} {r : Term (interval Γ)} (b : OpenBox A φ r) (t : Term A) : Prop :=
  Term.reindex t (graph r) = b.base ∧ ∀ x h, t.val x = b.tube.val x h

theorem constant_partial_interval {Γ : Context.{u}} {S : Type u} {φ : Subcontext Γ}
    (t : PartialSection (constantFamily (total (interval Γ)) S)
      (φ.reindex (projection (interval Γ))))
    (x : Γ.Elements) (h : φ.holds x) (r s : (interval Γ).obj x) :
    t.val (extendObj (interval Γ) x r) h = t.val (extendObj (interval Γ) x s) h :=
  (t.natural (intervalArgument (𝟙 x) r) (φ.natural (freshBaseHom x) h)).symm.trans
    (t.natural (intervalArgument (𝟙 x) s) (φ.natural (freshBaseHom x) h))

def OpenBox.presentedFill {Γ : Context.{u}} {A : Family (total (interval Γ))}
    {S : Type u} (e : A ≅ constantFamily (total (interval Γ)) S)
    {φ : Subcontext Γ} {r : Term (interval Γ)} (b : OpenBox A φ r) : Term A :=
  Term.map e.inv (Term.reindex (Term.map (Functor.whiskerLeft (graph r).mapElements e.hom)
    b.base) (projection (interval Γ)))

theorem OpenBox.presentedFill_fills {Γ : Context.{u}} {A : Family (total (interval Γ))}
    {S : Type u} (e : A ≅ constantFamily (total (interval Γ)) S)
    {φ : Subcontext Γ} {r : Term (interval Γ)} (b : OpenBox A φ r) :
    b.Fills (b.presentedFill e) := by
  constructor
  · apply Term.ext
    intro x
    exact e.hom_inv_id_app_apply _ _
  · intro x h
    rcases x with @⟨I, γ, z⟩
    let t : PartialSection (constantFamily (total (interval Γ)) S)
        (φ.reindex (projection (interval Γ))) := {
      val := fun x h => e.hom.app x (b.tube.val x h)
      natural := fun f h => by rw [← e.hom.naturality_apply, b.tube.natural f h] }
    have ht := constant_partial_interval t (Γ.elementsMk I γ) h (r.val _) z
    change e.inv.app (extendObj (interval Γ) (Γ.elementsMk I γ) z)
      (e.hom.app (extendObj (interval Γ) (Γ.elementsMk I γ) (r.val _))
        (b.base.val (Γ.elementsMk I γ))) = _
    rw [← b.boundary (Γ.elementsMk I γ) h]
    change e.inv.app (extendObj (interval Γ) (Γ.elementsMk I γ) z) (t.val (extendObj (interval Γ) (Γ.elementsMk I γ) (r.val _)) h) = _
    rw [ht]
    exact e.hom_inv_id_app_apply _ _


def OpenBox.reindex {Γ Δ : Context.{u}} {A : Family (total (interval Γ))}
    {φ : Subcontext Γ} {r : Term (interval Γ)} (b : OpenBox A φ r) (σ : Δ ⟶ Γ) :
    OpenBox (Cartesian.reindex A (intervalSub σ)) (φ.reindex σ) (Term.reindex r σ) where
  tube := b.tube.reindex (intervalSub σ)
  base := Term.reindex b.base σ
  boundary x h := b.boundary (σ.mapElements.obj x) h

theorem OpenBox.presentedFill_reindex {Γ Δ : Context.{u}}
    {A : Family (total (interval Γ))} {S : Type u}
    (e : A ≅ constantFamily (total (interval Γ)) S)
    {φ : Subcontext Γ} {r : Term (interval Γ)} (b : OpenBox A φ r) (σ : Δ ⟶ Γ) :
    (b.reindex σ).presentedFill (Functor.isoWhiskerLeft (intervalSub σ).mapElements e) =
      Term.reindex (b.presentedFill e) (intervalSub σ) := rfl

structure Filling {Γ : Context.{u}} (A : Family Γ) where
  fill : {Δ : Context.{u}} → (p : total (interval Δ) ⟶ Γ) →
    (φ : Subcontext Δ) → (r : Term (interval Δ)) →
    OpenBox (reindex A p) φ r → Term (reindex A p)

structure Filling.Lawful {Γ : Context.{u}} {A : Family Γ} (F : Filling A) : Prop where
  fills : ∀ {Δ : Context.{u}} (p : total (interval Δ) ⟶ Γ)
    (φ : Subcontext Δ) (r : Term (interval Δ)) (b : OpenBox (reindex A p) φ r),
    b.Fills (F.fill p φ r b)
  uniform : ∀ {Δ Θ : Context.{u}} (p : total (interval Δ) ⟶ Γ)
    (φ : Subcontext Δ) (r : Term (interval Δ)) (b : OpenBox (reindex A p) φ r) (σ : Θ ⟶ Δ),
    F.fill (intervalSub σ ≫ p) (φ.reindex σ) (Term.reindex r σ) (b.reindex σ) =
      Term.reindex (F.fill p φ r b) (intervalSub σ)

def presentedFilling {Γ : Context.{u}} {A : Family Γ} {S : Type u}
    (e : A ≅ constantFamily Γ S) : Filling A where
  fill p _ _ b := b.presentedFill (Functor.isoWhiskerLeft p.mapElements e)

theorem presentedFilling_lawful {Γ : Context.{u}} {A : Family Γ} {S : Type u}
    (e : A ≅ constantFamily Γ S) : (presentedFilling e).Lawful where
  fills p _ _ b := b.presentedFill_fills (Functor.isoWhiskerLeft p.mapElements e)
  uniform _ _ _ _ _ := rfl

/-- Composition evaluates at any target dimension, including a variable. -/
def Filling.comp {Γ Δ : Context.{u}} {A : Family Γ} (F : Filling A)
    (p : total (interval Δ) ⟶ Γ) (φ : Subcontext Δ) (r s : Term (interval Δ))
    (b : OpenBox (reindex A p) φ r) : Term (reindex A (graph s ≫ p)) :=
  Term.reindex (F.fill p φ r b) (graph s)

/-- The source=target law holds locally on the equality subobject. -/
theorem Filling.comp_diagonal {Γ Δ : Context.{u}} {A : Family Γ} {F : Filling A}
    (hF : F.Lawful) (p : total (interval Δ) ⟶ Γ) (φ : Subcontext Δ)
    (r s : Term (interval Δ)) (b : OpenBox (reindex A p) φ r)
    (x : Δ.Elements) (h : r.val x = s.val x) :
    HEq ((F.comp p φ r s b).val x) (b.base.val x) := by
  have hb := congrArg (fun t => t.val x) (hF.fills p φ r b).1
  change (F.fill p φ r b).val (extendObj (interval Δ) x (r.val x)) = _ at hb
  change HEq ((F.fill p φ r b).val (extendObj (interval Δ) x (s.val x))) _
  rw [← h]
  exact heq_of_eq hb

theorem Filling.comp_tube {Γ Δ : Context.{u}} {A : Family Γ} {F : Filling A}
    (hF : F.Lawful) (p : total (interval Δ) ⟶ Γ) (φ : Subcontext Δ)
    (r s : Term (interval Δ)) (b : OpenBox (reindex A p) φ r)
    (x : Δ.Elements) (h : φ.holds x) :
    (F.comp p φ r s b).val x = b.tube.val (extendObj (interval Δ) x (s.val x)) h :=
  (hF.fills p φ r b).2 (extendObj (interval Δ) x (s.val x)) h

theorem constant_section_interval {Γ : Context.{u}} {S : Type u}
    (t : Term (constantFamily (total (interval Γ)) S)) (x : Γ.Elements)
    (r s : (interval Γ).obj x) :
    t.val (extendObj (interval Γ) x r) = t.val (extendObj (interval Γ) x s) :=
  (t.property (intervalArgument (𝟙 x) r)).symm.trans
    (t.property (intervalArgument (𝟙 x) s))

/-- An actual presentation determines every filler from its source graph. -/
theorem OpenBox.presentedFill_unique {Γ : Context.{u}} {A : Family (total (interval Γ))}
    {S : Type u} (e : A ≅ constantFamily (total (interval Γ)) S)
    {φ : Subcontext Γ} {r : Term (interval Γ)} (b : OpenBox A φ r)
    (t : Term A) (ht : Term.reindex t (graph r) = b.base) : t = b.presentedFill e := by
  apply Term.ext
  intro x
  rcases x with @⟨I, γ, z⟩
  have h := constant_section_interval (Term.map e.hom t) (Γ.elementsMk I γ) z (r.val _)
  have hb := congrArg (fun q => q.val (Γ.elementsMk I γ)) ht
  change t.val (extendObj (interval Γ) (Γ.elementsMk I γ) (r.val _)) = _ at hb
  dsimp only [Term.map] at h
  rw [hb] at h
  have hi := congrArg (e.inv.app (extendObj (interval Γ) (Γ.elementsMk I γ) z)) h
  rw [e.hom_inv_id_app_apply] at hi
  exact hi

def freshExtensionMap {Γ : Context.{u}} {x y : Γ.Elements} (f : x ⟶ y) :
    freshExtension x ⟶ freshExtension y :=
  intervalArgument (f ≫ freshBaseHom y) ⟨Cube.fresh y.obj.unop⟩

theorem intervalArgument_fresh {Γ : Context.{u}} {x y : Γ.Elements} (f : x ⟶ y)
    (r : (interval Γ).obj y) :
    freshExtensionMap f ≫ intervalArgument (𝟙 y) r = intervalArgument f r := by
  apply Functor.Elements.Hom.ext
  apply congrArg Quiver.Hom.op
  funext i
  refine Fin.cases ?_ (fun j => ?_) i
  · rfl
  · change ((f.hom.unop j).subst (Cube.drop y.obj.unop)).subst
      (Cube.pair (𝟙 y.obj.unop) r.down) = f.hom.unop j
    cases f.hom.unop j <;> rfl

theorem intervalArgument_square {Γ : Context.{u}}
    {x y : (total (interval Γ)).Elements} (f : x ⟶ y) :
    intervalArgument (𝟙 ((projection (interval Γ)).mapElements.obj x)) x.val.2 ≫ f =
      intervalArgument ((projection (interval Γ)).mapElements.map f) y.val.2 := by
  apply Functor.Elements.Hom.ext
  apply congrArg Quiver.Hom.op
  funext i
  refine Fin.cases ?_ (fun j => ?_) i
  · have h := (Sigma.mk.inj f.map_val).2
    exact congrArg (fun z => z.down 0) (eq_of_heq h)
  · rfl
def BijectiveRestrictions {Γ : Context.{u}} (A : Family Γ) : Prop :=
  ∀ {x y : Γ.Elements} (f : x ⟶ y), Function.Bijective (A.map f)

namespace InvertibleFilling
variable {Γ : Context.{u}} {A : Family (total (interval Γ))}
  (hA : BijectiveRestrictions A) {φ : Subcontext Γ} {r : Term (interval Γ)} (b : OpenBox A φ r)

noncomputable def coefficient (x : Γ.Elements) : A.obj (freshExtension x) :=
  (Equiv.ofBijective (A.map (intervalArgument (𝟙 x) (r.val x))) (hA _)).symm (b.base.val x)

theorem coefficient_source (x : Γ.Elements) :
    A.map (intervalArgument (𝟙 x) (r.val x)) (coefficient hA b x) = b.base.val x :=
  (Equiv.ofBijective _ (hA _)).apply_symm_apply _

theorem coefficient_natural {x y : Γ.Elements} (f : x ⟶ y) :
    A.map (freshExtensionMap f) (coefficient hA b x) = coefficient hA b y := by
  apply (hA (intervalArgument (𝟙 y) (r.val y))).1
  rw [coefficient_source, ← types_comp_apply, ← A.map_comp, intervalArgument_fresh]
  have hs := intervalArgument_square ((graph r).mapElements.map f)
  change intervalArgument (𝟙 x) (r.val x) ≫ (graph r).mapElements.map f =
    intervalArgument f (r.val y) at hs
  exact (congrArg (fun k => A.map k (coefficient hA b x)) hs.symm).trans
    ((congrArg (fun k => k (coefficient hA b x)) (A.map_comp (intervalArgument (𝟙 x) (r.val x)) ((graph r).mapElements.map f))).trans
      ((congrArg (A.map ((graph r).mapElements.map f)) (coefficient_source hA b x)).trans
        (b.base.property f)))

noncomputable def value (x : (total (interval Γ)).Elements) : A.obj x :=
  A.map (intervalArgument (𝟙 ((projection (interval Γ)).mapElements.obj x)) x.val.2)
    (coefficient hA b ((projection (interval Γ)).mapElements.obj x))

theorem value_natural {x y : (total (interval Γ)).Elements} (f : x ⟶ y) :
    A.map f (value hA b x) = value hA b y := by
  let g := (projection (interval Γ)).mapElements.map f
  let sx := intervalArgument (𝟙 ((projection (interval Γ)).mapElements.obj x)) x.val.2
  let sy := intervalArgument (𝟙 ((projection (interval Γ)).mapElements.obj y)) y.val.2
  let c := coefficient hA b ((projection (interval Γ)).mapElements.obj x)
  have hs : sx ≫ f = freshExtensionMap g ≫ sy :=
    (intervalArgument_square f).trans (intervalArgument_fresh g y.val.2).symm
  exact (congrArg (fun k => k c) (A.map_comp sx f).symm).trans
    ((congrArg (fun k => A.map k c) hs).trans
      ((congrArg (fun k => k c) (A.map_comp (freshExtensionMap g) sy)).trans
        (congrArg (A.map sy) (coefficient_natural hA b g))))

noncomputable def fill : Term A where
  val := value hA b
  property := value_natural hA b

theorem fill_fills : b.Fills (fill hA b) := by
  constructor
  · apply Term.ext
    exact coefficient_source hA b
  · intro x hx
    let a := (projection (interval Γ)).mapElements.obj x
    have hb : coefficient hA b a = b.tube.val (freshExtension a)
        (φ.natural (freshBaseHom a) hx) := by
      apply (hA (intervalArgument (𝟙 a) (r.val a))).1
      exact (coefficient_source hA b a).trans
        ((b.boundary a hx).symm.trans
          (b.tube.natural (intervalArgument (𝟙 a) (r.val a))
            (φ.natural (freshBaseHom a) hx)).symm)
    change A.map (intervalArgument (𝟙 a) x.val.2) (coefficient hA b a) = _
    rw [hb]
    exact b.tube.natural _ _

end InvertibleFilling

theorem sections_equal_source {Γ : Context.{u}} {A : Family (total (interval Γ))}
    (hA : BijectiveRestrictions A) (r : Term (interval Γ)) (t q : Term A)
    (h : Term.reindex t (graph r) = Term.reindex q (graph r)) : t = q := by
  apply Term.ext
  intro x
  let a := (projection (interval Γ)).mapElements.obj x
  have hc : t.val (freshExtension a) = q.val (freshExtension a) := by
    apply (hA (intervalArgument (𝟙 a) (r.val a))).1
    exact (t.property _).trans ((congrArg (fun z => z.val a) h).trans (q.property _).symm)
  exact (t.property (intervalArgument (𝟙 a) x.val.2)).symm.trans
    ((congrArg (A.map (intervalArgument (𝟙 a) x.val.2)) hc).trans (q.property _))

noncomputable def bijectiveFilling {Γ : Context.{u}} {A : Family Γ}
    (hA : BijectiveRestrictions A) : Filling A where
  fill p _ _ b := InvertibleFilling.fill (fun f => hA (p.mapElements.map f)) b

theorem bijectiveFilling_lawful {Γ : Context.{u}} {A : Family Γ}
    (hA : BijectiveRestrictions A) : (bijectiveFilling hA).Lawful where
  fills p _ _ b := InvertibleFilling.fill_fills (fun f => hA (p.mapElements.map f)) b
  uniform p φ r b σ := by
    apply sections_equal_source (fun f => hA ((intervalSub σ ≫ p).mapElements.map f))
      (Term.reindex r σ)
    exact (InvertibleFilling.fill_fills (fun f => hA ((intervalSub σ ≫ p).mapElements.map f))
      (b.reindex σ)).1.trans
        (congrArg (fun t => Term.reindex t σ)
          (InvertibleFilling.fill_fills (fun f => hA (p.mapElements.map f)) b).1).symm

end SquareKit.Cubical.Cartesian
