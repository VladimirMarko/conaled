import SquareKit.SheafGroupoid
import Mathlib.CategoryTheory.Limits.Shapes.Pullback.IsPullback.Basic

/-! Coordinates on a represented groupoid retain the actual arrows over a pair
of endpoint maps. Operations are reconstructed through the pullback property. -/
noncomputable section
set_option autoImplicit false
namespace SquareKit.SheafGroupoid
open CategoryTheory CategoryTheory.Limits
universe u v
variable {C : Type u} [Category.{v} C] {J : GrothendieckTopology C}
variable (G : Operations J) {U V W T S : Sheaf J (Type (max u v))}

/-- A presentation of all arrows over two endpoint maps, retaining the full pullback property. -/
structure Chart (u : U ⟶ G.objects) (v : V ⟶ G.objects) where
  coordinates : Sheaf J (Type (max u v))
  source : coordinates ⟶ U
  target : coordinates ⟶ V
  assembly : coordinates ⟶ G.arrows
  isPullback : IsPullback assembly (prod.lift source target)
    (prod.lift G.source G.target) (prod.map u v)

namespace Chart

/-- Every pair of endpoint maps has a canonical sheaf chart of all arrows between them. -/
def canonical (u : U ⟶ G.objects) (v : V ⟶ G.objects) : Chart G u v where
  coordinates := pullback (prod.lift G.source G.target) (prod.map u v)
  source := pullback.snd _ _ ≫ prod.fst
  target := pullback.snd _ _ ≫ prod.snd
  assembly := pullback.fst _ _
  isPullback := by
    have h : prod.lift
        (pullback.snd (prod.lift G.source G.target) (prod.map u v) ≫ prod.fst)
        (pullback.snd (prod.lift G.source G.target) (prod.map u v) ≫ prod.snd) =
        pullback.snd (prod.lift G.source G.target) (prod.map u v) := by
      apply prod.hom_ext <;> simp
    rw [h]
    exact IsPullback.of_hasPullback _ _

variable {G} {u : U ⟶ G.objects} {v : V ⟶ G.objects}
  (D : Chart G u v)

/-- Sections retain both selected endpoint lifts and the full coordinate arrow. -/
def Arrow (m : T ⟶ U) (n : T ⟶ V) :=
  {f : T ⟶ D.coordinates // f ≫ D.source = m ∧ f ≫ D.target = n}

@[reassoc] theorem assembly_source : D.assembly ≫ G.source = D.source ≫ u := by
  have h := congrArg (fun f => f ≫ prod.fst) D.isPullback.w
  simpa using h

@[reassoc] theorem assembly_target : D.assembly ≫ G.target = D.target ≫ v := by
  have h := congrArg (fun f => f ≫ prod.snd) D.isPullback.w
  simpa using h

/-- Actual arrows with specified lifted endpoints have unique coordinates. -/
def arrowEquiv (m : T ⟶ U) (n : T ⟶ V) :
    D.Arrow m n ≃ G.Arrow ⟨m ≫ u⟩ ⟨n ≫ v⟩ where
  toFun f := ⟨f.val ≫ D.assembly, by
    rw [Category.assoc, D.assembly_source, ← Category.assoc, f.property.1], by
    rw [Category.assoc, D.assembly_target, ← Category.assoc, f.property.2]⟩
  invFun f := ⟨D.isPullback.lift f.map (prod.lift m n) (by
      apply prod.hom_ext <;> simp [f.source, f.target]), by
    have h := D.isPullback.lift_snd f.map (prod.lift m n) (by
      apply prod.hom_ext <;> simp [f.source, f.target])
    constructor
    · simpa using congrArg (fun k => k ≫ prod.fst) h
    · simpa using congrArg (fun k => k ≫ prod.snd) h⟩
  left_inv f := by
    apply Subtype.ext
    apply D.isPullback.hom_ext
    · exact D.isPullback.lift_fst _ _ _
    · rw [D.isPullback.lift_snd]
      apply prod.hom_ext <;> simp [f.property.1, f.property.2]
  right_inv f := by
    apply Operations.Arrow.ext
    exact D.isPullback.lift_fst _ _ _

/-- A coordinate change is determined by its reconstruction of actual arrows. -/
def comparison (E : Chart G u v) (m : T ⟶ U) (n : T ⟶ V) :
    D.Arrow m n ≃ E.Arrow m n := (D.arrowEquiv m n).trans (E.arrowEquiv m n).symm

@[simp] theorem comparison_recovery (E : Chart G u v) (m : T ⟶ U) (n : T ⟶ V)
    (f : D.Arrow m n) : E.arrowEquiv m n (D.comparison E m n f) = D.arrowEquiv m n f :=
  (E.arrowEquiv m n).apply_symm_apply _

theorem comparison_trans (E F : Chart G u v) (m : T ⟶ U) (n : T ⟶ V)
    (f : D.Arrow m n) : E.comparison F m n (D.comparison E m n f) = D.comparison F m n f := by
  apply (F.arrowEquiv m n).injective
  simp only [comparison_recovery]


/-- Restrict coordinate arrows by precomposition at an arbitrary sheaf parameter. -/
def restrict (r : S ⟶ T) {m : T ⟶ U} {n : T ⟶ V} (f : D.Arrow m n) :
    D.Arrow (r ≫ m) (r ≫ n) :=
  ⟨r ≫ f.val, by simp [Category.assoc, f.property.1],
    by simp [Category.assoc, f.property.2]⟩

theorem arrowEquiv_restrict (r : S ⟶ T) {m : T ⟶ U} {n : T ⟶ V}
    (f : D.Arrow m n) :
    D.arrowEquiv (r ≫ m) (r ≫ n) (D.restrict r f) =
      (D.arrowEquiv m n f).restrict G r := by
  apply Operations.Arrow.ext
  exact Category.assoc _ _ _

/-- The output inverse chart may be chosen independently. -/
def inverse (E : Chart G v u) {m : T ⟶ U} {n : T ⟶ V} (f : D.Arrow m n) :
    E.Arrow n m := (E.arrowEquiv n m).symm ((D.arrowEquiv m n f).inverse G)

@[simp] theorem inverse_recovery (E : Chart G v u) {m : T ⟶ U} {n : T ⟶ V}
    (f : D.Arrow m n) :
    E.arrowEquiv n m (D.inverse E f) = (D.arrowEquiv m n f).inverse G :=
  (E.arrowEquiv n m).apply_symm_apply _

/-- Compose actual arrows and recover coordinates in an independently chosen output chart. -/
def comp {w : W ⟶ G.objects} (E : Chart G v w) (F : Chart G u w)
    {m : T ⟶ U} {n : T ⟶ V} {p : T ⟶ W} (f : D.Arrow m n) (g : E.Arrow n p) :
    F.Arrow m p := (F.arrowEquiv m p).symm ((D.arrowEquiv m n f).comp G (E.arrowEquiv n p g))

@[simp] theorem comp_recovery {w : W ⟶ G.objects} (E : Chart G v w) (F : Chart G u w)
    {m : T ⟶ U} {n : T ⟶ V} {p : T ⟶ W} (f : D.Arrow m n) (g : E.Arrow n p) :
    F.arrowEquiv m p (D.comp E F f g) = (D.arrowEquiv m n f).comp G (E.arrowEquiv n p g) :=
  (F.arrowEquiv m p).apply_symm_apply _

theorem comparison_inverse (D' : Chart G u v) (E E' : Chart G v u)
    {m : T ⟶ U} {n : T ⟶ V} (f : D.Arrow m n) :
    E.comparison E' n m (D.inverse E f) = D'.inverse E' (D.comparison D' m n f) := by
  apply (E'.arrowEquiv n m).injective
  simp only [comparison_recovery, inverse_recovery]

theorem comparison_comp {w : W ⟶ G.objects}
    (D' : Chart G u v) (E E' : Chart G v w) (F F' : Chart G u w)
    {m : T ⟶ U} {n : T ⟶ V} {p : T ⟶ W} (f : D.Arrow m n) (g : E.Arrow n p) :
    F.comparison F' m p (D.comp E F f g) =
      D'.comp E' F' (D.comparison D' m n f) (E.comparison E' n p g) := by
  apply (F'.arrowEquiv m p).injective
  simp only [comparison_recovery, comp_recovery]

/-- Identity arrows are recovered from the actual groupoid unit. -/
def ident (E : Chart G u u) (m : T ⟶ U) : E.Arrow m m :=
  (E.arrowEquiv m m).symm (Operations.Arrow.ident G ⟨m ≫ u⟩)

@[simp] theorem ident_recovery (E : Chart G u u) (m : T ⟶ U) :
    E.arrowEquiv m m (ident E m) = Operations.Arrow.ident G ⟨m ≫ u⟩ :=
  (E.arrowEquiv m m).apply_symm_apply _

theorem comparison_ident (E E' : Chart G u u) (m : T ⟶ U) :
    E.comparison E' m m (ident E m) = ident E' m := by
  apply (E'.arrowEquiv m m).injective
  simp only [comparison_recovery, ident_recovery]

theorem restrict_comp {w : W ⟶ G.objects} (E : Chart G v w) (F : Chart G u w)
    (r : S ⟶ T) {m : T ⟶ U} {n : T ⟶ V} {p : T ⟶ W}
    (f : D.Arrow m n) (g : E.Arrow n p) :
    F.restrict r (D.comp E F f g) = D.comp E F (D.restrict r f) (E.restrict r g) := by
  apply (F.arrowEquiv _ _).injective
  simp only [arrowEquiv_restrict, comp_recovery, Operations.Arrow.restrict_comp]
  rfl

theorem restrict_inverse (E : Chart G v u) (r : S ⟶ T)
    {m : T ⟶ U} {n : T ⟶ V} (f : D.Arrow m n) :
    E.restrict r (D.inverse E f) = D.inverse E (D.restrict r f) := by
  apply (E.arrowEquiv _ _).injective
  simp only [arrowEquiv_restrict, inverse_recovery, Operations.Arrow.restrict_inverse]
  rfl

theorem restrict_ident (E : Chart G u u) (r : S ⟶ T) (m : T ⟶ U) :
    E.restrict r (ident E m) = ident E (r ≫ m) := by
  apply (E.arrowEquiv _ _).injective
  simp only [arrowEquiv_restrict, ident_recovery, Operations.Arrow.restrict_ident]
  rfl

section Laws
variable [G.Laws]

theorem ident_comp (I : Chart G u u) {m : T ⟶ U} {n : T ⟶ V} (f : D.Arrow m n) :
    I.comp D D (ident I m) f = f := by
  apply (D.arrowEquiv _ _).injective
  simp only [comp_recovery, ident_recovery, Operations.Laws.id_comp]

theorem comp_ident (I : Chart G v v) {m : T ⟶ U} {n : T ⟶ V} (f : D.Arrow m n) :
    D.comp I D f (ident I n) = f := by
  apply (D.arrowEquiv _ _).injective
  simp only [comp_recovery, ident_recovery, Operations.Laws.comp_id]

theorem inverse_comp (E : Chart G v u) (I : Chart G v v)
    {m : T ⟶ U} {n : T ⟶ V} (f : D.Arrow m n) :
    E.comp D I (D.inverse E f) f = ident I n := by
  apply (I.arrowEquiv _ _).injective
  simp only [comp_recovery, inverse_recovery, ident_recovery, Operations.Laws.inv_comp]

theorem comp_inverse (E : Chart G v u) (I : Chart G u u)
    {m : T ⟶ U} {n : T ⟶ V} (f : D.Arrow m n) :
    D.comp E I f (D.inverse E f) = ident I m := by
  apply (I.arrowEquiv _ _).injective
  simp only [comp_recovery, inverse_recovery, ident_recovery, Operations.Laws.comp_inv]

theorem assoc {Q : Sheaf J (Type (max u v))} {w : W ⟶ G.objects} {q : Q ⟶ G.objects}
    (E : Chart G v w) (F : Chart G w q) (P : Chart G u w) (R : Chart G v q)
    (H : Chart G u q) {m : T ⟶ U} {n : T ⟶ V} {p : T ⟶ W} {z : T ⟶ Q}
    (f : D.Arrow m n) (g : E.Arrow n p) (h : F.Arrow p z) :
    P.comp F H (D.comp E P f g) h = D.comp R H f (E.comp F R g h) := by
  apply (H.arrowEquiv _ _).injective
  simp only [comp_recovery, Operations.Laws.assoc]

end Laws

end Chart
end SquareKit.SheafGroupoid
