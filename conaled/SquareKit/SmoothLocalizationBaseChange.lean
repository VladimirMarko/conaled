import SquareKit.SmoothPresentedLocalization
import Mathlib.RingTheory.Nilpotent.Basic

/-! Experimental universal base change for formal smooth localizations.
Arrows are smooth algebra maps; these pushout squares have geometric pullback variance. -/
noncomputable section
namespace SquareKit.SmoothAlgebra.PresentedLocalization
variable {n m a b c d : ℕ}
variable {C : Type*} [CommRing C] [Algebra ℝ C] [Structure C]

def map (r : Fin m → Free n) (p : Free n) (t : Fin b → Free a) (q : Free a)
    (h : Hom (Presentation.Carrier r) (Presentation.Carrier t))
    (he : h (Presentation.projection r p) = Presentation.projection t q) : Hom (Carrier r p) (Carrier t q) :=
  lift r p (Hom.comp (base t q) h) (by
    change IsUnit (base t q (h (Presentation.projection r p)))
    rw [he]
    exact base_isUnit t q)

@[simp] theorem map_base (r : Fin m → Free n) (p : Free n) (t : Fin b → Free a) (q : Free a)
    (h : Hom (Presentation.Carrier r) (Presentation.Carrier t))
    (he : h (Presentation.projection r p) = Presentation.projection t q) :
    Hom.comp (map r p t q h he) (base r p) = Hom.comp (base t q) h := by
  unfold map
  apply lift_base

theorem map_ident (r : Fin m → Free n) (p : Free n) : map r p r p Hom.ident rfl = Hom.ident := by
  apply unique r p
  exact map_base r p r p Hom.ident rfl

theorem map_comp (r : Fin m → Free n) (p : Free n) (t : Fin b → Free a) (q : Free a)
    (v : Fin d → Free c) (w : Free c)
    (h : Hom (Presentation.Carrier r) (Presentation.Carrier t))
    (j : Hom (Presentation.Carrier t) (Presentation.Carrier v))
    (he : h (Presentation.projection r p) = Presentation.projection t q)
    (je : j (Presentation.projection t q) = Presentation.projection v w) :
    Hom.comp (map t q v w j je) (map r p t q h he) =
      map r p v w (Hom.comp j h) (by change j (h _) = _; rw [he,je]) := by
  apply unique r p
  rw [← Hom.comp_assoc,map_base,Hom.comp_assoc,map_base,map_base,Hom.comp_assoc]

/-- The same quotient element gives canonical inverse comparisons between any representatives. -/
def compare (r : Fin m → Free n) (p q : Free n)
    (he : Presentation.projection r p = Presentation.projection r q) : Hom (Carrier r p) (Carrier r q) :=
  map r p r q Hom.ident he

theorem compare_base (r : Fin m → Free n) (p q : Free n)
    (he : Presentation.projection r p = Presentation.projection r q) :
    Hom.comp (compare r p q he) (base r p) = base r q := map_base r p r q Hom.ident he

theorem compare_inverse (r : Fin m → Free n) (p q : Free n)
    (he : Presentation.projection r p = Presentation.projection r q) :
    Hom.comp (compare r q p he.symm) (compare r p q he) = Hom.ident :=
  (map_comp r p r q r p Hom.ident Hom.ident he he.symm).trans (map_ident r p)

def atMap (r : Fin m → Free n) (s : Presentation.Carrier r) (t : Fin b → Free a)
    (h : Hom (Presentation.Carrier r) (Presentation.Carrier t)) : Hom (At r s) (At t (h s)) :=
  map r (representative r s) t (representative t (h s)) h (by simp)

theorem atMap_ident (r : Fin m → Free n) (s : Presentation.Carrier r) :
    atMap r s r Hom.ident = Hom.ident := map_ident r (representative r s)

theorem atMap_comp (r : Fin m → Free n) (s : Presentation.Carrier r)
    (t : Fin b → Free a) (v : Fin d → Free c)
    (h : Hom (Presentation.Carrier r) (Presentation.Carrier t))
    (j : Hom (Presentation.Carrier t) (Presentation.Carrier v)) :
    Hom.comp (atMap t (h s) v j) (atMap r s t h) = atMap r s v (Hom.comp j h) :=
  map_comp r (representative r s) t (representative t (h s)) v (representative v (j (h s))) h j (by simp) (by simp)

/-- A caller's representative and the internally chosen representative give inverse smooth maps. -/
def toChosen (r : Fin m → Free n) (s : Presentation.Carrier r) (p : Free n)
    (hp : Presentation.projection r p = s) : Hom (Carrier r p) (At r s) :=
  compare r p (representative r s) (hp.trans (representative_eq r s).symm)
def fromChosen (r : Fin m → Free n) (s : Presentation.Carrier r) (p : Free n)
    (hp : Presentation.projection r p = s) : Hom (At r s) (Carrier r p) :=
  compare r (representative r s) p ((representative_eq r s).trans hp.symm)
theorem chosen_inverse (r : Fin m → Free n) (s : Presentation.Carrier r) (p : Free n)
    (hp : Presentation.projection r p = s) : Hom.comp (fromChosen r s p hp) (toChosen r s p hp) = Hom.ident :=
  compare_inverse r p (representative r s) (hp.trans (representative_eq r s).symm)
theorem inverse_chosen (r : Fin m → Free n) (s : Presentation.Carrier r) (p : Free n)
    (hp : Presentation.projection r p = s) : Hom.comp (toChosen r s p hp) (fromChosen r s p hp) = Hom.ident :=
  compare_inverse r (representative r s) p ((representative_eq r s).trans hp.symm)

/-- Every compatible pair factors through the square, for arbitrary smooth targets. -/
def pushoutLift (r : Fin m → Free n) (p : Free n) (t : Fin b → Free a) (q : Free a)
    (h : Hom (Presentation.Carrier r) (Presentation.Carrier t))
    (he : h (Presentation.projection r p) = Presentation.projection t q)
    (u : Hom (Carrier r p) C) (v : Hom (Presentation.Carrier t) C)
    (hc : Hom.comp u (base r p) = Hom.comp v h) : Hom (Carrier t q) C :=
  lift t q v (by
    have hu := (base_isUnit r p).map u.toAlgHom
    have hh := congrArg (fun k : Hom (Presentation.Carrier r) C => k (Presentation.projection r p)) hc
    change u (base r p (Presentation.projection r p)) = v (h (Presentation.projection r p)) at hh
    change IsUnit (u (base r p (Presentation.projection r p))) at hu
    rw [hh,he] at hu
    exact hu)

theorem pushoutLift_base (r : Fin m → Free n) (p : Free n) (t : Fin b → Free a) (q : Free a)
    (h : Hom (Presentation.Carrier r) (Presentation.Carrier t))
    (he : h (Presentation.projection r p) = Presentation.projection t q)
    (u : Hom (Carrier r p) C) (v : Hom (Presentation.Carrier t) C)
    (hc : Hom.comp u (base r p) = Hom.comp v h) :
    Hom.comp (pushoutLift r p t q h he u v hc) (base t q) = v := by
  unfold pushoutLift
  apply lift_base

theorem pushoutLift_map (r : Fin m → Free n) (p : Free n) (t : Fin b → Free a) (q : Free a)
    (h : Hom (Presentation.Carrier r) (Presentation.Carrier t))
    (he : h (Presentation.projection r p) = Presentation.projection t q)
    (u : Hom (Carrier r p) C) (v : Hom (Presentation.Carrier t) C)
    (hc : Hom.comp u (base r p) = Hom.comp v h) :
    Hom.comp (pushoutLift r p t q h he u v hc) (map r p t q h he) = u := by
  apply unique r p
  rw [← Hom.comp_assoc,map_base,Hom.comp_assoc,pushoutLift_base,hc]

theorem pushout_universal (r : Fin m → Free n) (p : Free n) (t : Fin b → Free a) (q : Free a)
    (h : Hom (Presentation.Carrier r) (Presentation.Carrier t))
    (he : h (Presentation.projection r p) = Presentation.projection t q)
    (u : Hom (Carrier r p) C) (v : Hom (Presentation.Carrier t) C)
    (hc : Hom.comp u (base r p) = Hom.comp v h) :
    ∃! k : Hom (Carrier t q) C,
      Hom.comp k (map r p t q h he) = u ∧ Hom.comp k (base t q) = v := by
  refine ⟨pushoutLift r p t q h he u v hc,⟨pushoutLift_map _ _ _ _ _ _ _ _ _,pushoutLift_base _ _ _ _ _ _ _ _ _⟩,?_⟩
  intro k hk
  apply unique t q
  rw [hk.2,pushoutLift_base]

def unitRetraction (r : Fin m → Free n) (p : Free n) (hu : IsUnit (Presentation.projection r p)) : Hom (Carrier r p) (Presentation.Carrier r) :=
  lift r p Hom.ident hu

theorem unit_base_inverse (r : Fin m → Free n) (p : Free n) (hu : IsUnit (Presentation.projection r p)) :
    Hom.comp (unitRetraction r p hu) (base r p) = Hom.ident := lift_base r p Hom.ident hu

theorem unit_inverse_base (r : Fin m → Free n) (p : Free n) (hu : IsUnit (Presentation.projection r p)) :
    Hom.comp (base r p) (unitRetraction r p hu) = Hom.ident := by
  apply unique r p
  rw [← Hom.comp_assoc,unit_base_inverse]
  rfl

theorem nilpotent_subsingleton (r : Fin m → Free n) (p : Free n)
    (hn : IsNilpotent (Presentation.projection r p)) : Subsingleton (Carrier r p) := by
  by_contra h
  let : Nontrivial (Carrier r p) := not_subsingleton_iff_nontrivial.mp h
  exact (hn.map (base r p).toAlgHom).not_isUnit (base_isUnit r p)

end SquareKit.SmoothAlgebra.PresentedLocalization
