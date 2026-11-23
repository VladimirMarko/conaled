import SquareKit.SmoothBundleMorphisms
import Mathlib.Algebra.Group.Equiv.Opposite
import Mathlib.Algebra.Group.Action.Hom
import Mathlib.Algebra.Group.Action.Opposite

/-! Changing the group labels of a principal bundle, including conversion of
conventional right actions to left actions by inversion. -/
noncomputable section
namespace SquareKit.SmoothPrincipalBundle
open ManifoldRealization MulOpposite
open scoped Manifold ContDiff
section ChangeGroup
variable {n : ℕ} {G H B E : Type} [Group G] [Group H] [MulAction H E]
  [TopologicalSpace B] [TopologicalSpace E]
  [ChartedSpace (Space n) B] [ChartedSpace (Space n) E]

/-- Relabel sheets and the action together along a group isomorphism. -/
def LocalTrivialization.changeGroup {p : E → B}
    (t : LocalTrivialization (n := n) (G := H) p) (e : G ≃* H) :
    letI := MulAction.compHom E e.toMonoidHom
    LocalTrivialization (n := n) (G := G) p := by
  letI := MulAction.compHom E e.toMonoidHom
  exact {
    base := t.base
    isOpen_base := t.isOpen_base
    sheet g := t.sheet (e g)
    target g := t.target (e g)
    projection g := t.projection (e g)
    smooth_inverse g := t.smooth_inverse (e g)
    sheets x hx := by
      obtain ⟨h, hh, hu⟩ := t.sheets x hx
      refine ⟨e.symm h, ?_, ?_⟩
      · simpa using hh
      · intro g hg
        apply e.injective
        simpa using hu (e g) hg
    equivariant g h b hb := by
      change (t.sheet (e (g * h))).symm b = e g • (t.sheet (e h)).symm b
      rw [map_mul]
      exact t.equivariant (e g) (e h) b hb }

/-- The same smooth bundle with group labels transported by an isomorphism. -/
def Bundle.changeGroup (P : Bundle (n := n) (G := H) (B := B) (E := E))
    (e : G ≃* H) :
    letI := MulAction.compHom E e.toMonoidHom
    Bundle (n := n) (G := G) (B := B) (E := E) := by
  letI := MulAction.compHom E e.toMonoidHom
  exact {
    projection := P.projection
    smooth_projection := P.smooth_projection
    smooth_action g := P.smooth_action (e g)
    invariant g := P.invariant (e g)
    triviality b := by
      obtain ⟨t, ht⟩ := P.triviality b
      exact ⟨t.changeGroup e, ht⟩ }

end ChangeGroup

section Maps
variable {n : ℕ} {G H B E E' : Type} [Group G] [Group H]
  [MulAction H E] [MulAction H E']
  [TopologicalSpace B] [TopologicalSpace E] [TopologicalSpace E']
  [ChartedSpace (Space n) B] [ChartedSpace (Space n) E]
  [ChartedSpace (Space n) E']
variable {P : Bundle (n := n) (G := H) (B := B) (E := E)}
  {Q : Bundle (n := n) (G := H) (B := B) (E := E')}

/-- Relabelling changes no underlying bundle map or smoothness requirement. -/
def Map.changeGroupEquiv (e : G ≃* H) :
    letI := MulAction.compHom E e.toMonoidHom
    letI := MulAction.compHom E' e.toMonoidHom
    Map P Q ≃ Map (P.changeGroup e) (Q.changeGroup e) := by
  letI := MulAction.compHom E e.toMonoidHom
  letI := MulAction.compHom E' e.toMonoidHom
  exact {
    toFun f := {
      toFun := f.toFun
      smooth := f.smooth
      projection := f.projection
      equivariant g := f.equivariant (e g) }
    invFun f := {
      toFun := f.toFun
      smooth := f.smooth
      projection := f.projection
      equivariant h x := by
        obtain ⟨g, rfl⟩ := e.surjective h
        exact f.equivariant g x }
    left_inv f := Map.ext _ _ rfl
    right_inv f := Map.ext _ _ rfl }

theorem Map.changeGroupEquiv_apply (e : G ≃* H) (f : Map P Q) :
    letI := MulAction.compHom E e.toMonoidHom
    letI := MulAction.compHom E' e.toMonoidHom
    (Map.changeGroupEquiv e f).toFun = f.toFun := rfl

theorem Map.changeGroupEquiv_ident (e : G ≃* H)
    (P : Bundle (n := n) (G := H) (B := B) (E := E)) :
    letI := MulAction.compHom E e.toMonoidHom
    Map.changeGroupEquiv e (Map.ident P) = Map.ident (P.changeGroup e) := rfl

variable {E'' : Type} [MulAction H E''] [TopologicalSpace E'']
  [ChartedSpace (Space n) E'']

theorem Map.changeGroupEquiv_comp (e : G ≃* H)
    {R : Bundle (n := n) (G := H) (B := B) (E := E'')}
    (f : Map P Q) (g : Map Q R) :
    letI := MulAction.compHom E e.toMonoidHom
    letI := MulAction.compHom E' e.toMonoidHom
    letI := MulAction.compHom E'' e.toMonoidHom
    Map.changeGroupEquiv e (f.comp g) =
      (Map.changeGroupEquiv e f).comp (Map.changeGroupEquiv e g) := rfl

end Maps

section Equivariance
variable {G H E M : Type} [Group G] [Group H] [MulAction H E] [MulAction H M]

/-- The same conversion applies to independently given equivariant target maps. -/
theorem equivariant_changeGroup_iff (e : G ≃* H) (f : E → M) :
    (∀ (g : G) x, f (e g • x) = e g • f x) ↔
      ∀ (h : H) x, f (h • x) = h • f x := by
  constructor
  · intro hf h x
    obtain ⟨g, rfl⟩ := e.surjective h
    exact hf g x
  · intro hf g x
    exact hf (e g) x

end Equivariance

section RightAction
variable {n : ℕ} {G B E : Type} [Group G] [MulAction Gᵐᵒᵖ E]

/-- A conventional right action becomes a left action by `g • e = e · g⁻¹`. -/
abbrev inverseAction : MulAction G E := MulAction.compHom E (MulEquiv.inv' G).toMonoidHom

theorem inverseAction_smul (g : G) (x : E) :
    @SMul.smul G E inverseAction.toSMul g x = op g⁻¹ • x := rfl

/-- This equivalence also converts equivariance of an independent target map. -/
theorem right_equivariant_iff {M : Type} [MulAction Gᵐᵒᵖ M] (f : E → M) :
    (∀ (g : G) x, f (op g⁻¹ • x) = op g⁻¹ • f x) ↔
      ∀ (g : G) x, f (op g • x) = op g • f x := by
  constructor
  · intro hf g x
    simpa using hf g⁻¹ x
  · intro hf g x
    exact hf g⁻¹ x

variable [TopologicalSpace B] [TopologicalSpace E]
  [ChartedSpace (Space n) B] [ChartedSpace (Space n) E]

/-- Right bundles use the ordinary bundle contract for the opposite group. -/
abbrev RightBundle := Bundle (n := n) (G := Gᵐᵒᵖ) (B := B) (E := E)

def RightBundle.toLeft (P : RightBundle (n := n) (G := G) (B := B) (E := E)) :
    letI := inverseAction (G := G) (E := E)
    Bundle (n := n) (G := G) (B := B) (E := E) :=
  P.changeGroup (MulEquiv.inv' G)

/-- In ordinary right-action notation the sheet indexed by `h * g` is the
right translate by `g` of the sheet indexed by `h`. -/
theorem LocalTrivialization.right_sheet {p : E → B}
    (t : LocalTrivialization (n := n) (G := Gᵐᵒᵖ) p)
    (g h : G) (b : B) (hb : b ∈ t.base) :
    (t.sheet (op (h * g))).symm b = op g • (t.sheet (op h)).symm b :=
  t.equivariant (op g) (op h) b hb

/-- Conversion inverts sheet labels as well as the action. -/
theorem LocalTrivialization.toLeft_sheet {p : E → B}
    (t : LocalTrivialization (n := n) (G := Gᵐᵒᵖ) p) (g : G) :
    letI := inverseAction (G := G) (E := E)
    (t.changeGroup (MulEquiv.inv' G)).sheet g = t.sheet (op g⁻¹) := rfl

theorem LocalTrivialization.toLeft_sheet_recover {p : E → B}
    (t : LocalTrivialization (n := n) (G := Gᵐᵒᵖ) p) (g : G) :
    letI := inverseAction (G := G) (E := E)
    (t.changeGroup (MulEquiv.inv' G)).sheet g⁻¹ = t.sheet (op g) := by
  change t.sheet (op (g⁻¹)⁻¹) = t.sheet (op g)
  rw [inv_inv]

/-- Smoothness is unchanged by the inverse-action convention. This applies
to the total space and, independently, to a smooth target action. -/
theorem right_smooth_iff :
    (∀ g : G, ContMDiff (Model n) (Model n) ∞ (fun x : E => op g⁻¹ • x)) ↔
      ∀ g : G, ContMDiff (Model n) (Model n) ∞ (fun x : E => op g • x) := by
  constructor
  · intro h g
    simpa using h g⁻¹
  · intro h g
    exact h g⁻¹

end RightAction

/-- On a regular right torsor the converted action is right multiplication by
the inverse, including for noncommutative groups. -/
theorem inverseAction_regular {G : Type} [Group G] (g x : G) :
    @SMul.smul G G (inverseAction (G := G) (E := G)).toSMul g x = x * g⁻¹ := rfl

end SquareKit.SmoothPrincipalBundle
