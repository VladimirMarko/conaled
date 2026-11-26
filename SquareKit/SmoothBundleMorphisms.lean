import SquareKit.SmoothPrincipalBundle

/-! Ordinary smooth equivariant maps between supplied principal bundles. -/
noncomputable section
namespace SquareKit.SmoothPrincipalBundle
open ManifoldRealization
open scoped Manifold ContDiff
variable {n : ℕ} {G B E E' E'' : Type} [Group G]
  [MulAction G E] [MulAction G E'] [MulAction G E'']
  [TopologicalSpace B] [TopologicalSpace E] [TopologicalSpace E'] [TopologicalSpace E'']
  [ChartedSpace (Space n) B] [ChartedSpace (Space n) E]
  [ChartedSpace (Space n) E'] [ChartedSpace (Space n) E'']

structure Map (P : Bundle (n := n) (G := G) (B := B) (E := E))
    (Q : Bundle (n := n) (G := G) (B := B) (E := E')) where
  toFun : E → E'
  smooth : ContMDiff (modelWithCorners n) (modelWithCorners n) ∞ toFun
  projection : ∀ e, Q.projection (toFun e) = P.projection e
  equivariant : ∀ (g : G) e, toFun (g • e) = g • toFun e

namespace Map
variable {P : Bundle (n := n) (G := G) (B := B) (E := E)}
  {Q : Bundle (n := n) (G := G) (B := B) (E := E')}
  {R : Bundle (n := n) (G := G) (B := B) (E := E'')}

@[ext] theorem ext (f g : Map P Q) (h : f.toFun = g.toFun) : f = g := by
  cases f; cases g; cases h; rfl

def ident (P : Bundle (n := n) (G := G) (B := B) (E := E)) : Map P P where
  toFun := id
  smooth := contMDiff_id
  projection _ := rfl
  equivariant _ _ := rfl

def comp (f : Map P Q) (g : Map Q R) : Map P R where
  toFun := g.toFun ∘ f.toFun
  smooth := g.smooth.comp f.smooth
  projection e := (g.projection _).trans (f.projection e)
  equivariant a e := by simp only [Function.comp_apply, f.equivariant, g.equivariant]

@[simp] theorem ident_comp (f : Map P Q) : (ident P).comp f = f := rfl
@[simp] theorem comp_ident (f : Map P Q) : f.comp (ident Q) = f := rfl

end Map

namespace Bundle
variable (P : Bundle (n := n) (G := G) (B := B) (E := E))

/-- Every base point has a point above it, derived from one local sheet. -/
theorem projection_surjective : Function.Surjective P.projection := by
  intro b
  obtain ⟨t, hb⟩ := P.triviality b
  exact ⟨(t.sheet 1).symm b, t.projection_inverse 1 b hb⟩

/-- The ordinary sheets imply transitivity on each fiber. -/
theorem exists_smul_eq (e e' : E) (h : P.projection e = P.projection e') :
    ∃ g : G, g • e = e' := by
  obtain ⟨t, hb⟩ := P.triviality (P.projection e)
  obtain ⟨a, ha, _⟩ := t.sheets e hb
  obtain ⟨b, hb', _⟩ := t.sheets e' (h ▸ hb)
  refine ⟨b * a⁻¹, ?_⟩
  rw [t.action_on_sheet (b * a⁻¹) a e ha hb]
  simp only [mul_assoc, inv_mul_cancel, mul_one]
  rw [h, t.inverse_projection b e' hb']

end Bundle

namespace Map
variable {P : Bundle (n := n) (G := G) (B := B) (E := E)}
  {Q : Bundle (n := n) (G := G) (B := B) (E := E')}
  (f : Map P Q)

theorem bijective : Function.Bijective f.toFun := by
  constructor
  · intro e e' h
    have hp : P.projection e = P.projection e' := by
      rw [← f.projection, ← f.projection, h]
    obtain ⟨g, hg⟩ := P.exists_smul_eq e e' hp
    have he : g • f.toFun e = (1 : G) • f.toFun e := by
      rw [← f.equivariant, hg, h, one_smul]
    have h1 := Q.action_free g 1 (f.toFun e) he
    simpa [h1] using hg
  · intro e'
    obtain ⟨e, he⟩ := P.projection_surjective (Q.projection e')
    obtain ⟨g, hg⟩ := Q.exists_smul_eq (f.toFun e) e' ((f.projection e).trans he)
    exact ⟨g • e, (f.equivariant g e).trans hg⟩

def equiv : E ≃ E' := Equiv.ofBijective f.toFun f.bijective

end Map
end SquareKit.SmoothPrincipalBundle
namespace SquareKit.SmoothPrincipalBundle
open ManifoldRealization
open scoped Manifold ContDiff
variable {n : ℕ} {G B E E' E'' M : Type} [Group G]
  [MulAction G E] [MulAction G E'] [MulAction G E'']
  [TopologicalSpace B] [TopologicalSpace E] [TopologicalSpace E'] [TopologicalSpace E'']
  [ChartedSpace (Space n) B] [ChartedSpace (Space n) E]
  [ChartedSpace (Space n) E'] [ChartedSpace (Space n) E'']

/-- Maps to a fixed target are part of the ordinary arrow contract. -/
structure TargetMap (P : Bundle (n := n) (G := G) (B := B) (E := E))
    (Q : Bundle (n := n) (G := G) (B := B) (E := E')) (F : E → M) (F' : E' → M)
    extends Map P Q where
  target : ∀ e, F' (toFun e) = F e

namespace TargetMap
variable {P : Bundle (n := n) (G := G) (B := B) (E := E)}
  {Q : Bundle (n := n) (G := G) (B := B) (E := E')}
  {R : Bundle (n := n) (G := G) (B := B) (E := E'')}
  {F : E → M} {F' : E' → M} {F'' : E'' → M}

@[ext] theorem ext (f g : TargetMap P Q F F') (h : f.toMap = g.toMap) : f = g := by
  cases f; cases g; cases h; rfl

def ident (P : Bundle (n := n) (G := G) (B := B) (E := E)) (F : E → M) : TargetMap P P F F where
  toMap := Map.ident P
  target _ := rfl

def comp (f : TargetMap P Q F F') (g : TargetMap Q R F' F'') : TargetMap P R F F'' where
  toMap := f.toMap.comp g.toMap
  target e := (g.target _).trans (f.target e)

end TargetMap
end SquareKit.SmoothPrincipalBundle
