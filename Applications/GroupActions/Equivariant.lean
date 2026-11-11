import Applications.GroupActions.Schreier
import Applications.Orbifolds.Equivariant

/-! Equivariant changes of labelled generators. This module imports only the
algebraic action-functor layer; no smooth geometry is needed. -/

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

open CategoryTheory Quiver
namespace Schreier
universe v
variable {G H K : Type*} {X Y Z : Type v} {S T U : Type*}
  [Group G] [Group H] [Group K] [MulAction G X] [MulAction H Y] [MulAction K Z]
  {ι : S → G} {κ : T → H} {μ : U → K}

/-- Generator compatibility is separate from equivariance of the vertices. -/
def equivariantEdges (φ : G →* H) (f : X → Y)
    (hf : ∀ g x, f (g • x) = φ g • f x)
    (σ : S → T) (hs : ∀ s, κ (σ s) = φ (ι s)) :
    SchreierGraph X ι ⥤q SchreierGraph Y κ where
  obj x := ⟨f x.toVertex⟩
  map e := ⟨σ e.val, by
    apply SchreierGraph.ext
    change κ (σ e.val) • f _ = f _
    rw [hs, ← hf]
    exact congrArg f (congrArg SchreierGraph.toVertex e.property)⟩

/-- The induced map preserves raw paths, including direction and generator indices. -/
def equivariantPaths (φ : G →* H) (f : X → Y)
    (hf : ∀ g x, f (g • x) = φ g • f x)
    (σ : S → T) (hs : ∀ s, κ (σ s) = φ (ι s)) :
    PathCategory X ι ⥤ PathCategory Y κ where
  obj := (equivariantEdges φ f hf σ hs).symmetrify.obj
  map := (equivariantEdges φ f hf σ hs).symmetrify.mapPath
  map_id _ := rfl
  map_comp p q := Prefunctor.mapPath_comp _ p q

theorem equivariant_label (φ : G →* H) (f : X → Y)
    (hf : ∀ g x, f (g • x) = φ g • f x)
    (σ : S → T) (hs : ∀ s, κ (σ s) = φ (ι s))
    {x y : PathCategory X ι} (p : x ⟶ y) :
    label κ ((equivariantPaths φ f hf σ hs).map p) = φ (label ι p) := by
  induction p with
  | nil => exact φ.map_one.symm
  | cons p e ih =>
    cases e with
    | inl e =>
      change κ (σ e.val) * label κ ((equivariantPaths φ f hf σ hs).map p) =
        φ (ι e.val * label ι p)
      rw [hs, ih, map_mul]
    | inr e =>
      change (κ (σ e.val))⁻¹ * label κ ((equivariantPaths φ f hf σ hs).map p) =
        φ ((ι e.val)⁻¹ * label ι p)
      rw [hs, ih, map_mul, map_inv]

/-- The native commuting diagram retains both objects and action-arrow labels. -/
theorem interpretation_equivariant (φ : G →* H) (f : X → Y)
    (hf : ∀ g x, f (g • x) = φ g • f x)
    (σ : S → T) (hs : ∀ s, κ (σ s) = φ (ι s)) :
    equivariantPaths φ f hf σ hs ⋙ interpretation κ =
      interpretation ι ⋙ Orbifolds.actionFunctor φ f hf := by
  fapply CategoryTheory.Functor.ext
  · intro x; rfl
  · intro x y p
    simp only [eqToHom_refl, Category.id_comp, Category.comp_id]
    apply Functor.Elements.Hom.ext
    exact equivariant_label φ f hf σ hs p

theorem equivariantPaths_id :
    equivariantPaths (ι := ι) (MonoidHom.id G) (id : X → X)
      (fun _ _ => rfl) id (fun _ => rfl) = 𝟭 (PathCategory X ι) := by
  fapply CategoryTheory.Functor.ext
  · intro x; rfl
  · intro x y p
    simp only [eqToHom_refl, Category.id_comp, Category.comp_id]
    induction p with
    | nil => rfl
    | cons p e ih =>
      change Path.cons _ _ = Path.cons _ _
      congr 1
      cases e <;> rfl

theorem equivariantPaths_comp (φ : G →* H) (ψ : H →* K)
    (f : X → Y) (g : Y → Z)
    (hf : ∀ a x, f (a • x) = φ a • f x)
    (hg : ∀ b y, g (b • y) = ψ b • g y)
    (σ : S → T) (τ : T → U)
    (hs : ∀ s, κ (σ s) = φ (ι s)) (ht : ∀ t, μ (τ t) = ψ (κ t)) :
    equivariantPaths (ψ.comp φ) (g ∘ f) (fun a x => by simp [hf, hg])
        (τ ∘ σ) (fun s => by simp [ht, hs]) =
      equivariantPaths φ f hf σ hs ⋙ equivariantPaths ψ g hg τ ht := by
  fapply CategoryTheory.Functor.ext
  · intro x; rfl
  · intro x y p
    simp only [eqToHom_refl, Category.id_comp, Category.comp_id]
    induction p with
    | nil => rfl
    | cons p e ih =>
      change Path.cons _ _ = Path.cons _ _
      congr 1
      cases e <;> rfl

/-- A public client composes interpretation and two changes using shared maps.
Its composition theorem is obtained from shared laws, with no path induction. -/
def twiceChanged (ι : S → G) (φ : G →* H) (ψ : H →* K)
    (f : X → Y) (g : Y → Z)
    (hf : ∀ a x, f (a • x) = φ a • f x)
    (hg : ∀ b y, g (b • y) = ψ b • g y) :=
  ((rawMap ι).comp (SquareKit.RawMap.ofFunctor (Orbifolds.actionFunctor φ f hf))).comp
    (SquareKit.RawMap.ofFunctor (Orbifolds.actionFunctor ψ g hg))

theorem twiceChanged_laws (ι : S → G) (φ : G →* H) (ψ : H →* K)
    (f : X → Y) (g : Y → Z)
    (hf : ∀ a x, f (a • x) = φ a • f x)
    (hg : ∀ b y, g (b • y) = ψ b • g y) :
    SquareKit.MapLaws (twiceChanged ι φ ψ f g hf hg)
      (semanticEquiv ι) (SquareKit.equality _) :=
  SquareKit.RawMap.comp_laws
    (SquareKit.RawMap.comp_laws (semantic_laws ι) (SquareKit.RawMap.ofFunctor_laws _))
    (SquareKit.RawMap.ofFunctor_laws _)

theorem twiceChanged_comp (ι : S → G) (φ : G →* H) (ψ : H →* K)
    (f : X → Y) (g : Y → Z)
    (hf : ∀ a x, f (a • x) = φ a • f x)
    (hg : ∀ b y, g (b • y) = ψ b • g y)
    {x y z : PathCategory X ι} (p : x ⟶ y) (q : y ⟶ z) :
    (twiceChanged ι φ ψ f g hf hg).map (p ≫ q) =
      (twiceChanged ι φ ψ f g hf hg).map p ≫
        (twiceChanged ι φ ψ f g hf hg).map q :=
  (twiceChanged_laws ι φ ψ f g hf hg).comp q p

/-- The twice-changed shared-map client agrees with changing both path representations
before interpretation. The proof consumes the public naturality result twice. -/
theorem twiceChanged_agrees (φ : G →* H) (ψ : H →* K)
    (f : X → Y) (g : Y → Z)
    (hf : ∀ a x, f (a • x) = φ a • f x)
    (hg : ∀ b y, g (b • y) = ψ b • g y)
    (σ : S → T) (τ : T → U)
    (hs : ∀ s, κ (σ s) = φ (ι s)) (ht : ∀ t, μ (τ t) = ψ (κ t))
    {x y : PathCategory X ι} (p : x ⟶ y) :
    (interpretation μ).map ((equivariantPaths ψ g hg τ ht).map
      ((equivariantPaths φ f hf σ hs).map p)) =
      (twiceChanged ι φ ψ f g hf hg).map p := by
  apply Functor.Elements.Hom.ext
  change label μ _ = ψ (φ (label ι p))
  rw [equivariant_label, equivariant_label]

end Schreier
