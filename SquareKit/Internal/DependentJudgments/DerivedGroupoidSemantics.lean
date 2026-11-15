import SquareKit.Internal.DependentJudgments.DerivedPathSemantics
import SquareKit.Internal.PathTransport.ConcatSemantics

/-! The generated recipes act by the frozen groupoid operations. These
identifications use discrete primitive and identity fibers, not a higher model. -/
noncomputable section
namespace SquareKit.Internal.DependentJudgments.Contextual.DerivedSemantics.Groupoid
open CategoryTheory PathTransport.GroupoidModel PathTransport.GroupoidModel.PathComparison
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
universe u
variable (C : Type u) [Groupoid.{u} C] (B : C ⥤ Type u)
local notation "M" => Instance.fullModel C B

/-- Supply the schematic source B by the actual fiber at the generic base point. -/
def genericFiber (G : Grpd.{u,u}) : (M).Family ((M).extend G (constant C)) :=
  primitiveFiber B («variable» (constant C))

/-- Identification with the frozen primitive functor action, using discrete
J uniqueness. This is stronger than returning the selected J operation. -/
theorem transportSection_action {G : Grpd.{u,u}}
    (x : Section (constant (Γ := G) C)) (b : Section (primitiveFiber B x)) :
    (transportSection M (constant C) (genericFiber C B G) ⟨x⟩ ⟨b⟩).down =
      PathTransport.GroupoidModel.DerivedSemantics.transport B x b := by
  exact PathTransport.GroupoidModel.SourceSemantics.canonicalJ_transport C B x b

/-- Applying the generated transport recipe at its actual endpoint acts by
B.map on the selected path, with no loss of the selected fiber element. -/
theorem transportValue_action {G : Grpd.{u,u}}
    (x y : Section (constant (Γ := G) C))
    (p : Section (identityFamily (constant C) x y)) (b : Section (primitiveFiber B x))
    (g : G) :
    ((transportValue M (constant C) (genericFiber C B G) ⟨x⟩ ⟨y⟩ ⟨p⟩ ⟨b⟩).down.obj g).as =
      B.map (p.obj g).as (b.obj g).as := by
  change ((transportSection M (constant C) (genericFiber C B G) ⟨x⟩ ⟨b⟩).down.obj
    ⟨⟨g, y.obj g⟩, p.obj g⟩).as = _
  rw [transportSection_action]
  rfl

/-- Canonical right-path composition over the full endpoint-and-path context. -/
def concatSection {G : Grpd.{u,u}}
    (x y : Section (constant (Γ := G) C))
    (p : Section (identityFamily (constant C) x y)) :
    Section (motive M (constant C)
      ((M).toStructuralModel.pathFamily (constant C) ⟨x⟩) ⟨y⟩) :=
  PathTransport.GroupoidModel.DerivedSemantics.composePaths (constant C)
    (x.reindex (PathTransport.GroupoidModel.weaken (PathFamily (constant C) y) ⋙ PathTransport.GroupoidModel.weaken (constant C)))
    (y.reindex (PathTransport.GroupoidModel.weaken (PathFamily (constant C) y) ⋙ PathTransport.GroupoidModel.weaken (constant C)))
    (PathTransport.GroupoidModel.DerivedSemantics.endpoint y)
    (p.reindex (PathTransport.GroupoidModel.weaken (PathFamily (constant C) y) ⋙ PathTransport.GroupoidModel.weaken (constant C)))
    («variable» (PathFamily (constant C) y))

/-- Discrete identity fibers identify right-path J with actual composition.
The frozen left-path recipe is identified with this same operation elsewhere. -/
theorem concatSection_action {G : Grpd.{u,u}}
    (x y : Section (constant (Γ := G) C))
    (p : Section (identityFamily (constant C) x y)) :
    (transportSection M (constant C) ((M).toStructuralModel.pathFamily (constant C) ⟨x⟩)
      ⟨y⟩ ⟨p⟩).down = concatSection C B x y p := by
  let : ∀ g, IsDiscrete ((motive M (constant C)
      ((M).toStructuralModel.pathFamily (constant C) ⟨x⟩) ⟨y⟩).obj g) :=
    fun _ => inferInstanceAs (IsDiscrete (Discrete _))
  apply Instance.contextualJ_unique
  apply Section.ext_discrete
  intro g
  apply Discrete.ext
  change (p.obj g).as ≫ 𝟙 (y.obj g) = (p.obj g).as
  exact Category.comp_id _

theorem concatValue_action {G : Grpd.{u,u}}
    (x y z : Section (constant (Γ := G) C))
    (p : Section (identityFamily (constant C) x y))
    (q : Section (identityFamily (constant C) y z)) (g : G) :
    ((concatValue M (constant C) ⟨x⟩ ⟨y⟩ ⟨z⟩ ⟨p⟩ ⟨q⟩).down.obj g).as =
      (p.obj g).as ≫ (q.obj g).as := by
  change ((transportSection M (constant C) ((M).toStructuralModel.pathFamily (constant C) ⟨x⟩)
    ⟨y⟩ ⟨p⟩).down.obj ⟨⟨g, z.obj g⟩, q.obj g⟩).as = _
  rw [concatSection_action]
  rfl

/-- These are substitutions of actual semantic contexts, not substitutions
of the source recipe's schematic variables. -/
theorem transportValue_reindex_twice {G H K : Grpd.{u,u}}
    (x y : Section (constant (Γ := G) C))
    (p : Section (identityFamily (constant C) x y)) (b : Section (primitiveFiber B x))
    (σ : H ⥤ G) (τ : K ⥤ H) :
    ((transportValue M (constant C) (genericFiber C B G) ⟨x⟩ ⟨y⟩ ⟨p⟩ ⟨b⟩).down.reindex σ).reindex τ =
      (transportValue M (constant C) (genericFiber C B K)
        ⟨(x.reindex σ).reindex τ⟩ ⟨(y.reindex σ).reindex τ⟩
        ⟨(p.reindex σ).reindex τ⟩ ⟨(b.reindex σ).reindex τ⟩).down := by
  apply Section.ext_discrete (A := primitiveFiber B ((y.reindex σ).reindex τ))
  intro k
  apply Discrete.ext
  change ((transportValue M (constant C) (genericFiber C B G) ⟨x⟩ ⟨y⟩ ⟨p⟩ ⟨b⟩).down.obj
    (σ.obj (τ.obj k))).as = _
  rw [transportValue_action, transportValue_action]
  rfl

theorem concatValue_reindex_twice {G H K : Grpd.{u,u}}
    (x y z : Section (constant (Γ := G) C))
    (p : Section (identityFamily (constant C) x y))
    (q : Section (identityFamily (constant C) y z)) (σ : H ⥤ G) (τ : K ⥤ H) :
    ((concatValue M (constant C) ⟨x⟩ ⟨y⟩ ⟨z⟩ ⟨p⟩ ⟨q⟩).down.reindex σ).reindex τ =
      (concatValue M (constant C)
        ⟨(x.reindex σ).reindex τ⟩ ⟨(y.reindex σ).reindex τ⟩ ⟨(z.reindex σ).reindex τ⟩
        ⟨(p.reindex σ).reindex τ⟩ ⟨(q.reindex σ).reindex τ⟩).down := by
  apply Section.ext_discrete (A := identityFamily (constant C)
    ((x.reindex σ).reindex τ) ((z.reindex σ).reindex τ))
  intro k
  apply Discrete.ext
  change ((concatValue M (constant C) ⟨x⟩ ⟨y⟩ ⟨z⟩ ⟨p⟩ ⟨q⟩).down.obj
    (σ.obj (τ.obj k))).as = _
  rw [concatValue_action, concatValue_action]
  rfl

abbrev transportRecipe : Expression (Fin 9) :=
  Contextual.transport (.var 0) (.var 1) (.var 2) (.var 3) (.var 4) (.var 5) (.var 6)
abbrev transportRecipeTwice : Expression (Fin 9) :=
  subTm (subTm transportRecipe (.var 7)) (.var 8)

def transportEnvironment {G H K : Grpd.{u,u}}
    (x y : Section (constant (Γ := G) C))
    (p : Section (identityFamily (constant C) x y)) (b : Section (primitiveFiber B x))
    (σ : H ⥤ G) (τ : K ⥤ H) : Fin 9 → Value (M).toStructuralModel :=
  ![.context G, .family G (constant C), .family ((M).extend G (constant C)) (genericFiber C B G),
    .term G (constant C) ⟨x⟩, .term G (constant C) ⟨y⟩,
    .term G (identityFamily (constant C) x y) ⟨p⟩, .term G (primitiveFiber B x) ⟨b⟩,
    .substitution H G ⟨σ⟩, .substitution K H ⟨τ⟩]

theorem transportRecipe_eval {G H K : Grpd.{u,u}}
    (x y : Section (constant (Γ := G) C))
    (p : Section (identityFamily (constant C) x y)) (b : Section (primitiveFiber B x))
    (σ : H ⥤ G) (τ : K ⥤ H) :
    transportRecipe.eval (algebra M) (transportEnvironment C B x y p b σ τ) =
      .term G (primitiveFiber B y)
        (transportValue M (constant C) (genericFiber C B G) ⟨x⟩ ⟨y⟩ ⟨p⟩ ⟨b⟩) :=
  transport_eval M _ _ _ _ _ _ _ _ G (constant C) (genericFiber C B G)
    ⟨x⟩ ⟨y⟩ ⟨p⟩ ⟨b⟩ rfl rfl rfl rfl rfl rfl rfl

/-- Observation of the interpreted source recipe is the frozen functor action. -/
theorem transportRecipe_action {G H K : Grpd.{u,u}}
    (x y : Section (constant (Γ := G) C))
    (p : Section (identityFamily (constant C) x y)) (b : Section (primitiveFiber B x))
    (σ : H ⥤ G) (τ : K ⥤ H) (g : G) :
    Option.map (fun t : (M).Section G (primitiveFiber B y) => (t.down.obj g).as)
      ((transportRecipe.eval (algebra M) (transportEnvironment C B x y p b σ τ)).termAt G
        (primitiveFiber B y)) = some (B.map (p.obj g).as (b.obj g).as) := by
  rw [transportRecipe_eval]
  simp only [Value.termAt_term, Option.map_some]
  exact congrArg some (transportValue_action C B x y p b g)

abbrev concatRecipe : Expression (Fin 7) :=
  Contextual.concat (.var 0) (.var 1) (.var 2) (.var 3) (.var 4) (.var 5) (.var 6)

def concatEnvironment {G : Grpd.{u,u}} (x y z : Section (constant (Γ := G) C))
    (p : Section (identityFamily (constant C) x y))
    (q : Section (identityFamily (constant C) y z)) : Fin 7 → Value (M).toStructuralModel :=
  ![.context G, .family G (constant C), .term G (constant C) ⟨x⟩,
    .term G (constant C) ⟨y⟩, .term G (constant C) ⟨z⟩,
    .term G (identityFamily (constant C) x y) ⟨p⟩,
    .term G (identityFamily (constant C) y z) ⟨q⟩]

theorem concatRecipe_eval {G : Grpd.{u,u}} (x y z : Section (constant (Γ := G) C))
    (p : Section (identityFamily (constant C) x y))
    (q : Section (identityFamily (constant C) y z)) :
    concatRecipe.eval (algebra M) (concatEnvironment C B x y z p q) =
      .term G (identityFamily (constant C) x z) (concatValue M (constant C) ⟨x⟩ ⟨y⟩ ⟨z⟩ ⟨p⟩ ⟨q⟩) :=
  concat_eval M _ _ _ _ _ _ _ _ G (constant C) ⟨x⟩ ⟨y⟩ ⟨z⟩ ⟨p⟩ ⟨q⟩
    rfl rfl rfl rfl rfl rfl rfl

/-- The interpreted right-path source recipe has exactly the frozen left-path
recipe's composition action; their raw J recipes need not coincide. -/
theorem concatRecipe_action {G : Grpd.{u,u}} (x y z : Section (constant (Γ := G) C))
    (p : Section (identityFamily (constant C) x y))
    (q : Section (identityFamily (constant C) y z)) (g : G) :
    Option.map (fun t : (M).Section G (identityFamily (constant C) x z) => (t.down.obj g).as)
      ((concatRecipe.eval (algebra M) (concatEnvironment C B x y z p q)).termAt G
        (identityFamily (constant C) x z)) = some ((p.obj g).as ≫ (q.obj g).as) := by
  rw [concatRecipe_eval]
  simp only [Value.termAt_term, Option.map_some]
  exact congrArg some (concatValue_action C B x y z p q g)

set_option backward.defeqAttrib.useBackward false in
/-- Object substitution of the source transport twice equals fresh evaluation
of the unchanged source recipe in the twice-reindexed environment. -/
theorem transportRecipe_reindex_twice {G H K : Grpd.{u,u}}
    (x y : Section (constant (Γ := G) C))
    (p : Section (identityFamily (constant C) x y)) (b : Section (primitiveFiber B x))
    (σ : H ⥤ G) (τ : K ⥤ H) :
    transportRecipeTwice.eval (algebra M) (transportEnvironment C B x y p b σ τ) =
      transportRecipe.eval (algebra M)
        (transportEnvironment C B ((x.reindex σ).reindex τ) ((y.reindex σ).reindex τ)
          ((p.reindex σ).reindex τ) ((b.reindex σ).reindex τ) (𝟭 K) (𝟭 K)) := by
  have h := transportRecipe_eval C B x y p b σ τ
  have h1 := subTm_eval M (transportEnvironment C B x y p b σ τ)
    transportRecipe (.var 7) G H (primitiveFiber B y)
    (transportValue M (constant C) (genericFiber C B G) ⟨x⟩ ⟨y⟩ ⟨p⟩ ⟨b⟩) ⟨σ⟩ h rfl
  have h2 := subTm_eval M (transportEnvironment C B x y p b σ τ)
    (subTm transportRecipe (.var 7)) (.var 8) H K _ _ ⟨τ⟩ h1 rfl
  have hf := transportRecipe_eval C B ((x.reindex σ).reindex τ) ((y.reindex σ).reindex τ)
    ((p.reindex σ).reindex τ) ((b.reindex σ).reindex τ) (𝟭 K) (𝟭 K)
  simp only [Instance.fullModel, Instance.structuralModel] at h2
  have h2' : transportRecipeTwice.eval (algebra M) (transportEnvironment C B x y p b σ τ) =
      @Value.term ((M).toStructuralModel) K (primitiveFiber B ((y.reindex σ).reindex τ))
        ⟨((transportValue M (constant C) (genericFiber C B G) ⟨x⟩ ⟨y⟩ ⟨p⟩ ⟨b⟩).down.reindex σ).reindex τ⟩ := h2
  rw [h2', hf]
  apply congrArg (@Value.term ((M).toStructuralModel) K (primitiveFiber B ((y.reindex σ).reindex τ)))
  exact congrArg (ULift.up.{u+1}) (transportValue_reindex_twice C B x y p b σ τ)

section FrozenSource
open PathTransport PathTransport.Typed PathTransport.Typed.Authoring
variable {Γ : RawCtx} {γ : CtxCode.{u+1}}

/-- Direct comparison with the frozen source transport's selected action. -/
theorem transportRecipe_frozen (hΓ : CtxDeriv Γ γ) {x y : BasePoint Γ γ}
    (p : Path x y) (b : FiberElement x) (g : ↥(show Grpd.{u,u} from γ M)) :
    Option.map (fun t : (M).Section (γ M) (primitiveFiber B (y.code M).down) => (t.down.obj g).as)
      ((transportRecipe.eval (algebra M)
        (transportEnvironment C B (x.code M).down (y.code M).down (p.code M).down (b.code M).down
          (𝟭 ↥(show Grpd.{u,u} from γ M)) (𝟭 ↥(show Grpd.{u,u} from γ M)))).termAt (γ M) (primitiveFiber B (y.code M).down)) =
      some ((((PathTransport.Typed.Authoring.transport hΓ p b).code M).down.obj g).as) := by
  rw [transportRecipe_action]
  exact congrArg some (PathTransport.GroupoidModel.SourceSemantics.transport_obj C B hΓ p b g).symm

/-- The new right-path J and the frozen left-path J retain the same composite
arrow in this groupoid model; no equality of their source syntax is asserted. -/
theorem concatRecipe_frozen (hΓ : CtxDeriv Γ γ) {x y z : BasePoint Γ γ}
    (p : Path x y) (q : Path y z) (g : ↥(show Grpd.{u,u} from γ M)) :
    Option.map (fun t : (M).Section (γ M)
        (identityFamily (constant C) (x.code M).down (z.code M).down) => (t.down.obj g).as)
      ((concatRecipe.eval (algebra M)
        (concatEnvironment C B (x.code M).down (y.code M).down (z.code M).down
          (p.code M).down (q.code M).down)).termAt (γ M)
        (identityFamily (constant C) (x.code M).down (z.code M).down)) =
      some ((((PathTransport.Typed.Authoring.concat hΓ p q).code M).down.obj g).as) := by
  rw [concatRecipe_action]
  exact congrArg some (PathTransport.GroupoidModel.ConcatSemantics.concat_obj C B hΓ x p q g).symm

end FrozenSource

end SquareKit.Internal.DependentJudgments.Contextual.DerivedSemantics.Groupoid
