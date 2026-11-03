import SquareKit.Internal.MixedSetting
import SquareKit.Internal.PresheafGraphs

/-! Experimental finite formation in presheaves. The parameter is a subfunctor,
and both parts of a model must restrict. Classical selection is inherited from
`FiniteSetting.modelSectionEquiv`; source decidability is not assumed. -/
namespace SquareKit.Internal.PresheafSetting
set_option backward.isDefEq.respectTransparency false
open CategoryTheory Opposite
universe v
variable {J : Type v} [SmallCategory J]
variable {X Y Z : Jᵒᵖ ⥤ Type}

abbrev Presentation (X : Jᵒᵖ ⥤ Type) := Subfunctor X

def stage (T : Presentation X) (j : Jᵒᵖ) : FiniteSetting.Presentation (X.obj j) :=
  ⟨T.obj j⟩

def restrict (T : Presentation X) {j k : Jᵒᵖ} (f : j ⟶ k) (x : X.obj j) :
    FiniteSetting.Fiber (stage T j) x → FiniteSetting.Fiber (stage T k) (X.map f x)
  | .inl h => .inl ⟨T.map f h.down⟩
  | .inr _ => .inr ()

@[simp] theorem restrict_left (T : Presentation X) {j k : Jᵒᵖ} (f : j ⟶ k)
    (x : X.obj j) (a : FiniteSetting.Fiber (stage T j) x) :
    (restrict T f x a).isLeft = a.isLeft := by cases a <;> rfl

@[simp] theorem restrict_right (T : Presentation X) {j k : Jᵒᵖ} (f : j ⟶ k)
    (x : X.obj j) (a : FiniteSetting.Fiber (stage T j) x) :
    (restrict T f x a).isRight = a.isRight := by cases a <;> rfl

/-- Fibres are propositions plus a singleton, so a tag determines an element. -/
theorem fiber_ext {T : FiniteSetting.Presentation α} {x : α}
    {a b : FiniteSetting.Fiber T x} (h : a.isLeft = b.isLeft) : a = b := by
  cases a <;> cases b <;> simp_all only [Sum.isLeft_inl, Sum.isLeft_inr, Bool.true_eq_false, Bool.false_eq_true]
  all_goals exact congrArg _ (Subsingleton.elim _ _)

/-- The same finite source syntax denotes subpresheaves, with unions for disjunction. -/
def sourceFormula (T P Q : Subfunctor X) : FiniteSetting.Formula → Subfunctor X
  | .p => P
  | .q => Q
  | .parameter => T
  | .top => ⊤
  | .bottom => ⊥
  | .and a b => sourceFormula T P Q a ⊓ sourceFormula T P Q b
  | .or a b => sourceFormula T P Q a ⊔ sourceFormula T P Q b

theorem source_evaluation (T P Q : Subfunctor X) (a : FiniteSetting.Formula)
    (j : Jᵒᵖ) (x : X.obj j) :
    (sourceFormula T P Q a).obj j x ↔ a.eval (T.obj j) (P.obj j) (Q.obj j) x := by
  induction a with
  | p | q | parameter | top | bottom => rfl
  | and a b ha hb => exact and_congr ha hb
  | or a b ha hb => exact or_congr ha hb

theorem source_satisfaction (T P Q : Subfunctor X) :
    (∀ i, sourceFormula T P Q (FiniteSetting.axioms i).premise ≤
      sourceFormula T P Q (FiniteSetting.axioms i).conclusion) ↔
    ∀ j, FiniteSetting.Satisfies (stage T j) (P.obj j) (Q.obj j) := by
  constructor
  · intro h j i x hx
    exact (source_evaluation _ _ _ _ j x).mp
      (h i j ((source_evaluation _ _ _ _ j x).mpr hx))
  · intro h i j x hx
    exact (source_evaluation _ _ _ _ j x).mpr
      (h j i x ((source_evaluation _ _ _ _ j x).mp hx))

/-- Same three source sequents at each stage, with subpresheaf predicates. -/
structure Model (T : Presentation X) where
  P : Subfunctor X
  Q : Subfunctor X
  satisfies : ∀ j, FiniteSetting.Satisfies (stage T j) (P.obj j) (Q.obj j)

def Model.stage {T : Presentation X} (M : Model T) (j : Jᵒᵖ) :
    FiniteSetting.Model (stage T j) := ⟨M.P.obj j, M.Q.obj j, M.satisfies j⟩

@[ext] theorem Model.ext {T : Presentation X} {M N : Model T}
    (h : ∀ j, M.stage j = N.stage j) : M = N := by
  have hp : M.P = N.P := by ext j x; exact iff_of_eq (congrFun (congrArg FiniteSetting.Model.P (h j)) x)
  have hq : M.Q = N.Q := by ext j x; exact iff_of_eq (congrFun (congrArg FiniteSetting.Model.Q (h j)) x)
  cases M; cases N; cases hp; cases hq; rfl

structure Section (T : Presentation X) where
  val : ∀ j, FiniteSetting.Section (stage T j)
  natural : ∀ {j k} (f : j ⟶ k) x, restrict T f x (val j x) = val k (X.map f x)

@[ext] theorem Section.ext {T : Presentation X} {s t : Section T}
    (h : ∀ j, s.val j = t.val j) : s = t := by
  cases s; cases t; congr; funext j; exact h j

def Section.toModel {T : Presentation X} (s : Section T) : Model T where
  P := { obj j := (s.val j).toModel.P
         map f := by intro x h; change (s.val _ _).isLeft = true at *
                     rw [← s.natural f x, restrict_left]; exact h }
  Q := { obj j := (s.val j).toModel.Q
         map f := by intro x h; change (s.val _ _).isRight = true at *
                     rw [← s.natural f x, restrict_right]; exact h }
  satisfies j := (s.val j).toModel.satisfies

/-- Both predicates being stable prevents a section from changing summands. -/
noncomputable def Model.toSection {T : Presentation X} (M : Model T) : Section T where
  val j := (M.stage j).toSection
  natural {j k} f x := by
    classical
    apply fiber_ext
    simp only [restrict_left]
    have hi := congrArg FiniteSetting.Model.P ((M.stage j).toSection_toModel)
    have hk := congrArg FiniteSetting.Model.P ((M.stage k).toSection_toModel)
    change ((M.stage j).toSection x).isLeft = ((M.stage k).toSection (X.map f x)).isLeft
    apply Bool.eq_iff_iff.mpr
    change (M.stage j).toSection.toModel.P x ↔ (M.stage k).toSection.toModel.P (X.map f x)
    rw [hi, hk]
    constructor
    · intro hx; exact M.P.map f hx
    · intro hp
      rcases (FiniteSetting.satisfies_iff _ _ _).mp (M.satisfies j) with ⟨hc, _, _⟩
      rcases hc x with hx | hx
      · exact hx
      · exact False.elim (((FiniteSetting.satisfies_iff _ _ _).mp (M.satisfies k)).2.1 _
          ⟨hp, M.Q.map f hx⟩)

noncomputable def modelSectionEquiv (T : Presentation X) : Model T ≃ Section T where
  toFun := Model.toSection
  invFun := Section.toModel
  left_inv M := by apply Model.ext; intro j; exact (M.stage j).toSection_toModel
  right_inv s := by apply Section.ext; intro j; exact (s.val j).toModel_toSection

/-- Equality of total points retains the base and the summand. -/
theorem total_ext {T : FiniteSetting.Presentation α} {a b : FiniteSetting.Total T}
    (h : a.1 = b.1) (ht : a.2.isLeft = b.2.isLeft) : a = b := by
  rcases a with ⟨x, a⟩; rcases b with ⟨y, b⟩
  dsimp at h; cases h
  exact Sigma.ext rfl (heq_of_eq (fiber_ext ht))

/-- The formed object is an actual presheaf, retaining the base point. -/
def total (T : Presentation X) : Jᵒᵖ ⥤ Type where
  obj j := FiniteSetting.Total (stage T j)
  map f := ↾fun a => ⟨X.map f a.1, restrict T f a.1 a.2⟩
  map_id j := by
    apply ConcreteCategory.hom_ext
    intro a
    apply total_ext
    · exact ConcreteCategory.congr_hom (X.map_id j) a.1
    · exact restrict_left T _ _ _
  map_comp f g := by
    apply ConcreteCategory.hom_ext
    intro a
    apply total_ext
    · exact ConcreteCategory.congr_hom (X.map_comp f g) a.1
    · change (restrict T (f ≫ g) _ _).isLeft = (restrict T g _ (restrict T f _ _)).isLeft
      simp

def projection (T : Presentation X) : total T ⟶ X where
  app _ := ↾Sigma.fst

def Section.graph {T : Presentation X} (s : Section T) : X ⟶ total T where
  app j := ↾fun x => ⟨x, s.val j x⟩
  naturality j k f := by ext x; exact Sigma.ext rfl (heq_of_eq (s.natural f x).symm)

def subst (T : Presentation X) (σ : Y ⟶ X) : Presentation Y := T.preimage σ

def Model.subst {T : Presentation X} (M : Model T) (σ : Y ⟶ X) : Model (subst T σ) where
  P := M.P.preimage σ
  Q := M.Q.preimage σ
  satisfies j := ((M.stage j).subst (σ.app j)).satisfies

def Section.subst {T : Presentation X} (s : Section T) (σ : Y ⟶ X) : Section (subst T σ) where
  val j := (s.val j).subst (σ.app j)
  natural {j k} f y := by
    apply fiber_ext
    exact (restrict_left (PresheafSetting.subst T σ) f y _).trans
      ((restrict_left T f (σ.app j y) _).symm.trans
        ((congrArg Sum.isLeft (s.natural f (σ.app j y))).trans
          (congrArg (fun x => (s.val k x).isLeft) (NatTrans.naturality_apply σ f y).symm)))

@[simp] theorem correspondence_subst {T : Presentation X} (M : Model T) (σ : Y ⟶ X) :
    modelSectionEquiv (subst T σ) (M.subst σ) = (modelSectionEquiv T M).subst σ := by
  apply Section.ext; intro j; exact (M.stage j).toSection_subst (σ.app j)

@[simp] theorem section_model_subst {T : Presentation X} (s : Section T) (σ : Y ⟶ X) :
    (s.subst σ).toModel = s.toModel.subst σ := by apply Model.ext; intro j; rfl


@[simp] theorem subst_id (T : Presentation X) : subst T (𝟙 X) = T := rfl
@[simp] theorem subst_comp (T : Presentation X) (σ : Y ⟶ X) (τ : Z ⟶ Y) :
    subst (subst T σ) τ = subst T (τ ≫ σ) := rfl
@[simp] theorem Model.subst_id {T : Presentation X} (M : Model T) : M.subst (𝟙 X) = M := rfl
@[simp] theorem Model.subst_comp {T : Presentation X} (M : Model T)
    (σ : Y ⟶ X) (τ : Z ⟶ Y) : (M.subst σ).subst τ = M.subst (τ ≫ σ) := rfl
@[simp] theorem Section.subst_id {T : Presentation X} (s : Section T) : s.subst (𝟙 X) = s := rfl
@[simp] theorem Section.subst_comp {T : Presentation X} (s : Section T)
    (σ : Y ⟶ X) (τ : Z ⟶ Y) : (s.subst σ).subst τ = s.subst (τ ≫ σ) := rfl

def totalMap (T : Presentation X) (σ : Y ⟶ X) : total (subst T σ) ⟶ total T where
  app j := ↾FiniteSetting.totalMap (stage T j) (σ.app j)
  naturality j k f := by
    ext a
    apply total_ext
    · exact NatTrans.naturality_apply σ f a.1
    · change (restrict (subst T σ) f a.1 a.2).isLeft = (restrict T f _ a.2).isLeft
      exact (restrict_left _ _ _ _).trans (restrict_left T f _ _).symm

theorem totalMap_projection (T : Presentation X) (σ : Y ⟶ X) :
    totalMap T σ ≫ projection T = projection (subst T σ) ≫ σ := rfl

theorem totalMap_id (T : Presentation X) : totalMap T (𝟙 X) = 𝟙 (total T) := rfl

theorem totalMap_comp (T : Presentation X) (σ : Y ⟶ X) (τ : Z ⟶ Y) :
    totalMap (subst T σ) τ ≫ totalMap T σ = totalMap T (τ ≫ σ) := rfl

def genericSection (T : Presentation X) : Section (subst T (projection T)) where
  val j := FiniteSetting.genericSection (stage T j)
  natural f a := by
    apply fiber_ext
    exact (restrict_left _ _ _ _).trans (restrict_left T f _ _).symm

theorem Section.graph_projection {T : Presentation X} (s : Section T) :
    s.graph ≫ projection T = 𝟙 X := rfl

theorem genericSection_recovery {T : Presentation X} (s : Section T) :
    (genericSection T).subst s.graph = s := rfl

def genericModel (T : Presentation X) : Model (subst T (projection T)) :=
  (genericSection T).toModel

theorem genericSection_subst (T : Presentation X) (σ : Y ⟶ X) :
    (genericSection T).subst (totalMap T σ) = genericSection (subst T σ) := rfl

theorem genericModel_subst (T : Presentation X) (σ : Y ⟶ X) :
    (genericModel T).subst (totalMap T σ) = genericModel (subst T σ) := rfl

theorem genericModel_recovery {T : Presentation X} (M : Model T) :
    (genericModel T).subst M.toSection.graph = M := by
  apply Model.ext; intro j; exact (M.stage j).toSection_toModel

/-- Chosen pullback, using the existing equality-bearing Set pullbacks at stages.
Restriction is transported through their equivalence; `pullback_original_map`
below proves it is the restriction on the original total family. -/
def pullback (T : Presentation X) (σ : Y ⟶ X) : Jᵒᵖ ⥤ Type where
  obj j := FiniteSetting.Pullback (stage T j) (σ.app j)
  map {j k} f := ↾fun a => (FiniteSetting.pullbackEquiv (stage T k) (σ.app k)).symm
    ((total (subst T σ)).map f (FiniteSetting.pullbackEquiv (stage T j) (σ.app j) a))
  map_id j := by
    apply ConcreteCategory.hom_ext; intro a
    change _ = a
    rw [(total (subst T σ)).map_id]
    exact (FiniteSetting.pullbackEquiv (stage T j) (σ.app j)).symm_apply_apply a
  map_comp {j k l} f g := by
    apply ConcreteCategory.hom_ext; intro a
    change _ = (FiniteSetting.pullbackEquiv (stage T l) (σ.app l)).symm
      ((total (subst T σ)).map g ((FiniteSetting.pullbackEquiv (stage T k) (σ.app k))
        ((FiniteSetting.pullbackEquiv (stage T k) (σ.app k)).symm _)))
    rw [Equiv.apply_symm_apply, (total (subst T σ)).map_comp]
    rfl

/-- Formation/substitution comparison is a natural isomorphism. -/
def comparison (T : Presentation X) (σ : Y ⟶ X) : pullback T σ ≅ total (subst T σ) where
  hom := { app j := ↾FiniteSetting.pullbackEquiv (stage T j) (σ.app j)
           naturality j k f := by ext a; exact Equiv.apply_symm_apply _ _ }
  inv := { app j := ↾(FiniteSetting.pullbackEquiv (stage T j) (σ.app j)).symm
           naturality j k f := by ext a; dsimp [pullback]; rw [Equiv.apply_symm_apply] }
  hom_inv_id := by ext j a; exact Equiv.symm_apply_apply _ a
  inv_hom_id := by ext j a; exact Equiv.apply_symm_apply _ a

def pullbackProjection (T : Presentation X) (σ : Y ⟶ X) : pullback T σ ⟶ Y :=
  (comparison T σ).hom ≫ projection (subst T σ)

def pullbackOriginal (T : Presentation X) (σ : Y ⟶ X) : pullback T σ ⟶ total T :=
  (comparison T σ).hom ≫ totalMap T σ

@[simp] theorem pullback_projection (T : Presentation X) (σ : Y ⟶ X) (j : Jᵒᵖ)
    (a : (pullback T σ).obj j) : (pullbackProjection T σ).app j a = a.base := rfl

@[simp] theorem pullback_original (T : Presentation X) (σ : Y ⟶ X) (j : Jᵒᵖ)
    (a : (pullback T σ).obj j) : (pullbackOriginal T σ).app j a = a.original :=
  FiniteSetting.pullback_original (stage T j) (σ.app j) a

theorem pullback_original_map (T : Presentation X) (σ : Y ⟶ X) {j k : Jᵒᵖ}
    (f : j ⟶ k) (a : (pullback T σ).obj j) :
    ((pullback T σ).map f a).original = (total T).map f a.original := by
  simpa only [pullback_original] using NatTrans.naturality_apply (pullbackOriginal T σ) f a

theorem pullback_square (T : Presentation X) (σ : Y ⟶ X) :
    pullbackOriginal T σ ≫ projection T = pullbackProjection T σ ≫ σ := rfl

def pullbackGeneric (T : Presentation X) (σ : Y ⟶ X) :
    Model (subst (subst T σ) (pullbackProjection T σ)) :=
  (genericModel (subst T σ)).subst (comparison T σ).hom

/-- The generic dependent section is retained on the pullback. -/
def pullbackGenericSection (T : Presentation X) (σ : Y ⟶ X) :
    Section (subst (subst T σ) (pullbackProjection T σ)) :=
  (genericSection (subst T σ)).subst (comparison T σ).hom

theorem pullback_generic_section_stage (T : Presentation X) (σ : Y ⟶ X)
    (j : Jᵒᵖ) (a : (pullback T σ).obj j) :
    (pullbackGenericSection T σ).val j a =
      (show FiniteSetting.Fiber (stage T j) (σ.app j a.base) from a.over ▸ a.original.2) := rfl

theorem pullback_partition (T : Presentation X) (σ : Y ⟶ X) (j : Jᵒᵖ)
    (a : (pullback T σ).obj j) :
    ((pullbackGeneric T σ).P.obj j a ↔ (genericModel T).P.obj j a.original) ∧
    ((pullbackGeneric T σ).Q.obj j a ↔ (genericModel T).Q.obj j a.original) :=
  FiniteSetting.pullback_partition (stage T j) (σ.app j) a

/-- Every model's section is natural on the pullback as well. -/
def pullbackSection {T : Presentation X} (s : Section T) (σ : Y ⟶ X) : Y ⟶ pullback T σ :=
  (s.subst σ).graph ≫ (comparison T σ).inv

theorem pullback_correspondence {T : Presentation X} (M : Model T) (σ : Y ⟶ X) :
    pullbackSection (modelSectionEquiv T M) σ ≫ (comparison T σ).hom =
      (modelSectionEquiv (subst T σ) (M.subst σ)).graph := by
  rw [correspondence_subst]; simp [pullbackSection]

theorem pullback_model_recovery {T : Presentation X} (M : Model T) (σ : Y ⟶ X) :
    (pullbackGeneric T σ).subst (pullbackSection M.toSection σ) = M.subst σ := by
  apply Model.ext; intro j
  exact FiniteSetting.pullback_model_recovery (M.stage j) (σ.app j)

theorem comparison_identity (T : Presentation X) :
    (comparison T (𝟙 X)).hom = pullbackOriginal T (𝟙 X) := rfl

/-- Rebase the pullback naturally; the stage theorem identifies the equality certificate. -/
def pullbackRebase (T : Presentation X) (σ : Y ⟶ X) (τ : Z ⟶ Y) :
    pullback (subst T σ) τ ⟶ pullback T (τ ≫ σ) :=
  (comparison (subst T σ) τ).hom ≫ (comparison T (τ ≫ σ)).inv

theorem pullback_rebase_stage (T : Presentation X) (σ : Y ⟶ X) (τ : Z ⟶ Y)
    (j : Jᵒᵖ) (a : (pullback (subst T σ) τ).obj j) :
    (pullbackRebase T σ τ).app j a =
      FiniteSetting.pullbackRebase (stage T j) (σ.app j) (τ.app j) a := by
  apply (FiniteSetting.pullbackEquiv (stage T j) ((τ ≫ σ).app j)).injective
  change (FiniteSetting.pullbackEquiv _ _) ((FiniteSetting.pullbackEquiv _ _).symm _) = _
  rw [Equiv.apply_symm_apply]
  exact (FiniteSetting.pullback_composition (stage T j) (σ.app j) (τ.app j) a).symm

theorem comparison_composition (T : Presentation X) (σ : Y ⟶ X) (τ : Z ⟶ Y) :
    pullbackRebase T σ τ ≫ (comparison T (τ ≫ σ)).hom =
      (comparison (subst T σ) τ).hom := by simp [pullbackRebase]

theorem generic_composition (T : Presentation X) (σ : Y ⟶ X) (τ : Z ⟶ Y) :
    (pullbackGeneric T (τ ≫ σ)).subst (pullbackRebase T σ τ) =
      pullbackGeneric (subst T σ) τ := by
  apply Model.ext; intro j
  apply FiniteSetting.Model.ext <;> funext a
  · change (FiniteSetting.pullbackModel _ _).P ((pullbackRebase T σ τ).app j a) = _
    rw [pullback_rebase_stage]
    exact congrFun (congrArg FiniteSetting.Model.P
      (FiniteSetting.pullback_model_composition (stage T j) (σ.app j) (τ.app j))) a
  · change (FiniteSetting.pullbackModel _ _).Q ((pullbackRebase T σ τ).app j a) = _
    rw [pullback_rebase_stage]
    exact congrFun (congrArg FiniteSetting.Model.Q
      (FiniteSetting.pullback_model_composition (stage T j) (σ.app j) (τ.app j))) a


/-- Generic membership observed in a constant Boolean presheaf. -/
def tag (T : Presentation X) : total T ⟶ (Functor.const Jᵒᵖ).obj Bool where
  app _ := ↾fun a => a.2.isLeft
  naturality j k f := by ext a; exact restrict_left T f a.1 a.2

def pulledTag (T : Presentation X) (σ : Y ⟶ X) :
    pullback T σ ⟶ (Functor.const Jᵒᵖ).obj Bool := pullbackOriginal T σ ≫ tag T

theorem tag_comparison (T : Presentation X) (σ : Y ⟶ X) :
    (comparison T σ).inv ≫ pulledTag T σ = tag (subst T σ) := rfl

/-- Equality is a subfunctor equalizer, conjunction intersection, and existence
an objectwise image, exactly as in `Presheaf.Model.formula`. Both routes use
`Graph.forward` and `Graph.backward` through the existing presheaf soundness. -/
theorem formed_graph (T : Presentation X) (σ : Y ⟶ X) :
    (Presheaf.graphModel (𝟙 (total (subst T σ))) (tag (subst T σ))).formula
      (Graph.composite .first .second) =
    (Presheaf.graphModel (𝟙 (total (subst T σ))) (tag (subst T σ))).formula
      (Graph.result .first .second) := Presheaf.graph_valid _ _

theorem pulled_graph (T : Presentation X) (σ : Y ⟶ X) :
    (Presheaf.graphModel (comparison T σ).inv (pulledTag T σ)).formula
      (Graph.composite .first .second) =
    (Presheaf.graphModel (comparison T σ).inv (pulledTag T σ)).formula
      (Graph.result .first .second) := Presheaf.graph_valid _ _

/-- Stage evaluation agrees with #121, now with natural arrows and predicates. -/
theorem graph_routes (T : Presentation X) (σ : Y ⟶ X) (j : Jᵒᵖ)
    (a : (total (subst T σ)).obj j) (b : Bool) :
    ((∃ p : (pullback T σ).obj j, p = (comparison T σ).inv.app j a ∧
      b = p.original.2.isLeft) ↔ b = a.2.isLeft) ∧
    ((∃ c : (total (subst T σ)).obj j, c = a ∧ b = c.2.isLeft) ↔ b = a.2.isLeft) := by
  constructor
  · have h := Presheaf.graph_evaluation (comparison T σ).inv (pulledTag T σ) j a b
    have ho : ∀ p : (pullback T σ).obj j,
        (pulledTag T σ).app j p = p.original.2.isLeft := by
      intro p
      exact congrArg (fun a => a.2.isLeft) (pullback_original T σ j p)
    simp only [ho] at h
    exact h
  · exact Presheaf.graph_evaluation (𝟙 (total (subst T σ))) (tag (subst T σ)) j a b

theorem graph_comparison (T : Presentation X) (σ : Y ⟶ X) (j : Jᵒᵖ)
    (a : (total (subst T σ)).obj j) (b : Bool) :
    (∃ p : (pullback T σ).obj j, p = (comparison T σ).inv.app j a ∧
      b = p.original.2.isLeft) ↔
    (∃ c : (total (subst T σ)).obj j, c = a ∧ b = c.2.isLeft) :=
  (graph_routes T σ j a b).1.trans (graph_routes T σ j a b).2.symm

theorem graph_generic (T : Presentation X) (σ : Y ⟶ X) (j : Jᵒᵖ)
    (a : (total (subst T σ)).obj j) :
    (∃ p : (pullback T σ).obj j, p = (comparison T σ).inv.app j a ∧
      true = p.original.2.isLeft) ↔ (genericModel (subst T σ)).P.obj j a :=
  (graph_routes T σ j a true).1.trans eq_comm

/-- Binder-sensitive source substitution remains the presheaf preimage law. -/
theorem graph_substitution (T : Presentation X) (σ : Y ⟶ X)
    (θ : Sub Graph.Arrow [.input, .output] Δ) :
    (Presheaf.graphModel (comparison T σ).inv (pulledTag T σ)).formula
      ((Graph.composite .first .second).subst θ) =
    ((Presheaf.graphModel (comparison T σ).inv (pulledTag T σ)).formula
      (Graph.composite .first .second)).preimage
      ((Presheaf.graphModel (comparison T σ).inv (pulledTag T σ)).substitution θ) :=
  Presheaf.Model.formula_substitution _ _ θ

end SquareKit.Internal.PresheafSetting
