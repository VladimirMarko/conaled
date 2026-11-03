import SquareKit.Internal.PresheafGraphs
import Examples.InternalGraphs
import Examples.InternalRelations

/-! A two-stage presheaf with a restriction that forgets a coordinate.
The graph pipeline increments then doubles; its witness (4,5) restricts to 4.
A binary relation compares visible coordinates and permits distinct sections.
Ordinary graph/relation clients remain imported unchanged beside this adapter.
-/
namespace Examples.PresheafInternal
open CategoryTheory Opposite SquareKit.Internal SquareKit.Internal.Presheaf

inductive Stage where | coarse | fine
inductive Step : Stage → Stage → Type where
  | ident (i) : Step i i
  | refine : Step .coarse .fine

def Step.comp : Step a b → Step b c → Step a c
  | .ident _, g => g
  | .refine, .ident _ => .refine

instance : SmallCategory Stage where
  Hom := Step
  id := Step.ident
  comp := Step.comp
  id_comp := by intros; cases ‹Step _ _› <;> rfl
  comp_id := by intros; cases ‹Step _ _› <;> rfl
  assoc := by intros a b c d f g h; cases f <;> cases g <;> cases h <;> rfl

abbrev sections : Stage → Type
  | .coarse => Nat
  | .fine => Nat × Nat

def restrictStep : Step a b → sections b → sections a
  | .ident _, x => x
  | .refine, x => x.1

abbrev data : Stageᵒᵖ ⥤ Type where
  obj j := sections j.unop
  map f := ↾restrictStep f.unop
  map_id _ := rfl
  map_comp f g := by
    apply ConcreteCategory.hom_ext
    intro x
    exact (show ∀ {a b c} (f : Step a b) (g : Step b c) (x : sections c),
      restrictStep (f.comp g) x = restrictStep f (restrictStep g x) from
      by intros a b c f g x; cases f <;> cases g <;> rfl) g.unop f.unop x

def actSection (h : Nat → Nat) : (i : Stage) → sections i → sections i
  | .coarse, x => h x
  | .fine, x => (h x.1, h x.2)

def act (h : Nat → Nat) : data ⟶ data where
  app j := ↾actSection h j.unop
  naturality j k f := by
    apply ConcreteCategory.hom_ext
    intro x
    exact (show ∀ {a b} (f : Step a b) (x : sections b),
      actSection h a (restrictStep f x) = restrictStep f (actSection h b x) from
      by intros a b f x; cases f <;> rfl) f.unop x

def inc := act (fun n => n + 1)
def double := act (fun n => n * 2)
def drop : op Stage.fine ⟶ op Stage.coarse := Quiver.Hom.op (show Stage.coarse ⟶ Stage.fine from Step.refine)

theorem distinct_sections : (3, 4) ≠ (3, 5) ∧
    data.map drop (3, 4) = data.map drop (3, 5) := by
  constructor
  · decide
  · rfl

/-- The witness computed before restriction agrees with the coarse witness. -/
theorem restricted_witness : data.map drop (inc.app (op .fine) (3, 4)) =
    inc.app (op .coarse) (data.map drop (3, 4)) :=
  (show inc.app (op .coarse) (data.map drop (3, 4)) =
    data.map drop (inc.app (op .fine) (3, 4)) from
      NatTrans.naturality_apply inc drop (show data.obj (op .fine) from (3, 4))).symm

theorem fine_graph : (∃ b, b = inc.app (op .fine) (3, 4) ∧
    (8, 10) = double.app (op .fine) b) :=
  (graph_evaluation inc double (op .fine) (3, 4) (8, 10)).mpr rfl

theorem coarse_graph : (∃ b, b = inc.app (op .coarse) 3 ∧
    8 = double.app (op .coarse) b) :=
  (graph_evaluation inc double (op .coarse) 3 8).mpr rfl

/-- Restrict the interpreted existential itself, not independent Set proofs. -/
theorem restricted_graph :
    ((graphModel inc double).formula (Graph.composite .first .second)).obj (op .coarse)
      ((graphModel inc double).restrict drop (graphEnv inc double (op .fine) (3, 4) (8, 10))) :=
  (graphModel inc double).formula_restrict _ drop _
    (((graphModel inc double).evaluation _ _ _).mpr fine_graph)

/-- Translation by two commutes with increment, then translation by four
commutes with doubling. Both surviving horizontal maps are nonidentity. -/
def firstSquare : NaturalSquare inc inc where
  impl := act (fun n => n + 2)
  spec := act (fun n => n + 2)
  commutes := by
    ext j x
    rcases j with ⟨j⟩
    cases j <;> rfl

def secondSquare : NaturalSquare double double where
  impl := act (fun n => n + 2)
  spec := act (fun n => n + 4)
  commutes := by
    ext j x
    rcases j with ⟨j⟩
    cases j <;> dsimp [double, act, actSection] <;> simp [Nat.add_mul]

/-- The public square comparison at each end of the restriction arrow. -/
example := vertical_evaluation firstSquare secondSquare (fun _ _ => rfl) (op .fine)
example := vertical_evaluation firstSquare secondSquare (fun _ _ => rfl) (op .coarse)

def visibleSection : (i : Stage) → sections i → Nat
  | .coarse, x => x
  | .fine, x => x.1

def visible (j : Stageᵒᵖ) : data.obj j → Nat := visibleSection j.unop

def visibleOrder : Subfunctor (Presheaf.product data data) where
  obj j xy := visible j xy.1 ≤ visible j xy.2
  map f := by
    intro xy h
    have stable : ∀ {a b} (f : Step a b) (x : sections b),
        visibleSection a (restrictStep f x) = visibleSection b x := by
      intros a b f x; cases f <;> rfl
    change visibleSection _ (restrictStep f.unop xy.1) ≤
      visibleSection _ (restrictStep f.unop xy.2)
    simpa only [stable] using (show visibleSection _ xy.1 ≤ visibleSection _ xy.2 from h)

inductive ValueSort where | value
inductive Relation : ValueSort → ValueSort → Type where | le : Relation .value .value
abbrev FunctionSymbol (_ _ : ValueSort) := PEmpty

def relationalModel : Model (J := Stage) FunctionSymbol Relation where
  carrier _ := data
  arrow f := nomatch f
  relation | .le => visibleOrder

def orderedPair : Formula FunctionSymbol [.value, .value] Relation :=
  .atom .le (.var .zero) (.var (.succ .zero))

def pairEnv (j : Stageᵒᵖ) (x y : data.obj j) :
    Env (relationalModel.fiber j) [.value, .value] :=
  Env.extend x (Env.extend y (fun {_} (i : Var [] _) => nomatch i))

theorem fine_order : (relationalModel.formula orderedPair).obj (op .fine)
    (pairEnv (op .fine) (3, 9) (4, 0)) :=
  (relationalModel.evaluation _ _ _).mpr (show 3 ≤ 4 from by decide)

theorem restricted_order : (relationalModel.formula orderedPair).obj (op .coarse)
    (relationalModel.restrict drop (pairEnv (op .fine) (3, 9) (4, 0))) :=
  relationalModel.formula_restrict _ drop _ fine_order

theorem order_rejects_reverse : ¬ (relationalModel.formula orderedPair).obj (op .fine)
    (pairEnv (op .fine) (5, 0) (4, 9)) := by
  intro h
  have := (relationalModel.evaluation _ _ _).mp h
  exact (by decide : ¬ 5 ≤ 4) this

/-- Projection image keeps a local witness with an invisible coordinate. -/
theorem ordered_witness :
    (relationalModel.formula (.ex orderedPair)).obj (op .fine)
      (Env.extend (4, 0) (fun {_} (i : Var [] _) => nomatch i)) :=
  (relationalModel.image_projection _ _ _).mpr ⟨(3, 9), fine_order⟩

example : (relationalModel.formula (.ex orderedPair)).obj (op .coarse)
    (relationalModel.restrict drop
      (Env.extend (4, 0) (fun {_} (i : Var [] _) => nomatch i))) :=
  relationalModel.formula_restrict _ drop _ ordered_witness

-- Swap is a nonidentity substitution; these checks exercise binder lifting
-- and Beck–Chevalley on the same relation predicate as the concrete case.
def swap : Sub FunctionSymbol [.value, .value] [.value, .value]
  | _, .zero => .var (.succ .zero)
  | _, .succ .zero => .var .zero

example : relationalModel.formula (orderedPair.subst swap) =
    (relationalModel.formula orderedPair).preimage (relationalModel.substitution swap) :=
  relationalModel.formula_substitution _ _

example (Q : Subfunctor (relationalModel.context [.value, .value, .value])) :
    (Q.image relationalModel.projection).preimage (relationalModel.substitution swap) =
      (Q.preimage (relationalModel.substitution swap.lift)).image relationalModel.projection :=
  relationalModel.beck_chevalley Q swap

example (Q : Subfunctor (relationalModel.context [.value, .value])) :
    (Q ⊓ (relationalModel.formula (.eq (.var .zero) (.var .zero))).preimage
      relationalModel.projection).image relationalModel.projection =
    Q.image relationalModel.projection ⊓ relationalModel.formula (.eq (.var .zero) (.var .zero)) :=
  relationalModel.frobenius _ _

-- The context laws also apply to the nonidentity swap, including under a
-- binder whose new variable must remain fixed.
example : relationalModel.substitution (fun i => (swap i).subst swap) =
    relationalModel.substitution swap ≫ relationalModel.substitution swap :=
  relationalModel.substitution_comp swap swap

example : relationalModel.substitution (Γ := [.value, .value]) (fun i => .var i) = 𝟙 _ :=
  relationalModel.substitution_id

example : relationalModel.term ((Term.var Var.zero).subst swap) =
    relationalModel.substitution swap ≫ relationalModel.term (.var .zero) :=
  relationalModel.term_substitution swap (.var .zero)

example : relationalModel.substitution (swap.lift (b := .value)) ≫ relationalModel.projection =
    relationalModel.projection ≫ relationalModel.substitution swap :=
  relationalModel.projection_substitution swap

example : relationalModel.equality ((Term.var Var.zero).subst swap)
    ((Term.var (Var.succ Var.zero)).subst swap) =
    (relationalModel.equality (.var .zero) (.var (.succ .zero))).preimage
      (relationalModel.substitution swap) :=
  relationalModel.equality_substitution _ _ swap

example : ((relationalModel.formula orderedPair) ⊓ relationalModel.formula (orderedPair.subst swap)).preimage
    (relationalModel.substitution swap) =
    (relationalModel.formula orderedPair).preimage (relationalModel.substitution swap) ⊓
    (relationalModel.formula (orderedPair.subst swap)).preimage (relationalModel.substitution swap) :=
  relationalModel.conjunction_substitution _ _ swap

example (Q : Subfunctor (relationalModel.context [.value, .value, .value])) :
    Q.image relationalModel.projection ≤ relationalModel.formula orderedPair ↔
      Q ≤ (relationalModel.formula orderedPair).preimage relationalModel.projection :=
  relationalModel.exists_adjunction Q _

example : (fun {t} (i : Var [ValueSort.value, .value] t) =>
    relationalModel.restrict drop (pairEnv (op .fine) (3, 9) (4, 0)) i) =
    (fun {t} (i : Var [ValueSort.value, .value] t) =>
      Env.extend (3 : Nat) (relationalModel.restrict drop
        (Env.extend (4, 0) (fun {_} (i : Var [] _) => nomatch i))) i) :=
  relationalModel.restrict_extend drop _ _

-- Retained-assumption elimination and derivation substitution use model
-- soundness directly; no model-specific induction is supplied by this client.
example (h : Formula FunctionSymbol [.value] Relation) :
    relationalModel.Valid (.conj h (.ex orderedPair)) h :=
  relationalModel.sound (Rules.existsElimWith Rules.andLeft)

example : relationalModel.Valid (orderedPair.subst swap) (orderedPair.subst swap) :=
  relationalModel.sound (Rules.substitute swap Rules.hypothesis)

example (j : Stageᵒᵖ) (ρ η : (relationalModel.context []).obj j) : @ρ = @η :=
  relationalModel.empty_context j ρ η

-- Ordinary direct calls coexist with the presheaf model in this module.
example (n : Nat) : (∃ m, m = n + 1 ∧ 2 * (n + 1) = 2 * m) :=
  (Graph.inSet (fun x => x + 1) (fun x => 2 * x) n _).mpr rfl

end Examples.PresheafInternal
