import SquareKit.EquationComposition
import Applications.Languages.IndexedCompositional
import Applications.Languages.Transposition

/-! The union/scalar fragment has binding-free output equations and constant
finite successor templates. Selected decisions survive both presentations and
arbitrary finite mixtures. Native parser and trie APIs remain independent. -/
namespace LanguageWitnesses.EquationComposition
open SquareKit.IndexedCompositional
open SquareKit.EquationTranspose (Expr DataProgram)
open SquareKit.EquationComposition (compile compileRows)
variable {α : Type}

inductive Op (α : Type) : IndexedCompositional.Index α → Type 1
  | union (P Q : Language α) (n : Nat) : Op α (fun w => P w ⊕ Q w,n)
  | scale (P : Language α) (n : Nat) {A : Type} (d : Decision A) : Op α (fun w => A × P w,n)

abbrev signature : Signature (IndexedCompositional.Index α) where
  Op := Op α
  arity | .union _ _ _ => 2 | .scale _ _ _ => 1
  child | .union P Q n, k => (Fin.cases P (fun _ => Q) k,n)
        | .scale P n _, _ => (P,n)

abbrev behavior := IndexedCompositional.behavior (α := α)
abbrev Source := IndexedCompositional.Source (α := α)
abbrev Target := IndexedCompositional.Target (α := α)

inductive Prim : Type 1 → Type 1 → Type 2
  | literal {A : Type 1} (value : A) : Prim PUnit A
  | child {j} (op : Op α j) (k : Fin (signature.arity op)) :
      Prim (ULift.{1} (SquareKit.EquationComposition.Outputs signature behavior op))
        (ULift.{1} (behavior.Output (signature.child op k)))
  | sum {A B : Type} : Prim (ULift.{1} (Decision A) × ULift.{1} (Decision B))
      (ULift.{1} (Decision (A ⊕ B)))
  | prod {A B : Type} : Prim (ULift.{1} (Decision A) × ULift.{1} (Decision B))
      (ULift.{1} (Decision (A × B)))

def meaning : Prim (α := α) A B → A → B
  | .literal value, _ => value
  | .child _ k, xs => ⟨xs.down k⟩
  | .sum, (x,y) => ⟨x.down.sum y.down⟩
  | .prod, (x,y) => ⟨x.down.prod y.down⟩

def equations : DataProgram (SquareKit.EquationComposition.signature (signature (α := α)) behavior)
    (Prim (α := α)) where
  body p obs _ := match obs with
    | .output => match p with
      | ⟨_, .union P Q n⟩ => .prim .sum (.pair
          (.prim (.child (.union P Q n) 0) (.var .first))
          (.prim (.child (.union P Q n) 1) (.var .first)))
      | ⟨_, .scale P n d⟩ => .prim .prod (.pair
          (.prim (.literal ⟨d⟩) (.var .second))
          (.prim (.child (.scale P n d) 0) (.var .first)))
    | .next a => match p with
      | ⟨_, .union _ _ 0⟩ => nomatch a
      | ⟨_, .union P Q (n+1)⟩ =>
          .prim (.literal ⟨.node (.union (derivative P a) (derivative Q a) n)
            (fun k => Fin.cases
              (.leaf (by
                exact @Slot.succ (IndexedCompositional.Index α) signature behavior _
                  (Op.union P Q (n+1)) ⟨0, by exact Nat.zero_lt_succ 1⟩ a))
              (fun _ => .leaf (by
                exact @Slot.succ (IndexedCompositional.Index α) signature behavior _
                  (Op.union P Q (n+1)) ⟨1, by exact Nat.lt_succ_self 1⟩ a)) k)⟩) (.var .second)
      | ⟨_, .scale _ 0 _⟩ => nomatch a
      | ⟨_, .scale P (n+1) d⟩ =>
          .prim (.literal ⟨.node (.scale (derivative P a) n d)
            (fun _ => .leaf (Slot.succ (S := signature) (B := behavior) (op := Op.scale P (n+1) d) 0 a))⟩) (.var .second)

def rule : Rule signature (behavior (α := α)) := compile equations meaning

def sourceAlgebra : {j : IndexedCompositional.Index α} → (op : signature.Op j) →
    (∀ k, Source (signature.child op k)) → Source j
  | _, .union _ _ _, xs => .union (xs 0) (xs 1)
  | _, .scale _ _ d, xs => .scale d (xs 0)

def targetAlgebra : {j : IndexedCompositional.Index α} → (op : signature.Op j) →
    (∀ k, Target (signature.child op k)) → Target j
  | _, .union _ _ _, xs => WitnessTrie.union (xs 0) (xs 1)
  | _, .scale _ _ d, xs => WitnessTrie.scale d (xs 0)

theorem sourceCompatible [DecidableEq α] :
    (rule (α := α)).Compatible sourceAlgebra IndexedCompositional.source where
  output j op xs := by
    cases op with
    | union P Q n => cases n <;> rfl
    | scale P n d => cases n <;> rfl
  next j op xs a := by
    cases op with
    | union P Q n => cases n with
      | zero => exact nomatch a
      | succ n => rfl
    | scale P n d => cases n with
      | zero => exact nomatch a
      | succ n => rfl

theorem targetCompatible :
    (rule (α := α)).Compatible targetAlgebra IndexedCompositional.target where
  output j op xs := by
    cases op with
    | union P Q n =>
      change (IndexedCompositional.target (fun w => P w ⊕ Q w,n) (WitnessTrie.union (xs 0) (xs 1))).1 =
        ((IndexedCompositional.target _ (xs 0)).1).sum ((IndexedCompositional.target _ (xs 1)).1)
      cases n <;> cases xs 0 <;> cases xs 1 <;> rfl
    | scale P n d =>
      change (IndexedCompositional.target (_,n) (WitnessTrie.scale d (xs 0))).1 =
        d.prod ((IndexedCompositional.target _ (xs 0)).1)
      cases n <;> cases xs 0 <;> rfl
  next j op xs a := by
    cases op with
    | union P Q n => cases n with
      | zero => exact nomatch a
      | succ n =>
        change (IndexedCompositional.target _ (WitnessTrie.union (xs 0) (xs 1))).2 a =
          WitnessTrie.union ((IndexedCompositional.target _ (xs 0)).2 a)
            ((IndexedCompositional.target _ (xs 1)).2 a)
        cases xs 0; cases xs 1; rfl
    | scale P n d => cases n with
      | zero => exact nomatch a
      | succ n =>
        change (IndexedCompositional.target _ (WitnessTrie.scale d (xs 0))).2 a =
          WitnessTrie.scale d ((IndexedCompositional.target _ (xs 0)).2 a)
        cases xs 0; rfl

/-- An existing source equation cell is recovered, including left-selected witnesses. -/
theorem original_union_output [DecidableEq α] {P Q : Language α}
    (p : Parser P) (q : Parser Q) (n : Nat) :
    rule.out (.union P Q n) (fun k => Fin.cases p.nullable (fun _ => q.nullable) k) =
      (Transposition.equations.observe Transposition.meaning .nullable
        ⟨.union P Q,(p,q)⟩ PUnit.unit).down := rfl

/-- Successor requests agree with the source derive cell after interpreting slots. -/
theorem original_union_next [DecidableEq α] {P Q : Language α}
    (n : Nat) (a : α)
    (xs : ∀ k, Source (signature.child (Op.union P Q (n+1)) k)) :
    Term.fold sourceAlgebra
      (Rule.slots (S := signature) (B := behavior) (.union P Q (n+1)) xs
        (fun k b => (IndexedCompositional.source _ (xs k)).2 b))
      (rule.step (.union P Q (n+1)) (fun k => (IndexedCompositional.source _ (xs k)).1) a) =
      Transposition.equations.observe Transposition.meaning (.derive a)
        ⟨.union P Q,(xs 0,xs 1)⟩ PUnit.unit := rfl

theorem original_scale_output [DecidableEq α] {P : Language α} {A : Type}
    (p : Parser P) (d : Decision A) (n : Nat) :
    rule.out (.scale P n d) (fun _ => p.nullable) =
      (Transposition.equations.observe Transposition.meaning .nullable
        ⟨.scale A P,(⟨d⟩,p)⟩ PUnit.unit).down := rfl

theorem original_scale_next [DecidableEq α] {P : Language α} {A : Type}
    (n : Nat) (a : α) (d : Decision A)
    (xs : ∀ k, Source (signature.child (Op.scale P (n+1) d) k)) :
    Term.fold sourceAlgebra
      (Rule.slots (S := signature) (B := behavior) (.scale P (n+1) d) xs
        (fun k b => (IndexedCompositional.source _ (xs k)).2 b))
      (rule.step (.scale P (n+1) d) (fun k => (IndexedCompositional.source _ (xs k)).1) a) =
      Transposition.equations.observe Transposition.meaning (.derive a)
        ⟨.scale A P,(⟨d⟩,xs 0)⟩ PUnit.unit := rfl

/-- No desired composite equality is assumed: both folds use the shared theorem. -/
theorem recovered [DecidableEq α] {P : Language α} {n}
    (t : Term signature Source (P,n)) (word : List α) (bound : word.length ≤ n) :
    (Term.fold targetAlgebra IndexedCompositional.unfold t).lookup word bound =
      (Term.fold sourceAlgebra (fun _ x => x) t).parse word := by
  have ht := (rule (α := α)).fold_morphism targetAlgebra IndexedCompositional.target
    targetCompatible IndexedCompositional.source IndexedCompositional.unfold
    IndexedCompositional.unfold_morphism
  have hs := (rule (α := α)).fold_morphism sourceAlgebra IndexedCompositional.source
    sourceCompatible IndexedCompositional.source (fun _ x => x)
    ⟨fun _ _ => rfl, fun _ _ _ => rfl⟩
  rw [← IndexedCompositional.read_target, IndexedCompositional.read_morphism _ _ _ ht]
  rw [← IndexedCompositional.read_morphism _ _ _ hs, IndexedCompositional.read_source]

end LanguageWitnesses.EquationComposition
