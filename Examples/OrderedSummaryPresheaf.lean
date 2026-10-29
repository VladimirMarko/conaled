import Examples.OrderedSummary
import Examples.PresheafInternal
import SquareKit.Internal.Associativity

/-! The unchanged existential reassociation derivations interpreted in Set and
in a nonconstant presheaf. Only conjunction/existence reasoning is transported;
list induction and cache construction remain ordinary local proofs. -/
namespace Examples.OrderedSummaryPresheaf
open CategoryTheory Opposite SquareKit.Internal SquareKit.Internal.Presheaf
open Sequences.OrderedSummary
open Examples.PresheafInternal (Stage Step)

abbrev FineSequence := List (Nat × Bool)
abbrev FineCache := FineSequence × Diagnostic

def R (r : FineCache) (xs : FineSequence) : Prop := xs = r.1 ∧ r.2 = diagnostic xs
def S (xs : FineSequence) (m : Diagnostic) : Prop := m = diagnostic xs
def T (m : Diagnostic) (o : Nat) : Prop := o = m.1.toAdd

/-- Set soundness of the same two source derivations, retaining both witnesses. -/
theorem cached_set (r : FineCache) (o : Nat) :
    (∃ m, (∃ xs, R r xs ∧ S xs m) ∧ T m o) ↔
      (∃ xs, R r xs ∧ ∃ m, S xs m ∧ T m o) :=
  Associativity.inSet R S T r o

theorem plain_set (r : FineSequence) (o : Nat) :
    (∃ m, (∃ xs, xs = r ∧ S xs m) ∧ T m o) ↔
      (∃ xs, xs = r ∧ ∃ m, S xs m ∧ T m o) :=
  Associativity.inSet (fun r xs => xs = r) S T r o

/-- A two-stage diagram uses the existing walking-arrow category. -/
abbrev Sections (C F : Type) : Stage → Type
  | .coarse => C
  | .fine => F

def restrict (C F : Type) (down : F → C) : Step a b → Sections C F b → Sections C F a
  | .ident _, x => x
  | .refine, x => down x

abbrev diagram (C F : Type) (down : F → C) : Stageᵒᵖ ⥤ Type where
  obj j := Sections C F j.unop
  map f := ↾restrict C F down f.unop
  map_id _ := rfl
  map_comp f g := by
    apply ConcreteCategory.hom_ext
    intro x
    exact (show ∀ {a b c} (f : Step a b) (g : Step b c) (x : Sections C F c),
      restrict C F down (f.comp g) x = restrict C F down f (restrict C F down g x) from
      by intros a b c f g x; cases f <;> cases g <;> rfl) g.unop f.unop x

abbrev sequences := diagram (List Nat) FineSequence (List.map Prod.fst)
abbrev summaries := diagram Nat Diagnostic (fun m => m.1.toAdd)
abbrev observations : Stageᵒᵖ ⥤ Type where
  obj _ := Nat
  map _ := ↾id
abbrev caches := Presheaf.product sequences summaries

def summarize : (j : Stage) → Sections (List Nat) FineSequence j → Sections Nat Diagnostic j
  | .coarse, xs => xs.length
  | .fine, xs => diagnostic xs

def observe : (j : Stage) → Sections Nat Diagnostic j → Nat
  | .coarse, n => n
  | .fine, m => m.1.toAdd

/-- Forgetting labels commutes with the same ordinary diagnostic summary. -/
theorem summarize_restrict {a b} (f : Step a b) (xs : Sections (List Nat) FineSequence b) :
    summarize a (restrict _ _ (List.map Prod.fst) f xs) =
      restrict _ _ (fun m : Diagnostic => m.1.toAdd) f (summarize b xs) := by
  cases f with
  | ident => rfl
  | refine =>
    change (xs.map Prod.fst).length = (diagnostic xs).1.toAdd
    rw [diagnostic_value]
    simp

def summaryMap : sequences ⟶ summaries where
  app j := ↾summarize j.unop
  naturality j k f := by
    ext xs
    exact summarize_restrict f.unop xs

def appendSequence : (j : Stage) → Sections (List Nat) FineSequence j →
    Sections (List Nat) FineSequence j → Sections (List Nat) FineSequence j
  | .coarse, xs, ys => xs ++ ys
  | .fine, xs, ys => xs ++ ys

/-- Ordered append is natural; forgetting labels does not reorder elements. -/
def appendMap : Presheaf.product sequences sequences ⟶ sequences where
  app j := ↾fun p => appendSequence j.unop p.1 p.2
  naturality j k f := by
    ext p
    exact (show ∀ {a b} (f : Step a b) (xs ys : Sections (List Nat) FineSequence b),
      appendSequence a (restrict _ _ (List.map Prod.fst) f xs)
        (restrict _ _ (List.map Prod.fst) f ys) =
      restrict _ _ (List.map Prod.fst) f (appendSequence b xs ys) from by
      intros a b f xs ys
      cases f with
      | ident => rfl
      | refine => exact List.map_append.symm) f.unop p.1 p.2

/-- Cache construction commutes with restriction because summary does. -/
def cacheMap : sequences ⟶ caches where
  app j := ↾fun xs => (xs, summaryMap.app j xs)
  naturality j k f := by
    ext xs
    apply Prod.ext
    · rfl
    · exact NatTrans.naturality_apply summaryMap f xs

def observationMap : summaries ⟶ observations where
  app j := ↾observe j.unop
  naturality j k f := by
    ext m
    exact (show ∀ {a b} (f : Step a b) (m : Sections Nat Diagnostic b),
      observe a (restrict _ _ (fun m : Diagnostic => m.1.toAdd) f m) =
        observe b m from
      by intros a b f m; cases f <;> rfl) f.unop m

/-- First projection does not require a valid cache; validity is a relation. -/
def sequenceMap : caches ⟶ sequences where
  app _ := ↾Prod.fst

def summaryProjection : caches ⟶ summaries where
  app _ := ↾Prod.snd

def cachedRelation : Subfunctor (Presheaf.product caches sequences) where
  obj j rx := rx.2 = rx.1.1 ∧ rx.1.2 = summaryMap.app j rx.2
  map {j k} f := by
    rintro ⟨r,xs⟩ ⟨hseq,hsummary⟩
    change sequences.map f xs = sequences.map f r.1 ∧
      summaries.map f r.2 = summaryMap.app k (sequences.map f xs)
    constructor
    · exact congrArg (sequences.map f) hseq
    · rw [hsummary]
      exact (NatTrans.naturality_apply summaryMap f xs).symm

/-- Equality graphs of natural operations are stable subfunctors. -/
def graphRelation {X Y : Stageᵒᵖ ⥤ Type} (f : X ⟶ Y) :
    Subfunctor (Presheaf.product X Y) where
  obj j xy := xy.2 = f.app j xy.1
  map g := by
    rintro ⟨x,y⟩ h
    change Y.map g y = f.app _ (X.map g x)
    change y = f.app _ x at h
    rw [h]
    exact (NatTrans.naturality_apply f g x).symm

def cachedModel : Model (J := Stage) Associativity.Arrow Associativity.Relation where
  carrier | .input => caches | .first => sequences | .second => summaries | .output => observations
  arrow f := nomatch f
  relation | .first => cachedRelation | .second => graphRelation summaryMap
           | .third => graphRelation observationMap

def plainModel : Model (J := Stage) Associativity.Arrow Associativity.Relation where
  carrier | .input => sequences | .first => sequences | .second => summaries | .output => observations
  arrow f := nomatch f
  relation | .first => graphRelation (𝟙 sequences) | .second => graphRelation summaryMap
           | .third => graphRelation observationMap

abbrev left := Associativity.left (F := Associativity.Arrow)
  Associativity.Relation.first .second .third
abbrev right := Associativity.right (F := Associativity.Arrow)
  Associativity.Relation.first .second .third

/-- Both models interpret the existing proof; no stagewise associativity proof. -/
theorem cached_valid : cachedModel.formula left = cachedModel.formula right :=
  le_antisymm (cachedModel.sound (Associativity.forward _ _ _))
    (cachedModel.sound (Associativity.backward _ _ _))

theorem plain_valid : plainModel.formula left = plainModel.formula right :=
  le_antisymm (plainModel.sound (Associativity.forward _ _ _))
    (plainModel.sound (Associativity.backward _ _ _))

def cachedEnv (j : Stageᵒᵖ) (r : caches.obj j) (o : observations.obj j) :
    Env (cachedModel.fiber j) [.input,.output] :=
  Env.extend r (Env.extend o (fun {_} (i : Var [] _) => nomatch i))

theorem restrict_cachedEnv {j k : Stageᵒᵖ} (f : j ⟶ k) (r : caches.obj j) (o : Nat) :
    (fun {s} (i : Var [Associativity.RelSort.input,.output] s) => cachedModel.restrict f (cachedEnv j r o) i) =
      (fun {s} (i : Var [Associativity.RelSort.input,.output] s) => cachedEnv k (caches.map f r) o i) := by
  funext s i
  cases i with
  | zero => rfl
  | succ i => cases i with
    | zero => rfl
    | succ i => nomatch i

def plainEnv (j : Stageᵒᵖ) (r : sequences.obj j) (o : observations.obj j) :
    Env (plainModel.fiber j) [.input,.output] :=
  Env.extend r (Env.extend o (fun {_} (i : Var [] _) => nomatch i))

/-- Ordinary endpoints of interpreted existential validity retain both witnesses. -/
theorem cached_evaluation (j : Stageᵒᵖ) (r : caches.obj j) (o : observations.obj j) :
    (∃ m, (∃ xs, (xs = r.1 ∧ r.2 = summaryMap.app j xs) ∧ m = summaryMap.app j xs) ∧
      o = observationMap.app j m) ↔
    (∃ xs, (xs = r.1 ∧ r.2 = summaryMap.app j xs) ∧
      ∃ m, m = summaryMap.app j xs ∧ o = observationMap.app j m) := by
  have h := congrArg (fun Q => Q.obj j (cachedEnv j r o)) cached_valid
  exact (cachedModel.evaluation left j _).symm.trans
    ((iff_of_eq h).trans (cachedModel.evaluation right j _))

theorem plain_evaluation (j : Stageᵒᵖ) (r : sequences.obj j) (o : observations.obj j) :
    (∃ m, (∃ xs, xs = r ∧ m = summaryMap.app j xs) ∧ o = observationMap.app j m) ↔
    (∃ xs, xs = r ∧ ∃ m, m = summaryMap.app j xs ∧ o = observationMap.app j m) := by
  have h := congrArg (fun Q => Q.obj j (plainEnv j r o)) plain_valid
  exact (plainModel.evaluation left j _).symm.trans
    ((iff_of_eq h).trans (plainModel.evaluation right j _))

abbrev fine := op Stage.fine
abbrev coarse := op Stage.coarse
abbrev drop := Examples.PresheafInternal.drop

def good : FineCache := ([(3,true)], (Multiplicative.ofAdd 1, FreeMonoid.ofList [true]))
def bad : FineCache := ([(3,true)], (Multiplicative.ofAdd 1, FreeMonoid.ofList [false]))

theorem good_set : ∃ xs, R good xs ∧ ∃ m, S xs m ∧ T m 1 := by
  apply (cached_set good 1).mp
  exact ⟨good.2, ⟨good.1, ⟨rfl,rfl⟩, rfl⟩, rfl⟩

theorem good_fine : (cachedModel.formula left).obj fine (cachedEnv fine good 1) := by
  apply (cachedModel.evaluation left fine _).mpr
  exact ⟨good.2, ⟨good.1, ⟨rfl,rfl⟩, rfl⟩, rfl⟩

/-- Restrict the interpreted predicate, including its existential witnesses. -/
theorem good_coarse : (cachedModel.formula left).obj coarse
    (cachedEnv coarse ([3],1) 1) := by
  have h := cachedModel.formula_restrict left drop (cachedEnv fine good 1) good_fine
  exact (congrArg ((cachedModel.formula left).obj coarse)
    (restrict_cachedEnv drop good 1)).mp h

theorem good_reassociated : ∃ xs, (xs = good.1 ∧ good.2 = diagnostic xs) ∧
    ∃ m, m = diagnostic xs ∧ 1 = m.1.toAdd :=
  (cached_evaluation fine good 1).mp ((cachedModel.evaluation left fine _).mp good_fine)

theorem bad_fine : ¬ (cachedModel.formula left).obj fine (cachedEnv fine bad 1) := by
  intro h
  obtain ⟨m, ⟨xs, ⟨hxs,hcache⟩, _⟩, _⟩ := (cachedModel.evaluation left fine _).mp h
  change xs = bad.1 at hxs
  subst xs
  change bad.2 = diagnostic bad.1 at hcache
  rw [diagnostic_value] at hcache
  exact Bool.noConfusion (congrArg (fun p : Diagnostic => p.2.toList.head!) hcache)

theorem bad_restrict : caches.map drop bad = ([3],1) := rfl

/-- Restriction preserves validity but cannot reflect it. -/
theorem no_validity_reflection : ¬ (∀ r : caches.obj fine,
    (cachedModel.formula left).obj coarse (cachedModel.restrict drop (cachedEnv fine r 1)) →
    (cachedModel.formula left).obj fine (cachedEnv fine r 1)) := by
  intro reflects
  apply bad_fine
  apply reflects bad
  exact (congrArg ((cachedModel.formula left).obj coarse)
    (restrict_cachedEnv drop bad 1)).mpr good_coarse

theorem no_equality_reflection : caches.map drop good = caches.map drop bad ∧ good ≠ bad := by
  constructor
  · rfl
  · intro h
    exact Bool.noConfusion (congrArg (fun r : FineCache => r.2.2.toList.head!) h)

example : ∃ xs, xs = ([(3,true)] : FineSequence) ∧
    ∃ m, m = diagnostic xs ∧ 1 = m.1.toAdd :=
  (plain_evaluation fine [(3,true)] 1).mp ⟨diagnostic [(3,true)], ⟨[(3,true)],rfl,rfl⟩,rfl⟩

example : ∃ xs, xs = ([3] : List Nat) ∧ ∃ m, m = xs.length ∧ 1 = m :=
  (plain_evaluation coarse [3] 1).mp ⟨1,⟨[3],rfl,rfl⟩,rfl⟩

end Examples.OrderedSummaryPresheaf
