import SquareKit.EquationTranspose
import SquareKit.IndexedCompositional

/-! A binding-free equation fragment whose results are outputs or finite typed
successor templates. Transposition changes presentation; compatibility with an
independent algebra remains a separate obligation. -/
namespace SquareKit.EquationComposition
open IndexedCompositional
universe i o b a x d
variable {I : Type i} (S : Signature.{i,o} I) (B : Behavior.{i,b,a} I)

/-- Requests are part of the observer name so that its result index can depend on them. -/
inductive Observer (j : I) where
  | output
  | next (r : B.Request j)

abbrev Outputs {j} (op : S.Op j) := ∀ k, B.Output (S.child op k)

/-- The equation index includes the constructor: successor slots depend on it.
The only constructor at that index carries the child-output block. -/
def signature : EquationTranspose.Signature (Sigma S.Op) where
  Constructor _ := PUnit
  Observer p := Observer B p.1
  fields {p} _ := ULift.{max i o b a} (Outputs S B p.2)
  arguments _ := PUnit
  result {p} obs := match obs with
    | .output => ULift.{max i o b a} (B.Output p.1)
    | .next r => ULift.{max i o b a} (Term S (Slot S B p.2) (B.next p.1 r))

variable {S B}
variable {P : Type (max i o b a) → Type (max i o b a) → Type ((max i o b a)+1)}

def compile (p : EquationTranspose.DataProgram (signature S B) P)
    (m : ∀ {A C}, P A C → A → C) : Rule S B where
  out {j} op xs := (p.observe m (i := ⟨j,op⟩) .output ⟨PUnit.unit, ⟨xs⟩⟩ PUnit.unit).down
  step {j} op xs r := (p.observe m (i := ⟨j,op⟩) (.next r) ⟨PUnit.unit, ⟨xs⟩⟩ PUnit.unit).down

def compileRows (p : EquationTranspose.CodataProgram (signature S B) P)
    (m : ∀ {A C}, P A C → A → C) : Rule S B where
  out {j} op xs := (p.construct m (i := ⟨j,op⟩) PUnit.unit ⟨xs⟩ .output PUnit.unit).down
  step {j} op xs r := (p.construct m (i := ⟨j,op⟩) PUnit.unit ⟨xs⟩ (.next r) PUnit.unit).down

/-- Equality includes original-child slots, successor requests, and result indices;
no semantic compatibility assumption is needed to change presentation. -/
theorem compile_transpose (p : EquationTranspose.DataProgram (signature S B) P)
    (m : ∀ {A C}, P A C → A → C) : compileRows (EquationTranspose.transpose p) m = compile p m := by
  have ho : @Rule.out _ _ _ (compileRows (EquationTranspose.transpose p) m) = @Rule.out _ _ _ (compile p m) := by
    funext j op xs
    have h := EquationTranspose.transpose_preserves p m
      (i := ⟨j,op⟩) PUnit.unit (ULift.up xs) (.output (B := B)) PUnit.unit
    exact congrArg (fun z : ULift.{max i o b a} (B.Output j) => z.down) h
  have hs : @Rule.step _ _ _ (compileRows (EquationTranspose.transpose p) m) = @Rule.step _ _ _ (compile p m) := by
    funext j op xs r
    have h := EquationTranspose.transpose_preserves p m
      (i := ⟨j,op⟩) PUnit.unit (ULift.up xs) (.next (B := B) r) PUnit.unit
    exact congrArg (fun z : ULift.{max i o b a} (Term S (Slot S B op) (B.next j r)) => z.down) h
  exact congrArg₂ (fun out step => Rule.mk out step) ho hs

/-- The shared all-term theorem applies after local semantic obligations are proved. -/
theorem observations (p : EquationTranspose.DataProgram (signature S B) P)
    (m : ∀ {A C}, P A C → A → C)
    {D : I → Type d} {X : I → Type x}
    (alg : ∀ {j} (op : S.Op j), (∀ k, D (S.child op k)) → D j)
    (native : B.Coalgebra D) (h : (compile p m).Compatible alg native)
    (c : B.Coalgebra X) (f : ∀ j, X j → D j) (hf : B.Morphism c native f)
    {j k} (path : B.Path j k) (t : Term S X j) :
    B.observe native path (Term.fold alg f t) =
      B.observe ((compileRows (EquationTranspose.transpose p) m).lift c) path t := by
  rw [compile_transpose]
  exact B.observe_morphism _ _ _ ((compile p m).fold_morphism alg native h c f hf) path t

end SquareKit.EquationComposition
