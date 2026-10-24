import ArtifactAudit
import Lean
import ConLeche.Denotes

/-! Conditional formula comparison only. And/Exists laws below are additional
semantic premises, not consequences established here from checker acceptance.
No proof-term, declaration, or installed-Lean translation is claimed. -/
namespace GraphAdapter
open ConLeche ConLeche.SetTheory ConLeche.SetModel
universe w
variable {V : Type w} [SetTheory V]

def existsName : Name := .str .anonymous "Exists"
def eqExpr (u : Level) (A a b : Expr) : Expr :=
  .app (.app (.app (.const eqName [u]) A) a) b
/-- Open de Bruijn context: z, x, g, f, C, B, A. -/
def result (u : Level) : Expr :=
  eqExpr u (.bvar 4) (.bvar 0) (.app (.bvar 2) (.app (.bvar 3) (.bvar 1)))
/-- Under the witness binder: y, z, x, g, f, C, B, A. -/
def body (u : Level) : Expr :=
  .app (.app (.const andName [])
    (eqExpr u (.bvar 6) (.bvar 0) (.app (.bvar 4) (.bvar 2))))
    (eqExpr u (.bvar 5) (.bvar 1) (.app (.bvar 3) (.bvar 0)))
def composite (u : Level) : Expr :=
  .app (.app (.const existsName [u]) (.bvar 5)) (.lam (.bvar 5) (body u))
def assignment (x z A B C F G : V) : Nat → V
  | 0 => z | 1 => x | 2 => G | 3 => F | 4 => C | 5 => B | _ => A

/-- Primitive lookup certificates and the two semantic equations not exposed by
ConLeche.Model. This is an explicit conditional interface, not model existence. -/
structure Primitives (m : Model V env) (u : Level) (φ : LevelParam → Nat) where
  eqInfo : ConstantInfo
  eq_lookup : env.find? eqName = some eqInfo
  eq_levels : eqInfo.toConstantVal.levelParams.length = 1
  andInfo : ConstantInfo
  and_lookup : env.find? andName = some andInfo
  and_levels : andInfo.toConstantVal.levelParams.length = 0
  existsInfo : ConstantInfo
  exists_lookup : env.find? existsName = some existsInfo
  exists_levels : existsInfo.toConstantVal.levelParams.length = 1
  and_law : ∀ p q : Prop,
    app (app (m.cval andName (Level.substFn φ andInfo.toConstantVal.levelParams []))
      (truthVal p)) (truthVal q) = truthVal (p ∧ q)
  exists_law : ∀ (A : V) (P : V → Prop), A ∈ˢ univ (Level.eval φ u) →
    app (app (m.cval existsName
      (Level.substFn φ existsInfo.toConstantVal.levelParams [u])) A)
      (lamV A (fun a => truthVal (P a))) = truthVal (∃ a, a ∈ˢ A ∧ P a)

variable {env : Env} {m : Model V env} {u : Level} {φ : LevelParam → Nat}
variable (pr : Primitives m u φ)
include pr

theorem eq_denotes {ρ : Nat → V} {Ae ae be : Expr} {A a b : V}
    (hA : Denotes m.cval env φ ρ Ae A) (ha : Denotes m.cval env φ ρ ae a)
    (hb : Denotes m.cval env φ ρ be b)
    (hAu : A ∈ˢ univ (Level.eval φ u)) (haA : a ∈ˢ A) (hbA : b ∈ˢ A) :
    Denotes m.cval env φ ρ (eqExpr u Ae ae be) (truthVal (a = b)) := by
  have he := Denotes.const (cval := m.cval) (φ := φ) (ρ := ρ)
    (us := [u]) pr.eq_lookup (by simpa using pr.eq_levels.symm)
  have h := Denotes.app (Denotes.app (Denotes.app he hA) ha) hb
  rw [m.eq_equality u φ ρ _ A a b he hAu haA hbA] at h
  simpa only [eqExpr, eqv] using h

/-- The graph formula under an arbitrary prefix of unrelated binders.
The assignment equation states exactly how its free variables are interpreted. -/
theorem graph_denotes_shift (A B C F G x z : V) (offset : Nat) (ρ : Nat → V)
    (hρ : ∀ i, ρ (offset + i) = assignment x z A B C F G i)
    (hB : B ∈ˢ univ (Level.eval φ u)) (hC : C ∈ˢ univ (Level.eval φ u))
    (hf : ∀ a, a ∈ˢ A → app F a ∈ˢ B)
    (hg : ∀ b, b ∈ˢ B → app G b ∈ˢ C) (hx : x ∈ˢ A) (hz : z ∈ˢ C) :
    Denotes m.cval env φ ρ ((composite u).liftLooseBVars offset 0)
      (truthVal (∃ y, y ∈ˢ B ∧ y = app F x ∧ z = app G y)) ∧
    Denotes m.cval env φ ρ ((result u).liftLooseBVars offset 0)
      (truthVal (z = app G (app F x))) := by
  have atIndex (i : Nat) : Denotes m.cval env φ ρ (.bvar (offset + i))
      (assignment x z A B C F G i) := by
    rw [← hρ i]
    exact Denotes.bvar
  have underWitness (y : V) (i : Nat) :
      Denotes m.cval env φ (push y ρ) (.bvar (offset + (i + 1)))
        (assignment x z A B C F G i) := by
    rw [← hρ i, ← Nat.add_assoc]
    exact Denotes.bvar
  have hbody (y : V) (hy : y ∈ˢ B) :
      Denotes m.cval env φ (push y ρ) ((body u).liftLooseBVars offset 1)
        (truthVal (y = app F x ∧ z = app G y)) := by
    have hleft := eq_denotes pr (underWitness y 5) (Denotes.bvar (i := 0))
      (Denotes.app (underWitness y 3) (underWitness y 1)) hB hy (hf x hx)
    have hright := eq_denotes pr (underWitness y 4) (underWitness y 0)
      (Denotes.app (underWitness y 2) (Denotes.bvar (i := 0))) hC hz (hg y hy)
    have hand := Denotes.const (cval := m.cval) (φ := φ) (ρ := push y ρ)
      (us := []) pr.and_lookup (by simpa using pr.and_levels.symm)
    have h := Denotes.app (Denotes.app hand hleft) hright
    rw [pr.and_law] at h
    simpa [body, eqExpr, Expr.liftLooseBVars, Nat.add_comm, assignment, push] using h
  have hex := Denotes.const (cval := m.cval) (φ := φ) (ρ := ρ)
    (us := [u]) pr.exists_lookup (by simpa using pr.exists_levels.symm)
  have h := Denotes.app (Denotes.app hex (atIndex 5)) (Denotes.lam (atIndex 5) hbody)
  change Denotes _ _ _ _ _
    (app (app _ B) (lamV B (fun y => truthVal (y = app F x ∧ z = app G y)))) at h
  rw [pr.exists_law B _ hB] at h
  constructor
  · simpa only [composite, Expr.liftLooseBVars, Nat.add_comm, Nat.zero_le, ↓reduceIte] using h
  · have h := eq_denotes pr (atIndex 4) (atIndex 0)
      (Denotes.app (atIndex 2) (Denotes.app (atIndex 3) (atIndex 1)))
      hC hz (hg _ (hf x hx))
    simpa [result, eqExpr, Expr.liftLooseBVars, Nat.add_comm, assignment] using h

theorem graph_denotes (A B C F G x z : V)
    (hB : B ∈ˢ univ (Level.eval φ u)) (hC : C ∈ˢ univ (Level.eval φ u))
    (hf : ∀ a, a ∈ˢ A → app F a ∈ˢ B)
    (hg : ∀ b, b ∈ˢ B → app G b ∈ˢ C) (hx : x ∈ˢ A) (hz : z ∈ˢ C) :
    Denotes m.cval env φ (assignment x z A B C F G) (composite u)
      (truthVal (∃ y, y ∈ˢ B ∧ y = app F x ∧ z = app G y)) ∧
    Denotes m.cval env φ (assignment x z A B C F G) (result u)
      (truthVal (z = app G (app F x))) := by
  exact graph_denotes_shift pr A B C F G x z 0 (assignment x z A B C F G)
      (fun i => by rw [Nat.zero_add]) hB hC hf hg hx hz

/-- Native carrier membership is retained, including empty carrier sets. -/
def Member (A : V) := {a : V // a ∈ˢ A}
noncomputable def arrow (A B F : V) (hf : ∀ a, a ∈ˢ A → app F a ∈ˢ B) :
    Member A → Member B := fun a => ⟨app F a.val, hf a.val a.property⟩

theorem graph_comparison (A B C F G : V)
    (hB : B ∈ˢ univ (Level.eval φ u)) (hC : C ∈ˢ univ (Level.eval φ u))
    (hf : ∀ a, a ∈ˢ A → app F a ∈ˢ B)
    (hg : ∀ b, b ∈ˢ B → app G b ∈ˢ C)
    (x : Member A) (z : Member C) (P Q : V)
    (hP : Denotes m.cval env φ (assignment x.val z.val A B C F G) (composite u) P)
    (hQ : Denotes m.cval env φ (assignment x.val z.val A B C F G) (result u) Q) :
    ((pt : V) ∈ˢ P ↔ ∃ y : Member B, y = arrow A B F hf x ∧ z = arrow B C G hg y) ∧
    ((pt : V) ∈ˢ Q ↔ z = arrow B C G hg (arrow A B F hf x)) := by
  obtain ⟨hP', hQ'⟩ := graph_denotes pr A B C F G x.val z.val hB hC hf hg x.property z.property
  obtain rfl := Denotes_functional hP hP'
  obtain rfl := Denotes_functional hQ hQ'
  simp only [mem_truthVal, and_true]
  constructor
  · constructor
    · rintro ⟨y, hy, he, hz⟩
      exact ⟨⟨y, hy⟩, Subtype.ext he, Subtype.ext hz⟩
    · rintro ⟨y, he, hz⟩
      exact ⟨y.val, y.property, congrArg Subtype.val he, congrArg Subtype.val hz⟩
  · exact ⟨fun h => Subtype.ext h, fun h => congrArg Subtype.val h⟩

/-- A use of the comparison: eliminate the native middle witness forward,
and choose f(x) backward. This does not add a graph truth premise. -/
theorem graph_truth (A B C F G : V)
    (hB : B ∈ˢ univ (Level.eval φ u)) (hC : C ∈ˢ univ (Level.eval φ u))
    (hf : ∀ a, a ∈ˢ A → app F a ∈ˢ B)
    (hg : ∀ b, b ∈ˢ B → app G b ∈ˢ C)
    (x : Member A) (z : Member C) (P Q : V)
    (hP : Denotes m.cval env φ (assignment x.val z.val A B C F G) (composite u) P)
    (hQ : Denotes m.cval env φ (assignment x.val z.val A B C F G) (result u) Q) :
    (pt : V) ∈ˢ P ↔ (pt : V) ∈ˢ Q := by
  obtain ⟨hp, hq⟩ := graph_comparison pr A B C F G hB hC hf hg x z P Q hP hQ
  rw [hp, hq]
  constructor
  · rintro ⟨y, rfl, hz⟩
    exact hz
  · intro hz
    exact ⟨arrow A B F hf x, rfl, hz⟩

end GraphAdapter

#print axioms GraphAdapter.existsName
#print axioms GraphAdapter.eqExpr
#print axioms GraphAdapter.result
#print axioms GraphAdapter.body
#print axioms GraphAdapter.composite
#print axioms GraphAdapter.assignment
#print axioms GraphAdapter.Primitives
#print axioms GraphAdapter.Primitives.mk
#print axioms GraphAdapter.Primitives.rec
#print axioms GraphAdapter.Primitives.recOn
#print axioms GraphAdapter.Primitives.casesOn
#print axioms GraphAdapter.Primitives.eqInfo
#print axioms GraphAdapter.Primitives.eq_lookup
#print axioms GraphAdapter.Primitives.eq_levels
#print axioms GraphAdapter.Primitives.andInfo
#print axioms GraphAdapter.Primitives.and_lookup
#print axioms GraphAdapter.Primitives.and_levels
#print axioms GraphAdapter.Primitives.existsInfo
#print axioms GraphAdapter.Primitives.exists_lookup
#print axioms GraphAdapter.Primitives.exists_levels
#print axioms GraphAdapter.Primitives.and_law
#print axioms GraphAdapter.Primitives.exists_law
#print axioms GraphAdapter.eq_denotes
#print axioms GraphAdapter.graph_denotes_shift
#print axioms GraphAdapter.graph_denotes
#print axioms GraphAdapter.Member
#print axioms GraphAdapter.arrow
#print axioms GraphAdapter.graph_comparison
#print axioms GraphAdapter.graph_truth

#audit_graph_module
