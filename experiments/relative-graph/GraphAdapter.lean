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

theorem graph_denotes (A B C F G x z : V)
    (hB : B ∈ˢ univ (Level.eval φ u)) (hC : C ∈ˢ univ (Level.eval φ u))
    (hf : ∀ a, a ∈ˢ A → app F a ∈ˢ B)
    (hg : ∀ b, b ∈ˢ B → app G b ∈ˢ C) (hx : x ∈ˢ A) (hz : z ∈ˢ C) :
    Denotes m.cval env φ (assignment x z A B C F G) (composite u)
      (truthVal (∃ y, y ∈ˢ B ∧ y = app F x ∧ z = app G y)) ∧
    Denotes m.cval env φ (assignment x z A B C F G) (result u)
      (truthVal (z = app G (app F x))) := by
  let ρ := assignment x z A B C F G
  have hbody (y : V) (hy : y ∈ˢ B) :
      Denotes m.cval env φ (push y ρ) (body u)
        (truthVal (y = app F x ∧ z = app G y)) := by
    have hleft := eq_denotes pr
      (ρ := push y ρ) (Ae := .bvar 6) (ae := .bvar 0)
      (be := .app (.bvar 4) (.bvar 2))
      Denotes.bvar Denotes.bvar (Denotes.app Denotes.bvar Denotes.bvar)
      hB hy (hf x hx)
    have hright := eq_denotes pr
      (ρ := push y ρ) (Ae := .bvar 5) (ae := .bvar 1)
      (be := .app (.bvar 3) (.bvar 0))
      Denotes.bvar Denotes.bvar (Denotes.app Denotes.bvar Denotes.bvar)
      hC hz (hg y hy)
    have hand := Denotes.const (cval := m.cval) (φ := φ) (ρ := push y ρ)
      (us := []) pr.and_lookup (by simpa using pr.and_levels.symm)
    have h := Denotes.app (Denotes.app hand hleft) hright
    rw [pr.and_law] at h
    exact h
  have hex := Denotes.const (cval := m.cval) (φ := φ) (ρ := ρ)
    (us := [u]) pr.exists_lookup (by simpa using pr.exists_levels.symm)
  have hb : Denotes m.cval env φ ρ (.bvar 5) B := Denotes.bvar
  have h := Denotes.app (Denotes.app hex hb) (Denotes.lam hb hbody)
  rw [pr.exists_law B _ hB] at h
  refine ⟨h, ?_⟩
  exact eq_denotes pr Denotes.bvar Denotes.bvar
    (Denotes.app Denotes.bvar (Denotes.app Denotes.bvar Denotes.bvar))
    hC hz (hg _ (hf x hx))

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
#print axioms GraphAdapter.graph_denotes
#print axioms GraphAdapter.Member
#print axioms GraphAdapter.arrow
#print axioms GraphAdapter.graph_comparison
#print axioms GraphAdapter.graph_truth

-- Current-module roots include generated and private kernel declarations.
-- As in ProofAudit, runtime artifacts are skipped by safety metadata;
-- source declarations marked unsafe are rejected.
open Lean Elab Command in
run_cmd do
  let env ← getEnv
  let candidates := env.constants.foldStage2 (fun acc n ci => acc.push (n, ci)) #[]
  let mut roots : Array Name := #[]
  for (n, ci) in candidates do
    if (env.getModuleIdxFor? n).isSome then continue
    if ci.isUnsafe then
      if (declRangeExt.find? env n).isSome then
        throwError "Unsafe source declaration {n}"
    else
      roots := roots.push n
  let mut union : NameSet := {}
  for n in roots do
    for a in (← liftCoreM (Lean.collectAxioms n)) do
      unless a == ``propext || a == ``Classical.choice || a == ``Quot.sound do
        throwError "Forbidden axiom {a} in {n}"
      union := union.insert a
  logInfo m!"GraphAdapter current-module audit: {roots.size} safe roots; axioms {union.toList}"
