import SquareKit.Internal.Cubical.TypeFormers

/-! Natural numbers with dependent elimination in the constructed presheaf model. -/
namespace SquareKit.Cubical.Presheaf
open CategoryTheory
universe u

abbrev natFamily (Γ : Context.{u}) : Family Γ :=
  (Functor.const Γ.Elements).obj (ULift.{u} ℕ)

def natZero (Γ : Context.{u}) : Term (natFamily Γ) where
  val _ := ⟨0⟩
  property _ := rfl

def natSucc {Γ : Context.{u}} (n : Term (natFamily Γ)) : Term (natFamily Γ) where
  val x := ⟨(n.val x).down + 1⟩
  property f := congrArg (fun k : ULift ℕ => ULift.up (k.down + 1)) (n.property f)

/-- A dependent successor method, coherent under every restriction. -/
structure NatStep {Γ : Context.{u}} (B : Family (total (natFamily Γ))) where
  val : ∀ (x : Γ.Elements) (n : ℕ), B.obj (extendObj (natFamily Γ) x ⟨n⟩) →
    B.obj (extendObj (natFamily Γ) x ⟨n+1⟩)
  naturality : ∀ {x y : Γ.Elements} (f : x ⟶ y) (n : ℕ)
      (b : B.obj (extendObj (natFamily Γ) x ⟨n⟩)),
    B.map (extendHom (natFamily Γ) f ⟨n+1⟩) (val x n b) =
      val y n (B.map (extendHom (natFamily Γ) f ⟨n⟩) b)

/-- Increment the number while retaining its base environment. -/
def natSuccessorSub (Γ : Context.{u}) : total (natFamily Γ) ⟶ total (natFamily Γ) :=
  pair (projection (natFamily Γ)) (natSucc (generic (natFamily Γ)))

/-- A typed successor method has context Γ,n,b and result B at n+1. -/
abbrev NatStepTerm {Γ : Context.{u}} (B : Family (total (natFamily Γ))) :=
  Term (reindex B (projection B ≫ natSuccessorSub Γ))

def NatStep.ofTerm {Γ : Context.{u}} {B : Family (total (natFamily Γ))}
    (t : NatStepTerm B) : NatStep B where
  val x n b := t.val (extendObj B (extendObj (natFamily Γ) x ⟨n⟩) b)
  naturality f n b := t.property (extendHom B (extendHom (natFamily Γ) f ⟨n⟩) b)

def NatStep.toTerm {Γ : Context.{u}} {B : Family (total (natFamily Γ))}
    (s : NatStep B) : NatStepTerm B where
  val e := s.val (Γ.elementsMk e.obj e.val.1.1) e.val.1.2.down e.val.2
  property {x y} f := by
    rcases x with @⟨I, ⟨x, ⟨n⟩⟩, b⟩
    rcases y with @⟨J, y, c⟩
    rcases f with ⟨f,h⟩
    change I ⟶ J at f
    change totalMap B f ⟨⟨x, ⟨n⟩⟩, b⟩ = ⟨y,c⟩ at h
    cases h
    let g : Γ.elementsMk I x ⟶ Γ.elementsMk J (Γ.map f x) :=
      Functor.Elements.homMk f rfl
    exact s.naturality g n b

@[simp] theorem NatStep.ofTerm_toTerm {Γ : Context.{u}} {B : Family (total (natFamily Γ))}
    (s : NatStep B) : NatStep.ofTerm s.toTerm = s := rfl

@[simp] theorem NatStep.toTerm_ofTerm {Γ : Context.{u}} {B : Family (total (natFamily Γ))}
    (t : NatStepTerm B) : (NatStep.ofTerm t).toTerm = t := rfl

/-- Recursion is constructed fiber by fiber; coherence follows by induction. -/
def natRecValue {Γ : Context.{u}} {B : Family (total (natFamily Γ))}
    (z : Term (reindex B (pair (𝟙 Γ) (natZero Γ)))) (s : NatStep B)
    (x : Γ.Elements) : (n : ℕ) → B.obj (extendObj (natFamily Γ) x ⟨n⟩)
  | 0 => z.val x
  | n+1 => s.val x n (natRecValue z s x n)

theorem natRecValue_natural {Γ : Context.{u}} {B : Family (total (natFamily Γ))}
    (z : Term (reindex B (pair (𝟙 Γ) (natZero Γ)))) (s : NatStep B)
    {x y : Γ.Elements} (f : x ⟶ y) (n : ℕ) :
    B.map (extendHom (natFamily Γ) f ⟨n⟩) (natRecValue z s x n) =
      natRecValue z s y n := by
  induction n with
  | zero => exact z.property f
  | succ n ih => exact (s.naturality f n _).trans (congrArg (s.val y n) ih)

/-- The eliminator is a section of an arbitrary dependent motive. -/
def natElim {Γ : Context.{u}} {B : Family (total (natFamily Γ))}
    (z : Term (reindex B (pair (𝟙 Γ) (natZero Γ)))) (s : NatStep B) : Term B where
  val e := natRecValue z s (Γ.elementsMk e.obj e.val.1) e.val.2.down
  property {x y} f := by
    rcases x with @⟨I, x, ⟨n⟩⟩
    rcases y with @⟨J, y, ⟨m⟩⟩
    rcases f with ⟨f,h⟩
    change I ⟶ J at f
    change (⟨Γ.map f x, ULift.up n⟩ : Σ _ : Γ.obj J, ULift ℕ) = ⟨y, ULift.up m⟩ at h
    cases h
    let g : Γ.elementsMk I x ⟶ Γ.elementsMk J (Γ.map f x) :=
      Functor.Elements.homMk f rfl
    exact natRecValue_natural z s g n

@[simp] theorem natElim_zero {Γ : Context.{u}} {B : Family (total (natFamily Γ))}
    (z : Term (reindex B (pair (𝟙 Γ) (natZero Γ)))) (s : NatStep B) :
    Term.reindex (natElim z s) (pair (𝟙 Γ) (natZero Γ)) = z := rfl

@[simp] theorem natElim_succ {Γ : Context.{u}} {B : Family (total (natFamily Γ))}
    (z : Term (reindex B (pair (𝟙 Γ) (natZero Γ)))) (s : NatStep B)
    (x : Γ.Elements) (n : ℕ) :
    (natElim z s).val (extendObj (natFamily Γ) x ⟨n+1⟩) =
      s.val x n ((natElim z s).val (extendObj (natFamily Γ) x ⟨n⟩)) := rfl

@[simp] theorem natFamily_reindex {Γ Δ : Context.{u}} (σ : Δ ⟶ Γ) :
    reindex (natFamily Γ) σ = natFamily Δ := rfl

@[simp] theorem natZero_reindex {Γ Δ : Context.{u}} (σ : Δ ⟶ Γ) :
    Term.reindex (natZero Γ) σ = natZero Δ := rfl

theorem natSucc_reindex {Γ Δ : Context.{u}} (n : Term (natFamily Γ)) (σ : Δ ⟶ Γ) :
    Term.reindex (natSucc n) σ = natSucc (Term.reindex n σ) := rfl

def NatStep.reindex {Γ Δ : Context.{u}} {B : Family (total (natFamily Γ))}
    (s : NatStep B) (σ : Δ ⟶ Γ) : NatStep (Presheaf.reindex B (liftSub (natFamily Γ) σ)) where
  val x n b := s.val (σ.mapElements.obj x) n b
  naturality f n b := s.naturality (σ.mapElements.map f) n b

theorem natElim_reindex {Γ Δ : Context.{u}} {B : Family (total (natFamily Γ))}
    (z : Term (reindex B (pair (𝟙 Γ) (natZero Γ)))) (s : NatStep B) (σ : Δ ⟶ Γ) :
    Term.reindex (natElim z s) (liftSub (natFamily Γ) σ) =
      natElim (B := reindex B (liftSub (natFamily Γ) σ)) (Term.reindex z σ) (s.reindex σ) := by
  apply Term.ext
  intro e
  rcases e with @⟨I, x, ⟨n⟩⟩
  induction n with
  | zero => rfl
  | succ n ih => exact congrArg (s.val (Γ.elementsMk I (σ.app I x)) n) ih

end SquareKit.Cubical.Presheaf
