import SquareKit.Internal.DependentJudgments.CoherentTypePresentations
import SquareKit.Internal.DependentJudgments.DerivedPathSemantics

/-! Specified coherent comparison for the selected derived recipes in the native
Type model. Native identity is truncated; these comparisons are not higher-model
faithfulness claims. The general strict-map theorem has independent scope. -/
namespace SquareKit.Internal.DependentJudgments.NativeDerivedComparisons
open PathTransport.Typed StructuralModel Contextual.DerivedSemantics CoherentTypePresentations
set_option backward.isDefEq.respectTransparency false
universe u
variable {Base : Type u} {Fiber : Base → Type u}
local notation "M" => NativeType.model Base Fiber
local notation "S" => NativeType.structuralModel Base Fiber
variable {Γ Δ : Type u} {e : Γ ≃ Δ} {A : Γ → Type u} {A' : Δ → Type u}
variable (f : FamilyComparison e A A')
variable {B : Sigma A → Type u} {B' : Sigma A' → Type u}
variable (g : FamilyComparison f.total B B')

/-- The type comparison over a selected section is induced from the comparison
of its displayed family. The section square supplies the necessary transport. -/
def atSection (x : (γ : Γ) → A γ) :
    FamilyComparison e (fun γ => B ⟨γ, x γ⟩) (fun δ => B' ⟨δ, f.term x δ⟩) := fun γ =>
  (g ⟨γ, x γ⟩).trans (Equiv.cast
    (congrArg (fun a => B' ⟨e γ, a⟩) (f.term_apply x γ).symm))

theorem atSection_term (x : (γ : Γ) → A γ) (t : (z : Sigma A) → B z) :
    (atSection f g x).term (fun γ => t ⟨γ, x γ⟩) =
      fun δ => g.term t ⟨δ, f.term x δ⟩ := by
  funext δ
  obtain ⟨γ, rfl⟩ := e.surjective δ
  rw [(atSection f g x).term_apply (fun γ => t ⟨γ, x γ⟩) γ]
  change cast (congrArg (fun a => B' ⟨e γ, a⟩) (f.term_apply x γ).symm)
    (g ⟨γ, x γ⟩ (t ⟨γ, x γ⟩)) = _
  rw [← g.term_apply t ⟨γ, x γ⟩]
  have hcast : ∀ {a b : A' (e γ)} (h : a = b),
      cast (congrArg (fun a => B' ⟨e γ, a⟩) h) (g.term t ⟨e γ, a⟩) =
        g.term t ⟨e γ, b⟩ := by
    intro a b h
    cases h
    rfl
  exact hcast (f.term_apply x γ).symm

def path (x y : (γ : Γ) → A γ)
    (p : (S).Section Γ ((S).identity A ⟨x⟩ ⟨y⟩)) :
    (S).Section Δ ((S).identity A' ⟨f.term x⟩ ⟨f.term y⟩) :=
  ⟨(f.identityFamily x y).term p.down⟩

theorem identitySection_unique (x y : (γ : Γ) → A γ)
    (p q : (S).Section Γ ((S).identity A ⟨x⟩ ⟨y⟩)) : p = q := by
  apply ULift.ext
  funext γ
  apply ULift.ext
  exact Subsingleton.elim _ _

/-- Selected transport, including its result family, commutes with the specified
presentation change. The native path elimination used here is stated openly. -/
theorem transport_compare (x y : (γ : Γ) → A γ)
    (p : (S).Section Γ ((S).identity A ⟨x⟩ ⟨y⟩))
    (b : (S).Section Γ ((S).subTy B ((S).sectionSub A ⟨x⟩))) :
    (atSection f g y).term (transportValue M A B ⟨x⟩ ⟨y⟩ p b).down =
      (transportValue M A' B' ⟨f.term x⟩ ⟨f.term y⟩ (path f x y p)
        ⟨(atSection f g x).term b.down⟩).down := by
  have he : x = y := funext (fun γ => (p.down γ).down.down)
  subst y
  have hp : p = (M).reflexivity A ⟨x⟩ := identitySection_unique x x _ _
  rw [hp, transportValue_refl]
  have hpath : path f x x ((M).reflexivity A ⟨x⟩) =
      (M).reflexivity A' ⟨f.term x⟩ := identitySection_unique (f.term x) (f.term x) _ _
  rw [hpath, transportValue_refl]

theorem concat_compare (x y z : (γ : Γ) → A γ)
    (p : (S).Section Γ ((S).identity A ⟨x⟩ ⟨y⟩))
    (q : (S).Section Γ ((S).identity A ⟨y⟩ ⟨z⟩)) :
    path f x z (concatValue M A ⟨x⟩ ⟨y⟩ ⟨z⟩ p q) =
      concatValue M A' ⟨f.term x⟩ ⟨f.term y⟩ ⟨f.term z⟩ (path f x y p) (path f y z q) :=
  identitySection_unique (f.term x) (f.term z) _ _

theorem iteratedTransport_compare (x y z : (γ : Γ) → A γ)
    (p : (S).Section Γ ((S).identity A ⟨x⟩ ⟨y⟩))
    (q : (S).Section Γ ((S).identity A ⟨y⟩ ⟨z⟩))
    (b : (S).Section Γ ((S).subTy B ((S).sectionSub A ⟨x⟩))) :
    (atSection f g z).term
      (transportValue M A B ⟨y⟩ ⟨z⟩ q (transportValue M A B ⟨x⟩ ⟨y⟩ p b)).down =
      (transportValue M A' B' ⟨f.term y⟩ ⟨f.term z⟩ (path f y z q)
        (transportValue M A' B' ⟨f.term x⟩ ⟨f.term y⟩ (path f x y p)
          ⟨(atSection f g x).term b.down⟩)).down := by
  have h := transport_compare f g y z q (transportValue M A B ⟨x⟩ ⟨y⟩ p b)
  have hi := congrArg ULift.up (transport_compare f g x y p b)
  rw [hi] at h
  exact h

theorem compositeTransport_compare (x y z : (γ : Γ) → A γ)
    (p : (S).Section Γ ((S).identity A ⟨x⟩ ⟨y⟩))
    (q : (S).Section Γ ((S).identity A ⟨y⟩ ⟨z⟩))
    (b : (S).Section Γ ((S).subTy B ((S).sectionSub A ⟨x⟩))) :
    (atSection f g z).term
      (transportValue M A B ⟨x⟩ ⟨z⟩ (concatValue M A ⟨x⟩ ⟨y⟩ ⟨z⟩ p q) b).down =
      (transportValue M A' B' ⟨f.term x⟩ ⟨f.term z⟩
        (concatValue M A' ⟨f.term x⟩ ⟨f.term y⟩ ⟨f.term z⟩ (path f x y p) (path f y z q))
        ⟨(atSection f g x).term b.down⟩).down := by
  have h := transport_compare f g x z (concatValue M A ⟨x⟩ ⟨y⟩ ⟨z⟩ p q) b
  rw [concat_compare] at h
  exact h

/-- Native object-identity families compare after the constructed endpoint
comparisons. This does not reflect decoded equality into source equality. -/
def identityComparison {C : Γ → Type u} {D : Δ → Type u}
    (c : FamilyComparison e C D) (s t : (γ : Γ) → C γ)
    (s' t' : (δ : Δ) → D δ) (hs : c.term s = s') (ht : c.term t = t') :
    FamilyComparison e (fun γ => ULift.{u} (PLift (s γ = t γ)))
      (fun δ => ULift.{u} (PLift (s' δ = t' δ))) := by
  subst s'; subst t'
  exact c.identityFamily s t

/-- The certificate family's comparison is derived from the value and
composite-transport comparisons, retaining the value in the identity type. -/
def etaFamily (x y z : (γ : Γ) → A γ)
    (p : (S).Section Γ ((S).identity A ⟨x⟩ ⟨y⟩))
    (q : (S).Section Γ ((S).identity A ⟨y⟩ ⟨z⟩))
    (b : (S).Section Γ ((S).subTy B ((S).sectionSub A ⟨x⟩))) :=
  identityComparison (atSection f g z)
    (transportValue M A B ⟨y⟩ ⟨z⟩ q (transportValue M A B ⟨x⟩ ⟨y⟩ p b)).down
    (transportValue M A B ⟨x⟩ ⟨z⟩ (concatValue M A ⟨x⟩ ⟨y⟩ ⟨z⟩ p q) b).down
    (transportValue M A' B' ⟨f.term y⟩ ⟨f.term z⟩ (path f y z q)
      (transportValue M A' B' ⟨f.term x⟩ ⟨f.term y⟩ (path f x y p)
        ⟨(atSection f g x).term b.down⟩)).down
    (transportValue M A' B' ⟨f.term x⟩ ⟨f.term z⟩
      (concatValue M A' ⟨f.term x⟩ ⟨f.term y⟩ ⟨f.term z⟩ (path f x y p) (path f y z q))
      ⟨(atSection f g x).term b.down⟩).down
    (iteratedTransport_compare f g x y z p q b)
    (compositeTransport_compare f g x y z p q b)

theorem eta_compare (x y z : (γ : Γ) → A γ)
    (p : (S).Section Γ ((S).identity A ⟨x⟩ ⟨y⟩))
    (q : (S).Section Γ ((S).identity A ⟨y⟩ ⟨z⟩))
    (b : (S).Section Γ ((S).subTy B ((S).sectionSub A ⟨x⟩))) :
    (etaFamily f g x y z p q b).term (etaValue M A B ⟨x⟩ ⟨y⟩ ⟨z⟩ p q b).down =
      (etaValue M A' B' ⟨f.term x⟩ ⟨f.term y⟩ ⟨f.term z⟩ (path f x y p) (path f y z q)
        ⟨(atSection f g x).term b.down⟩).down :=
  Subsingleton.elim _ _

/-- The source of dependent action includes transport of the selected section.
Both that transport and the section square enter this comparison. -/
theorem apd_source_compare (x y : (γ : Γ) → A γ)
    (p : (S).Section Γ ((S).identity A ⟨x⟩ ⟨y⟩))
    (t : (S).Section (Sigma A) B) :
    (atSection f g y).term
      (transportValue M A B ⟨x⟩ ⟨y⟩ p ((M).subTm t ((S).sectionSub A ⟨x⟩))).down =
      (transportValue M A' B' ⟨f.term x⟩ ⟨f.term y⟩ (path f x y p)
        ((M).subTm ⟨g.term t.down⟩ ((S).sectionSub A' ⟨f.term x⟩))).down := by
  have h := transport_compare f g x y p ((M).subTm t ((S).sectionSub A ⟨x⟩))
  have hb : (⟨(atSection f g x).term (((M).subTm t ((S).sectionSub A ⟨x⟩)).down)⟩ :
      (S).Section Δ ((S).subTy B' ((S).sectionSub A' ⟨f.term x⟩))) =
      (M).subTm ⟨g.term t.down⟩ ((S).sectionSub A' ⟨f.term x⟩) := by
    apply ULift.ext
    exact atSection_term f g x t.down
  rw [hb] at h
  exact h

/-- The dependent action's identity-family comparison is constructed from the
transported-source and target-section comparisons. -/
def apdFamily (x y : (γ : Γ) → A γ)
    (p : (S).Section Γ ((S).identity A ⟨x⟩ ⟨y⟩))
    (t : (S).Section (Sigma A) B) :=
  identityComparison (atSection f g y)
    (transportValue M A B ⟨x⟩ ⟨y⟩ p ((M).subTm t ((S).sectionSub A ⟨x⟩))).down
    ((M).subTm t ((S).sectionSub A ⟨y⟩)).down
    (transportValue M A' B' ⟨f.term x⟩ ⟨f.term y⟩ (path f x y p)
      ((M).subTm ⟨g.term t.down⟩ ((S).sectionSub A' ⟨f.term x⟩))).down
    ((M).subTm ⟨g.term t.down⟩ ((S).sectionSub A' ⟨f.term y⟩)).down
    (apd_source_compare f g x y p t) (atSection_term f g y t.down)

/-- The actual selected semantic apd recipe is preserved. Native identity
fibers are subsingletons; this last step has only that stated Type-model scope. -/
theorem apd_compare (x y : (γ : Γ) → A γ)
    (p : (S).Section Γ ((S).identity A ⟨x⟩ ⟨y⟩))
    (t : (S).Section (Sigma A) B) :
    (apdFamily f g x y p t).term (apdValue M A B ⟨x⟩ ⟨y⟩ p t).down =
      (apdValue M A' B' ⟨f.term x⟩ ⟨f.term y⟩ (path f x y p) ⟨g.term t.down⟩).down :=
  Subsingleton.elim _ _

/-- A separately constructed target section may replace the transported one.
The heterogeneous equality retains its actual identity-family index. -/
theorem apd_compare_section (x y : (γ : Γ) → A γ)
    (p : (S).Section Γ ((S).identity A ⟨x⟩ ⟨y⟩))
    (t : (S).Section (Sigma A) B) (t' : (S).Section (Sigma A') B')
    (ht : g.term t.down = t'.down) :
    HEq (⟨(apdFamily f g x y p t).term
      (apdValue M A B ⟨x⟩ ⟨y⟩ p t).down⟩ : (S).Section Δ _)
      (apdValue M A' B' ⟨f.term x⟩ ⟨f.term y⟩ (path f x y p) t') := by
  have hsection : (⟨g.term t.down⟩ : (S).Section (Sigma A') B') = t' := ULift.ext ht
  subst t'
  exact heq_of_eq (ULift.ext (apd_compare f g x y p t))

section CertificateSection
variable (x y z : (γ : Γ) → A γ)
variable (q : (NativeType.structuralModel Base Fiber).Section Γ ((NativeType.structuralModel Base Fiber).identity A ⟨y⟩ ⟨z⟩))
variable (b : (NativeType.structuralModel Base Fiber).Section Γ ((NativeType.structuralModel Base Fiber).subTy B ((NativeType.structuralModel Base Fiber).sectionSub A ⟨x⟩)))

abbrev PathFamily := fun γ => ULift.{u} (PLift (x γ = y γ))
abbrev PathBase := Sigma (PathFamily x y)
abbrev TargetPathBase := Sigma (PathFamily (f.term x) (f.term y))

def liftedFamilyComparison : FamilyComparison (f.identityFamily x y).total
    (fun s : PathBase x y => A s.1) (fun s : TargetPathBase f x y => A' s.1) := fun s => f s.1

def liftedDependentComparison : FamilyComparison (liftedFamilyComparison f x y).total
    (fun s => B ⟨s.1.1, s.2⟩) (fun s => B' ⟨s.1.1, s.2⟩) :=
  fun s => g ⟨s.1.1, s.2⟩

abbrev liftedPoint (t : (γ : Γ) → A γ) := fun s : PathBase x y => t s.1
abbrev variablePath : (S).Section (PathBase x y)
    ((S).identity (fun s => A s.1) ⟨liftedPoint x y x⟩ ⟨liftedPoint x y y⟩) :=
  ⟨fun s => s.2⟩
abbrev liftedLastPath : (S).Section (PathBase x y)
    ((S).identity (fun s => A s.1) ⟨liftedPoint x y y⟩ ⟨liftedPoint x y z⟩) :=
  ⟨fun s => q.down s.1⟩
abbrev liftedInput : (S).Section (PathBase x y)
    ((S).subTy (fun s => B ⟨s.1.1, s.2⟩)
      ((S).sectionSub (fun s => A s.1) ⟨liftedPoint x y x⟩)) :=
  ⟨fun s => b.down s.1⟩

def selectedEtaType := (M).identity
  ((M).subTy (fun s : (v : PathBase x y) × A v.1 => B ⟨s.1.1, s.2⟩)
    ((S).sectionSub (fun s : PathBase x y => A s.1) ⟨liftedPoint x y z⟩))
  (transportValue M (fun s : PathBase x y => A s.1) (fun s => B ⟨s.1.1, s.2⟩)
    ⟨liftedPoint x y y⟩ ⟨liftedPoint x y z⟩ (liftedLastPath (Base := Base) (Fiber := Fiber) x y z q)
    (transportValue M (fun s : PathBase x y => A s.1) (fun s => B ⟨s.1.1, s.2⟩)
      ⟨liftedPoint x y x⟩ ⟨liftedPoint x y y⟩ (variablePath (Base := Base) (Fiber := Fiber) x y)
      (liftedInput (Base := Base) (Fiber := Fiber) x y b)))
  (transportValue M (fun s : PathBase x y => A s.1) (fun s => B ⟨s.1.1, s.2⟩)
    ⟨liftedPoint x y x⟩ ⟨liftedPoint x y z⟩
    (concatValue M (fun s : PathBase x y => A s.1) ⟨liftedPoint x y x⟩ ⟨liftedPoint x y y⟩ ⟨liftedPoint x y z⟩
      (variablePath (Base := Base) (Fiber := Fiber) x y) (liftedLastPath (Base := Base) (Fiber := Fiber) x y z q))
    (liftedInput (Base := Base) (Fiber := Fiber) x y b))

def selectedEtaSection := etaValue M (fun s : PathBase x y => A s.1)
  (fun s => B ⟨s.1.1, s.2⟩) ⟨liftedPoint x y x⟩ ⟨liftedPoint x y y⟩ ⟨liftedPoint x y z⟩
  (variablePath (Base := Base) (Fiber := Fiber) x y) (liftedLastPath (Base := Base) (Fiber := Fiber) x y z q) (liftedInput (Base := Base) (Fiber := Fiber) x y b)

def selectedEtaFamilyComparison := etaFamily (Base := Base) (Fiber := Fiber) (liftedFamilyComparison f x y)
  (liftedDependentComparison f g x y) (liftedPoint x y x) (liftedPoint x y y) (liftedPoint x y z)
  (variablePath (Base := Base) (Fiber := Fiber) x y) (liftedLastPath (Base := Base) (Fiber := Fiber) x y z q) (liftedInput (Base := Base) (Fiber := Fiber) x y b)

def targetEtaSection := (etaValue M (fun s : TargetPathBase f x y => A' s.1) (fun s => B' ⟨s.1.1, s.2⟩)
        ⟨(liftedFamilyComparison f x y).term (liftedPoint x y x)⟩
        ⟨(liftedFamilyComparison f x y).term (liftedPoint x y y)⟩
        ⟨(liftedFamilyComparison f x y).term (liftedPoint x y z)⟩
        (path (liftedFamilyComparison f x y) _ _ (variablePath (Base := Base) (Fiber := Fiber) x y))
        (path (liftedFamilyComparison f x y) _ _ (liftedLastPath (Base := Base) (Fiber := Fiber) x y z q))
        ⟨(atSection (liftedFamilyComparison f x y) (liftedDependentComparison f g x y)
          (liftedPoint x y x)).term (liftedInput (Base := Base) (Fiber := Fiber) x y b).down⟩)

/-- Specialization to the actual eta section in its varying first-path context.
The compared family was constructed from the selected transport values above. -/
theorem selectedEtaSection_compare :
    (selectedEtaFamilyComparison (Base := Base) (Fiber := Fiber) f g x y z q b).term (selectedEtaSection (Base := Base) (Fiber := Fiber) x y z q b).down =
      (targetEtaSection f g x y z q b).down :=
  eta_compare (liftedFamilyComparison f x y) (liftedDependentComparison f g x y)
    (liftedPoint x y x) (liftedPoint x y y) (liftedPoint x y z)
    (variablePath (Base := Base) (Fiber := Fiber) x y) (liftedLastPath (Base := Base) (Fiber := Fiber) x y z q) (liftedInput (Base := Base) (Fiber := Fiber) x y b)

private def codomainFamily {X Y : Type u} {e : X ≃ Y} {C : X → Type u} {D : Y → Type u}
    (_ : FamilyComparison e C D) : Y → Type u := D

/-- The target family is exactly the codomain of the constructed comparison. -/
def targetEtaType : TargetPathBase f x y → Type u :=
  codomainFamily (selectedEtaFamilyComparison (Base := Base) (Fiber := Fiber) f g x y z q b)

/-- The target section in that inherited apd comparison is the independently
constructed eta section, by its derived comparison above. -/
theorem apdEta_target_section :
    (⟨(selectedEtaFamilyComparison (Base := Base) (Fiber := Fiber) f g x y z q b).term
      (selectedEtaSection (Base := Base) (Fiber := Fiber) x y z q b).down⟩ :
      (S).Section _ _) = targetEtaSection f g x y z q b := by
  apply ULift.ext
  exact selectedEtaSection_compare f g x y z q b

/-- Builder output: the families and actual selected eta sections with their
constructed comparison. This is not an ordinary-author compatibility input. -/
structure EtaPresentation (eP : PathBase x y ≃ TargetPathBase f x y) where
  sourceFamily : PathBase x y → Type u
  targetFamily : TargetPathBase f x y → Type u
  families : FamilyComparison eP sourceFamily targetFamily
  source : (S).Section (PathBase x y) sourceFamily
  target : (S).Section (TargetPathBase f x y) targetFamily
  compared : families.term source.down = target.down

def etaPresentation : EtaPresentation (Base := Base) (Fiber := Fiber) f x y (f.identityFamily x y).total where
  sourceFamily := selectedEtaType (Base := Base) (Fiber := Fiber) x y z q b
  targetFamily := targetEtaType f g x y z q b
  families := selectedEtaFamilyComparison (Base := Base) (Fiber := Fiber) f g x y z q b
  source := selectedEtaSection (Base := Base) (Fiber := Fiber) x y z q b
  target := targetEtaSection f g x y z q b
  compared := selectedEtaSection_compare f g x y z q b

/-- The compared action retains the independently constructed target section
and the transported source of its identity family. -/
def EtaPresentation.DependentActionCompared
    (E : EtaPresentation (Base := Base) (Fiber := Fiber) f x y (f.identityFamily x y).total)
    (p p' : (γ : Γ) → PathFamily x y γ)
    (h : (S).Section Γ ((S).identity (PathFamily x y) ⟨p⟩ ⟨p'⟩)) : Prop :=
    HEq (⟨(apdFamily (f.identityFamily x y) E.families p p' h E.source).term
      (apdValue M (PathFamily x y) E.sourceFamily ⟨p⟩ ⟨p'⟩ h E.source).down⟩ : (S).Section Δ _)
      (apdValue M (PathFamily (f.term x) (f.term y)) E.targetFamily
        ⟨(f.identityFamily x y).term p⟩ ⟨(f.identityFamily x y).term p'⟩
        (path (f.identityFamily x y) p p' h) E.target)

theorem EtaPresentation.dependentAction_compare
    (E : EtaPresentation (Base := Base) (Fiber := Fiber) f x y (f.identityFamily x y).total)
    (p p' : (γ : Γ) → PathFamily x y γ)
    (h : (S).Section Γ ((S).identity (PathFamily x y) ⟨p⟩ ⟨p'⟩)) :
    E.DependentActionCompared f x y p p' h :=
  apd_compare_section (f.identityFamily x y) E.families p p' h E.source E.target E.compared

/-- The selected eta section and its dependent action inherit the constructed
presentation comparison. The source of apd still contains transport in K. -/
theorem apdEta_compare
    (p p' : (γ : Γ) → PathFamily x y γ)
    (h : (S).Section Γ ((S).identity (PathFamily x y) ⟨p⟩ ⟨p'⟩)) :
    (etaPresentation f g x y z q b).DependentActionCompared f x y p p' h :=
  (etaPresentation f g x y z q b).dependentAction_compare f x y p p' h

end CertificateSection
end SquareKit.Internal.DependentJudgments.NativeDerivedComparisons
