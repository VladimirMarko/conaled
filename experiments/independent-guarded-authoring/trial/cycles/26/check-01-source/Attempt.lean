import SquareKit.Internal.DependentJudgments.PresentedPath
import SquareKit.Internal.DependentJudgments.PresentedSoundness
import Examples.GuardedLeftConcatenation

/-! Independent #108 attempt. The upstream inv/inv-inv declarations are from
agda-unimath 75518656f287c203b41cb7f71df46e02b987a084, MIT, copyright (c) 2022
Egbert Maarten Rijke. The full notice is retained in experiments/independent-guarded-authoring/trial/inputs/upstream/LICENSE.md. -/
noncomputable section
namespace SquareKit.Internal.DependentJudgments.Contextual.TelescopePresentation.IndependentInv
open GuardedTheory LeftConcatFrame
set_option backward.isDefEq.respectTransparency false
variable {V : Type} {Ω : List (Judgment V)}
variable {Γ Δ A x y p σ D d : Expression V}

-- Generic public based-J operations imported into the named presentation theory.
def basedTyped (hx : Tm (Ω := Ω) Γ A x) (hD : Ty (Ω := Ω) (path A x) D)
    (hd : Tm (Ω := Ω) Γ (subTy D (root A x)) d) :
    Tm (Ω := Ω) (path A x) D (basedJ A x D d) :=
  ternary (Contextual.Tm.basedJ (Γ := Γ) (.hypothesis (by simp)) (.hypothesis (by simp))
    (.hypothesis (by simp))) hx hD hd

def basedBeta (hx : Tm (Ω := Ω) Γ A x) (hD : Ty (Ω := Ω) (path A x) D)
    (hd : Tm (Ω := Ω) Γ (subTy D (root A x)) d) :
    Equal (Ω := Ω) (subTm (basedJ A x D d) (root A x)) d :=
  ternary (Contextual.Tm.basedJBeta (Γ := Γ) (.hypothesis (by simp)) (.hypothesis (by simp))
    (.hypothesis (by simp))) hx hD hd

def basedSub (hx : Tm (Ω := Ω) Γ A x) (hD : Ty (Ω := Ω) (path A x) D)
    (hd : Tm (Ω := Ω) Γ (subTy D (root A x)) d) (hs : Sub (Ω := Ω) Δ Γ σ) :
    Equal (Ω := Ω) (subTm (basedJ A x D d) (pathSub A x σ))
      (basedJ (subTy A σ) (subTm x σ) (subTy D (pathSub A x σ)) (subTm d σ)) :=
  quaternary (Contextual.Tm.basedJSub (Γ := Γ) (Δ := Δ) (.hypothesis (by simp)) (.hypothesis (by simp))
    (.hypothesis (by simp)) (.hypothesis (by simp))) hx hD hd hs

abbrev reverseMotive (Γ A x : Expression V) :=
  Contextual.identity (pathType Γ A x) (moving Γ A x) (fixed Γ A x)
abbrev reverseGeneric (Γ A x : Expression V) :=
  basedJ A x (reverseMotive Γ A x) (Contextual.reflexivity A x)
abbrev reverse (Γ A x y p : Expression V) :=
  subTm (reverseGeneric Γ A x) (Contextual.endpoint Γ A x y p)

def motiveTyped (hx : Tm (Ω := Ω) Γ A x) :
    Ty (Ω := Ω) (path A x) (reverseMotive Γ A x) :=
  (movingTyped hx).identity (fixedTyped hx)

def motiveRoot (hx : Tm (Ω := Ω) Γ A x) :
    Equal (Ω := Ω) (subTy (reverseMotive Γ A x) (root A x)) (Contextual.identity A x x) :=
  ((movingTyped hx).identitySub (fixedTyped hx) hx.root).transitive
    (Equal.identity (PresentedPath.pathTypeRoot hx) (movingRoot hx) (fixedRoot hx))

def branchTyped (hx : Tm (Ω := Ω) Γ A x) :
    Tm (Ω := Ω) Γ (subTy (reverseMotive Γ A x) (root A x)) (Contextual.reflexivity A x) :=
  hx.reflexivity.convert (motiveRoot hx).symmetric

def genericTyped (hx : Tm (Ω := Ω) Γ A x) :
    Tm (Ω := Ω) (path A x) (reverseMotive Γ A x) (reverseGeneric Γ A x) :=
  basedTyped hx (motiveTyped hx) (branchTyped hx)

def reverseTyped (hx : Tm (Ω := Ω) Γ A x) (hy : Tm (Ω := Ω) Γ A y)
    (hp : Tm (Ω := Ω) Γ (Contextual.identity A x y) p) :
    Tm (Ω := Ω) Γ (Contextual.identity A y x) (reverse Γ A x y p) :=
  ((genericTyped hx).substitute (hx.endpoint hy hp)).convert
    (((movingTyped hx).identitySub (fixedTyped hx) (hx.endpoint hy hp)).transitive
      (Equal.identity (LeftConcatArguments.pathTypeAt hx hy hp)
        (LeftConcatArguments.movingAt hx hy hp) (LeftConcatArguments.fixedAt hx hy hp)))

def reverseRefl (hx : Tm (Ω := Ω) Γ A x) :
    Equal (Ω := Ω) (reverse Γ A x x (Contextual.reflexivity A x)) (Contextual.reflexivity A x) :=
  (Equal.subTm (.reflexive _) hx.rootDef.symmetric).transitive
    (basedBeta hx (motiveTyped hx) (branchTyped hx))


def genericSub (hx : Tm (Ω := Ω) Γ A x) (hs : Sub (Ω := Ω) Δ Γ σ) :
    Equal (Ω := Ω) (subTm (reverseGeneric Γ A x) (pathSub A x σ))
      (reverseGeneric Δ (subTy A σ) (subTm x σ)) :=
  (basedSub hx (motiveTyped hx) (branchTyped hx) hs).transitive
    (Equal.j (.reflexive _) (.reflexive _) (.reflexive _)
      (((movingTyped hx).identitySub (fixedTyped hx) (hx.pathSub hs)).transitive
        (Equal.identity (LeftConcatReindex.pathTypeSub hx hs)
          (LeftConcatReindex.movingSub hx hs) (LeftConcatReindex.fixedSub hx hs)))
      (hx.reflSub hs))

def reverseSub (hx : Tm (Ω := Ω) Γ A x) (hy : Tm (Ω := Ω) Γ A y)
    (hp : Tm (Ω := Ω) Γ (Contextual.identity A x y) p) (hs : Sub (Ω := Ω) Δ Γ σ) :
    Equal (Ω := Ω) (subTm (reverse Γ A x y p) σ)
      (reverse Δ (subTy A σ) (subTm x σ) (subTm y σ) (subTm p σ)) :=
  ((genericTyped hx).subComp (hx.endpoint hy hp) hs).transitive
    ((Equal.subTm (.reflexive _) (hx.pathSubEndpoint hy hp hs).symmetric).transitive
      (((genericTyped hx).subComp (hx.pathSub hs)
        ((hx.substitute hs).endpoint (hy.substitute hs)
          ((hp.substitute hs).convert (hx.identitySub hy hs)))).symmetric.transitive
        (Equal.subTm (genericSub hx hs) (.reflexive _))))

theorem reflexivity_subst {W : Type} (s : V → Expression W) (a x : Expression V) :
    (Contextual.reflexivity a x).subst s = Contextual.reflexivity (a.subst s) (x.subst s) := by
  apply congrArg (@FinitaryTerm.node signature.Operation signature.arity W (.inr .reflexivity))
  funext i
  fin_cases i <;> rfl

theorem reverse_subst {W : Type} (s : V → Expression W) (g a x y p : Expression V) :
    (reverse g a x y p).subst s = reverse (g.subst s) (a.subst s) (x.subst s) (y.subst s) (p.subst s) := by
  simp only [reverse, reverseGeneric, reverseMotive, basedJ, pathType, moving, fixed,
    LeftConcatFrame.pathProjection, Contextual.endpoint, Contextual.pathFamily, Contextual.sectionSub,
    LeftConcatRecipe.subTm_subst, LeftConcatRecipe.subTy_subst, LeftConcatRecipe.path_subst,
    LeftConcatRecipe.telNil_subst, LeftConcatRecipe.pair_subst, LeftConcatRecipe.extend_subst,
    LeftConcatRecipe.weaken_subst, LeftConcatRecipe.generic_subst, LeftConcatRecipe.identity_subst,
    LeftConcatRecipe.identitySub_subst, LeftConcatRecipe.j_subst, reflexivity_subst]

def reverseCongr {g g' a a' x x' y y' p p' : Expression V}
    (hg : Equal (Ω := Ω) g g') (ha : Equal (Ω := Ω) a a')
    (hx : Equal (Ω := Ω) x x') (hy : Equal (Ω := Ω) y y') (hp : Equal (Ω := Ω) p p') :
    Equal (Ω := Ω) (reverse g a x y p) (reverse g' a' x' y' p') := by
  have e := Equal.recipe (reverse (.var 0) (.var 1) (.var 2) (.var 3) (.var 4) : Expression (Fin 5))
    ![g,a,x,y,p] ![g',a',x',y',p']
    (Fin.cases hg (Fin.cases ha (Fin.cases hx (Fin.cases hy (Fin.cases hp (fun i => nomatch i))))))
  rw [reverse_subst, reverse_subst] at e
  simpa [Term.subst, Term.var, FinitaryTerm.bind] using e


abbrev doubled (Γ A x y p : Expression V) := reverse Γ A y x (reverse Γ A x y p)
def doubledTyped (hx : Tm (Ω := Ω) Γ A x) (hy : Tm (Ω := Ω) Γ A y)
    (hp : Tm (Ω := Ω) Γ (Contextual.identity A x y) p) :
    Tm (Ω := Ω) Γ (Contextual.identity A x y) (doubled Γ A x y p) :=
  reverseTyped hy hx (reverseTyped hx hy hp)
def doubledSub (hx : Tm (Ω := Ω) Γ A x) (hy : Tm (Ω := Ω) Γ A y)
    (hp : Tm (Ω := Ω) Γ (Contextual.identity A x y) p) (hs : Sub (Ω := Ω) Δ Γ σ) :
    Equal (Ω := Ω) (subTm (doubled Γ A x y p) σ)
      (doubled Δ (subTy A σ) (subTm x σ) (subTm y σ) (subTm p σ)) :=
  (reverseSub hy hx (reverseTyped hx hy hp) hs).transitive
    (reverseCongr (.reflexive _) (.reflexive _) (.reflexive _) (.reflexive _)
      (reverseSub hx hy hp hs))
def doubledCongr {g g' a a' x x' y y' p p' : Expression V}
    (hg : Equal (Ω := Ω) g g') (ha : Equal (Ω := Ω) a a')
    (hx : Equal (Ω := Ω) x x') (hy : Equal (Ω := Ω) y y') (hp : Equal (Ω := Ω) p p') :
    Equal (Ω := Ω) (doubled g a x y p) (doubled g' a' x' y' p') :=
  reverseCongr hg ha hy hx (reverseCongr hg ha hx hy hp)
def doubledRefl (hx : Tm (Ω := Ω) Γ A x) :
    Equal (Ω := Ω) (doubled Γ A x x (Contextual.reflexivity A x)) (Contextual.reflexivity A x) :=
  (reverseCongr (.reflexive _) (.reflexive _) (.reflexive _) (.reflexive _)
    (reverseRefl hx)).transitive (reverseRefl hx)

open PresentedPath
abbrev genericDouble (Γ A x : Expression V) :=
  doubled (path A x) (pathType Γ A x) (fixed Γ A x) (moving Γ A x) (pathProof Γ A x)
abbrev involutionMotive (Γ A x : Expression V) :=
  Contextual.identity (Contextual.identity (pathType Γ A x) (fixed Γ A x) (moving Γ A x))
    (genericDouble Γ A x) (pathProof Γ A x)
def doubleTyped (hx : Tm (Ω := Ω) Γ A x) :=
  doubledTyped (fixedTyped hx) (movingTyped hx) (pathProofTyped hx)
def involutionMotiveTyped (hx : Tm (Ω := Ω) Γ A x) :
    Ty (Ω := Ω) (path A x) (involutionMotive Γ A x) :=
  (doubleTyped hx).identity (pathProofTyped hx)
def doubleRoot (hx : Tm (Ω := Ω) Γ A x) :
    Equal (Ω := Ω) (subTm (genericDouble Γ A x) (root A x)) (Contextual.reflexivity A x) :=
  (doubledSub (fixedTyped hx) (movingTyped hx) (pathProofTyped hx) hx.root).transitive
    ((doubledCongr (.reflexive _) (pathTypeRoot hx) (fixedRoot hx) (movingRoot hx)
      (pathProofRoot hx)).transitive (doubledRefl hx))
def involutionRoot (hx : Tm (Ω := Ω) Γ A x) :
    Equal (Ω := Ω) (subTy (involutionMotive Γ A x) (root A x))
      (Contextual.identity (Contextual.identity A x x) (Contextual.reflexivity A x) (Contextual.reflexivity A x)) :=
  ((doubleTyped hx).identitySub (pathProofTyped hx) hx.root).transitive
    (Equal.identity
      (((fixedTyped hx).identitySub (movingTyped hx) hx.root).transitive
        (Equal.identity (pathTypeRoot hx) (fixedRoot hx) (movingRoot hx)))
      (doubleRoot hx) (pathProofRoot hx))
def involutionBranch (hx : Tm (Ω := Ω) Γ A x) :
    Tm (Ω := Ω) Γ (subTy (involutionMotive Γ A x) (root A x))
      (Contextual.reflexivity (Contextual.identity A x x) (Contextual.reflexivity A x)) :=
  hx.reflexivity.reflexivity.convert (involutionRoot hx).symmetric
abbrev involutionGeneric (Γ A x : Expression V) :=
  basedJ A x (involutionMotive Γ A x)
    (Contextual.reflexivity (Contextual.identity A x x) (Contextual.reflexivity A x))
def involutionGenericTyped (hx : Tm (Ω := Ω) Γ A x) :
    Tm (Ω := Ω) (path A x) (involutionMotive Γ A x) (involutionGeneric Γ A x) :=
  basedTyped hx (involutionMotiveTyped hx) (involutionBranch hx)

def pathProofAt (hx : Tm (Ω := Ω) Γ A x) (hy : Tm (Ω := Ω) Γ A y)
    (hp : Tm (Ω := Ω) Γ (Contextual.identity A x y) p) :
    Equal (Ω := Ω) (subTm (pathProof Γ A x) (Contextual.endpoint Γ A x y p)) p :=
  hx.pathFamily.variablePair hy.section (hp.convert (hx.pathFamilySection hy).symmetric)
def doubleAt (hx : Tm (Ω := Ω) Γ A x) (hy : Tm (Ω := Ω) Γ A y)
    (hp : Tm (Ω := Ω) Γ (Contextual.identity A x y) p) :
    Equal (Ω := Ω) (subTm (genericDouble Γ A x) (Contextual.endpoint Γ A x y p))
      (doubled Γ A x y p) :=
  (doubledSub (fixedTyped hx) (movingTyped hx) (pathProofTyped hx) (hx.endpoint hy hp)).transitive
    (doubledCongr (.reflexive _) (LeftConcatArguments.pathTypeAt hx hy hp)
      (LeftConcatArguments.fixedAt hx hy hp) (LeftConcatArguments.movingAt hx hy hp)
      (pathProofAt hx hy hp))
def involutionAt (hx : Tm (Ω := Ω) Γ A x) (hy : Tm (Ω := Ω) Γ A y)
    (hp : Tm (Ω := Ω) Γ (Contextual.identity A x y) p) :
    Equal (Ω := Ω) (subTy (involutionMotive Γ A x) (Contextual.endpoint Γ A x y p))
      (Contextual.identity (Contextual.identity A x y) (doubled Γ A x y p) p) :=
  ((doubleTyped hx).identitySub (pathProofTyped hx) (hx.endpoint hy hp)).transitive
    (Equal.identity
      (((fixedTyped hx).identitySub (movingTyped hx) (hx.endpoint hy hp)).transitive
        (Equal.identity (LeftConcatArguments.pathTypeAt hx hy hp)
          (LeftConcatArguments.fixedAt hx hy hp) (LeftConcatArguments.movingAt hx hy hp)))
      (doubleAt hx hy hp) (pathProofAt hx hy hp))
abbrev involution (Γ A x y p : Expression V) :=
  subTm (involutionGeneric Γ A x) (Contextual.endpoint Γ A x y p)
/-- Generated arbitrary-path inv-inv, retaining the selected certificate. -/
def involutionTyped (hx : Tm (Ω := Ω) Γ A x) (hy : Tm (Ω := Ω) Γ A y)
    (hp : Tm (Ω := Ω) Γ (Contextual.identity A x y) p) :
    Tm (Ω := Ω) Γ (Contextual.identity (Contextual.identity A x y) (doubled Γ A x y p) p)
      (involution Γ A x y p) :=
  ((involutionGenericTyped hx).substitute (hx.endpoint hy hp)).convert (involutionAt hx hy hp)


/-- Reindex the same certificate, normalizing both endpoints by derived laws. -/
def involutionReindexed (hx : Tm (Ω := Ω) Γ A x) (hy : Tm (Ω := Ω) Γ A y)
    (hp : Tm (Ω := Ω) Γ (Contextual.identity A x y) p) (hs : Sub (Ω := Ω) Δ Γ σ) :
    Tm (Ω := Ω) Δ
      (Contextual.identity (Contextual.identity (subTy A σ) (subTm x σ) (subTm y σ))
        (doubled Δ (subTy A σ) (subTm x σ) (subTm y σ) (subTm p σ)) (subTm p σ))
      (subTm (involution Γ A x y p) σ) :=
  ((involutionTyped hx hy hp).substitute hs).convert
    (((doubledTyped hx hy hp).identitySub hp hs).transitive
      (Equal.identity (hx.identitySub hy hs) (doubledSub hx hy hp hs) (.reflexive _)))

/-- The reflexive specialization retains the source-selected second identity. -/
def involutionRefl (hx : Tm (Ω := Ω) Γ A x) :
    Equal (Ω := Ω) (involution Γ A x x (Contextual.reflexivity A x))
      (Contextual.reflexivity (Contextual.identity A x x) (Contextual.reflexivity A x)) :=
  (Equal.subTm (.reflexive _) hx.rootDef.symmetric).transitive
    (basedBeta hx (involutionMotiveTyped hx) (involutionBranch hx))

namespace Semantics
open CategoryTheory PathTransport.GroupoidModel PathTransport.Typed
set_option backward.defeqAttrib.useBackward true
universe u
variable (C : Type u) [Groupoid.{u} C] (B : C ⥤ Type u)
local notation "M" => Instance.fullModel C B

/-- Pointwise reversal retains the actual arrow in an arbitrary family. -/
def inverseSection {G : Grpd.{u,u}} (A : G ⥤ Grpd.{u,u}) (x y : Section A)
    (p : Section (identityFamily A x y)) : Section (identityFamily A y x) where
  obj g := ⟨inv (p.obj g).as⟩
  map {g h} f := Discrete.eqToHom (by
    have hp := Discrete.eq_of_hom (p.map f)
    change inv (x.map f) ≫ (A.map f).map (p.obj g).as ≫ y.map f = (p.obj h).as at hp
    change inv (y.map f) ≫ (A.map f).map (inv (p.obj g).as) ≫ x.map f = inv (p.obj h).as
    rw [← hp]
    simp)
  map_id _ := Subsingleton.elim _ _
  map_comp _ _ := Subsingleton.elim _ _

abbrev reverseRecipe : Expression (Fin 5) := reverse (.var 0) (.var 1) (.var 2) (.var 3) (.var 4)
def environment {G : Grpd.{u,u}} (A : G ⥤ Grpd.{u,u}) (x y : Section A)
    (p : Section (identityFamily A x y)) : Fin 5 → Value (M).toStructuralModel :=
  ![.context G, .family G A, .term G A ⟨x⟩, .term G A ⟨y⟩,
    .term G (identityFamily A x y) ⟨p⟩]
abbrev paths {G : Grpd.{u,u}} (A : G ⥤ Grpd.{u,u}) (x : Section A) : Grpd.{u,u} :=
  (M).toStructuralModel.pathContext A ⟨x⟩
abbrev carrier {G : Grpd.{u,u}} (A : G ⥤ Grpd.{u,u}) (x : Section A) :=
  PathComparison.retract A x ⋙ A
abbrev first {G : Grpd.{u,u}} (A : G ⥤ Grpd.{u,u}) (x : Section A) :=
  x.reindex (PathComparison.retract A x)
abbrev second {G : Grpd.{u,u}} (A : G ⥤ Grpd.{u,u}) (x : Section A) :=
  («variable» A).reindex (PathTransport.GroupoidModel.weaken (PathComparison.PathFamily A x))
abbrev witness {G : Grpd.{u,u}} (A : G ⥤ Grpd.{u,u}) (x : Section A) :
    Section (identityFamily (carrier A x) (first A x) (second A x)) :=
  «variable» (PathComparison.PathFamily A x)
abbrev motive {G : Grpd.{u,u}} (A : G ⥤ Grpd.{u,u}) (x : Section A) :=
  identityFamily (carrier A x) (second A x) (first A x)
def branch {G : Grpd.{u,u}} (A : G ⥤ Grpd.{u,u}) (x : Section A) :
    (M).Section G ((M).subTy (Γ := paths C B A x) (motive A x) ((M).toStructuralModel.rootSub A ⟨x⟩)) :=
  ⟨reflexivitySection A x⟩
def selected {G : Grpd.{u,u}} (A : G ⥤ Grpd.{u,u}) (x : Section A) :=
  (M).j A ⟨x⟩ .nil (motive A x) (branch C B A x)

theorem motive_eval {G : Grpd.{u,u}} (A : G ⥤ Grpd.{u,u}) (x y : Section A)
    (p : Section (identityFamily A x y)) :
    (reverseMotive (.var 0) (.var 1) (.var 2)).eval (algebra M) (environment C B A x y p) =
      .family (paths C B A x) (motive A x) := by
  simp [reverseMotive, pathType, moving, fixed, LeftConcatFrame.pathProjection,
    Contextual.pathFamily, Term.eval, algebra, operation, DependentJudgments.operation,
    environment, StructuralModel.pathContext, StructuralModel.pathFamily]
  constructor

theorem generic_eval {G : Grpd.{u,u}} (A : G ⥤ Grpd.{u,u}) (x y : Section A)
    (p : Section (identityFamily A x y)) :
    (reverseGeneric (.var 0) (.var 1) (.var 2)).eval (algebra M) (environment C B A x y p) =
      .term (paths C B A x) (motive A x) (selected C B A x) := by
  apply DerivedSemantics.basedJ_eval M _ _ _ _ _ G A ⟨x⟩ (motive A x) (branch C B A x)
  · rfl
  · rfl
  · exact motive_eval C B A x y p
  · simp [Term.eval, algebra, operation, environment]
    constructor <;> rfl

theorem selected_inverse {G : Grpd.{u,u}} (A : G ⥤ Grpd.{u,u}) (x : Section A) :
    (selected C B A x).down = inverseSection (G := paths C B A x) (carrier A x) (first A x) (second A x) (witness A x) := by
  apply Instance.contextualJ_unique
  apply Section.ext_discrete
  intro g
  apply Discrete.ext
  change inv (𝟙 _) = 𝟙 _
  simp

theorem selected_at {G : Grpd.{u,u}} (A : G ⥤ Grpd.{u,u}) (x y : Section A)
    (p : Section (identityFamily A x y)) :
    (M).subTm (selected C B A x) ((M).toStructuralModel.endpointSub A ⟨x⟩ ⟨y⟩ ⟨p⟩) =
      ⟨inverseSection A x y p⟩ := by
  have hs : selected C B A x =
      ⟨inverseSection (G := paths C B A x) (carrier A x) (first A x) (second A x) (witness A x)⟩ :=
    ULift.ext (selected_inverse C B A x)
  rw [hs]
  rfl

theorem reverseRecipe_eval {G : Grpd.{u,u}} (A : G ⥤ Grpd.{u,u}) (x y : Section A)
    (p : Section (identityFamily A x y)) :
    reverseRecipe.eval (algebra M) (environment C B A x y p) =
      .term G (identityFamily A y x) ⟨inverseSection A x y p⟩ := by
  have he := DerivedSemantics.endpoint_eval M (environment C B A x y p)
    (.var 0) (.var 1) (.var 2) (.var 3) (.var 4) G A ⟨x⟩ ⟨y⟩ ⟨p⟩ rfl rfl rfl rfl rfl
  have h := DerivedSemantics.subTm_eval M (environment C B A x y p)
    (reverseGeneric (.var 0) (.var 1) (.var 2)) (Contextual.endpoint (.var 0) (.var 1) (.var 2) (.var 3) (.var 4))
    (paths C B A x) G (motive A x) (selected C B A x) ((M).toStructuralModel.endpointSub A ⟨x⟩ ⟨y⟩ ⟨p⟩)
    (generic_eval C B A x y p) he
  change reverseRecipe.eval (algebra M) (environment C B A x y p) = _ at h
  rw [h]
  apply congrArg (@Value.term (M).toStructuralModel G (identityFamily A y x))
  exact selected_at C B A x y p

theorem reverse_eval {V : Type} (ρ : V → Value (M).toStructuralModel)
    (g a sx sy sp : Expression V) (G : Grpd.{u,u}) (A : G ⥤ Grpd.{u,u})
    (x y : Section A) (p : Section (identityFamily A x y))
    (hg : g.eval (algebra M) ρ = .context G)
    (ha : a.eval (algebra M) ρ = .family G A)
    (hx : sx.eval (algebra M) ρ = .term G A ⟨x⟩)
    (hy : sy.eval (algebra M) ρ = .term G A ⟨y⟩)
    (hp : sp.eval (algebra M) ρ = .term G (identityFamily A x y) ⟨p⟩) :
    (reverse g a sx sy sp).eval (algebra M) ρ =
      .term G (identityFamily A y x) ⟨inverseSection A x y p⟩ := by
  have he : (fun i => (![g,a,sx,sy,sp] i).eval (algebra M) ρ) = environment C B A x y p := by
    funext i
    fin_cases i <;> first | exact hg | exact ha | exact hx | exact hy | exact hp
  have hs : reverseRecipe.subst ![g,a,sx,sy,sp] = reverse g a sx sy sp :=
    reverse_subst _ _ _ _ _ _
  rw [← hs, Term.eval_subst, he]
  exact reverseRecipe_eval C B A x y p

abbrev doubleRecipe : Expression (Fin 5) := doubled (.var 0) (.var 1) (.var 2) (.var 3) (.var 4)
abbrev certificateRecipe : Expression (Fin 5) := involution (.var 0) (.var 1) (.var 2) (.var 3) (.var 4)
abbrev doubleSection {G : Grpd.{u,u}} (A : G ⥤ Grpd.{u,u}) (x y : Section A)
    (p : Section (identityFamily A x y)) := inverseSection A y x (inverseSection A x y p)

theorem double_eval {G : Grpd.{u,u}} (A : G ⥤ Grpd.{u,u}) (x y : Section A)
    (p : Section (identityFamily A x y)) :
    doubleRecipe.eval (algebra M) (environment C B A x y p) =
      .term G (identityFamily A x y) ⟨doubleSection A x y p⟩ :=
  reverse_eval C B (environment C B A x y p) (.var 0) (.var 1) (.var 3) (.var 2)
    reverseRecipe G A y x (inverseSection A x y p) rfl rfl rfl rfl
    (reverseRecipe_eval C B A x y p)

abbrev inputs : List (Contextual.Judgment (Fin 5)) :=
  [term (.var 0) (.var 1) (.var 2), term (.var 0) (.var 1) (.var 3),
    term (.var 0) (Contextual.identity (.var 1) (.var 2) (.var 3)) (.var 4)]
abbrev conclusion : Expression (Fin 5) :=
  Contextual.identity (Contextual.identity (.var 1) (.var 2) (.var 3)) doubleRecipe (.var 4)
def source : Tm (Ω := inputs) (.var 0) conclusion certificateRecipe :=
  involutionTyped (.hypothesis (by simp [inputs])) (.hypothesis (by simp [inputs]))
    (.hypothesis (by simp [inputs]))

theorem inputs_valid {G : Grpd.{u,u}} (A : G ⥤ Grpd.{u,u}) (x y : Section A)
    (p : Section (identityFamily A x y)) :
    ∀ a ∈ inputs, a.eval (TelescopePresentation.model M).toAlgebra (environment C B A x y p) := by
  intro a ha
  simp only [inputs, List.mem_cons, List.not_mem_nil, or_false] at ha
  rcases ha with rfl | rfl | rfl
  · exact ⟨G, A, ⟨x⟩, rfl, rfl, rfl⟩
  · exact ⟨G, A, ⟨y⟩, rfl, rfl, rfl⟩
  · refine ⟨G, identityFamily A x y, ⟨p⟩, rfl, ?_, rfl⟩
    simp [Term.eval, TelescopePresentation.model, algebra, operation, environment]
    rfl

theorem conclusion_eval {G : Grpd.{u,u}} (A : G ⥤ Grpd.{u,u}) (x y : Section A)
    (p : Section (identityFamily A x y)) :
    conclusion.eval (algebra M) (environment C B A x y p) =
      .family G (identityFamily (identityFamily A x y) (doubleSection A x y p) p) := by
  apply DerivedSemantics.identity_eval M _ _ _ _ G (identityFamily A x y)
    ⟨doubleSection A x y p⟩ ⟨p⟩
  · exact DerivedSemantics.identity_eval M _ _ _ _ G A ⟨x⟩ ⟨y⟩ rfl rfl rfl
  · exact double_eval C B A x y p
  · rfl

/-- The witness is the value of the generated source proof, not a replacement proof. -/
theorem certificate_evaluates {G : Grpd.{u,u}} (A : G ⥤ Grpd.{u,u}) (x y : Section A)
    (p : Section (identityFamily A x y)) :
    ∃ selected : (M).Section G (identityFamily (identityFamily A x y) (doubleSection A x y p) p),
      certificateRecipe.eval (algebra M) (environment C B A x y p) =
        .term G (identityFamily (identityFamily A x y) (doubleSection A x y p) p) selected :=
  source.evaluates M (environment C B A x y p) (inputs_valid C B A x y p)
    G (identityFamily (identityFamily A x y) (doubleSection A x y p) p) rfl
    (conclusion_eval C B A x y p)

include C B in
/-- Extract the ordinary arrow equation from that same interpreted source witness. -/
theorem double_inverse_from_source {G : Grpd.{u,u}} (A : G ⥤ Grpd.{u,u}) (x y : Section A)
    (p : Section (identityFamily A x y)) (g : G) : inv (inv (p.obj g).as) = (p.obj g).as := by
  obtain ⟨s, hs⟩ := certificate_evaluates C B A x y p
  exact Discrete.eq_of_hom (s.down.obj g).as


namespace C4Consumers
open Examples.GroupoidTransport Examples.GuardedLeftConcatenation
local notation "N" => Instance.fullModel C4

def observed (B : C4 ⥤ Type) (n : ZMod 4) : Option (Examples.GroupoidTransport.point ⟶ Examples.GroupoidTransport.point) :=
  Option.map (fun t : (N B).Section G (identityFamily (constant C4) base base) =>
    (t.down.obj ⟨PUnit.unit⟩).as)
    ((doubleRecipe.eval (algebra (N B)) (environment C4 B (constant C4) base base (labeled n))).termAt G
      (identityFamily (constant C4) base base))
def observedSingle (B : C4 ⥤ Type) (n : ZMod 4) : Option (Examples.GroupoidTransport.point ⟶ Examples.GroupoidTransport.point) :=
  Option.map (fun t : (N B).Section G (identityFamily (constant C4) base base) =>
    (t.down.obj ⟨PUnit.unit⟩).as)
    ((reverseRecipe.eval (algebra (N B)) (environment C4 B (constant C4) base base (labeled n))).termAt G
      (identityFamily (constant C4) base base))

theorem observed_eq (B : C4 ⥤ Type) (n : ZMod 4) : observed B n = some (label n) := by
  unfold observed
  rw [double_eval]
  simp only [Value.termAt_term, Option.map_some]
  exact congrArg some (double_inverse_from_source C4 B (constant C4) base base (labeled n) ⟨PUnit.unit⟩)

theorem observedSingle_eq (B : C4 ⥤ Type) (n : ZMod 4) : observedSingle B n = some (label (-n)) := by
  unfold observedSingle
  rw [reverseRecipe_eval]
  simp only [Value.termAt_term, Option.map_some]
  simp only [inverseSection, Examples.GuardedLeftConcatenation.labeled, Examples.GroupoidTransport.label, Option.some.injEq]
  apply IsIso.inv_eq_of_hom_inv_id
  change Multiplicative.ofAdd (-n) * Multiplicative.ofAdd n = 1
  exact inv_mul_cancel (Multiplicative.ofAdd n)

/-- Each label has a certificate from the same source proof and its actual evaluation. -/
theorem certified (B : C4 ⥤ Type) (n : ZMod 4) :
    ∃ s : (N B).Section G
        (identityFamily (identityFamily (constant C4) base base)
          (doubleSection (constant C4) base base (labeled n)) (labeled n)),
      certificateRecipe.eval (algebra (N B)) (environment C4 B (constant C4) base base (labeled n)) =
        .term G (identityFamily (identityFamily (constant C4) base base)
          (doubleSection (constant C4) base base (labeled n)) (labeled n)) s ∧
      observed B n = some (label n) := by
  obtain ⟨s, hs⟩ := certificate_evaluates C4 B (constant C4) base base (labeled n)
  exact ⟨s, hs, observed_eq B n⟩

example : observedSingle faithful 1 = some (label 3) := by rw [observedSingle_eq]; rfl
example : observedSingle ineffective 1 = some (label 3) := by rw [observedSingle_eq]; rfl
example : observed faithful 1 = some (label 1) := observed_eq faithful 1
example : observed ineffective 1 = some (label 1) := observed_eq ineffective 1
example (n : ZMod 4) := certified faithful n
example (n : ZMod 4) := certified ineffective n

theorem ineffective_distinct : observed ineffective 1 ≠ observed ineffective 0 := by
  rw [observed_eq, observed_eq]
  intro h
  exact (by decide : (1 : ZMod 4) ≠ 0) (labels_injective (Option.some.inj h))
end C4Consumers
end Semantics

end SquareKit.Internal.DependentJudgments.Contextual.TelescopePresentation.IndependentInv
