import SquareKit.Internal.DependentJudgments.FiniteTailTranslation
import SquareKit.Internal.DependentJudgments.LiftFunctoriality

/-! Author operations for the existing finite-telescope presentation theory.
These import derived contextual rules through the existing theory embedding;
no rule, semantic assumption, or object-language constructor is added. -/
noncomputable section
namespace SquareKit.Internal.DependentJudgments.Contextual.TelescopePresentation
open GuardedTheory
set_option backward.isDefEq.respectTransparency false
variable {V : Type} {Ω : List (Judgment V)}
variable {Γ Δ Θ A B x y t u σ τ T D d : Expression V}

abbrev Ctx (Γ : Expression V) := Derivation theory Ω (context Γ)
abbrev Ty (Γ A : Expression V) := Derivation theory Ω (family Γ A)
abbrev Tm (Γ A t : Expression V) := Derivation theory Ω (term Γ A t)
abbrev Sub (Δ Γ σ : Expression V) := Derivation theory Ω (substitution Δ Γ σ)
abbrev Equal (s t : Expression V) := Derivation theory Ω (.eq s t)

namespace Ty
def extend (h : Ty (Ω := Ω) Γ A) : Ctx (Ω := Ω) (Contextual.extend Γ A) :=
  unary (Contextual.Ty.extend (.hypothesis List.mem_cons_self)) h
def context (h : Ty (Ω := Ω) Γ A) : Ctx (Ω := Ω) Γ :=
  unary (Contextual.Ty.context (.hypothesis List.mem_cons_self)) h
def weaken (h : Ty (Ω := Ω) Γ A) : Sub (Ω := Ω) (Contextual.extend Γ A) Γ (Contextual.weaken Γ A) :=
  unary (Contextual.Ty.weaken (.hypothesis List.mem_cons_self)) h
def generic (h : Ty (Ω := Ω) Γ A) :
    Tm (Ω := Ω) (Contextual.extend Γ A) (subTy A (Contextual.weaken Γ A)) (Contextual.generic Γ A) :=
  unary (Contextual.Ty.generic (.hypothesis List.mem_cons_self)) h
def substitute (h : Ty (Ω := Ω) Γ A) (hs : Sub (Ω := Ω) Δ Γ σ) : Ty (Ω := Ω) Δ (subTy A σ) :=
  binary (Contextual.Ty.substitute (.hypothesis List.mem_cons_self) (.hypothesis (List.mem_cons_of_mem _ List.mem_cons_self))) h hs
def subComp (h : Ty (Ω := Ω) Γ A) (hs : Sub (Ω := Ω) Δ Γ σ) (ht : Sub (Ω := Ω) Θ Δ τ) :
    Equal (Ω := Ω) (subTy (subTy A σ) τ) (subTy A (Contextual.comp σ τ)) :=
  ternary (Contextual.Ty.subComp (.hypothesis List.mem_cons_self) (.hypothesis (List.mem_cons_of_mem _ List.mem_cons_self)) (.hypothesis (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ List.mem_cons_self)))) h hs ht
def subId (h : Ty (Ω := Ω) Γ A) : Equal (Ω := Ω) (subTy A (identitySub Γ)) A :=
  unary (Contextual.Ty.subId (.hypothesis List.mem_cons_self)) h
def recontext (h : Ty (Ω := Ω) Γ A) (e : Equal (Ω := Ω) Γ Δ) : Ty (Ω := Ω) Δ A :=
  binary (Contextual.Ty.recontext (.hypothesis List.mem_cons_self) (.hypothesis (List.mem_cons_of_mem _ List.mem_cons_self))) h e
def weakenPair (h : Ty (Ω := Ω) Γ A) (hs : Sub (Ω := Ω) Δ Γ σ)
    (ht : Tm (Ω := Ω) Δ (subTy A σ) t) :
    Equal (Ω := Ω) (Contextual.comp (Contextual.weaken Γ A) (Contextual.pair A σ t)) σ :=
  ternary (Contextual.Ty.weakenPair (.hypothesis List.mem_cons_self) (.hypothesis (List.mem_cons_of_mem _ List.mem_cons_self)) (.hypothesis (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ List.mem_cons_self)))) h hs ht
def variablePair (h : Ty (Ω := Ω) Γ A) (hs : Sub (Ω := Ω) Δ Γ σ)
    (ht : Tm (Ω := Ω) Δ (subTy A σ) t) :
    Equal (Ω := Ω) (subTm (Contextual.generic Γ A) (Contextual.pair A σ t)) t :=
  ternary (Contextual.Ty.variablePair (.hypothesis List.mem_cons_self) (.hypothesis (List.mem_cons_of_mem _ List.mem_cons_self)) (.hypothesis (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ List.mem_cons_self)))) h hs ht
end Ty
namespace Tm
def family (h : Tm (Ω := Ω) Γ A t) : Ty (Ω := Ω) Γ A :=
  unary (Contextual.Tm.family (.hypothesis List.mem_cons_self)) h
def substitute (h : Tm (Ω := Ω) Γ A t) (hs : Sub (Ω := Ω) Δ Γ σ) :
    Tm (Ω := Ω) Δ (subTy A σ) (subTm t σ) :=
  binary (Contextual.Tm.substitute (.hypothesis List.mem_cons_self) (.hypothesis (List.mem_cons_of_mem _ List.mem_cons_self))) h hs
def convert (h : Tm (Ω := Ω) Γ A t) (e : Equal (Ω := Ω) A B) : Tm (Ω := Ω) Γ B t :=
  binary (Contextual.Tm.convert (.hypothesis List.mem_cons_self) (.hypothesis (List.mem_cons_of_mem _ List.mem_cons_self))) h e
def recontext (h : Tm (Ω := Ω) Γ A t) (e : Equal (Ω := Ω) Γ Δ) : Tm (Ω := Ω) Δ A t :=
  binary (Contextual.Tm.recontext (.hypothesis List.mem_cons_self) (.hypothesis (List.mem_cons_of_mem _ List.mem_cons_self))) h e
def changeTerm (h : Tm (Ω := Ω) Γ A t) (e : Equal (Ω := Ω) t u) : Tm (Ω := Ω) Γ A u :=
  binary (Contextual.Tm.changeTerm (.hypothesis List.mem_cons_self) (.hypothesis (List.mem_cons_of_mem _ List.mem_cons_self))) h e
def identity (h : Tm (Ω := Ω) Γ A x) (k : Tm (Ω := Ω) Γ A y) : Ty (Ω := Ω) Γ (Contextual.identity A x y) :=
  binary (Contextual.Tm.identity (.hypothesis List.mem_cons_self) (.hypothesis (List.mem_cons_of_mem _ List.mem_cons_self))) h k
def reflexivity (h : Tm (Ω := Ω) Γ A x) : Tm (Ω := Ω) Γ (Contextual.identity A x x) (Contextual.reflexivity A x) :=
  unary (Contextual.Tm.reflexivity (.hypothesis List.mem_cons_self)) h
def subComp (h : Tm (Ω := Ω) Γ A t) (hs : Sub (Ω := Ω) Δ Γ σ) (ht : Sub (Ω := Ω) Θ Δ τ) :
    Equal (Ω := Ω) (subTm (subTm t σ) τ) (subTm t (Contextual.comp σ τ)) :=
  ternary (Contextual.Tm.subComp (.hypothesis List.mem_cons_self) (.hypothesis (List.mem_cons_of_mem _ List.mem_cons_self)) (.hypothesis (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ List.mem_cons_self)))) h hs ht
def subId (h : Tm (Ω := Ω) Γ A t) : Equal (Ω := Ω) (subTm t (identitySub Γ)) t :=
  unary (Contextual.Tm.subId (.hypothesis List.mem_cons_self)) h
def identitySub (h : Tm (Ω := Ω) Γ A x) (k : Tm (Ω := Ω) Γ A y) (hs : Sub (Ω := Ω) Δ Γ σ) :
    Equal (Ω := Ω) (subTy (Contextual.identity A x y) σ)
      (Contextual.identity (subTy A σ) (subTm x σ) (subTm y σ)) :=
  ternary (Contextual.Tm.identitySub (.hypothesis List.mem_cons_self) (.hypothesis (List.mem_cons_of_mem _ List.mem_cons_self)) (.hypothesis (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ List.mem_cons_self)))) h k hs
end Tm
namespace Ctx
def identity (h : Ctx (Ω := Ω) Γ) : Sub (Ω := Ω) Γ Γ (identitySub Γ) :=
  unary (Contextual.Ctx.identity (.hypothesis List.mem_cons_self)) h
end Ctx
namespace Sub
def comp (hs : Sub (Ω := Ω) Δ Γ σ) (ht : Sub (Ω := Ω) Θ Δ τ) : Sub (Ω := Ω) Θ Γ (Contextual.comp σ τ) :=
  binary (Contextual.Sub.comp (.hypothesis List.mem_cons_self) (.hypothesis (List.mem_cons_of_mem _ List.mem_cons_self))) hs ht
def pair (h : Ty (Ω := Ω) Γ A) (hs : Sub (Ω := Ω) Δ Γ σ) (ht : Tm (Ω := Ω) Δ (subTy A σ) t) :
    Sub (Ω := Ω) Δ (Contextual.extend Γ A) (Contextual.pair A σ t) :=
  ternary (Contextual.Sub.pair (.hypothesis List.mem_cons_self) (.hypothesis (List.mem_cons_of_mem _ List.mem_cons_self)) (.hypothesis (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ List.mem_cons_self)))) h hs ht
def resource (hs : Sub (Ω := Ω) Δ Γ σ) (e : Equal (Ω := Ω) Δ Θ) : Sub (Ω := Ω) Θ Γ σ :=
  binary (Contextual.Sub.resource (.hypothesis List.mem_cons_self) (.hypothesis (List.mem_cons_of_mem _ List.mem_cons_self))) hs e
def retarget (hs : Sub (Ω := Ω) Δ Γ σ) (e : Equal (Ω := Ω) Γ Θ) : Sub (Ω := Ω) Δ Θ σ :=
  binary (Contextual.Sub.retarget (.hypothesis List.mem_cons_self) (.hypothesis (List.mem_cons_of_mem _ List.mem_cons_self))) hs e
end Sub
namespace Equal
def subTy (h : Equal (Ω := Ω) A B) (k : Equal (Ω := Ω) σ τ) : Equal (Ω := Ω) (Contextual.subTy A σ) (Contextual.subTy B τ) :=
  binary (Contextual.Equal.subTy (.hypothesis List.mem_cons_self) (.hypothesis (List.mem_cons_of_mem _ List.mem_cons_self))) h k
def subTm (h : Equal (Ω := Ω) t u) (k : Equal (Ω := Ω) σ τ) : Equal (Ω := Ω) (Contextual.subTm t σ) (Contextual.subTm u τ) :=
  binary (Contextual.Equal.subTm (.hypothesis List.mem_cons_self) (.hypothesis (List.mem_cons_of_mem _ List.mem_cons_self))) h k
def comp (h : Equal (Ω := Ω) x y) (k : Equal (Ω := Ω) σ τ) : Equal (Ω := Ω) (Contextual.comp x σ) (Contextual.comp y τ) :=
  binary (Contextual.Equal.comp (.hypothesis List.mem_cons_self) (.hypothesis (List.mem_cons_of_mem _ List.mem_cons_self))) h k
def identity (h : Equal (Ω := Ω) A B) (k : Equal (Ω := Ω) x y) (l : Equal (Ω := Ω) t u) :
    Equal (Ω := Ω) (Contextual.identity A x t) (Contextual.identity B y u) :=
  ternary (Contextual.Equal.identity (.hypothesis List.mem_cons_self) (.hypothesis (List.mem_cons_of_mem _ List.mem_cons_self)) (.hypothesis (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ List.mem_cons_self)))) h k l
end Equal

namespace Tm
def path (hx : Tm (Ω := Ω) Γ A x) : Ctx (Ω := Ω) (Contextual.path A x) :=
  unary (Contextual.Tm.path (.hypothesis List.mem_cons_self)) hx
def pathFamily (hx : Tm (Ω := Ω) Γ A x) : Ty (Ω := Ω) (Contextual.extend Γ A) (Contextual.pathFamily Γ A x) :=
  unary (Contextual.Tm.pathFamily (.hypothesis List.mem_cons_self)) hx
def pathDef (hx : Tm (Ω := Ω) Γ A x) : Equal (Ω := Ω) (Contextual.path A x)
    (Contextual.extend (Contextual.extend Γ A) (Contextual.pathFamily Γ A x)) :=
  unary (Contextual.Tm.pathDef (.hypothesis List.mem_cons_self)) hx
def pathProjection (hx : Tm (Ω := Ω) Γ A x) : Sub (Ω := Ω) (Contextual.path A x)
    (Contextual.extend Γ A) (Contextual.weaken (Contextual.extend Γ A) (Contextual.pathFamily Γ A x)) :=
  unary (Contextual.Tm.pathProjection (.hypothesis List.mem_cons_self)) hx
def root (hx : Tm (Ω := Ω) Γ A x) : Sub (Ω := Ω) Γ (Contextual.path A x) (Contextual.root A x) :=
  unary (Contextual.Tm.root (.hypothesis List.mem_cons_self)) hx
def «section» (hx : Tm (Ω := Ω) Γ A x) : Sub (Ω := Ω) Γ (Contextual.extend Γ A) (sectionSub Γ A x) :=
  unary (Contextual.Tm.section (.hypothesis List.mem_cons_self)) hx
def rootProjection (hx : Tm (Ω := Ω) Γ A x) : Equal (Ω := Ω)
    (Contextual.comp (Contextual.weaken (Contextual.extend Γ A) (Contextual.pathFamily Γ A x)) (Contextual.root A x))
    (sectionSub Γ A x) :=
  unary (Contextual.Tm.rootProjection (.hypothesis List.mem_cons_self)) hx
def weakenSection (ht : Tm (Ω := Ω) Γ B t) (hx : Tm (Ω := Ω) Γ A x) : Equal (Ω := Ω)
    (subTm (subTm t (Contextual.weaken Γ A)) (sectionSub Γ A x)) t :=
  binary (Contextual.Tm.weakenSection (.hypothesis List.mem_cons_self)
    (.hypothesis (List.mem_cons_of_mem _ List.mem_cons_self))) ht hx
def sectionGeneric (hx : Tm (Ω := Ω) Γ A x) : Equal (Ω := Ω)
    (subTm (Contextual.generic Γ A) (sectionSub Γ A x)) x :=
  unary (Contextual.Tm.sectionGeneric (.hypothesis List.mem_cons_self)) hx
def endpoint (hx : Tm (Ω := Ω) Γ A x) (hy : Tm (Ω := Ω) Γ A y)
    (hp : Tm (Ω := Ω) Γ (Contextual.identity A x y) t) : Sub (Ω := Ω) Γ (Contextual.path A x) (Contextual.endpoint Γ A x y t) :=
  ternary (Contextual.Tm.endpoint (.hypothesis List.mem_cons_self)
    (.hypothesis (List.mem_cons_of_mem _ List.mem_cons_self))
    (.hypothesis (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ List.mem_cons_self)))) hx hy hp
end Tm
abbrev Tel (n : Nat) (Γ T : Expression V) := Derivation theory Ω (telescope n Γ T)
namespace Tm
def j (hx : Tm (Ω := Ω) Γ A x) (hT : Tel (Ω := Ω) n (Contextual.path A x) T)
    (hD : Ty (Ω := Ω) (total T) D)
    (hd : Tm (Ω := Ω) (total (pullback T (Contextual.root A x))) (subTy D (rootTail A x T)) d) :
    Tm (Ω := Ω) (total T) D (Contextual.j A x T D d) :=
  quaternary (Contextual.Tm.j (.hypothesis List.mem_cons_self)
    (.hypothesis (List.mem_cons_of_mem _ List.mem_cons_self))
    (.hypothesis (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ List.mem_cons_self)))
    (.hypothesis (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ List.mem_cons_self))))) hx hT hD hd
def jBeta (hx : Tm (Ω := Ω) Γ A x) (hT : Tel (Ω := Ω) n (Contextual.path A x) T)
    (hD : Ty (Ω := Ω) (total T) D)
    (hd : Tm (Ω := Ω) (total (pullback T (Contextual.root A x))) (subTy D (rootTail A x T)) d) :
    Equal (Ω := Ω) (subTm (Contextual.j A x T D d) (rootTail A x T)) d :=
  quaternary (Contextual.Tm.jBeta (.hypothesis List.mem_cons_self)
    (.hypothesis (List.mem_cons_of_mem _ List.mem_cons_self))
    (.hypothesis (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ List.mem_cons_self)))
    (.hypothesis (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ List.mem_cons_self))))) hx hT hD hd
end Tm

namespace Sub
def lift (hs : Sub (Ω := Ω) Δ Γ σ) (hA : Ty (Ω := Ω) Γ A) :
    Sub (Ω := Ω) (Contextual.extend Δ (subTy A σ)) (Contextual.extend Γ A) (liftSyntax Δ A σ) :=
  binary (Contextual.Sub.lift (.hypothesis List.mem_cons_self)
    (.hypothesis (List.mem_cons_of_mem _ List.mem_cons_self))) hs hA
def liftWeaken (hs : Sub (Ω := Ω) Δ Γ σ) (hA : Ty (Ω := Ω) Γ A) : Equal (Ω := Ω)
    (Contextual.comp (Contextual.weaken Γ A) (liftSyntax Δ A σ)) (Contextual.comp σ (Contextual.weaken Δ (subTy A σ))) :=
  binary (Contextual.Sub.liftWeaken (.hypothesis List.mem_cons_self)
    (.hypothesis (List.mem_cons_of_mem _ List.mem_cons_self))) hs hA
def liftGeneric (hs : Sub (Ω := Ω) Δ Γ σ) (hA : Ty (Ω := Ω) Γ A) : Equal (Ω := Ω)
    (subTm (Contextual.generic Γ A) (liftSyntax Δ A σ)) (Contextual.generic Δ (subTy A σ)) :=
  binary (Contextual.Sub.liftGeneric (.hypothesis List.mem_cons_self)
    (.hypothesis (List.mem_cons_of_mem _ List.mem_cons_self))) hs hA
def assoc {Ξ υ : Expression V} (hs : Sub (Ω := Ω) Δ Γ σ) (ht : Sub (Ω := Ω) Θ Δ τ)
    (hv : Sub (Ω := Ω) Ξ Θ υ) : Equal (Ω := Ω) (Contextual.comp (Contextual.comp σ τ) υ) (Contextual.comp σ (Contextual.comp τ υ)) :=
  ternary (Contextual.Sub.assoc (.hypothesis List.mem_cons_self)
    (.hypothesis (List.mem_cons_of_mem _ List.mem_cons_self))
    (.hypothesis (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ List.mem_cons_self)))) hs ht hv
def idLeft (hs : Sub (Ω := Ω) Δ Γ σ) : Equal (Ω := Ω) (Contextual.comp (identitySub Γ) σ) σ :=
  unary (Contextual.Sub.idLeft (.hypothesis List.mem_cons_self)) hs
def idRight (hs : Sub (Ω := Ω) Δ Γ σ) : Equal (Ω := Ω) (Contextual.comp σ (identitySub Δ)) σ :=
  unary (Contextual.Sub.idRight (.hypothesis List.mem_cons_self)) hs
end Sub
namespace Ty
def weakenSection (ht : Ty (Ω := Ω) Γ B) (hx : Tm (Ω := Ω) Γ A x) : Equal (Ω := Ω)
    (subTy (subTy B (Contextual.weaken Γ A)) (sectionSub Γ A x)) B :=
  binary (Contextual.Ty.weakenSection (.hypothesis List.mem_cons_self)
    (.hypothesis (List.mem_cons_of_mem _ List.mem_cons_self))) ht hx
end Ty

namespace Ty
def weakenLift (hB : Ty (Ω := Ω) Γ B) (hA : Ty (Ω := Ω) Γ A)
    (hs : Sub (Ω := Ω) Δ Γ σ) : Equal (Ω := Ω)
    (subTy (subTy B (Contextual.weaken Γ A)) (liftSyntax Δ A σ))
    (subTy (subTy B σ) (Contextual.weaken Δ (subTy A σ))) :=
  (hB.subComp hA.weaken (hs.lift hA)).transitive
    ((Equal.subTy (.reflexive _) (hs.liftWeaken hA)).transitive
      (hB.subComp hs (hA.substitute hs).weaken).symmetric)
end Ty

namespace Tm
/-- Substitution beneath a dependent binder is derived from its display square. -/
def weakenLift (ht : Tm (Ω := Ω) Γ B t) (hA : Ty (Ω := Ω) Γ A)
    (hs : Sub (Ω := Ω) Δ Γ σ) : Equal (Ω := Ω)
    (subTm (subTm t (Contextual.weaken Γ A)) (liftSyntax Δ A σ))
    (subTm (subTm t σ) (Contextual.weaken Δ (subTy A σ))) :=
  (ht.subComp hA.weaken (hs.lift hA)).transitive
    ((Equal.subTm (.reflexive _) (hs.liftWeaken hA)).transitive
      (ht.subComp hs (hA.substitute hs).weaken).symmetric)
/-- A source conversion remains usable beneath a dependent binder after
substitution. No decoded semantic equality is supplied by the caller. -/
def weakenLiftEqual (ht : Tm (Ω := Ω) Γ B t) (hu : Tm (Ω := Ω) Γ B u)
    (hA : Ty (Ω := Ω) Γ A) (hs : Sub (Ω := Ω) Δ Γ σ)
    (e : Equal (Ω := Ω) (subTm t σ) (subTm u σ)) : Equal (Ω := Ω)
    (subTm (subTm t (Contextual.weaken Γ A)) (liftSyntax Δ A σ))
    (subTm (subTm u (Contextual.weaken Γ A)) (liftSyntax Δ A σ)) :=
  (ht.weakenLift hA hs).transitive
    ((Equal.subTm e (.reflexive _)).transitive (hu.weakenLift hA hs).symmetric)
end Tm

namespace Tm
def endpointProjection (hx : Tm (Ω := Ω) Γ A x) (hy : Tm (Ω := Ω) Γ A y)
    (hp : Tm (Ω := Ω) Γ (Contextual.identity A x y) t) : Equal (Ω := Ω)
    (Contextual.comp (Contextual.weaken (Contextual.extend Γ A) (Contextual.pathFamily Γ A x))
      (Contextual.endpoint Γ A x y t)) (sectionSub Γ A y) :=
  ternary (Contextual.Tm.endpointProjection (.hypothesis List.mem_cons_self)
    (.hypothesis (List.mem_cons_of_mem _ List.mem_cons_self))
    (.hypothesis (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ List.mem_cons_self)))) hx hy hp
/-- Lookup of an earlier term after appending a dependent argument. -/
def weakenPair (ht : Tm (Ω := Ω) Γ B u) (hA : Ty (Ω := Ω) Γ A)
    (hs : Sub (Ω := Ω) Δ Γ σ) (hv : Tm (Ω := Ω) Δ (subTy A σ) t) : Equal (Ω := Ω)
    (subTm (subTm u (Contextual.weaken Γ A)) (Contextual.pair A σ t)) (subTm u σ) :=
  (ht.subComp hA.weaken (Sub.pair hA hs hv)).transitive
    (Equal.subTm (.reflexive _) (hA.weakenPair hs hv))
end Tm
namespace Ty
def weakenPairType (hB : Ty (Ω := Ω) Γ B) (hA : Ty (Ω := Ω) Γ A)
    (hs : Sub (Ω := Ω) Δ Γ σ) (hv : Tm (Ω := Ω) Δ (subTy A σ) t) : Equal (Ω := Ω)
    (subTy (subTy B (Contextual.weaken Γ A)) (Contextual.pair A σ t)) (subTy B σ) :=
  (hB.subComp hA.weaken (Sub.pair hA hs hv)).transitive
    (Equal.subTy (.reflexive _) (hA.weakenPair hs hv))
end Ty

namespace Equal
def pair {a a' b b' c c' : Expression V} (ha : Equal (Ω := Ω) a a')
    (hb : Equal (Ω := Ω) b b') (hc : Equal (Ω := Ω) c c') :
    Equal (Ω := Ω) (Contextual.pair a b c) (Contextual.pair a' b' c') :=
  ternary (Contextual.Equal.pair (.hypothesis List.mem_cons_self)
    (.hypothesis (List.mem_cons_of_mem _ List.mem_cons_self))
    (.hypothesis (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ List.mem_cons_self)))) ha hb hc
end Equal
namespace Ty
def pairComp (hA : Ty (Ω := Ω) Γ A) (hs : Sub (Ω := Ω) Δ Γ σ)
    (ht : Tm (Ω := Ω) Δ (subTy A σ) t) (hτ : Sub (Ω := Ω) Θ Δ τ) : Equal (Ω := Ω)
    (Contextual.comp (Contextual.pair A σ t) τ)
    (Contextual.pair A (Contextual.comp σ τ) (subTm t τ)) :=
  quaternary (Contextual.Ty.pairComp (.hypothesis List.mem_cons_self)
    (.hypothesis (List.mem_cons_of_mem _ List.mem_cons_self))
    (.hypothesis (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ List.mem_cons_self)))
    (.hypothesis (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ List.mem_cons_self))))) hA hs ht hτ
end Ty
namespace Tm
def rootDef (hx : Tm (Ω := Ω) Γ A x) : Equal (Ω := Ω) (Contextual.root A x)
    (Contextual.pair (Contextual.pathFamily Γ A x) (sectionSub Γ A x) (Contextual.reflexivity A x)) :=
  unary (Contextual.Tm.rootDef (.hypothesis List.mem_cons_self)) hx
end Tm
namespace Sub
/-- A display-map lift commutes with pairing, including dependent components. -/
def liftPair (hs : Sub (Ω := Ω) Δ Γ σ) (hA : Ty (Ω := Ω) Γ A)
    (hτ : Sub (Ω := Ω) Θ Δ τ) (hv : Tm (Ω := Ω) Θ (subTy (subTy A σ) τ) t) :
    Equal (Ω := Ω) (Contextual.comp (liftSyntax Δ A σ) (Contextual.pair (subTy A σ) τ t))
      (Contextual.pair A (Contextual.comp σ τ) t) := by
  let hB := hA.substitute hs
  let hp := Sub.pair hB hτ hv
  have first := hA.pairComp (hs.comp hB.weaken)
    (hB.generic.convert (hA.subComp hs hB.weaken)) hp
  have base := (hs.assoc hB.weaken hp).transitive
    (Equal.comp (.reflexive _) (hB.weakenPair hτ hv))
  exact first.transitive (Equal.pair (.reflexive _) base (hB.variablePair hτ hv))
end Sub

/-- Import a five-premise derived source operation into the named extension. -/
def quinary {a b c d e f : Judgment V}
    (h : Derivation Contextual.theory [a,b,c,d,e] f)
    (ha : Derivation theory Ω a) (hb : Derivation theory Ω b) (hc : Derivation theory Ω c)
    (hd : Derivation theory Ω d) (he : Derivation theory Ω e) : Derivation theory Ω f :=
  importProof h (by
    classical
    intro j hj
    simp at hj
    by_cases h : j = a
    · subst j; exact ha
    · by_cases h' : j = b
      · subst j; exact hb
      · by_cases h'' : j = c
        · subst j; exact hc
        · by_cases hlastCase : j = d
          · subst j; exact hd
          · have hlast := (((hj.resolve_left h).resolve_left h').resolve_left h'').resolve_left hlastCase
            subst j; exact he)

namespace Equal
/-- Congruence of a recipe is derived structurally from generated equalities. -/
def recipe {W : Type} (r : Expression W) (s t : W → Expression V)
    (h : ∀ w, Equal (Ω := Ω) (s w) (t w)) : Equal (Ω := Ω) (r.subst s) (r.subst t) := by
  induction r with
  | leaf w => exact h w
  | node op args ih => exact Derivation.congruence op ih
def extend {a a' b b' : Expression V} (ha : Equal (Ω := Ω) a a') (hb : Equal (Ω := Ω) b b') :
    Equal (Ω := Ω) (Contextual.extend a b) (Contextual.extend a' b') :=
  binary (Contextual.Equal.extend (.hypothesis List.mem_cons_self)
    (.hypothesis (List.mem_cons_of_mem _ List.mem_cons_self))) ha hb
def weaken {a a' b b' : Expression V} (ha : Equal (Ω := Ω) a a') (hb : Equal (Ω := Ω) b b') :
    Equal (Ω := Ω) (Contextual.weaken a b) (Contextual.weaken a' b') :=
  binary (Contextual.Equal.weaken (.hypothesis List.mem_cons_self)
    (.hypothesis (List.mem_cons_of_mem _ List.mem_cons_self))) ha hb

def generic {a a' b b' : Expression V} (ha : Equal (Ω := Ω) a a') (hb : Equal (Ω := Ω) b b') :
    Equal (Ω := Ω) (Contextual.generic a b) (Contextual.generic a' b') :=
  binary (Contextual.Equal.generic (.hypothesis List.mem_cons_self)
    (.hypothesis (List.mem_cons_of_mem _ List.mem_cons_self))) ha hb
def liftSyntax {a a' b b' c c' : Expression V} (ha : Equal (Ω := Ω) a a')
    (hb : Equal (Ω := Ω) b b') (hc : Equal (Ω := Ω) c c') :
    Equal (Ω := Ω) (Contextual.liftSyntax a b c) (Contextual.liftSyntax a' b' c') := by
  unfold Contextual.liftSyntax
  exact Equal.pair hb (Equal.comp hc (Equal.weaken ha (Equal.subTy hb hc)))
    (Equal.generic ha (Equal.subTy hb hc))
def telNil {a a' : Expression V} (ha : Equal (Ω := Ω) a a') :
    Equal (Ω := Ω) (Contextual.telNil a) (Contextual.telNil a') := by
  have e := recipe (Contextual.telNil (.var 0) : Expression (Fin 1)) ![a] ![a']
    (Fin.cases ha (fun i => nomatch i))
  simpa using e
def telCons {a a' b b' : Expression V} (ha : Equal (Ω := Ω) a a')
    (hb : Equal (Ω := Ω) b b') :
    Equal (Ω := Ω) (Contextual.telCons a b) (Contextual.telCons a' b') := by
  have e := recipe (Contextual.telCons (.var 0) (.var 1) : Expression (Fin 2)) ![a,b] ![a',b']
    (Fin.cases ha (Fin.cases hb (fun i => nomatch i)))
  simpa using e

def total {a b : Expression V} (h : Equal (Ω := Ω) a b) :
    Equal (Ω := Ω) (Contextual.total a) (Contextual.total b) :=
  unary (Contextual.Equal.total (.hypothesis List.mem_cons_self)) h
def rootTail {a a' x x' t t' : Expression V} (ha : Equal (Ω := Ω) a a')
    (hx : Equal (Ω := Ω) x x') (ht : Equal (Ω := Ω) t t') :
    Equal (Ω := Ω) (Contextual.rootTail a x t) (Contextual.rootTail a' x' t') :=
  Derivation.congruence (T := theory) (Sum.inr Operation.rootTail)
    (Fin.cases ha (Fin.cases hx (Fin.cases ht (fun i => nomatch i))))
def j {a a' x x' t t' d d' b b' : Expression V} (ha : Equal (Ω := Ω) a a')
    (hx : Equal (Ω := Ω) x x') (ht : Equal (Ω := Ω) t t')
    (hd : Equal (Ω := Ω) d d') (hb : Equal (Ω := Ω) b b') :
    Equal (Ω := Ω) (Contextual.j a x t d b) (Contextual.j a' x' t' d' b') :=
  Derivation.congruence (T := theory) (Sum.inr Operation.j)
    (Fin.cases ha (Fin.cases hx (Fin.cases ht (Fin.cases hd (Fin.cases hb (fun i => nomatch i))))))

def reflexivity {a a' x x' : Expression V} (ha : Equal (Ω := Ω) a a') (hx : Equal (Ω := Ω) x x') :
    Equal (Ω := Ω) (Contextual.reflexivity a x) (Contextual.reflexivity a' x') :=
  binary (Contextual.Equal.reflexivity (.hypothesis List.mem_cons_self)
    (.hypothesis (List.mem_cons_of_mem _ List.mem_cons_self))) ha hx

end Equal
namespace Tm
def pathSub (hx : Tm (Ω := Ω) Γ A x) (hs : Sub (Ω := Ω) Δ Γ σ) :
    Sub (Ω := Ω) (Contextual.path (subTy A σ) (subTm x σ)) (Contextual.path A x) (Contextual.pathSub A x σ) :=
  binary (Contextual.Tm.pathSub (.hypothesis List.mem_cons_self)
    (.hypothesis (List.mem_cons_of_mem _ List.mem_cons_self))) hx hs
def pathSubProjection (hx : Tm (Ω := Ω) Γ A x) (hs : Sub (Ω := Ω) Δ Γ σ) :
    Equal (Ω := Ω) (comp (Contextual.weaken (Contextual.extend Γ A) (Contextual.pathFamily Γ A x)) (Contextual.pathSub A x σ))
      (comp (liftSyntax Δ A σ) (Contextual.weaken (Contextual.extend Δ (subTy A σ)) (Contextual.pathFamily Δ (subTy A σ) (subTm x σ)))) :=
  binary (Contextual.Tm.pathSubProjection (.hypothesis List.mem_cons_self)
    (.hypothesis (List.mem_cons_of_mem _ List.mem_cons_self))) hx hs
def rootTail (hx : Tm (Ω := Ω) Γ A x) (hT : Tel (Ω := Ω) n (Contextual.path A x) T) :
    Sub (Ω := Ω) (total (pullback T (Contextual.root A x))) (total T) (Contextual.rootTail A x T) :=
  binary (Contextual.Tm.rootTail (.hypothesis List.mem_cons_self)
    (.hypothesis (List.mem_cons_of_mem _ List.mem_cons_self))) hx hT
def pathTailMap (hx : Tm (Ω := Ω) Γ A x) (hT : Tel (Ω := Ω) n (Contextual.path A x) T)
    (hs : Sub (Ω := Ω) Δ Γ σ) :
    Sub (Ω := Ω) (total (Contextual.pathTail A x T σ)) (total T) (Contextual.pathTailMap A x T σ) :=
  ternary (Contextual.Tm.pathTailMap (.hypothesis List.mem_cons_self)
    (.hypothesis (List.mem_cons_of_mem _ List.mem_cons_self))
    (.hypothesis (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ List.mem_cons_self)))) hx hT hs
def branchMap (hx : Tm (Ω := Ω) Γ A x) (hT : Tel (Ω := Ω) n (Contextual.path A x) T)
    (hs : Sub (Ω := Ω) Δ Γ σ) :
    Sub (Ω := Ω) (total (pullback (Contextual.pathTail A x T σ) (Contextual.root (subTy A σ) (subTm x σ))))
      (total (pullback T (Contextual.root A x))) (Contextual.branchMap A x T σ) := by
  have e := Derivation.rule (T := theory) (Γ := Ω) (Sum.inl (Sum.inr (.branchMap n))) ![Γ,A,x,T,Δ,σ]
    (Fin.cases (by simpa [Tm, theory, Contextual.theory, Theory.extend, Contextual.rule] using hx)
      (Fin.cases (by simpa [Tel, theory, Contextual.theory, Theory.extend, Contextual.rule] using hT)
        (Fin.cases (by simpa [Sub, theory, Contextual.theory, Theory.extend, Contextual.rule] using hs) (fun i => nomatch i))))
  simpa [Sub, theory, Contextual.theory, Theory.extend, Contextual.rule] using e

def pathSubEndpoint {p : Expression V} (hx : Tm (Ω := Ω) Γ A x) (hy : Tm (Ω := Ω) Γ A y)
    (hp : Tm (Ω := Ω) Γ (Contextual.identity A x y) p) (hs : Sub (Ω := Ω) Δ Γ σ) : Equal (Ω := Ω)
    (comp (Contextual.pathSub A x σ) (Contextual.endpoint Δ (subTy A σ) (subTm x σ) (subTm y σ) (subTm p σ)))
    (comp (Contextual.endpoint Γ A x y p) σ) :=
  quaternary (Contextual.Tm.pathSubEndpoint (.hypothesis List.mem_cons_self)
    (.hypothesis (List.mem_cons_of_mem _ List.mem_cons_self))
    (.hypothesis (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ List.mem_cons_self)))
    (.hypothesis (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ List.mem_cons_self))))) hx hy hp hs

def pathFamilySection (hx : Tm (Ω := Ω) Γ A x) (hy : Tm (Ω := Ω) Γ A y) :
    Equal (Ω := Ω) (subTy (Contextual.pathFamily Γ A x) (sectionSub Γ A y)) (Contextual.identity A x y) :=
  binary (Contextual.Tm.pathFamilySection (.hypothesis List.mem_cons_self)
    (.hypothesis (List.mem_cons_of_mem _ List.mem_cons_self))) hx hy
def reflSub (hx : Tm (Ω := Ω) Γ A x) (hs : Sub (Ω := Ω) Δ Γ σ) :
    Equal (Ω := Ω) (subTm (Contextual.reflexivity A x) σ) (Contextual.reflexivity (subTy A σ) (subTm x σ)) :=
  binary (Contextual.Tm.reflSub (.hypothesis List.mem_cons_self)
    (.hypothesis (List.mem_cons_of_mem _ List.mem_cons_self))) hx hs

def jSub (hx : Tm (Ω := Ω) Γ A x) (hT : Tel (Ω := Ω) n (Contextual.path A x) T)
    (hD : Ty (Ω := Ω) (total T) D)
    (hd : Tm (Ω := Ω) (total (pullback T (Contextual.root A x))) (subTy D (Contextual.rootTail A x T)) d)
    (hs : Sub (Ω := Ω) Δ Γ σ) :
    Equal (Ω := Ω) (subTm (Contextual.j A x T D d) (Contextual.pathTailMap A x T σ))
      (Contextual.j (subTy A σ) (subTm x σ) (Contextual.pathTail A x T σ)
        (subTy D (Contextual.pathTailMap A x T σ)) (reindexBranch A x T σ D d)) :=
  quinary (Contextual.Tm.jSub (.hypothesis List.mem_cons_self)
    (.hypothesis (List.mem_cons_of_mem _ List.mem_cons_self))
    (.hypothesis (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ List.mem_cons_self)))
    (.hypothesis (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ List.mem_cons_self))))
    (.hypothesis (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ List.mem_cons_self)))))) hx hT hD hd hs
end Tm
end SquareKit.Internal.DependentJudgments.Contextual.TelescopePresentation
