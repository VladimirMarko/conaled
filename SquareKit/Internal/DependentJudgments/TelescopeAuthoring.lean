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
end SquareKit.Internal.DependentJudgments.Contextual.TelescopePresentation
