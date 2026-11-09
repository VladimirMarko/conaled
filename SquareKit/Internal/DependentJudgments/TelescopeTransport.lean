import SquareKit.Internal.DependentJudgments.TelescopeAuthoring

/-! Existing transport operations imported into the named presentation theory. -/
noncomputable section
namespace SquareKit.Internal.DependentJudgments.Contextual.TelescopePresentation
open GuardedTheory
set_option backward.isDefEq.respectTransparency false
variable {V : Type} {Ω : List (Judgment V)}
variable {Γ Δ A B x y p u σ : Expression V}
def senary {a b c d e f g : Judgment V}
    (h : Derivation Contextual.theory [a,b,c,d,e,f] g)
    (ha : Derivation theory Ω a) (hb : Derivation theory Ω b) (hc : Derivation theory Ω c)
    (hd : Derivation theory Ω d) (he : Derivation theory Ω e) (hf : Derivation theory Ω f) : Derivation theory Ω g :=
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
        · by_cases h3 : j = d
          · subst j; exact hd
          · by_cases h4 : j = e
            · subst j; exact he
            · have hlast := ((((hj.resolve_left h).resolve_left h').resolve_left h'').resolve_left h3).resolve_left h4
              subst j; exact hf)

def Tm.transport (hB : Ty (Ω := Ω) (Contextual.extend Γ A) B)
    (hx : Tm (Ω := Ω) Γ A x)
    (hy : Tm (Ω := Ω) Γ A y)
    (hp : Tm (Ω := Ω) Γ (Contextual.identity A x y) p)
    (hu : Tm (Ω := Ω) Γ (subTy B (sectionSub Γ A x)) u) :
    Tm (Ω := Ω) Γ (subTy B (sectionSub Γ A y)) (Contextual.transport Γ A B x y p u) :=
  quinary (Contextual.Tm.transport
    (.hypothesis List.mem_cons_self)
    (.hypothesis (List.mem_cons_of_mem _ List.mem_cons_self))
    (.hypothesis (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ List.mem_cons_self)))
    (.hypothesis (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ List.mem_cons_self))))
    (.hypothesis (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ List.mem_cons_self)))))) hB hx hy hp hu

def Tm.transportRefl (hB : Ty (Ω := Ω) (Contextual.extend Γ A) B)
    (hx : Tm (Ω := Ω) Γ A x)
    (hu : Tm (Ω := Ω) Γ (subTy B (sectionSub Γ A x)) u) :
    Equal (Ω := Ω) (Contextual.transport Γ A B x x (Contextual.reflexivity A x) u) u :=
  ternary (Contextual.Tm.transportRefl
    (.hypothesis List.mem_cons_self)
    (.hypothesis (List.mem_cons_of_mem _ List.mem_cons_self))
    (.hypothesis (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ List.mem_cons_self)))) hB hx hu

def Tm.transportSub (hB : Ty (Ω := Ω) (Contextual.extend Γ A) B)
    (hx : Tm (Ω := Ω) Γ A x)
    (hy : Tm (Ω := Ω) Γ A y)
    (hp : Tm (Ω := Ω) Γ (Contextual.identity A x y) p)
    (hu : Tm (Ω := Ω) Γ (subTy B (sectionSub Γ A x)) u)
    (hs : Sub (Ω := Ω) Δ Γ σ) :
    Equal (Ω := Ω) (subTm (Contextual.transport Γ A B x y p u) σ) (Contextual.transport Δ (subTy A σ) (subTy B (liftSyntax Δ A σ)) (subTm x σ) (subTm y σ) (subTm p σ) (subTm u σ)) :=
  senary (Contextual.Tm.transportSub
    (.hypothesis List.mem_cons_self)
    (.hypothesis (List.mem_cons_of_mem _ List.mem_cons_self))
    (.hypothesis (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ List.mem_cons_self)))
    (.hypothesis (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ List.mem_cons_self))))
    (.hypothesis (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ List.mem_cons_self)))))
    (.hypothesis (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ List.mem_cons_self))))))) hB hx hy hp hu hs

def Ty.sectionLift (hB : Ty (Ω := Ω) (Contextual.extend Γ A) B)
    (hs : Sub (Ω := Ω) Δ Γ σ)
    (hx : Tm (Ω := Ω) Γ A x) :
    Equal (Ω := Ω) (subTy (subTy B (liftSyntax Δ A σ)) (sectionSub Δ (subTy A σ) (subTm x σ))) (subTy (subTy B (sectionSub Γ A x)) σ) :=
  ternary (Contextual.Ty.sectionLift
    (.hypothesis List.mem_cons_self)
    (.hypothesis (List.mem_cons_of_mem _ List.mem_cons_self))
    (.hypothesis (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ List.mem_cons_self)))) hB hs hx

end SquareKit.Internal.DependentJudgments.Contextual.TelescopePresentation
