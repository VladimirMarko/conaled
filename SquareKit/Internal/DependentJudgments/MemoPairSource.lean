import SquareKit.Internal.DependentJudgments.MemoPair
import SquareKit.Internal.DependentJudgments.Sigma.Recovery
import SquareKit.Internal.DependentJudgments.DerivedPathSemantics

/-! Object pair introduction for the memo's value and chosen certificate.
The old contextual arguments are embedded unchanged into the sum extension. -/
namespace SquareKit.Internal.DependentJudgments.MemoPair
open GuardedTheory
set_option backward.isDefEq.respectTransparency false
variable {V : Type} {Ω : List (Contextual.Judgment V)}

abbrev sourceCertificateFamily (g a c : Contextual.Expression V) :=
  Contextual.identity (Contextual.subTy a (Contextual.weaken g a))
    (Contextual.generic g a) (Contextual.subTm c (Contextual.weaken g a))

abbrev sourcePair (g a c v η : Contextual.Expression V) : Sigma.Expression V :=
  Sigma.pair (g.inl Sigma.extraSignature) (a.inl Sigma.extraSignature)
    ((sourceCertificateFamily g a c).inl Sigma.extraSignature)
    (v.inl Sigma.extraSignature) (η.inl Sigma.extraSignature)

variable {g a c v η : Contextual.Expression V}

def sourceCertificateFamily_typed (hc : Contextual.Tm (Ω := Ω) g a c) :
    Contextual.Ty (Ω := Ω) (Contextual.extend g a) (sourceCertificateFamily g a c) :=
  hc.family.generic.identity (hc.substitute hc.family.weaken)

def sourceCertificateFamily_at (hc : Contextual.Tm (Ω := Ω) g a c)
    (hv : Contextual.Tm (Ω := Ω) g a v) :
    Contextual.Equal (Ω := Ω)
      (Contextual.subTy (sourceCertificateFamily g a c) (Contextual.sectionSub g a v))
      (Contextual.identity a v c) :=
  (hc.family.generic.identitySub (hc.substitute hc.family.weaken) hv.section).transitive
    (Contextual.Equal.identity (hc.family.weakenSection hv) hv.sectionGeneric
      (hc.weakenSection hv))

noncomputable def sourcePair_typed (hc : Contextual.Tm (Ω := Ω) g a c)
    (hv : Contextual.Tm (Ω := Ω) g a v)
    (hη : Contextual.Tm (Ω := Ω) g (Contextual.identity a v c) η) :
    Sigma.Tm (Ω := Ω.map (Atom.inl Sigma.extraSignature)) (g.inl Sigma.extraSignature)
      (Sigma.sigma (a.inl Sigma.extraSignature)
        ((sourceCertificateFamily g a c).inl Sigma.extraSignature)) (sourcePair g a c v η) :=
  by
    apply Sigma.Tm.pair
    · convert Sigma.retain hc.family using 1
      apply congrArg (Atom.pred _); funext i
      fin_cases i <;> rfl
    · convert Sigma.retain (sourceCertificateFamily_typed hc) using 1
      apply congrArg (Atom.pred _)
      funext i
      fin_cases i
      · apply congrArg (Term.app (S := Sigma.signature) (.inl (.inl .extend)))
        funext j
        fin_cases j <;> rfl
      · rfl
    · convert Sigma.retain hv using 1
      apply congrArg (Atom.pred _); funext i
      fin_cases i <;> rfl
    · convert Sigma.retain (hη.convert (sourceCertificateFamily_at hc hv).symmetric) using 1
      apply congrArg (Atom.pred _)
      funext i
      fin_cases i
      · rfl
      · apply congrArg (Term.app (S := Sigma.signature) (.inl (.inl .subTy)))
        funext j
        fin_cases j
        · rfl
        · apply congrArg (Term.app (S := Sigma.signature) (.inl (.inl .pair)))
          funext k
          fin_cases k
          · rfl
          · apply congrArg (Term.app (S := Sigma.signature) (.inl (.inl .id)))
            funext l
            fin_cases l
            rfl
          · rfl
      · rfl

end SquareKit.Internal.DependentJudgments.MemoPair
