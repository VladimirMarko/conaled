import Examples.AssemblyCertificateTransport
import SquareKit.AssemblyFamilySubstitution

/-! A jointly tracked capacity-varying section and its uniform extension. -/
namespace CompleteCertificateFamily
open Realizability Realizability.Assembly AssemblyCertificateFamily

abbrev natAssembly := encoded Nat

noncomputable def parameterSequence : Hom natAssembly partialSequences :=
  curry ((fst natAssembly natAssembly).comp (programLiftUnit natAssembly))

noncomputable def parameterSection (T : Assembly) : Hom (prod natAssembly T) (boundedFamily (Hom.id natAssembly)) :=
  factor _ (pair (fst natAssembly T) ((fst natAssembly T).comp parameterSequence)) (fun x => by
    intro k v hv
    have he := (curry_apply ((fst natAssembly natAssembly).comp (programLiftUnit natAssembly)) x.1 k).symm.trans hv
    have hx : x.1 = v := Option.some.inj he
    exact (congrArg (fun a : Nat => v < a+k+1) hx).mpr (by omega))

theorem parameterSection_base (T : Assembly) :
    (parameterSection T).comp (familyBase (Hom.id natAssembly)) = fst natAssembly T := Hom.ext fun _ => rfl

theorem parameter_extension :
    extendFamily (Hom.id natAssembly) (parameterSection iterationCuts) (parameterSection_base _) =
      parameterSection finalCuts :=
  family_extension_unique _ _ _ (extendFamily_base _ _ _) (parameterSection_base _)
    (extendFamily_restrict _ _ _)

example : ((familyComparison (Hom.id natAssembly)).hom.toFun
    ((extendFamily (Hom.id natAssembly) (parameterSection iterationCuts) (parameterSection_base _)).toFun
      ((3 : Nat), ⟨none⟩))).2.val 2 =
      Part.some (⟨⟨3, by decide⟩, [2,1,0], rfl⟩ : VaryingPartialCertificates.Cert 3 2) := by
  let q := (extendFamily (Hom.id natAssembly) (parameterSection iterationCuts) (parameterSection_base _)).toFun
    ((3 : Nat), ⟨none⟩)
  have hc : q.val.2.toFun (2 : Nat) = some (3 : Nat) :=
    congrArg (fun h => (h.toFun ((3 : Nat), ⟨none⟩)).val.2.toFun (2 : Nat)) parameter_extension
  obtain ⟨a,ha,hv⟩ := (recover_graph (⟨q.val.2,q.property⟩ : (boundedSequences 3).Carrier) 2 3).mpr hc
  have he : a = (⟨⟨3, by decide⟩, [2,1,0], rfl⟩ : VaryingPartialCertificates.Cert 3 2) :=
    VaryingPartialCertificates.Cert.ext (Fin.ext hv)
  exact Part.eq_some_iff.mpr (he ▸ ha)

/-- The theorem applies to every tracked parameter map, with no surjectivity requirement. -/
example {Δ : Assembly} (f : Hom Δ natAssembly) :
    reindexFamilySection (Hom.id natAssembly) f finalCuts
        (extendFamily (Hom.id natAssembly) (parameterSection iterationCuts) (parameterSection_base _))
        (extendFamily_base _ _ _) =
      extendFamily (f.comp (Hom.id natAssembly))
        (reindexFamilySection (Hom.id natAssembly) f iterationCuts (parameterSection iterationCuts)
          (parameterSection_base _))
        (reindexFamilySection_base _ _ _ _ _) :=
  extendFamily_reindex _ _ _ _

end CompleteCertificateFamily
