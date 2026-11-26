import SquareKit.Internal.Cubical.NaturalUnivalenceLaws
import Examples.CubicalSmallFamilies
import Examples.CubicalNativeUnivalenceTransport
import Examples.CubicalPathConversion

/-! Observations of composed and reversed universe transport, with a varying
finite family and a control separating native paths from host equality. -/
set_option autoImplicit false
set_option warningAsError true
namespace Examples.CompositionalUnivalence
open CategoryTheory SquareKit.Cubical SquareKit.Cubical.Presheaf
open SmallUniverse SmallUniverse.NativeUnivalence
open Examples.CubicalGlue Examples.CubicalUnivalenceTransport

abbrev code (S : Type) := (constantLocal terminal S).code
abbrev nativeMap {S T : Type} (e : S ≃ T) := Raising.map (codeIso e).hom
noncomputable def nativeEquivalence {S T : Type} (e : S ≃ T) :=
  HomotopyEquivalence.ofIso (Raising.iso (codeIso e))
def nativeInput {S : Type} (s : S) := Raising.raiseTerm (input s)
def observe {S : Type} (x : Term (liftedDecode (code S))) : Term (constantFamily terminal S) :=
  Term.map (constantLocal terminal S).decodeCodeIso.hom (Raising.lowerTerm x)

theorem observe_input {S : Type} (s : S) : observe (nativeInput s) = constantSection s :=
  Term.map_iso_roundtrip (constantLocal terminal S).decodeCodeIso.symm (constantSection s)

private theorem input_action {S T : Type} (e : S ≃ T) (s : S) :
    Term.map (codeIso e).hom (input s) = input (e s) := by
  apply Term.map_injective_of_iso (constantLocal terminal T).decodeCodeIso
  exact (codeIso_action e s).trans
    (Term.map_iso_roundtrip (constantLocal terminal T).decodeCodeIso.symm (constantSection (e s))).symm

theorem nativeInput_action {S T : Type} (e : S ≃ T) (s : S) :
    Term.map (nativeMap e) (nativeInput s) = nativeInput (e s) :=
  congrArg Raising.raiseTerm (input_action e s)

theorem observe_path {S : Type} {x y : Term (liftedDecode (code S))}
    (p : Term (homogeneousPath (liftedDecode (code S)) x y)) : observe x = observe y :=
  constantFamily_path_endpoints (homogeneousPathMap (constantLocal terminal S).decodeCodeIso.hom
    (Raising.lowerPath p))

noncomputable def equivalencePath {S T : Type} (e : S ≃ T) :=
  ua (code S) (code T) (nativeMap e) (nativeEquivalence e)

noncomputable def observedConcat {S T V : Type} (e : S ≃ T) (d : T ≃ V) (s : S) :=
  observe (Term.map (pathToMap (homogeneousConcat (filling _) (filling_lawful _)
    (equivalencePath e) (equivalencePath d))) (nativeInput s))

/-- This evaluates the selected transport along the actual concatenated path. -/
theorem observedConcat_eq {S T V : Type} (e : S ≃ T) (d : T ≃ V) (s : S) :
    observedConcat e d s = constantSection (d (e s)) := by
  have h := observe_path (compositeTransportComparison (code S) (code T) (code V)
    (nativeMap e) (nativeEquivalence e) (nativeMap d) (nativeEquivalence d) (nativeInput s))
  have ha : Term.map (nativeMap e ≫ nativeMap d) (nativeInput s) = nativeInput (d (e s)) :=
    (congrArg (Term.map (nativeMap d)) (nativeInput_action e s)).trans (nativeInput_action d (e s))
  exact h.symm.trans ((congrArg observe ha).trans (observe_input (d (e s))))

theorem boolean_twice_true : observedConcat booleanTransposition booleanTransposition true =
    constantSection true := observedConcat_eq _ _ _

theorem successor_twice_three : observedConcat CubicalStateTransport.successor
    CubicalStateTransport.successor 3 = constantSection 5 := observedConcat_eq _ _ _

theorem successor_predecessor_three : observedConcat CubicalStateTransport.successor
    CubicalStateTransport.successor.symm 3 = constantSection 3 := observedConcat_eq _ _ _

noncomputable def observedInverse {S T : Type} (e : S ≃ T) (t : T) :=
  observe (Term.map (inverseMap (code S) (code T) (nativeMap e) (nativeEquivalence e)) (nativeInput t))

theorem observedInverse_eq {S T : Type} (e : S ≃ T) (t : T) :
    observedInverse e t = constantSection (e.symm t) := by
  have ha : Term.map (nativeMap e) (nativeInput (e.symm t)) = nativeInput t :=
    (nativeInput_action e (e.symm t)).trans (congrArg nativeInput (e.apply_symm_apply t))
  have h := observe_path (inverseLeft (code S) (code T) (nativeMap e) (nativeEquivalence e)
    (nativeInput (e.symm t)))
  exact (congrArg (fun x => observe (Term.map
    (inverseMap (code S) (code T) (nativeMap e) (nativeEquivalence e)) x)) ha).symm.trans
    (h.trans (observe_input (e.symm t)))

theorem selected_inverse_three : observedInverse CubicalStateTransport.successor 3 =
    constantSection 2 := observedInverse_eq _ _

private theorem nativeInput_action_three {S T V W : Type}
    (e : S ≃ T) (d : T ≃ V) (k : V ≃ W) (s : S) :
    Term.map ((nativeMap e ≫ nativeMap d) ≫ nativeMap k) (nativeInput s) =
      nativeInput (k (d (e s))) :=
  (congrArg (fun x => Term.map (nativeMap k) (Term.map (nativeMap d) x))
    (nativeInput_action e s)).trans
      ((congrArg (Term.map (nativeMap k)) (nativeInput_action d (e s))).trans
        (nativeInput_action k (d (e s))))

noncomputable def observedLeftTriple {S T V W : Type}
    (e : S ≃ T) (d : T ≃ V) (k : V ≃ W) (s : S) :=
  observe (Term.map (pathToMap (leftTriplePath (code S) (code T) (code V) (code W)
    (nativeMap e) (nativeEquivalence e) (nativeMap d) (nativeEquivalence d)
    (nativeMap k) (nativeEquivalence k))) (nativeInput s))

noncomputable def observedRightTriple {S T V W : Type}
    (e : S ≃ T) (d : T ≃ V) (k : V ≃ W) (s : S) :=
  observe (Term.map (pathToMap (rightTriplePath (code S) (code T) (code V) (code W)
    (nativeMap e) (nativeEquivalence e) (nativeMap d) (nativeEquivalence d)
    (nativeMap k) (nativeEquivalence k))) (nativeInput s))

theorem observedLeftTriple_eq {S T V W : Type}
    (e : S ≃ T) (d : T ≃ V) (k : V ≃ W) (s : S) :
    observedLeftTriple e d k s = constantSection (k (d (e s))) := by
  have h := observe_path (leftTripleTransport (code S) (code T) (code V) (code W)
    (nativeMap e) (nativeEquivalence e) (nativeMap d) (nativeEquivalence d)
    (nativeMap k) (nativeEquivalence k) (nativeInput s))
  exact h.symm.trans ((congrArg observe (nativeInput_action_three e d k s)).trans
    (observe_input (k (d (e s)))))

theorem observedRightTriple_eq {S T V W : Type}
    (e : S ≃ T) (d : T ≃ V) (k : V ≃ W) (s : S) :
    observedRightTriple e d k s = constantSection (k (d (e s))) := by
  have h := observe_path (rightTripleTransport (code S) (code T) (code V) (code W)
    (nativeMap e) (nativeEquivalence e) (nativeMap d) (nativeEquivalence d)
    (nativeMap k) (nativeEquivalence k) (nativeInput s))
  exact h.symm.trans ((congrArg observe (nativeInput_action_three e d k s)).trans
    (observe_input (k (d (e s)))))

/-- Both bracketings of three actual universe-path transports send 3 to 6. -/
theorem triple_successor_three :
    observedLeftTriple CubicalStateTransport.successor CubicalStateTransport.successor
      CubicalStateTransport.successor 3 = constantSection 6 ∧
    observedRightTriple CubicalStateTransport.successor CubicalStateTransport.successor
      CubicalStateTransport.successor 3 = constantSection 6 :=
  ⟨observedLeftTriple_eq _ _ _ _, observedRightTriple_eq _ _ _ _⟩

/-- The Boolean loop and reflexive path are unequal as host path terms. -/
theorem booleanLoop_ne_reflexive : equivalencePath booleanTransposition ≠ homogeneousRefl (term (code Bool)) := by
  intro h
  have ht := observe_path (uaComparison (code Bool) (code Bool) (nativeMap booleanTransposition)
    (nativeEquivalence booleanTransposition) (nativeInput true))
  have hr := observe_path (reflexiveTransportComparison (code Bool) (nativeInput true))
  have hm := congrArg (fun p : Term (paths (code Bool) (code Bool)) => observe (Term.map (pathToMap p) (nativeInput true))) h
  have hf := (congrArg observe (nativeInput_action booleanTransposition true)).trans (observe_input false)
  have bad : constantSection false = constantSection true :=
    hf.symm.trans (ht.trans (hm.trans (hr.trans (observe_input true))))
  exact Bool.false_ne_true (congrArg (fun t => t.val
    (terminal.elementsMk (Opposite.op ⟨0⟩) PUnit.unit)) bad)

/-- Existing cubical contraction supplies a native path whose observed endpoints
are distinct in Lean equality. It therefore rejects host equality reflection. -/
theorem nativePath_does_not_reflect_host_equality :
    ¬ ∀ {Γ : Context.{0}} (B : Family (total (interval Γ)))
      (a : Term (reindex B (endpointSub Γ false)))
      (b : Term (reindex B (endpointSub Γ true))),
      Term (path B a b) → HEq a b := by
  intro reflect
  have h := reflect CubicalPathConversion.body CubicalPathConversion.origin CubicalPathConversion.identity
    (interpretedContractionPath CubicalContraction.lineSpace 1)
  have he := eq_of_heq h
  exact CubicalPathConversion.selected_endpoints_distinct
    (congrArg (fun t => (t.reindex CubicalPathConversion.chooseLine).val
      (terminal.elementsMk (Opposite.op ⟨1⟩) PUnit.unit)) he)

/-- The reused decoded finite family has non-equivalent fibers at parameters zero and one. -/
theorem finiteFiber_not_equivalent :
    ¬ Nonempty ((Presheaf.decode CubicalSmallFamilies.dependentCode).obj (CubicalSmallFamilies.atArgument 0) ≃
      (Presheaf.decode CubicalSmallFamilies.dependentCode).obj (CubicalSmallFamilies.atArgument 1)) :=
  CubicalSmallFamilies.nonconstant_decoded_fibers

abbrev finiteParameterContext := raisedContext (total (Presheaf.decode CubicalSmallFamilies.natCode))
noncomputable def finiteIdentityEquivalence :
    HomotopyEquivalence (𝟙 (liftedDecode CubicalSmallFamilies.dependentCode)) :=
  HomotopyEquivalence.ofIso (Iso.refl _)

/-- Composition applies over the whole varying family, before selecting a fiber. -/
noncomputable def finiteFamilyComposition :=
  NaturalUnivalenceLaws.composition CubicalSmallFamilies.dependentCode
    CubicalSmallFamilies.dependentCode CubicalSmallFamilies.dependentCode
    (𝟙 (liftedDecode CubicalSmallFamilies.dependentCode)) finiteIdentityEquivalence (𝟙 (liftedDecode CubicalSmallFamilies.dependentCode)) finiteIdentityEquivalence

noncomputable def finiteFamilyCompositionAt {Δ : Context.{1}} (σ : Δ ⟶ finiteParameterContext) :=
  NaturalUnivalenceLaws.composition (σ ≫ CubicalSmallFamilies.dependentCode)
    (σ ≫ CubicalSmallFamilies.dependentCode) (σ ≫ CubicalSmallFamilies.dependentCode)
    (Functor.whiskerLeft σ.mapElements (𝟙 (liftedDecode CubicalSmallFamilies.dependentCode))) (finiteIdentityEquivalence.reindex σ)
    (Functor.whiskerLeft σ.mapElements (𝟙 (liftedDecode CubicalSmallFamilies.dependentCode))) (finiteIdentityEquivalence.reindex σ)

/-- Recomputing after substitution retains the actual chosen native square. -/
theorem finiteFamilyComposition_reindex {Δ : Context.{1}} (σ : Δ ⟶ finiteParameterContext) :
    comparisonSquare (finiteFamilyCompositionAt σ) =
      (comparisonSquare finiteFamilyComposition).reindex
        (liftSub (interval (total (interval finiteParameterContext)))
          (liftSub (interval finiteParameterContext) σ)) :=
  NaturalUnivalenceLaws.composition_body_reindex CubicalSmallFamilies.dependentCode
    CubicalSmallFamilies.dependentCode CubicalSmallFamilies.dependentCode
    (𝟙 (liftedDecode CubicalSmallFamilies.dependentCode)) finiteIdentityEquivalence (𝟙 (liftedDecode CubicalSmallFamilies.dependentCode)) finiteIdentityEquivalence σ

end Examples.CompositionalUnivalence
