import SquareKit.Internal.Cubical.Judgments.HcompEnvironment
import Examples.CubicalSumFilling

/-! The source hcomp derivation retains an actual dependent pair. Its overlap
guard rejects incompatible cap and tube data. -/
namespace Examples.CubicalSourceHcomp
set_option backward.isDefEq.respectTransparency false
open CategoryTheory SquareKit SquareKit.Cubical Source GuardedTheory Presheaf
open Fillings CubicalPresheaf CubicalDiscreteFilling CubicalSumFilling

noncomputable def boundarySource : Derivation Fillings.theory
    (List.ofFn hcompBoundaryRule.premise) hcompBoundaryRule.conclusion := by
  have d := Derivation.rule (T := Fillings.theory) (.inr .hcompBoundary) GuardedTheory.Term.var
    (fun i => .hypothesis (List.mem_ofFn.mpr ⟨i,rfl⟩))
  simpa only [Fillings.theory,Theory.extend,Fillings.rule,Atom.subst_id] using d

theorem source_boundary (Γ : Context) (A : Family Γ) (F : Filling A) (φ : Cofibration Γ)
    (b : OpenBox (reindex A (Presheaf.projection (Presheaf.interval Γ))) φ) (hF : F.Lawful) :
    (F.hcomp φ b).reindex (restrictInclusion φ) =
      b.tube.toRestricted.reindex
        (restrictSubstitution (φ.reindex (Presheaf.projection (Presheaf.interval Γ))) (Presheaf.endpointSub Γ true)) := by
  let ρ := hcompEnvironment Γ A F φ b
  have h := Fillings.interpret boundarySource ρ (by
    intro p hp
    obtain ⟨i,rfl⟩ := List.mem_ofFn.mp hp
    exact hcompEnvironment_valid Γ A F φ b hF i)
  have ht := tubeEndpoint_eval (.var (0 : Fin 6)) (.var 3) (.var 4) ρ Γ _ φ b.tube.toRestricted rfl rfl rfl true
  change Source.operation .subTm ![Fillings.extraOperation .hcomp ![.context Γ,.family Γ A,.filling Γ A F,
    .cofibration Γ φ,.term _ _ b.tube.toRestricted,.term Γ A b.base],
    Fillings.extraOperation .inclusion ![.context Γ,.cofibration Γ φ]] = _ at h
  rw [ht,extra_hcomp Γ A F φ b,extra_inclusion] at h
  simp only [Source.operation,Matrix.cons_val_zero,Matrix.cons_val_one,Value.termIn_term] at h
  exact eq_of_heq (Value.term.inj h).2.2

theorem source_selected_pair (x : naturals.Elements) :
    (pairFilling.hcomp (Cofibration.top naturals) pairBox).val x = chosenPair.val x := by
  have h := source_boundary naturals (sigma argument result) pairFilling (Cofibration.top naturals) pairBox lawful
  exact congrArg (fun t => t.val ((restrictContext (Cofibration.top naturals)).elementsMk x.obj ⟨x.val,rfl⟩)) h

theorem source_two_substitutions :
    ((pairFilling.hcomp (Cofibration.top naturals) pairBox).reindex (twice ≫ successor)).val
      (naturals.elementsMk (Opposite.op ⟨0⟩) (2 : ℕ)) = ⟨(6 : ℕ),(6 : Fin 7)⟩ :=
  source_selected_pair ((twice ≫ successor).mapElements.obj (naturals.elementsMk (Opposite.op ⟨0⟩) (2 : ℕ)))

abbrev boolFamily := constantFamily naturals Bool
abbrev full := Cofibration.top naturals
abbrev badTube : PartialSection (reindex boolFamily (Presheaf.projection (Presheaf.interval naturals)))
    (full.reindex (Presheaf.projection (Presheaf.interval naturals))) :=
  PartialSection.ofTerm _ (constantBool (total (Presheaf.interval naturals)) true)

theorem incompatible_cap_invalid (F : Filling boolFamily) :
    Fillings.extraOperation .hcomp ![.context naturals,.family naturals boolFamily,.filling naturals boolFamily F,
      .cofibration naturals full,.term _ _ badTube.toRestricted,
      .term naturals boolFamily (constantBool naturals false)] = .invalid := by
  classical
  simp [Fillings.extraOperation,Value.familyAt_family,Value.fillingAt_filling,
    Value.cofibrationAt_cofibration,Value.termAt_term]
  exact ⟨naturals.elementsMk (Opposite.op ⟨0⟩) (0 : ℕ),rfl,by intro h; cases h⟩

end Examples.CubicalSourceHcomp
