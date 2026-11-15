import SquareKit.Internal.Cubical.Judgments.TransportEnvironment
import Examples.CubicalRestrictedTransport

/-! Actual source transport derivation, dependent endpoint computation and
rejection of a primitive application missing the constancy side condition. -/
namespace Examples.CubicalSourceFillings
set_option backward.isDefEq.respectTransparency false
open CategoryTheory SquareKit SquareKit.Cubical Source GuardedTheory Presheaf
open Fillings CubicalPresheaf CubicalDiscreteFilling CubicalRestrictedTransport

noncomputable def transportBoundarySource : Derivation Fillings.theory
    (List.ofFn transpBoundaryRule.premise) transpBoundaryRule.conclusion := by
  have d := Derivation.rule (T := Fillings.theory) (.inr .transpBoundary) GuardedTheory.Term.var
    (fun i => .hypothesis (List.mem_ofFn.mpr ⟨i,rfl⟩))
  simpa only [Fillings.theory,Theory.extend,Fillings.rule,Atom.subst_id] using d

theorem source_transport_boundary (Γ : Context) (B : Family (total (Presheaf.interval Γ)))
    (F : Filling B) (φ : Cofibration Γ) (a : Presheaf.Term (reindex B (Presheaf.endpointSub Γ false)))
    (hF : F.Lawful) (hc : RestrictedConstancy B φ) :
    HEq ((F.transp φ hc a).reindex (restrictInclusion φ)) (a.reindex (restrictInclusion φ)) := by
  have h := Fillings.interpret transportBoundarySource (transportEnvironment Γ B F φ a) (by
    intro p hp
    obtain ⟨i,rfl⟩ := List.mem_ofFn.mp hp
    exact transportEnvironment_valid Γ B F φ a hF hc i)
  change Source.operation .subTm ![Fillings.extraOperation .transp ![.context Γ,
    .family (total (Presheaf.interval Γ)) B,.filling (total (Presheaf.interval Γ)) B F,
    .cofibration Γ φ,.term Γ (reindex B (Presheaf.endpointSub Γ false)) a],
    Fillings.extraOperation .inclusion ![.context Γ,.cofibration Γ φ]] =
    Source.operation .subTm ![.term Γ (reindex B (Presheaf.endpointSub Γ false)) a,
      Fillings.extraOperation .inclusion ![.context Γ,.cofibration Γ φ]] at h
  rw [extra_transp Γ B F φ hc a,extra_inclusion] at h
  simp only [Source.operation,Matrix.cons_val_zero,Matrix.cons_val_one,Value.termIn_term] at h
  exact (Value.term.inj h).2.2

theorem full_face_selected (x : naturals.Elements) : transported.val x = finiteLast.val x := by
  have h := source_transport_boundary naturals lineFamily filler face finiteLast
    (discreteFilling_lawful q (fun n => Fin (n+1))) constancy
  have he := eq_of_heq h
  exact congrArg (fun t => t.val ((restrictContext face).elementsMk x.obj ⟨x.val,rfl⟩)) he

theorem source_two_substitutions :
    ((transported.reindex successor).reindex twice).val
      (naturals.elementsMk (Opposite.op ⟨0⟩) (2 : ℕ)) = (5 : Fin 6) :=
  full_face_selected ((twice ≫ successor).mapElements.obj (naturals.elementsMk (Opposite.op ⟨0⟩) (2 : ℕ)))

theorem erasure_rejected :
    (((transported.reindex successor).reindex twice).val
      (naturals.elementsMk (Opposite.op ⟨0⟩) (2 : ℕ))).val ≠ 0 := by
  rw [source_two_substitutions]
  decide

theorem missing_constancy_invalid (F : Filling zeroFiber)
    (a : Presheaf.Term (reindex zeroFiber (Presheaf.endpointSub terminal false))) :
    Fillings.extraOperation .transp ![.context terminal,.family line zeroFiber,.filling line zeroFiber F,
      .cofibration terminal (Cofibration.top terminal),
      .term terminal (reindex zeroFiber (Presheaf.endpointSub terminal false)) a] = .invalid := by
  simp [Fillings.extraOperation,Value.familyAt_family,Value.fillingAt_filling,
    Value.cofibrationAt_cofibration,Value.termAt_term,missing_constancy_rejected]

end Examples.CubicalSourceFillings
