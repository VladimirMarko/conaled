import SquareKit.Internal.Cubical.Judgments.FillingSyntax
import SquareKit.Internal.Cubical.Judgments.FillingValues

/-! The guarded operations use the supplied selected filler. No filler is
chosen from an existential fibrancy assertion or for an arbitrary raw family. -/
namespace SquareKit.Cubical.Source.Fillings
open GuardedTheory Presheaf CategoryTheory
universe u

noncomputable def extraOperation (op : Operation)
    (args : Fin (extraSignature.arity op) → Value.{u}) : Value.{u} := by
  classical
  exact match op with
  | .faceTop => match args 0 with
    | .context Γ => .cofibration Γ (Cofibration.top Γ)
    | _ => .invalid
  | .faceBot => match args 0 with
    | .context Γ => .cofibration Γ (Cofibration.bot Γ)
    | _ => .invalid
  | .faceJoin => match args 0 with
    | .context Γ => match (args 1).cofibrationAt Γ, (args 2).cofibrationAt Γ with
      | some φ, some ψ => .cofibration Γ (φ.join ψ)
      | _,_ => .invalid
    | _ => .invalid
  | .faceEndpoint b => match args 0 with
    | .context Γ => match (args 1).termAt Γ (Presheaf.interval Γ) with
      | some r => .cofibration Γ (Cofibration.endpoint r b)
      | none => .invalid
    | _ => .invalid
  | .subFace => match args 0,args 1 with
    | .context Δ,.context Γ => match (args 2).cofibrationAt Γ,(args 3).substitutionAt Δ Γ with
      | some φ,some σ => .cofibration Δ (φ.reindex σ)
      | _,_ => .invalid
    | _,_ => .invalid
  | .restriction => match args 0 with
    | .context Γ => match (args 1).cofibrationAt Γ with
      | some φ => .context (restrictContext φ)
      | none => .invalid
    | _ => .invalid
  | .inclusion => match args 0 with
    | .context Γ => match (args 1).cofibrationAt Γ with
      | some φ => .substitution (restrictContext φ) Γ (restrictInclusion φ)
      | none => .invalid
    | _ => .invalid
  | .restrictedSub => match args 0,args 1 with
    | .context Δ,.context Γ => match (args 2).cofibrationAt Γ,(args 3).substitutionAt Δ Γ with
      | some φ,some σ => .substitution (restrictContext (φ.reindex σ)) (restrictContext φ) (restrictSubstitution φ σ)
      | _,_ => .invalid
    | _,_ => .invalid
  | .subProvider => match args 0,args 1 with
    | .context Δ,.context Γ => match (args 2).fillingIn Γ,(args 3).substitutionAt Δ Γ with
      | some ⟨A,F⟩,some σ => .filling Δ (reindex A σ) (F.reindex σ)
      | _,_ => .invalid
    | _,_ => .invalid
  | .hcomp => match args 0 with
    | .context Γ => match (args 1).familyAt Γ with
      | some A => match (args 2).fillingAt Γ A,(args 3).cofibrationAt Γ with
        | some F,some φ =>
          let ψ := φ.reindex (Presheaf.projection (Presheaf.interval Γ))
          let B := reindex A (Presheaf.projection (Presheaf.interval Γ))
          match (args 4).termAt (restrictContext ψ) (reindex B (restrictInclusion ψ)),(args 5).termAt Γ A with
          | some u,some a =>
            let t := PartialSection.ofRestricted u
            if h : ∀ x hx, t.val ((Presheaf.endpointSub Γ false).mapElements.obj x) hx = a.val x then
              .term Γ A (F.hcomp φ {tube := t, base := a, boundary := h})
            else .invalid
          | _,_ => .invalid
        | _,_ => .invalid
      | none => .invalid
    | _ => .invalid
  | .transp => match args 0 with
    | .context Γ => match (args 1).familyAt (total (Presheaf.interval Γ)) with
      | some B => match (args 2).fillingAt (total (Presheaf.interval Γ)) B,(args 3).cofibrationAt Γ with
        | some F,some φ => match (args 4).termAt Γ (reindex B (Presheaf.endpointSub Γ false)) with
          | some a => if h : RestrictedConstancy B φ then
              .term Γ (reindex B (Presheaf.endpointSub Γ true)) (F.transp φ h a)
            else .invalid
          | none => .invalid
        | _,_ => .invalid
      | none => .invalid
    | _ => .invalid

def extraPredicate (p : Predicate) (args : Fin (extraSignature.arguments p) → Value.{u}) : Prop :=
  match p with
  | .face => ∃ Γ φ, args 0 = .context Γ ∧ args 1 = .cofibration Γ φ
  | .provider => ∃ Γ A F, args 0 = .context Γ ∧ args 1 = .family Γ A ∧ args 2 = .filling Γ A F ∧ F.Lawful

noncomputable def algebra : Algebra signature where
  Carrier := Value.{u}
  operation | .inl o => Paths.algebra.operation o | .inr o => extraOperation o
  predicate | .inl p => Paths.algebra.predicate p | .inr p => extraPredicate p

end SquareKit.Cubical.Source.Fillings
