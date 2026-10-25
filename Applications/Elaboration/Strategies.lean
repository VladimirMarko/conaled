import Applications.Elaboration.Elaborator

/-! Two admissible elaboration strategies. The second changes evaluation order
of pure natural additions. This is a fragment-specific transformation, not a
permission to reorder effects in another setting. -/
namespace Elaboration

def Core.reverseAdds : Core Γ Δ t → Core Γ Δ t
  | .numeral n => .numeral n
  | .variable x => .variable x
  | .constant x => .constant x
  | .metavariable k => .metavariable k
  | .plus a b => .plus b.reverseAdds a.reverseAdds
  | .pack u n a => .pack u n.reverseAdds a.reverseAdds
  | .fold p => .fold p.reverseAdds

theorem Core.reverseAdds_eval (c : Core Γ Δ t) (μ ρ δ) :
    c.reverseAdds.eval μ ρ δ = c.eval μ ρ δ := by
  induction c <;> simp_all [Core.reverseAdds, Core.eval, Nat.add_comm]

theorem Core.reverseAdds_typed (c : Core Γ Δ t) (θ : Assignment) :
    c.reverseAdds.Typed θ ↔ c.Typed θ := by
  induction c <;> simp_all [Core.reverseAdds, Core.Typed, and_comm]

def reorderSquare : Relational.RelSquare (coreRep Γ Δ t) (coreRep Γ Δ t) where
  impl := Core.reverseAdds
  spec := id
  preserves h := by
    dsimp [coreRep] at *
    rw [← h]
    funext μ ρ δ
    exact Core.reverseAdds_eval _ _ _ _

/-- Actual translation composition reuses Relational.compose and its law
transport; it need not construct a second generic square foundation. -/
def reorderedLowering : Relational.RelSquare (sourceRep Γ Δ t) (coreRep Γ Δ t) :=
  Relational.compose reorderSquare loweringSquare

theorem translation_composition (s : Source Γ Δ t) (μ ρ δ) :
    (reorderedLowering.impl s).eval μ ρ δ = s.eval μ ρ δ := by
  have h := reorderedLowering.preserves (r := s) (s := s.eval) rfl
  exact congrFun (congrFun (congrFun h μ) ρ) δ

def Output.reorder (o : Output Γ Δ) : Output Γ Δ :=
  ⟨o.inferred, o.code.reverseAdds, o.constraints⟩

theorem reorder_admissible {p : Phrase Γ Δ} {e} {o : Output Γ Δ}
    (h : Elaborates p e o) : Elaborates p e o.reorder := by
  obtain ⟨s, hs, hf, hc, ht⟩ := h
  exact ⟨s, hs, fun μ ρ δ => (Core.reverseAdds_eval o.code μ ρ δ).trans (hf μ ρ δ),
    hc, fun θ => (ht θ).trans (Core.reverseAdds_typed o.code θ).symm⟩

def elaborateReordered (p : Phrase Γ Δ) (e : Option Ty) : Except Diagnostic (Output Γ Δ) :=
  (elaborate p e).map Output.reorder

theorem elaborateReordered_sound {p : Phrase Γ Δ} {e o}
    (h : elaborateReordered p e = .ok o) : Elaborates p e o := by
  unfold elaborateReordered at h
  cases he : elaborate p e with
  | error d => simp [he, Except.map] at h
  | ok r =>
    simp [he, Except.map] at h
    subst o
    exact reorder_admissible (elaborate_sound he)

/-- Intermediate elaboration may strengthen constraints without changing the
code. The solution-set direction matters: arbitrary weakening is unsound. -/
def Pending (p : Phrase Γ Δ) (e : Option Ty) (o : Output Γ Δ)
    (cs : List Obligation) : Prop :=
  Elaborates p e o ∧ RefinesConstraints o.constraints cs

theorem Pending.refine {p : Phrase Γ Δ} {e o a b}
    (h : Pending p e o a) (r : RefinesConstraints a b) : Pending p e o b :=
  ⟨h.1, refine_constraints_comp h.2 r⟩

theorem Pending.accept {p : Phrase Γ Δ} {e o cs θ}
    (h : Pending p e o cs) (solved : Solves θ cs) : Accepted p e ⟨o, θ⟩ :=
  ⟨h.1, h.2 θ solved⟩

/-- Substitution may introduce new obligations; they must be discharged rather
than silently inheriting the old constraint set. -/
theorem Source.subst_solved (s : Source Γ Δ t) (σ : Substitution Γ Γ' Δ)
    (θ : Assignment) (hs : Solves θ s.requirements)
    (hσ : ∀ {u} (x : Var Γ u), Solves θ (σ x).requirements) :
    Solves θ (s.subst σ).requirements := by
  induction s with
  | lit | named => exact hs
  | bound x => exact hσ x
  | hole => exact hs
  | add a b ia ib =>
    exact (solves_append θ _ _).mpr ⟨ia ((solves_append θ _ _).mp hs).1,
      ib ((solves_append θ _ _).mp hs).2⟩
  | vector u n a iN iA =>
    intro c hc
    simp only [Source.subst, Source.requirements, List.mem_cons, List.mem_append] at hc
    rcases hc with rfl | hc | hc
    · exact hs _ (by simp [Source.requirements])
    · exact iN (fun d hd => hs d (by simp [Source.requirements, hd])) c hc
    · exact iA (fun d hd => hs d (by simp [Source.requirements, hd])) c hc
  | total p ih => exact ih hs

theorem lowered_substitution_typed (s : Source Γ Δ t) (σ : Substitution Γ Γ' Δ)
    (θ : Assignment) (hs : Solves θ s.requirements)
    (hσ : ∀ {u} (x : Var Γ u), Solves θ (σ x).requirements) :
    ((lower s).subst (fun x => lower (σ x))).Typed θ := by
  rw [← lower_subst]
  exact (lower_typed _ θ).mpr (s.subst_solved σ θ hs hσ)

theorem lowered_environment_extension (s : Source Γ Δ t) (μ ρ δ) (v : Ty.Value u) :
    (lower (s.renameGlobals (fun x => .there x))).eval μ ρ (δ.extend v) =
      (lower s).eval μ ρ δ := by
  rw [lower_sound, lower_sound, environment_extension]

end Elaboration
