import Applications.ClassicalControl.Machine

/-! Implicational adequacy for arbitrary predecessor-closed poles. No scanner
instruction is a typing axiom, and this interpretation does not decode arithmetic. -/
namespace ClassicalControl
namespace Source

inductive Formula where
  | atom : Nat → Formula
  | bottom
  | imp : Formula → Formula → Formula

abbrev Orthogonal (P : Pole) (X : Set Stack) (t : Term 0) : Prop :=
  ∀ π, π ∈ X → P.holds (.run t π)

def Falsity (P : Pole) (atoms : Nat → Set Stack) : Formula → Set Stack
  | .atom a => atoms a
  | .bottom => Set.univ
  | .imp A B => {s | ∃ u π, Orthogonal P (Falsity P atoms A) u ∧
      π ∈ Falsity P atoms B ∧ s = .arg u π}

abbrev Realizes (P : Pole) (atoms : Nat → Set Stack) (A : Formula) :=
  Orthogonal P (Falsity P atoms A)

theorem continuation (P : Pole) (atoms : Nat → Set Stack) (A B : Formula)
    (π : Stack) (hπ : π ∈ Falsity P atoms A) :
    Realizes P atoms (.imp A B) (.saved π) := by
  rintro _ ⟨u, ρ, hu, _, rfl⟩
  exact P.backwards .restore (hu π hπ)

/-- Peirce needs no inhabitant of B and works for every predecessor-closed pole. -/
theorem peirce (P : Pole) (atoms : Nat → Set Stack) (A B : Formula) :
    Realizes P atoms (.imp (.imp (.imp A B) A) A) .cc := by
  rintro _ ⟨f, π, hf, hπ, rfl⟩
  apply P.backwards .capture
  exact hf _ ⟨.saved π, π, continuation P atoms A B π hπ, hπ, rfl⟩

inductive HasType : (Fin n → Formula) → Term n → Formula → Prop where
  | var : HasType Γ (.var i) (Γ i)
  | lam : HasType (Fin.cases A Γ) b B → HasType Γ (.lam b) (.imp A B)
  | app : HasType Γ t (.imp A B) → HasType Γ u A → HasType Γ (.app t u) B
  | cc : HasType Γ .cc (.imp (.imp (.imp A B) A) A)

theorem typed_pure {Γ : Fin n → Formula} {t A} (h : HasType Γ t A) : Pure t := by
  induction h with
  | var => exact .var
  | lam _ ih => exact .lam ih
  | app _ _ it iu => exact .app it iu
  | cc => exact .cc

/-- Closing substitutions may contain runtime continuations. The derivation itself
uses exactly variable, lambda, application and control. -/
theorem adequacy (P : Pole) (atoms : Nat → Set Stack)
    {Γ : Fin n → Formula} {t A} (ht : HasType Γ t A)
    (σ : Fin n → Term 0) (hσ : ∀ i, Realizes P atoms (Γ i) (σ i)) :
    Realizes P atoms A (t.subst σ) := by
  induction ht with
  | var => exact hσ _
  | @lam n Γ A b B hb ih =>
    rintro _ ⟨u, π, hu, hπ, rfl⟩
    apply P.backwards .beta
    rw [Term.close_beta]
    apply ih (Fin.cases u σ) ?_ π hπ
    intro i; refine Fin.cases ?_ (fun i => ?_) i
    · exact hu
    · exact hσ i
  | app ht hu it iu =>
    intro π hπ
    apply P.backwards .app
    exact it σ hσ _ ⟨_, π, iu σ hσ, hπ, rfl⟩
  | @cc n Γ A B => exact peirce P atoms A B

theorem empty_subst (t : Term 0) (σ : Fin 0 → Term 0) : t.subst σ = t := by
  have h : σ = Term.var := by funext i; exact Fin.elim0 i
  rw [h, Term.subst_id]

/-- Restricted consistency is for closed proofs in the four typing rules. -/
theorem no_closed_bottom (t : Term 0) (Γ : Fin 0 → Formula) :
    ¬ HasType Γ t .bottom := by
  intro ht
  have hr := adequacy Pgood (fun _ => Set.univ) ht Term.var (fun i => Fin.elim0 i)
  rw [Term.subst_id] at hr
  exact restricted_coherence t (typed_pure ht) (hr .halt (Set.mem_univ _))

end Source
end ClassicalControl
