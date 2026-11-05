import SquareKit.Internal.Cubical.Judgments.PathsTheory
import Examples.CubicalPathConversion

/-! A source endpoint derivation is interpreted on the previously constructed
nonconstant contraction path. Its selected endpoints remain distinct. -/
namespace Examples.CubicalSourcePaths
set_option backward.isDefEq.respectTransparency false
open CategoryTheory SquareKit SquareKit.Cubical Source
open GuardedTheory Paths Presheaf CubicalPathConversion

noncomputable def zeroEndpointSource : Derivation theory
    (List.ofFn (endpointRule false).premise) (endpointRule false).conclusion := by
  have d := Derivation.rule (T := theory) (.inr (.endpoint false)) GuardedTheory.Term.var
    (fun i => .hypothesis (List.mem_ofFn.mpr ⟨i,rfl⟩))
  simpa only [theory,Theory.extend,Paths.rule,Atom.subst_id] using d

theorem source_zero_endpoint (Γ : Context) (B : Family (total (Presheaf.interval Γ)))
    (a₀ : Presheaf.Term (reindex B (Presheaf.endpointSub Γ false)))
    (a₁ : Presheaf.Term (reindex B (Presheaf.endpointSub Γ true)))
    (p : Presheaf.Term (normalizedPath B a₀ a₁)) :
    (normalizedPathApp p).reindex (Presheaf.endpointSub Γ false) = a₀ := by
  let ρ : Fin 5 → Value := ![.context Γ,.family (total (Presheaf.interval Γ)) B,
    .term Γ (reindex B (Presheaf.endpointSub Γ false)) a₀,
    .term Γ (reindex B (Presheaf.endpointSub Γ true)) a₁,.term Γ (normalizedPath B a₀ a₁) p]
  have he₀ := endpointSub_eval (.var (0 : Fin 5)) ρ Γ rfl false
  have he₁ := endpointSub_eval (.var (0 : Fin 5)) ρ Γ rfl true
  have h := interpret zeroEndpointSource ρ (by
    intro q hq
    rcases List.mem_ofFn.mp hq with ⟨i,rfl⟩
    fin_cases i
    · exact ⟨Γ,rfl⟩
    · refine ⟨total (Presheaf.interval Γ),B,?_,rfl⟩
      change Source.operation .extend ![.context Γ,Intervals.extraOperation .interval ![.context Γ]] = _
      rw [Intervals.extra_interval]
      simp [Source.operation]
    · refine ⟨Γ,reindex B (Presheaf.endpointSub Γ false),a₀,rfl,?_,rfl⟩
      change Source.operation .subTy ![.family (total (Presheaf.interval Γ)) B,
        (Paths.endpointSub (.var 0) false).eval Paths.algebra ρ] = _
      rw [he₀]
      simp [Source.operation]
    · refine ⟨Γ,reindex B (Presheaf.endpointSub Γ true),a₁,rfl,?_,rfl⟩
      change Source.operation .subTy ![.family (total (Presheaf.interval Γ)) B,
        (Paths.endpointSub (.var 0) true).eval Paths.algebra ρ] = _
      rw [he₁]
      simp [Source.operation]
    · exact ⟨Γ,normalizedPath B a₀ a₁,p,rfl,extra_path Γ B a₀ a₁,rfl⟩)
  change Source.operation .subTm ![extraOperation .app ![.context Γ,.family (total (Presheaf.interval Γ)) B,
      .term Γ (reindex B (Presheaf.endpointSub Γ false)) a₀,
      .term Γ (reindex B (Presheaf.endpointSub Γ true)) a₁,.term Γ (normalizedPath B a₀ a₁) p],
    (Paths.endpointSub (.var (0 : Fin 5)) false).eval Paths.algebra ρ] = .term Γ (reindex B (Presheaf.endpointSub Γ false)) a₀ at h
  rw [he₀,extra_app] at h
  simp only [Source.operation,Matrix.cons_val_zero,Matrix.cons_val_one,Value.termIn_term] at h
  exact eq_of_heq (Value.term.inj h).2.2

theorem contraction_source_zero :
    (normalizedPathApp contraction).reindex (Presheaf.endpointSub lineCubes false) = origin :=
  source_zero_endpoint lineCubes body origin CubicalPathConversion.identity contraction

theorem selected_source_zero :
    ((normalizedPathApp contraction).reindex (Presheaf.endpointSub lineCubes false)).reindex chooseLine =
      origin.reindex chooseLine :=
  congrArg (fun t => t.reindex chooseLine) contraction_source_zero

theorem selected_source_zero_differs_from_one :
    (((normalizedPathApp contraction).reindex (Presheaf.endpointSub lineCubes false)).reindex chooseLine).val
      (terminal.elementsMk (Opposite.op ⟨1⟩) PUnit.unit) ≠
    (CubicalPathConversion.identity.reindex chooseLine).val
      (terminal.elementsMk (Opposite.op ⟨1⟩) PUnit.unit) := by
  rw [selected_source_zero]
  exact selected_endpoints_distinct

end Examples.CubicalSourcePaths
