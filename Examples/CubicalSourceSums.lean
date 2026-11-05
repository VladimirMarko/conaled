import SquareKit.Internal.Cubical.Judgments.SumsTheory
import Examples.CubicalConversion

/-! Source packing cancellation and elimination into a motive depending on
the second component of a varying dependent pair. -/
namespace Examples.CubicalSourceSums
set_option backward.isDefEq.respectTransparency false
open CategoryTheory SquareKit.Cubical SquareKit.Cubical.Source
open SquareKit.GuardedTheory Sums Presheaf Examples.CubicalConversion Examples.CubicalPresheaf

noncomputable def betaSource :
    Derivation theory (List.ofFn betaRule.premise) betaRule.conclusion := by
  have d := Derivation.rule (T := theory) (.inr .beta) SquareKit.GuardedTheory.Term.var
    (fun i => .hypothesis (List.mem_ofFn.mpr ⟨i,rfl⟩))
  simpa only [theory,Theory.extend,Sums.rule,Atom.subst_id] using d

theorem source_pack_cancel (Γ : Context) (A : Family Γ) (B : Family (total A)) :
    sigmaPack A B ≫ sigmaUnpack A B = 𝟙 (total B) := by
  have h := interpret betaSource ![.context Γ,.family Γ A,.family (total A) B] (by
    intro p hp
    rcases List.mem_ofFn.mp hp with ⟨i,rfl⟩
    fin_cases i
    · exact ⟨Γ,A,rfl,rfl⟩
    · refine ⟨total A,B,?_,rfl⟩
      change Source.operation .extend ![.context Γ,.family Γ A] = _
      simp [Source.operation])
  change Source.operation .comp ![extraOperation .unpack ![.family Γ A,.family (total A) B],
    extraOperation .pack ![.family Γ A,.family (total A) B]] =
    Source.operation .id ![Source.operation .extend ![Source.operation .extend ![.context Γ,.family Γ A],.family (total A) B]] at h
  rw [extra_unpack,extra_pack] at h
  simp only [Source.operation,Matrix.cons_val_zero,Matrix.cons_val_one,
    Value.substitutionAt_substitution,Value.familyAt_family] at h
  exact eq_of_heq (Value.substitution.inj h).2.2

/-- The motive's size depends on the selected second component, whose type
already depends on the first component and the context index. -/
abbrev secondFiber : Family (total (Presheaf.sigma finiteFiber argumentFiber)) where
  obj e := Fin (e.val.2.2.val + 1)
  map {_x y} f := TypeCat.ofHom (Fin.cast (congrArg
    (fun z : (total (Presheaf.sigma finiteFiber argumentFiber)).obj y.obj =>
      z.2.2.val + 1) f.map_val))
  map_id _ := rfl
  map_comp _ _ := rfl

def body : Presheaf.Term (reindex secondFiber (sigmaPack finiteFiber argumentFiber)) where
  val e := Fin.last e.val.2.val
  property f := Fin.ext (congrArg (fun z => z.2.val) f.map_val)

theorem dependent_elimination_at_two :
    (sigmaElim body).val
      ((total (Presheaf.sigma finiteFiber argumentFiber)).elementsMk
        (Opposite.op ⟨0⟩) ⟨(3 : ℕ),(2 : Fin 4),(1 : Fin 3)⟩) = (1 : Fin 2) := rfl

theorem dependent_body_recovered :
    (sigmaElim body).reindex (sigmaPack finiteFiber argumentFiber) = body :=
  sigmaElim_beta body

end Examples.CubicalSourceSums
