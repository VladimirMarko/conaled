import SquareKit.Internal.Cubical.NativeUnivalenceUa
import SquareKit.Internal.Cubical.HomotopyEquivalenceSubstitution

set_option autoImplicit false
set_option warningAsError true
namespace SquareKit.Cubical.Presheaf
open CategoryTheory
universe u

namespace EquivalenceFamilies

theorem decodeMap_lam_apply {Γ : Context.{u}} {A B : Family Γ}
    (s : Term (reindex B (projection A))) (a : Term A) :
    Term.map (decodeMap (lam s)) a = s.reindex (pair (𝟙 Γ) a) := by
  apply Term.ext
  intro x
  rfl

end EquivalenceFamilies
namespace SmallUniverse.NativeUnivalence
variable {Γ Δ : Context.{u+1}} {a b : Γ ⟶ smallFamilyCodes.{u}}

/-- Substitute a native universe path, preserving its actual line. -/
def reindexPath (p : Term (paths a b)) (σ : Δ ⟶ Γ) :
    Term (paths (σ ≫ a) (σ ≫ b)) :=
  Term.map (pathReindex (reindex (family Γ) (projection (interval Γ)))
    (term a) (term b) σ) (p.reindex σ)

theorem codeOfPath_reindexPath (p : Term (paths a b)) (σ : Δ ⟶ Γ) :
    codeOfPath (reindexPath p σ) = liftSub (interval Γ) σ ≫ codeOfPath p := by
  rfl

private noncomputable def decodeLawful (c : Γ ⟶ smallFamilyCodes.{u}) : LawfulFamily Γ :=
  ⟨⟨liftedDecode c, NativeDecode.filling c⟩, NativeDecode.filling_lawful c⟩

private theorem decodeLawful_reindex (c : Γ ⟶ smallFamilyCodes.{u}) (σ : Δ ⟶ Γ) :
    (decodeLawful c).reindex σ = decodeLawful (σ ≫ c) := rfl

theorem pathToMap_reindex (p : Term (paths a b)) (σ : Δ ⟶ Γ) :
    Functor.whiskerLeft σ.mapElements (pathToMap p) = pathToMap (reindexPath p σ) := by
  have h := IntervalTransport.mapTo_reindex (NativeDecode.filling (codeOfPath p))
    (NativeDecode.filling_lawful (codeOfPath p)) (liftedDecode a) (liftedDecode b)
    (decode_zero p) (decode_one p) σ
  have hL : (decodeLawful (codeOfPath p)).reindex (liftSub (interval Γ) σ) =
      decodeLawful (codeOfPath (reindexPath p σ)) :=
    (decodeLawful_reindex _ _).trans (congrArg decodeLawful (codeOfPath_reindexPath p σ).symm)
  exact h.trans (eq_of_heq (IntervalTransport.mapTo_native_congr hL rfl rfl _ _
    (decode_zero (reindexPath p σ)) (decode_one (reindexPath p σ))))

theorem pathToEquivalence_reindex (p : Term (paths a b)) (σ : Δ ⟶ Γ) :
    HEq ((pathToEquivalence p).reindex σ) (pathToEquivalence (reindexPath p σ)) := by
  have h := IntervalTransport.equivalenceTo_reindex (NativeDecode.filling (codeOfPath p))
    (NativeDecode.filling_lawful (codeOfPath p)) (liftedDecode a) (liftedDecode b)
    (decode_zero p) (decode_one p) σ
  have hL : (decodeLawful (codeOfPath p)).reindex (liftSub (interval Γ) σ) =
      decodeLawful (codeOfPath (reindexPath p σ)) :=
    (decodeLawful_reindex _ _).trans (congrArg decodeLawful (codeOfPath_reindexPath p σ).symm)
  exact h.trans (IntervalTransport.equivalenceTo_native_congr hL rfl rfl _ _
    (decode_zero (reindexPath p σ)) (decode_one (reindexPath p σ)))

theorem reindexPath_generic (p : Term (paths a b)) :
    reindexPath (genericPath a b) (pair (A := paths a b) (𝟙 Γ) p) = p := by
  apply eq_of_heq
  apply pathTerm_hext
  rfl

theorem pathSection_pair {C : Family Γ}
    (s : Term (reindex (paths a b) (projection C))) (c : Term C) :
    reindexPath (a := projection C ≫ a) (b := projection C ≫ b)
      (Term.map (pathReindex (reindex (family Γ) (projection (interval Γ)))
        (term a) (term b) (projection C)) s) (pair (A := C) (𝟙 Γ) c) =
      s.reindex (pair (A := C) (𝟙 Γ) c) := by
  apply eq_of_heq
  apply pathTerm_hext
  rfl

private theorem pathToEquivalence_congr {p q : Term (paths a b)} (h : p = q) :
    HEq (pathToEquivalence p) (pathToEquivalence q) := by
  cases h
  rfl

/-- Evaluation recovers the full selected equivalence, including its contraction. -/
theorem pathEquivalence_generic (p : Term (paths a b)) :
    (⟨Functor.whiskerLeft (pair (A := paths a b) (𝟙 Γ) p).mapElements
        (pathToMap (genericPath a b)),
      (pathToEquivalence (genericPath a b)).reindex (pair (A := paths a b) (𝟙 Γ) p)⟩ :
      Σ f : liftedDecode a ⟶ liftedDecode b, HomotopyEquivalence f) =
      ⟨pathToMap p, pathToEquivalence p⟩ := by
  have hm := (pathToMap_reindex (genericPath a b) (pair (A := paths a b) (𝟙 Γ) p)).trans
    (congrArg (@pathToMap Γ a b) (reindexPath_generic p))
  have hE := (pathToEquivalence_reindex (genericPath a b) (pair (A := paths a b) (𝟙 Γ) p)).trans
    (pathToEquivalence_congr (reindexPath_generic p))
  exact Sigma.ext hm hE

theorem lowerChartEquivalence_comp {Θ : Context.{u}}
    (a b : Γ ⟶ smallFamilyCodes.{u}) (f : liftedDecode a ⟶ liftedDecode b)
    (E : HomotopyEquivalence f) (σ : Δ ⟶ Γ) (ρ : raisedContext Θ ⟶ Δ) :
    lowerChartEquivalence a b (ρ ≫ σ) f E =
      lowerChartEquivalence (σ ≫ a) (σ ≫ b) ρ
        (Functor.whiskerLeft σ.mapElements f) (E.reindex σ) := by
  exact congrArg
    (fun H : HomotopyEquivalence (Functor.whiskerLeft (ρ ≫ σ).mapElements f) =>
      Raising.lowerEquivalence (A := Presheaf.decode (ρ ≫ σ ≫ a))
        (B := Presheaf.decode (ρ ≫ σ ≫ b))
        (f := lowerChartMap a b (ρ ≫ σ) f) H)
    (E.reindex_comp σ ρ).symm

theorem chartCode_comp {Θ : Context.{u}}
    (a b : Γ ⟶ smallFamilyCodes.{u}) (f : liftedDecode a ⟶ liftedDecode b)
    (E : HomotopyEquivalence f) (σ : Δ ⟶ Γ) (ρ : raisedContext Θ ⟶ Δ) :
    chartCode a b f E (ρ ≫ σ) =
      chartCode (σ ≫ a) (σ ≫ b) (Functor.whiskerLeft σ.mapElements f) (E.reindex σ) ρ :=
  congrArg (fun H => Univalence.uaCode (ρ ≫ σ ≫ a) (ρ ≫ σ ≫ b)
    (lowerChartMap a b (ρ ≫ σ) f) H) (lowerChartEquivalence_comp a b f E σ ρ)

theorem uaLine_reindex (a b : Γ ⟶ smallFamilyCodes.{u})
    (f : liftedDecode a ⟶ liftedDecode b) (E : HomotopyEquivalence f) (σ : Δ ⟶ Γ) :
    (uaLine a b f E).reindex (liftSub (interval Γ) σ) =
      uaLine (σ ≫ a) (σ ≫ b) (Functor.whiskerLeft σ.mapElements f) (E.reindex σ) := by
  apply Term.ext
  intro x
  have h := congrArg (fun ρ : raisedContext (representable.{u} x.obj.unop) ⟶ Γ =>
    (chartCode a b f E ρ).app x.obj (chartPoint x))
    (chart_substitution σ (intervalBase x))
  exact h.trans (congrArg (fun c => c.app x.obj (chartPoint x))
    (chartCode_comp a b f E σ (chart (intervalBase x))))

theorem ua_reindex (a b : Γ ⟶ smallFamilyCodes.{u})
    (f : liftedDecode a ⟶ liftedDecode b) (E : HomotopyEquivalence f) (σ : Δ ⟶ Γ) :
    reindexPath (ua a b f E) σ =
      ua (σ ≫ a) (σ ≫ b) (Functor.whiskerLeft σ.mapElements f) (E.reindex σ) := by
  apply eq_of_heq
  apply pathTerm_hext
  exact uaLine_reindex a b f E σ

theorem equivalencePathSection_pair (c : Term (equivalences a b)) :
    (equivalencePathSection a b).reindex (pair (A := equivalences a b) (𝟙 Γ) c) =
      ua a b
        (Functor.whiskerLeft (pair (A := equivalences a b) (𝟙 Γ) c).mapElements (genericEquivalence a b).1)
        ((genericEquivalence a b).2.reindex (pair (A := equivalences a b) (𝟙 Γ) c)) := by
  have h := Term.map_iso_roundtrip
    (pathReindexIso (reindex (family Γ) (projection (interval Γ)))
      (term a) (term b) (projection (equivalences a b))).symm
    (ua (projection (equivalences a b) ≫ a) (projection (equivalences a b) ≫ b)
      (genericEquivalence a b).1 (genericEquivalence a b).2)
  exact (pathSection_pair (equivalencePathSection a b) c).symm.trans
    ((congrArg (fun p => reindexPath p (pair (A := equivalences a b) (𝟙 Γ) c)) h).trans
      (ua_reindex _ _ _ _ (pair (A := equivalences a b) (𝟙 Γ) c)))

end SmallUniverse.NativeUnivalence
end SquareKit.Cubical.Presheaf
