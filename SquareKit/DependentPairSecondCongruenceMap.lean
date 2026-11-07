import SquareKit.DependentPairFirstCongruenceMap
import SquareKit.DependentPairMapAssembly

namespace SquareKit.DependentPairJudgments
open DependentTheoryMaps DependentPairPresentations Elimination Judgment
namespace EFullCertificate
variable {I : Type} {premise : I → Judgment eliminationSignature}

abbrev Family (Γ : Context eliminationSignature V) (A : EExpr V) (B : EExpr (Fin 1 ⊕ V)) :=
  ∀ {W} (Δ : Context eliminationSignature W) (σ : Fin 1 ⊕ V → EExpr W),
    CertificateEnvironment.Env (R := eliminationPresentation) (premise := premise) (Γ.extend A) Δ σ →
    Cert (premise := premise) (type Δ (Expr.subst σ B))

private def familyRename {Γ : Context eliminationSignature V} {A : EExpr V} {B : EExpr (Fin 1 ⊕ V)}
    (family : Family (premise := premise) Γ A B) {Δ : Context eliminationSignature W} (ρ : V → W)
    (env : CertificateEnvironment.Env (R := eliminationPresentation) (premise := premise) Γ Δ (fun v => .var (ρ v)))
    (hA : Cert (premise := premise) (type Δ (Expr.rename ρ A))) :
    Cert (premise := premise) (type (Δ.extend (Expr.rename ρ A)) (Expr.rename (Sum.map id ρ) B)) := by
  have hA' : Cert (premise := premise) (type Δ (Expr.subst (fun v => .var (ρ v)) A)) := by
    simpa only [Expr.subst_vars] using hA
  have h := family _ _ (CertificateEnvironment.lift TypedSubstitution.fullEliminationStructural env A hA')
  have eq : Expr.lift (n := 1) (fun v => Expr.var (S := eliminationSignature) (ρ v)) =
      fun v => Expr.var (Sum.map id ρ v) := by funext v; cases v <;> rfl
  simpa only [Expr.subst_vars, eq] using h

private theorem inst_ren (B : EExpr (Fin 1 ⊕ V)) (f : EExpr (Fin 1 ⊕ V)) :
    instantiate (Expr.rename (Sum.map id Sum.inr) B) f =
      Expr.subst (Sum.elim (fun _ : Fin 1 => f) (fun v => Expr.var (Sum.inr v))) B := by
  rw [instantiate, Expr.subst_rename]
  congr 1
  funext v
  cases v <;> rfl

/-- Dependent motives agree by family substitution and first-projection congruence. -/
def secondMotiveCong {Γ : Context eliminationSignature V} {A A' : EExpr V} {B B' : EExpr (Fin 1 ⊕ V)}
    (hΓ : Cert (premise := premise) (ctx Γ)) (hA : Cert (premise := premise) (type Γ A))
    (hA' : Cert (premise := premise) (type Γ A'))
    (hB : Cert (premise := premise) (type (Γ.extend A) B))
    (_hB' : Cert (premise := premise) (type (Γ.extend A') B'))
    (hAA' : Cert (premise := premise) (typeEq Γ A A'))
    (family : Family (premise := premise) Γ A B)
    (family' : Family (premise := premise) Γ A' B')
    (eqFamily : ∀ {W} (Δ : Context eliminationSignature W) (σ : Fin 1 ⊕ V → EExpr W),
      CertificateEnvironment.Env (R := eliminationPresentation) (premise := premise) (Γ.extend A) Δ σ →
      Cert (premise := premise) (typeEq Δ (Expr.subst σ B) (Expr.subst σ B'))) :
    Cert (premise := premise) (typeEq (Γ.extend (S A B)) (secondMotive A B) (secondMotive A' B')) := by
  let Δ := Γ.extend (S A B)
  let Aw := Expr.rename (Sum.inr : V → Fin 1 ⊕ V) A
  let Aw' := Expr.rename (Sum.inr : V → Fin 1 ⊕ V) A'
  let Bw := Expr.rename (Sum.map id (Sum.inr : V → Fin 1 ⊕ V)) B
  let Bw' := Expr.rename (Sum.map id (Sum.inr : V → Fin 1 ⊕ V)) B'
  have hS := formation hΓ hA hB
  have env := CertificateEnvironment.weakenTarget TypedSubstitution.fullEliminationStructural
    (CertificateEnvironment.identity TypedSubstitution.fullEliminationStructural Γ hΓ) (S A B) hS
  have ha : Cert (premise := premise) (type Δ Aw) := CertificateEnvironment.weaken TypedSubstitution.fullEliminationStructural Γ (S A B) (.type A) hΓ hS hA
  have ha' : Cert (premise := premise) (type Δ Aw') := CertificateEnvironment.weaken TypedSubstitution.fullEliminationStructural Γ (S A B) (.type A') hΓ hS hA'
  have haa : Cert (premise := premise) (typeEq Δ Aw Aw') := CertificateEnvironment.weaken TypedSubstitution.fullEliminationStructural Γ (S A B) (.typeEq A A') hΓ hS hAA'
  have hb := familyRename family Sum.inr env ha
  have hb' := familyRename family' Sum.inr env ha'
  have haSub : Cert (premise := premise) (type Δ (Expr.subst (fun v => .var (Sum.inr v)) A)) := by simpa only [Expr.subst_vars] using ha
  have envA := CertificateEnvironment.lift TypedSubstitution.fullEliminationStructural env A haSub
  have hbb : Cert (premise := premise) (typeEq (Δ.extend Aw) Bw Bw') := by
    have h := eqFamily _ _ envA
    have eq : Expr.lift (n := 1) (fun v : V => Expr.var (S := eliminationSignature) (Sum.inr (α := Fin 1) v)) =
        fun v => Expr.var (Sum.map id Sum.inr v) := by funext v; cases v <;> rfl
    simpa only [Expr.rename, eq, Expr.subst_vars] using h
  have hsEq : Cert (premise := premise) (typeEq Δ (S Aw Bw) (S Aw' Bw')) := by
    let ps : ∀ i : Fin 7, Cert (premise := premise)
        ((EliminationCongruence.schema (.formation Δ Aw Aw' Bw Bw')).premises.get i) :=
      Fin.cases env.context (Fin.cases ha (Fin.cases ha' (Fin.cases hb (Fin.cases hb'
        (Fin.cases haa (Fin.cases hbb (fun i => nomatch i)))))))
    exact CertificateEnvironment.replay (fun _ h => h.property ▸ ps h.val)
      (TypedSubstitution.fullEliminationCongruence.certificate (.formation Δ Aw Aw' Bw Bw'))
  have hq : Cert (premise := premise) (term Δ (.var (.inl 0)) (S Aw Bw)) := by
    have h := structural (.variable Δ (.inl 0)) (Fin.cases env.context (fun i => nomatch i))
    have eq : Expr.rename (Sum.inr : V → Fin 1 ⊕ V) (S A B) = S Aw Bw := by
      rw [← Expr.subst_vars, subst_S]
      have liftEq : Expr.lift (n := 1) (fun v : V => Expr.var (S := eliminationSignature) (Sum.inr (α := Fin 1) v)) =
          fun v => Expr.var (Sum.map id Sum.inr v) := by funext v; cases v <;> rfl
      rw [liftEq, Expr.subst_vars, Expr.subst_vars]
    simpa only [StructuralRule.schema, term, Δ, Context.lookup, eq] using h
  have hq' := structural (.convert Δ (.var (.inl 0)) (S Aw Bw) (S Aw' Bw')) (Fin.cases hq (Fin.cases hsEq (fun i => nomatch i)))
  have hf := first env.context ha hb hq
  have hf' := first env.context ha' hb' hq'
  have haaSym := structural (.typeSymm Δ Aw Aw') (Fin.cases haa (fun i => nomatch i))
  have hf'common := structural (.convert Δ _ Aw' Aw) (Fin.cases hf' (Fin.cases haaSym (fun i => nomatch i)))
  have hqq := structural (.termRefl Δ (.var (.inl 0)) (S Aw Bw)) (Fin.cases hq (fun i => nomatch i))
  have hff := firstCong env.context ha ha' hb hb' haa hbb hqq hf hf'common
  have envW := CertificateEnvironment.weakenTarget TypedSubstitution.fullEliminationStructural env Aw ha
  have hx := structural (.variable (Δ.extend Aw) (.inl 0)) (Fin.cases envW.context (fun i => nomatch i))
  have haaW := CertificateEnvironment.weaken TypedSubstitution.fullEliminationStructural Δ Aw (.typeEq Aw Aw') env.context ha haa
  have hx' := structural (.convert (Δ.extend Aw) (.var (.inl 0)) (Expr.rename Sum.inr Aw) (Expr.rename Sum.inr Aw')) (Fin.cases hx (Fin.cases haaW (fun i => nomatch i)))
  have hxSub : Cert (premise := premise) (term (Δ.extend Aw) (.var (.inl 0))
      (Expr.subst (fun v : V => Expr.rename Sum.inr (Expr.var (Sum.inr v))) A')) := by
    simpa only [StructuralRule.schema, term, Aw', Expr.rename, Expr.subst_vars, Expr.rename_comp, Function.comp_def] using hx'
  have envCross := CertificateEnvironment.extendSource envW A' (.var (.inl 0)) hxSub
  have hbCross : Cert (premise := premise) (type (Δ.extend Aw) Bw') := by
    have h := family' _ _ envCross
    have eq : (Sum.elim (fun _ : Fin 1 => (Expr.var (S := eliminationSignature) (Sum.inl (0 : Fin 1))))
        (fun v : V => Expr.rename Sum.inr (Expr.var (Sum.inr v)))) =
        (fun v => Expr.var (Sum.map id (Sum.inr : V → Fin 1 ⊕ V) v)) := by
      funext v
      cases v with
      | inl i => have : i = 0 := Subsingleton.elim _ _; subst i; rfl
      | inr v => rfl
    simp only [Expr.rename] at h eq
    simpa only [eq, Expr.subst_vars] using h
  have hfSub : Cert (premise := premise) (term Δ (Elimination.first Aw Bw (.var (.inl 0))) (Expr.subst (fun v : V => .var (Sum.inr v)) A)) := by
    simpa only [Expr.subst_vars] using hf
  have heq := eqFamily _ _ (CertificateEnvironment.extendSource env A _ hfSub)
  have heq' := structural (.familyCong Δ Aw Bw' _ _) (Fin.cases env.context (Fin.cases ha (Fin.cases hbCross (Fin.cases hff (fun i => nomatch i)))))
  have heqInst : Cert (premise := premise) (typeEq Δ
      (instantiate Bw (Elimination.first Aw Bw (.var (.inl 0))))
      (instantiate Bw' (Elimination.first Aw Bw (.var (.inl 0))))) := by
    simpa only [Bw, Bw', inst_ren, Expr.rename] using heq
  exact structural (.typeTrans Δ _ _ _) (Fin.cases heqInst (Fin.cases heq' (fun i => nomatch i)))
end EFullCertificate

/-- Second projection congruence uses exactly the ten translated source premises. -/
def GSecondCongruence (Γ : Context projectionSignature V) (A A' : PExpr V)
    (B B' : PExpr (Fin 1 ⊕ V)) (p p' : PExpr V) :
    GCongruenceCertificate (.second Γ A A' B B' p p') := by
  let premise := GCongruencePremises (.second Γ A A' B B' p p')
  have hΓ : EFullCertificate.Cert (premise := premise) (ctx (Γ.map G)) := .hyp (0 : Fin 10)
  have hA : EFullCertificate.Cert (premise := premise) (type (Γ.map G) (G.act A)) := .hyp (1 : Fin 10)
  have hA' : EFullCertificate.Cert (premise := premise) (type (Γ.map G) (G.act A')) := .hyp (2 : Fin 10)
  have hB : EFullCertificate.Cert (premise := premise) (type ((Γ.map G).extend (G.act A)) (G.act B)) := .hyp (3 : Fin 10)
  have hB' : EFullCertificate.Cert (premise := premise) (type ((Γ.map G).extend (G.act A')) (G.act B')) := .hyp (4 : Fin 10)
  have hAA' : EFullCertificate.Cert (premise := premise) (typeEq (Γ.map G) (G.act A) (G.act A')) := .hyp (5 : Fin 10)
  have hBB' : EFullCertificate.Cert (premise := premise) (typeEq ((Γ.map G).extend (G.act A)) (G.act B) (G.act B')) := .hyp (6 : Fin 10)
  have hpp' : EFullCertificate.Cert (premise := premise) (termEq (Γ.map G) (G.act p) (G.act p') (S (G.act A) (G.act B))) := by
    have h : EFullCertificate.Cert (premise := premise) (premise (7 : Fin 10)) := .hyp _
    change EFullCertificate.Cert (map G (termEq Γ p p' (Projection.P A B))) at h
    simpa only [map, mapForm, termEq, G_P] using h

  have family : EFullCertificate.Family (premise := premise) (Γ.map G) (G.act A) (G.act B) :=
    by
    intro W Δ σ env
    exact MetavariableCertificate.apply (premise := premise) (3 : Fin 10) Δ σ env.context env.component
  have family' : EFullCertificate.Family (premise := premise) (Γ.map G) (G.act A') (G.act B') :=
    by
    intro W Δ σ env
    exact MetavariableCertificate.apply (premise := premise) (4 : Fin 10) Δ σ env.context env.component
  have eqFamily : ∀ {W} (Δ : Context eliminationSignature W) (σ : Fin 1 ⊕ V → EExpr W),
      CertificateEnvironment.Env (R := eliminationPresentation) (premise := premise)
        ((Γ.map G).extend (G.act A)) Δ σ →
      EFullCertificate.Cert (premise := premise) (typeEq Δ (Expr.subst σ (G.act B)) (Expr.subst σ (G.act B'))) :=
    by
    intro W Δ σ env
    exact MetavariableCertificate.apply (premise := premise) (6 : Fin 10) Δ σ env.context env.component
  have hDD' := EFullCertificate.secondMotiveCong hΓ hA hA' hB hB' hAA' family family' eqFamily
  have cΓ : ECertificate.Cert (premise := premise) (ctx (Γ.map G)) := .hyp (0 : Fin 10)
  have cA : ECertificate.Cert (premise := premise) (type (Γ.map G) (G.act A)) := .hyp (1 : Fin 10)
  have cA' : ECertificate.Cert (premise := premise) (type (Γ.map G) (G.act A')) := .hyp (2 : Fin 10)
  have cB : ECertificate.Cert (premise := premise) (type ((Γ.map G).extend (G.act A)) (G.act B)) := .hyp (3 : Fin 10)
  have cB' : ECertificate.Cert (premise := premise) (type ((Γ.map G).extend (G.act A')) (G.act B')) := .hyp (4 : Fin 10)
  have cf : ECertificate.Family (premise := premise) (Γ.map G) (G.act A) (G.act B) :=
    by
    intro W Δ σ env
    exact MetavariableCertificate.apply (premise := premise) (3 : Fin 10) Δ σ env.context env.component
  have cf' : ECertificate.Family (premise := premise) (Γ.map G) (G.act A') (G.act B') :=
    by
    intro W Δ σ env
    exact MetavariableCertificate.apply (premise := premise) (4 : Fin 10) Δ σ env.context env.component
  have hD := (ECertificate.secondMotiveType cΓ cA cB cf).mapRules eliminationInclusion
  have hD' := (ECertificate.secondMotiveType cΓ cA' cB' cf').mapRules eliminationInclusion
  have he := (ECertificate.secondBranch cΓ cA cB cf).mapRules eliminationInclusion
  have he' := (ECertificate.secondBranch cΓ cA' cB' cf').mapRules eliminationInclusion
  have hee' := EFullCertificate.structural (.termRefl (branchContext (Γ.map G) (G.act A) (G.act B))
    (Expr.rename flattenToNested (.var (.inl 1)))
    (branchType (G.act A) (G.act B) (secondMotive (G.act A) (G.act B))))
    (Fin.cases he (fun i => nomatch i))
  have hp : EFullCertificate.Cert (premise := premise) (term (Γ.map G)
      (Elimination.split (G.act A) (G.act B) (secondMotive (G.act A) (G.act B)) (.var (.inl 1)) (G.act p))
      (instantiate (secondMotive (G.act A) (G.act B)) (G.act p))) := by
    have h : EFullCertificate.Cert (premise := premise) (premise (8 : Fin 10)) := .hyp _
    change EFullCertificate.Cert (map G (term Γ (Projection.snd A B p) (instantiate B (Projection.fst A B p)))) at h
    rw [secondMotive_at]
    simpa only [map, mapForm, term, G_second, GCertificates.map_instantiate, G_first,
      secondMotive_at, Elimination.second, secondMotive] using h
  have hp' : EFullCertificate.Cert (premise := premise) (term (Γ.map G)
      (Elimination.split (G.act A') (G.act B') (secondMotive (G.act A') (G.act B')) (.var (.inl 1)) (G.act p'))
      (instantiate (secondMotive (G.act A) (G.act B)) (G.act p))) := by
    have h : EFullCertificate.Cert (premise := premise) (premise (9 : Fin 10)) := .hyp _
    change EFullCertificate.Cert (map G (term Γ (Projection.snd A' B' p') (instantiate B (Projection.fst A B p)))) at h
    rw [secondMotive_at]
    simpa only [map, mapForm, term, G_second, GCertificates.map_instantiate, G_first,
      secondMotive_at, Elimination.second, secondMotive] using h
  let r := EliminationCongruence.split (Γ.map G) (G.act A) (G.act A') (G.act B) (G.act B')
    (secondMotive (G.act A) (G.act B)) (secondMotive (G.act A') (G.act B'))
    (.var (.inl 1)) (.var (.inl 1)) (G.act p) (G.act p')
  let ps : ∀ i : Fin 16, EFullCertificate.Cert (premise := premise) (r.schema.premises.get i) :=
    Fin.cases hΓ (Fin.cases hA (Fin.cases hA' (Fin.cases hB (Fin.cases hB' (Fin.cases hAA' (Fin.cases hBB'
      (Fin.cases hD (Fin.cases hD' (Fin.cases hDD' (Fin.cases he (Fin.cases he'
      (Fin.cases hee' (Fin.cases hpp' (Fin.cases hp (Fin.cases hp' (fun i => nomatch i))))))))))))))))
  have result : EFullCertificate.Cert (premise := premise) r.schema.conclusion := CertificateEnvironment.replay (fun _ h => h.property ▸ ps h.val)
    (TypedSubstitution.fullEliminationCongruence.certificate r)
  change EFullCertificate.Cert (premise := premise) (termEq (Γ.map G)
    (Elimination.split (G.act A) (G.act B) (secondMotive (G.act A) (G.act B)) (.var (.inl 1)) (G.act p))
    (Elimination.split (G.act A') (G.act B') (secondMotive (G.act A') (G.act B')) (.var (.inl 1)) (G.act p'))
    (instantiate (secondMotive (G.act A) (G.act B)) (G.act p))) at result
  rw [secondMotive_at] at result
  change EFullCertificate.Cert (premise := premise)
    (map G (termEq Γ (Projection.snd A B p) (Projection.snd A' B' p') (instantiate B (Projection.fst A B p))))
  simpa only [r, EliminationCongruence.schema, map, mapForm, termEq, G_second,
    GCertificates.map_instantiate, G_first, Elimination.second, secondMotive_at, secondMotive] using result

end SquareKit.DependentPairJudgments
