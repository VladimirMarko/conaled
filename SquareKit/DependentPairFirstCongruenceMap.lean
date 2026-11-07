import SquareKit.DependentPairDirectCongruenceMaps

/-! First-projection congruence is a derived split-congruence certificate. -/
namespace SquareKit.DependentPairJudgments
open DependentTheoryMaps DependentPairPresentations Elimination Judgment

namespace EFullCertificate
variable {I : Type} {premise : I → Judgment eliminationSignature}

abbrev Cert := MetavariableCertificate eliminationPresentation premise

def structural (r : StructuralRule eliminationSignature)
    (ps : ∀ i : Fin (StructuralRule.schema r).premises.length,
      Cert (premise := premise) ((StructuralRule.schema r).premises.get i)) :
    Cert (premise := premise) (StructuralRule.schema r).conclusion :=
  CertificateEnvironment.rule TypedSubstitution.fullEliminationStructural r ps

def primitive (r : EliminationRule)
    (ps : ∀ i : Fin (EliminationRule.schema r).premises.length,
      Cert (premise := premise) ((EliminationRule.schema r).premises.get i)) :
    Cert (premise := premise) (EliminationRule.schema r).conclusion :=
  CertificateEnvironment.replay (fun _ h => h.property ▸ ps h.val)
    (TypedSubstitution.fullEliminationPrimitive.certificate r)

private def congruence (r : EliminationCongruence)
    (ps : ∀ i : Fin (EliminationCongruence.schema r).premises.length,
      Cert (premise := premise) ((EliminationCongruence.schema r).premises.get i)) :
    Cert (premise := premise) (EliminationCongruence.schema r).conclusion :=
  CertificateEnvironment.replay (fun _ h => h.property ▸ ps h.val)
    (TypedSubstitution.fullEliminationCongruence.certificate r)

def formation {Γ : Context eliminationSignature V} {A : EExpr V} {B : EExpr (Fin 1 ⊕ V)}
    (hΓ : Cert (premise := premise) (ctx Γ))
    (hA : Cert (premise := premise) (type Γ A))
    (hB : Cert (premise := premise) (type (Γ.extend A) B)) :
    Cert (premise := premise) (type Γ (S A B)) :=
  primitive (.formation Γ A B)
    (Fin.cases hΓ (Fin.cases hA (Fin.cases hB (fun i => nomatch i))))

def firstBranch {Γ : Context eliminationSignature V}
    {A : EExpr V} {B : EExpr (Fin 1 ⊕ V)}
    (hΓ : Cert (premise := premise) (ctx Γ))
    (hA : Cert (premise := premise) (type Γ A))
    (hB : Cert (premise := premise) (type (Γ.extend A) B)) :
    Cert (premise := premise) (term (branchContext Γ A B)
      (Expr.rename flattenToNested (.var (.inl 0))) (branchType A B (Expr.rename Sum.inr A))) := by
  have hΓA := structural (.extend Γ A) (Fin.cases hΓ (Fin.cases hA (fun i => nomatch i)))
  have hΓAB := structural (.extend (Γ.extend A) B) (Fin.cases hΓA (Fin.cases hB (fun i => nomatch i)))
  have hx := structural (.variable ((Γ.extend A).extend B) (Sum.inr (Sum.inl (0 : Fin 1))))
    (Fin.cases hΓAB (fun i => nomatch i))
  simpa only [StructuralRule.schema, Judgment.term, branchContext, first_branch_type,
    Context.lookup, Expr.rename_comp, Expr.rename, flattenToNested, Fin.val_zero, ite_true] using hx

/-- First projection typing in the full target presentation, derived from split. -/
def first {Γ : Context eliminationSignature V} {A p : EExpr V} {B : EExpr (Fin 1 ⊕ V)}
    (hΓ : Cert (premise := premise) (ctx Γ))
    (hA : Cert (premise := premise) (type Γ A))
    (hB : Cert (premise := premise) (type (Γ.extend A) B))
    (hp : Cert (premise := premise) (term Γ p (S A B))) :
    Cert (premise := premise) (term Γ (Elimination.first A B p) A) := by
  have hS := formation hΓ hA hB
  have hD := CertificateEnvironment.weaken TypedSubstitution.fullEliminationStructural
    Γ (S A B) (.type A) hΓ hS hA
  have he := firstBranch hΓ hA hB
  have hs := primitive (.split Γ A B (Expr.rename Sum.inr A) (.var (.inl 0)) p)
    (Fin.cases hΓ (Fin.cases hA (Fin.cases hB (Fin.cases hD (Fin.cases he
      (Fin.cases hp (fun i => nomatch i)))))))
  simpa only [EliminationRule.schema, term, Elimination.first, instantiate_constant] using hs

/-- Arbitrary certificate assumptions suffice: the motives are weakenings of
A and A', and the branches are the same selected first variable. -/
def firstCong {Γ : Context eliminationSignature V} {A A' p p' : EExpr V}
    {B B' : EExpr (Fin 1 ⊕ V)}
    (hΓ : Cert (premise := premise) (ctx Γ))
    (hA : Cert (premise := premise) (type Γ A))
    (hA' : Cert (premise := premise) (type Γ A'))
    (hB : Cert (premise := premise) (type (Γ.extend A) B))
    (hB' : Cert (premise := premise) (type (Γ.extend A') B'))
    (hAA' : Cert (premise := premise) (typeEq Γ A A'))
    (hBB' : Cert (premise := premise) (typeEq (Γ.extend A) B B'))
    (hpp' : Cert (premise := premise) (termEq Γ p p' (S A B)))
    (hp : Cert (premise := premise) (term Γ (Elimination.first A B p) A))
    (hp' : Cert (premise := premise) (term Γ (Elimination.first A' B' p') A)) :
    Cert (premise := premise) (termEq Γ (Elimination.first A B p) (Elimination.first A' B' p') A) := by
  have hS := formation hΓ hA hB
  have hS' := formation hΓ hA' hB'
  have hD := CertificateEnvironment.weaken TypedSubstitution.fullEliminationStructural
    Γ (S A B) (.type A) hΓ hS hA
  have hD' := CertificateEnvironment.weaken TypedSubstitution.fullEliminationStructural
    Γ (S A' B') (.type A') hΓ hS' hA'
  have hDD' := CertificateEnvironment.weaken TypedSubstitution.fullEliminationStructural
    Γ (S A B) (.typeEq A A') hΓ hS hAA'
  have he := firstBranch hΓ hA hB
  have he' := firstBranch hΓ hA' hB'
  have hee' := structural (.termRefl (branchContext Γ A B)
    (Expr.rename flattenToNested (.var (.inl 0))) (branchType A B (Expr.rename Sum.inr A)))
    (Fin.cases he (fun i => nomatch i))
  have hpSplit : Cert (premise := premise) (term Γ
      (Elimination.split A B (Expr.rename Sum.inr A) (.var (.inl 0)) p)
      (instantiate (Expr.rename Sum.inr A) p)) := by
    simpa only [Elimination.first, instantiate_constant] using hp
  have hpSplit' : Cert (premise := premise) (term Γ
      (Elimination.split A' B' (Expr.rename Sum.inr A') (.var (.inl 0)) p')
      (instantiate (Expr.rename Sum.inr A) p)) := by
    simpa only [Elimination.first, instantiate_constant] using hp'
  have hs := congruence (.split Γ A A' B B' (Expr.rename Sum.inr A) (Expr.rename Sum.inr A')
    (.var (.inl 0)) (.var (.inl 0)) p p')
    (Fin.cases hΓ (Fin.cases hA (Fin.cases hA' (Fin.cases hB (Fin.cases hB' (Fin.cases hAA' (Fin.cases hBB'
      (Fin.cases hD (Fin.cases hD' (Fin.cases hDD'
      (Fin.cases he (Fin.cases he' (Fin.cases hee' (Fin.cases hpp'
      (Fin.cases hpSplit (Fin.cases hpSplit' (fun i => nomatch i)))))))))))))))))
  simpa only [EliminationCongruence.schema, termEq, Elimination.first, instantiate_constant] using hs

end EFullCertificate

/-- The source first-congruence rule uses precisely its ten translated premises. -/
def GFirstCongruence (Γ : Context projectionSignature V) (A A' : PExpr V)
    (B B' : PExpr (Fin 1 ⊕ V)) (p p' : PExpr V) :
    GCongruenceCertificate (.first Γ A A' B B' p p') := by
  let premise := GCongruencePremises (.first Γ A A' B B' p p')
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
  have hp : EFullCertificate.Cert (premise := premise) (term (Γ.map G) (Elimination.first (G.act A) (G.act B) (G.act p)) (G.act A)) := by
    have h : EFullCertificate.Cert (premise := premise) (premise (8 : Fin 10)) := .hyp _
    change EFullCertificate.Cert (map G (term Γ (Projection.fst A B p) A)) at h
    simpa only [map, mapForm, term, G_first] using h
  have hp' : EFullCertificate.Cert (premise := premise) (term (Γ.map G) (Elimination.first (G.act A') (G.act B') (G.act p')) (G.act A)) := by
    have h : EFullCertificate.Cert (premise := premise) (premise (9 : Fin 10)) := .hyp _
    change EFullCertificate.Cert (map G (term Γ (Projection.fst A' B' p') A)) at h
    simpa only [map, mapForm, term, G_first] using h
  change EFullCertificate.Cert (premise := premise)
    (map G (termEq Γ (Projection.fst A B p) (Projection.fst A' B' p') A))
  simpa only [map, mapForm, termEq, G_first] using
    EFullCertificate.firstCong hΓ hA hA' hB hB' hAA' hBB' hpp' hp hp'

end SquareKit.DependentPairJudgments
