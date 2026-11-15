import SquareKit.DependentPairEliminationCertificates

/-! The concrete projection-to-eliminator map checks every primitive rule. -/
namespace SquareKit.DependentPairJudgments
open DependentTheoryMaps DependentPairPresentations Elimination Judgment

abbrev GPrimitivePremises (r : ProjectionRule true) :=
  fun i : Fin (ProjectionRule.schema r).premises.length => map G ((ProjectionRule.schema r).premises.get i)

def GPrimitiveCertificate (r : ProjectionRule true) :
    MetavariableCertificate Eη (GPrimitivePremises r) (map G (ProjectionRule.schema r).conclusion) := by
  cases r with
  | formation Γ A B =>
    let premise := GPrimitivePremises (.formation Γ A B)
    have hΓ : MetavariableCertificate Eη premise (ctx (Γ.map G)) := .hyp (0 : Fin 3)
    have hA : MetavariableCertificate Eη premise (type (Γ.map G) (G.act A)) := .hyp (1 : Fin 3)
    have hB : MetavariableCertificate Eη premise (type ((Γ.map G).extend (G.act A)) (G.act B)) := .hyp (2 : Fin 3)
    simpa only [ProjectionRule.schema, EliminationRule.schema, map, mapForm, type, term, termEq,
      G_P, G_pair, G_first, G_second, GCertificates.map_instantiate] using ECertificate.formation hΓ hA hB
  | pair Γ A B a b =>
    let premise := GPrimitivePremises (.pair Γ A B a b)
    have hΓ : MetavariableCertificate Eη premise (ctx (Γ.map G)) := .hyp (0 : Fin 5)
    have hA : MetavariableCertificate Eη premise (type (Γ.map G) (G.act A)) := .hyp (1 : Fin 5)
    have hB : MetavariableCertificate Eη premise (type ((Γ.map G).extend (G.act A)) (G.act B)) := .hyp (2 : Fin 5)
    have ha : MetavariableCertificate Eη premise (term (Γ.map G) (G.act a) (G.act A)) := .hyp (3 : Fin 5)
    have hb : MetavariableCertificate Eη premise (term (Γ.map G) (G.act b) (instantiate (G.act B) (G.act a))) := by
      have h : MetavariableCertificate Eη premise (premise (4 : Fin 5)) := .hyp _
      change MetavariableCertificate Eη premise (map G (term Γ b (instantiate B a))) at h
      simpa only [premise, GPrimitivePremises, ProjectionRule.schema, ProjectionRule.components,
        ProjectionRule.family, List.get, map, mapForm, term, GCertificates.map_instantiate] using h
    simpa only [ProjectionRule.schema, EliminationRule.schema, map, mapForm, type, term, termEq,
      G_P, G_pair, G_first, G_second, GCertificates.map_instantiate] using ECertificate.primitive (.pack (Γ.map G) (G.act A) (G.act B) (G.act a) (G.act b)) (Fin.cases hΓ (Fin.cases hA (Fin.cases hB (Fin.cases ha (Fin.cases hb (fun i => nomatch i))))))
  | first Γ A B p =>
    let premise := GPrimitivePremises (.first Γ A B p)
    have hΓ : MetavariableCertificate Eη premise (ctx (Γ.map G)) := .hyp (0 : Fin 4)
    have hA : MetavariableCertificate Eη premise (type (Γ.map G) (G.act A)) := .hyp (1 : Fin 4)
    have hB : MetavariableCertificate Eη premise (type ((Γ.map G).extend (G.act A)) (G.act B)) := .hyp (2 : Fin 4)
    have hp : MetavariableCertificate Eη premise (term (Γ.map G) (G.act p) (S (G.act A) (G.act B))) := by
      have h : MetavariableCertificate Eη premise (premise (3 : Fin 4)) := .hyp _
      change MetavariableCertificate Eη premise (map G (term Γ p (Projection.P A B))) at h
      simpa only [premise, GPrimitivePremises, ProjectionRule.schema, ProjectionRule.argument,
        ProjectionRule.family, List.get, map, mapForm, term, G_P] using h
    simpa only [ProjectionRule.schema, EliminationRule.schema, map, mapForm, type, term, termEq,
      G_P, G_pair, G_first, G_second, GCertificates.map_instantiate] using ECertificate.first hΓ hA hB (G.act p) hp
  | second Γ A B p =>
    let premise := GPrimitivePremises (.second Γ A B p)
    have hΓ : MetavariableCertificate Eη premise (ctx (Γ.map G)) := .hyp (0 : Fin 4)
    have hA : MetavariableCertificate Eη premise (type (Γ.map G) (G.act A)) := .hyp (1 : Fin 4)
    have hB : MetavariableCertificate Eη premise (type ((Γ.map G).extend (G.act A)) (G.act B)) := .hyp (2 : Fin 4)
    have hp : MetavariableCertificate Eη premise (term (Γ.map G) (G.act p) (S (G.act A) (G.act B))) := by
      have h : MetavariableCertificate Eη premise (premise (3 : Fin 4)) := .hyp _
      change MetavariableCertificate Eη premise (map G (term Γ p (Projection.P A B))) at h
      simpa only [premise, GPrimitivePremises, ProjectionRule.schema, ProjectionRule.argument,
        ProjectionRule.family, List.get, map, mapForm, term, G_P] using h
    have family : ECertificate.Family (premise := premise) (Γ.map G) (G.act A) (G.act B) := by
      intro W Δ σ env
      exact MetavariableCertificate.apply (R := Eη) (premise := premise) (2 : Fin 4) Δ σ env.context env.component
    simpa only [ProjectionRule.schema, EliminationRule.schema, map, mapForm, type, term, termEq,
      G_P, G_pair, G_first, G_second, GCertificates.map_instantiate] using ECertificate.second hΓ hA hB family (G.act p) hp
  | firstBeta Γ A B a b =>
    let premise := GPrimitivePremises (.firstBeta Γ A B a b)
    have hΓ : MetavariableCertificate Eη premise (ctx (Γ.map G)) := .hyp (0 : Fin 5)
    have hA : MetavariableCertificate Eη premise (type (Γ.map G) (G.act A)) := .hyp (1 : Fin 5)
    have hB : MetavariableCertificate Eη premise (type ((Γ.map G).extend (G.act A)) (G.act B)) := .hyp (2 : Fin 5)
    have ha : MetavariableCertificate Eη premise (term (Γ.map G) (G.act a) (G.act A)) := .hyp (3 : Fin 5)
    have hb : MetavariableCertificate Eη premise (term (Γ.map G) (G.act b) (instantiate (G.act B) (G.act a))) := by
      have h : MetavariableCertificate Eη premise (premise (4 : Fin 5)) := .hyp _
      change MetavariableCertificate Eη premise (map G (term Γ b (instantiate B a))) at h
      simpa only [premise, GPrimitivePremises, ProjectionRule.schema, ProjectionRule.components,
        ProjectionRule.family, List.get, map, mapForm, term, GCertificates.map_instantiate] using h
    simpa only [ProjectionRule.schema, EliminationRule.schema, map, mapForm, type, term, termEq,
      G_P, G_pair, G_first, G_second, GCertificates.map_instantiate] using ECertificate.firstBeta hΓ hA hB (G.act a) (G.act b) ha hb
  | secondBeta Γ A B a b =>
    let premise := GPrimitivePremises (.secondBeta Γ A B a b)
    have hΓ : MetavariableCertificate Eη premise (ctx (Γ.map G)) := .hyp (0 : Fin 5)
    have hA : MetavariableCertificate Eη premise (type (Γ.map G) (G.act A)) := .hyp (1 : Fin 5)
    have hB : MetavariableCertificate Eη premise (type ((Γ.map G).extend (G.act A)) (G.act B)) := .hyp (2 : Fin 5)
    have ha : MetavariableCertificate Eη premise (term (Γ.map G) (G.act a) (G.act A)) := .hyp (3 : Fin 5)
    have hb : MetavariableCertificate Eη premise (term (Γ.map G) (G.act b) (instantiate (G.act B) (G.act a))) := by
      have h : MetavariableCertificate Eη premise (premise (4 : Fin 5)) := .hyp _
      change MetavariableCertificate Eη premise (map G (term Γ b (instantiate B a))) at h
      simpa only [premise, GPrimitivePremises, ProjectionRule.schema, ProjectionRule.components,
        ProjectionRule.family, List.get, map, mapForm, term, GCertificates.map_instantiate] using h
    have family : ECertificate.Family (premise := premise) (Γ.map G) (G.act A) (G.act B) := by
      intro W Δ σ env
      exact MetavariableCertificate.apply (R := Eη) (premise := premise) (2 : Fin 5) Δ σ env.context env.component
    simpa only [ProjectionRule.schema, EliminationRule.schema, map, mapForm, type, term, termEq,
      G_P, G_pair, G_first, G_second, GCertificates.map_instantiate] using ECertificate.secondBeta hΓ hA hB family (G.act a) (G.act b) ha hb
  | eta allowed Γ A B p =>
    let premise := GPrimitivePremises (.eta allowed Γ A B p)
    have hΓ : MetavariableCertificate Eη premise (ctx (Γ.map G)) := .hyp (0 : Fin 4)
    have hA : MetavariableCertificate Eη premise (type (Γ.map G) (G.act A)) := .hyp (1 : Fin 4)
    have hB : MetavariableCertificate Eη premise (type ((Γ.map G).extend (G.act A)) (G.act B)) := .hyp (2 : Fin 4)
    have hp : MetavariableCertificate Eη premise (term (Γ.map G) (G.act p) (S (G.act A) (G.act B))) := by
      have h : MetavariableCertificate Eη premise (premise (3 : Fin 4)) := .hyp _
      change MetavariableCertificate Eη premise (map G (term Γ p (Projection.P A B))) at h
      simpa only [premise, GPrimitivePremises, ProjectionRule.schema, ProjectionRule.argument,
        ProjectionRule.family, List.get, map, mapForm, term, G_P] using h
    simpa only [ProjectionRule.schema, EliminationRule.schema, map, mapForm, type, term, termEq,
      G_P, G_pair, G_first, G_second, GCertificates.map_instantiate] using ECertificate.primitive (.eta (Γ.map G) (G.act A) (G.act B) (G.act p)) (Fin.cases hΓ (Fin.cases hA (Fin.cases hB (Fin.cases hp (fun i => nomatch i)))))

end SquareKit.DependentPairJudgments
