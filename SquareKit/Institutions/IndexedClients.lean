import SquareKit.Institutions.Capabilities
import Applications.Languages.ExactRewrites

namespace SquareKit.Institutions
open LanguageWitnesses

/-- A semantic observation includes either a selected parse or its refutation.
The universe lift permits symbolic parser syntax as a realization. -/
def languageSetting {α : Type} (P : Language α) : Setting.{0,0,1} :=
  ⟨List α, Unit, fun _ w => ULift.{1} (Decision (P w))⟩

def languageConnection {α : Type} {P Q : Language α} (e : ∀ w, Iso (P w) (Q w)) :
    Connection (languageSetting P) (languageSetting Q) :=
  ⟨id, id, fun _ w d => ⟨d.down.map (e w)⟩⟩

def parserRealization {α : Type} [DecidableEq α] (P : Language α) : Realization (languageSetting P) :=
  ⟨fun _ _ => Parser P, fun _ w p => ⟨p.parse w⟩⟩

theorem parse_transport {α : Type} [DecidableEq α] {P Q : Language α}
    (e : ∀ w, Iso (P w) (Q w)) (p : Parser P) (w : List α) :
    (Parser.transport e p).parse w = (p.parse w).map (e w) := by
  induction w generalizing P Q with
  | nil => rfl
  | cons a w ih => exact ih (fun w => e (a :: w)) (p.derive a)

def parserMap {α : Type} [DecidableEq α] {P Q : Language α} (e : ∀ w, Iso (P w) (Q w)) :
    RealizationMap (languageConnection e) (parserRealization P) (parserRealization Q) :=
  ⟨fun _ _ => Parser.transport e, fun _ w p => congrArg ULift.up (parse_transport e p w)⟩

theorem parser_pasting {α : Type} [DecidableEq α] {P Q R : Language α}
    (e : ∀ w, Iso (P w) (Q w)) (f : ∀ w, Iso (Q w) (R w)) (p : Parser P) (w : List α) :
    (Parser.transport f (.transport e p)).parse w = (p.parse w).map ((e w).trans (f w)) := by
  have h := congrArg ULift.down (((parserMap f).comp (parserMap e)).commutes () w p)
  exact h.trans (Decision.map_trans _ _ _)

/-- Constructor contexts use the existing local constructor/observer induction,
then the capability map, retaining the selected decision rather than its test. -/
theorem parser_context {α : Type} [DecidableEq α] {P Q R : Language α}
    (e : ∀ w, Iso (P w) (Q w)) (f : ∀ w, Iso (Q w) (R w)) {n}
    (t : IndexedCompositional.Term LanguageWitnesses.IndexedCompositional.signature
      LanguageWitnesses.IndexedCompositional.Source (P,n))
    (w : List α) (hw : w.length ≤ n) :
    (Parser.transport f (.transport e
      (IndexedCompositional.Term.fold LanguageWitnesses.IndexedCompositional.sourceAlgebra
        (fun _ p => p) t))).parse w =
    ((IndexedCompositional.Term.fold LanguageWitnesses.IndexedCompositional.targetAlgebra
      LanguageWitnesses.IndexedCompositional.unfold t).lookup w hw).map ((e w).trans (f w)) := by
  rw [parser_pasting, LanguageWitnesses.IndexedCompositional.recovered]

/-- Local capability composition also justifies fusion at holes underneath
arbitrary supported constructors, through the existing contextual induction. -/
theorem parser_contextual_fusion {α : Type} [DecidableEq α] {P : Language α} {n}
    (context : IndexedCompositional.Term LanguageWitnesses.IndexedCompositional.signature
      LanguageWitnesses.IndexedCompositional.TransportPair (P,n))
    (w : List α) (hw : w.length ≤ n) :
    (IndexedCompositional.Term.fold LanguageWitnesses.IndexedCompositional.sourceAlgebra
      (fun _ p => p) (context.bind LanguageWitnesses.IndexedCompositional.TransportPair.expanded)).parse w =
    (IndexedCompositional.Term.fold LanguageWitnesses.IndexedCompositional.sourceAlgebra
      (fun _ p => p) (context.bind LanguageWitnesses.IndexedCompositional.TransportPair.fused)).parse w := by
  apply LanguageWitnesses.IndexedCompositional.contextual_exact _ _ _ context w hw
  intro j site word _
  exact (parser_pasting site.first site.second site.parser word).trans
    (parse_transport (fun word => (site.first word).trans (site.second word)) site.parser word).symm

/-- A dependent family is a small capability with no proof syntax or compiler. -/
def familySetting {Γ : Type} (P : Γ → Type) : Setting.{0,0,0} :=
  ⟨Unit, Γ, fun γ _ => P γ⟩
def reindexConnection {Γ Δ : Type} (P : Γ → Type) (σ : Δ → Γ) :
    Connection (familySetting P) (familySetting (P ∘ σ)) :=
  ⟨id, σ, fun _ _ => id⟩

def Connection.section {Γ Δ : Type} {P : Γ → Type} {Q : Δ → Type}
    (f : Connection (familySetting P) (familySetting Q)) (s : ∀ γ, P γ) : ∀ δ, Q δ :=
  fun δ => f.evidence δ () (s (f.reduct δ))

theorem section_comp {Γ Δ Θ : Type} {P : Γ → Type} {Q : Δ → Type} {R : Θ → Type}
    (g : Connection (familySetting Q) (familySetting R))
    (f : Connection (familySetting P) (familySetting Q)) (s : ∀ γ, P γ) :
    (g.comp f).section s = g.section (f.section s) := by
  funext θ
  cases h : f.sentence ()
  rfl

theorem section_reindex_twice {Γ Δ Θ : Type} (P : Γ → Type) (σ : Δ → Γ) (τ : Θ → Δ)
    (s : ∀ γ, P γ) :
    ((reindexConnection (P ∘ σ) τ).comp (reindexConnection P σ)).section s =
      fun θ => s (σ (τ θ)) := rfl

end SquareKit.Institutions
