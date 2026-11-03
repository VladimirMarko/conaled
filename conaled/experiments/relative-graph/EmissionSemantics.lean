import EmissionEncoding
import SquareKit.Internal.GraphEmissionSquares
import PrimitiveLaws

namespace EmissionSemantics
open SquareKit.Internal ConLeche ConLeche.SetTheory ConLeche.SetModel
open EmissionEncoding
abbrev E := CoreSyntax.Expr
universe w
variable {V : Type w} [SetTheory V] {env : ConLeche.Env}
variable (m : ConLeche.Model V env) (φ : ConLeche.Name → Nat)

def Holds (ρ : Nat → V) (e : E) (v : V) : Prop :=
  ∃ r, encode e = some r ∧ Denotes m.cval env φ ρ r v

variable {m φ}
theorem Holds.var (ρ : Nat → V) (i : Nat) : Holds m φ ρ (.bvar i) (ρ i) :=
  ⟨_, rfl, .bvar⟩

theorem Holds.app {ρ : Nat → V} {f a : E} {F A : V}
    (hf : Holds m φ ρ f F) (ha : Holds m φ ρ a A) :
    Holds m φ ρ (.app f a) (app F A) := by
  obtain ⟨f', hf, hF⟩ := hf
  obtain ⟨a', ha, hA⟩ := ha
  exact ⟨.app f' a', by simp [encode, hf, ha], .app hF hA⟩

theorem Holds.rename {ρ σ : Nat → V} {e : E} {v : V}
    (h : Holds m φ ρ e v) (r : Nat → Nat) (hr : ∀ i, σ (r i) = ρ i) :
    Holds m φ σ (e.rename r) v := by
  obtain ⟨e', he, hd⟩ := h
  induction e generalizing e' ρ σ r v with
  | bvar i =>
    cases he
    cases hd
    simpa only [CoreSyntax.Expr.rename, hr] using Holds.var (m := m) (φ := φ) σ (r i)
  | sort u =>
    simp only [encode, bind, pure, Option.bind_eq_some_iff, Option.some.injEq] at he
    obtain ⟨u', hu, rfl⟩ := he
    cases hd
    exact ⟨_, by simp [CoreSyntax.Expr.rename, encode, hu], .sort⟩
  | const n us =>
    simp only [encode, bind, pure, Option.bind_eq_some_iff, Option.some.injEq] at he
    obtain ⟨us', hus, rfl⟩ := he
    cases hd with
    | const hf hl => exact ⟨_, by simp [CoreSyntax.Expr.rename, encode, hus], .const hf hl⟩
  | app f a ihf iha =>
    simp only [encode, bind, pure, Option.bind_eq_some_iff, Option.some.injEq] at he
    obtain ⟨f', hf, a', ha, rfl⟩ := he
    cases hd with
    | app hF hA => exact (ihf r hr _ hf hF).app (iha r hr _ ha hA)
  | lam a b iha ihb =>
    simp only [encode, bind, pure, Option.bind_eq_some_iff, Option.some.injEq] at he
    obtain ⟨a', ha, b', hb, rfl⟩ := he
    have lift (x : V) : ∀ i, push x σ (CoreSyntax.liftRen r i) = push x ρ i := by
      intro i; cases i <;> simp [CoreSyntax.liftRen, push, hr]
    cases hd with
    | lam hA hF =>
      obtain ⟨ar, har, hAr⟩ := iha r hr _ ha hA
      obtain ⟨br, hbr⟩ := rename_encodable b (CoreSyntax.liftRen r) ⟨b', hb⟩
      refine ⟨.lam ar br, by simp [CoreSyntax.Expr.rename, encode, har, hbr], .lam hAr ?_⟩
      intro x hx
      obtain ⟨br', hbr', hd'⟩ := ihb (CoreSyntax.liftRen r) (lift x) _ hb (hF x hx)
      rw [hbr] at hbr'; cases hbr'; exact hd'
  | all a b iha ihb =>
    simp only [encode, bind, pure, Option.bind_eq_some_iff, Option.some.injEq] at he
    obtain ⟨a', ha, b', hb, rfl⟩ := he
    have lift (x : V) : ∀ i, push x σ (CoreSyntax.liftRen r i) = push x ρ i := by
      intro i; cases i <;> simp [CoreSyntax.liftRen, push, hr]
    cases hd with
    | pi hA hB =>
      obtain ⟨ar, har, hAr⟩ := iha r hr _ ha hA
      obtain ⟨br, hbr⟩ := rename_encodable b (CoreSyntax.liftRen r) ⟨b', hb⟩
      refine ⟨.forallE ar br, by simp [CoreSyntax.Expr.rename, encode, har, hbr], .pi hAr ?_⟩
      intro x hx
      obtain ⟨br', hbr', hd'⟩ := ihb (CoreSyntax.liftRen r) (lift x) _ hb (hB x hx)
      rw [hbr] at hbr'; cases hbr'; exact hd'

theorem Holds.shift {ρ : Nat → V} {e : E} {v : V}
    (h : Holds m φ ρ e v) (x : V) : Holds m φ (push x ρ) e.shift v :=
  h.rename Nat.succ (fun _ => rfl)

/-- Set carriers and function values, separated from the laws they satisfy. -/
structure Setting (V : Type w) where
  carrier : GraphTarget.Ty → V
  arrow : Graph.Arrow s t → V

structure Laws (S : Setting V) (u : ConLeche.Level) (φ : ConLeche.Name → Nat) : Prop where
  carrier_mem : ∀ s, S.carrier s ∈ˢ univ (ConLeche.Level.eval φ u)
  arrow : ∀ {s t} (f : Graph.Arrow s t) x, x ∈ˢ S.carrier s →
    app (S.arrow f) x ∈ˢ S.carrier t

noncomputable def interpretation (S : Setting V) (L : Laws S u φ) : Interpretation Graph.Arrow where
  Carrier s := {x : V // x ∈ˢ S.carrier s}
  arrow f x := ⟨app (S.arrow f) x.val, L.arrow f x.val x.property⟩

structure Compatible (S : Setting V) (ρ : Nat → V) (em : GraphEmissionPure.Model) : Prop where
  carrier : ∀ s, Holds m φ ρ (em.carrier s) (S.carrier s)
  arrow : ∀ {s t} (f : Graph.Arrow s t), Holds m φ ρ (em.arrow f) (S.arrow f)

theorem Compatible.shift {S : Setting V} {ρ : Nat → V} {em : GraphEmissionPure.Model}
    (h : Compatible (m := m) (φ := φ) S ρ em) (x : V) :
    Compatible (m := m) (φ := φ) S (push x ρ) em.shift where
  carrier s := (h.carrier s).shift x
  arrow f := by
    simpa only [GraphEmissionPure.Model.shift, GraphEmissionPure.arrow_map] using (h.arrow f).shift x

def AssignmentCompatible (S : Setting V) (L : Laws S u φ) (ρ : Nat → V)
    (a : GraphEmissionPure.Assignment Γ) (η : SquareKit.Internal.Env (interpretation S L) Γ) : Prop :=
  ∀ s (i : Var Γ s), Holds m φ ρ (a i) (η i).val

theorem assignment_extend {S : Setting V} {L : Laws S u φ} {ρ : Nat → V}
    {a : GraphEmissionPure.Assignment Γ} {η : SquareKit.Internal.Env (interpretation S L) Γ}
    (h : AssignmentCompatible (m := m) S L ρ a η) (x : (interpretation S L).Carrier s) :
    AssignmentCompatible (m := m) S L (push x.val ρ)
      (GraphEmissionPure.extend (GraphEmissionPure.shift a) (.bvar 0)) (η.extend x) := by
  intro t i
  cases i with
  | zero => exact Holds.var _ 0
  | succ i => exact (h _ i).shift x.val

theorem term_denotes {S : Setting V} {L : Laws S u φ} {ρ : Nat → V}
    {em : GraphEmissionPure.Model} {a : GraphEmissionPure.Assignment Γ}
    {η : SquareKit.Internal.Env (interpretation S L) Γ}
    (hm : Compatible (m := m) (φ := φ) S ρ em)
    (ha : AssignmentCompatible (m := m) S L ρ a η) (t : GraphTarget.Term Γ s) :
    Holds m φ ρ (GraphEmissionPure.term em a t) (t.eval (interpretation S L) η).val := by
  induction t with
  | var i => exact ha _ i
  | app f t ih => exact (hm.arrow f).app ih

theorem Holds.denotes {ρ : Nat → V} {e : E} {v : V} {r : ConLeche.Expr}
    (h : Holds m φ ρ e v) (he : encode e = some r) : Denotes m.cval env φ ρ r v := by
  obtain ⟨r', hr', hd⟩ := h
  rw [he] at hr'; cases hr'; exact hd

theorem Holds.eq {ρ : Nat → V} {em : GraphEmissionPure.Model} {a b : E} {A x y : V}
    (pr : GraphAdapter.Primitives m u φ) (hu : U.encode em.level = some u)
    (hA : Holds m φ ρ (em.carrier s) A) (hx : Holds m φ ρ a x) (hy : Holds m φ ρ b y)
    (hAu : A ∈ˢ univ (ConLeche.Level.eval φ u)) (hxA : x ∈ˢ A) (hyA : y ∈ˢ A) :
    Holds m φ ρ (GraphEmissionPure.eq em s a b) (truthVal (x = y)) := by
  obtain ⟨Ae, hAe, hAd⟩ := hA
  obtain ⟨xe, hxe, hxd⟩ := hx
  obtain ⟨ye, hye, hyd⟩ := hy
  refine ⟨GraphAdapter.eqExpr u Ae xe ye, ?_, GraphAdapter.eq_denotes pr hAd hxd hyd hAu hxA hyA⟩
  simp [GraphEmissionPure.eq, CoreSyntax.Expr.app3, CoreSyntax.Expr.app2, encode, levels, hu, hAe, hxe, hye,
    GraphAdapter.eqExpr, N.encode, ConLeche.eqName]

/-- Meaning of every actually encoded formula. Primitive signatures and laws
are explicit; no graph truth or checker acceptance is assumed. -/
theorem formula_denotes {S : Setting V} {L : Laws S u φ} {ρ : Nat → V}
    {em : GraphEmissionPure.Model} {a : GraphEmissionPure.Assignment Γ}
    {η : SquareKit.Internal.Env (interpretation S L) Γ}
    (pr : GraphAdapter.Primitives m u φ) (hu : U.encode em.level = some u)
    (hm : Compatible (m := m) (φ := φ) S ρ em)
    (ha : AssignmentCompatible (m := m) S L ρ a η)
    (p : GraphTarget.Formula Γ) (r : ConLeche.Expr)
    (he : encode (GraphEmissionPure.formula em a p) = some r) :
    Denotes m.cval env φ ρ r (truthVal (p.eval (interpretation S L) η)) := by
  induction p generalizing em ρ r with
  | eq t v =>
    have h := Holds.eq pr hu (hm.carrier _) (term_denotes hm ha t) (term_denotes hm ha v)
      (L.carrier_mem _) (t.eval (interpretation S L) η).property (v.eval (interpretation S L) η).property
    have hd := h.denotes he
    have heq : (t.eval (interpretation S L) η).val = (v.eval (interpretation S L) η).val ↔
        t.eval (interpretation S L) η = v.eval (interpretation S L) η :=
      ⟨Subtype.ext, fun h => congrArg Subtype.val h⟩
    rw [propext heq] at hd
    exact hd
  | conj p q ihp ihq =>
    simp only [GraphEmissionPure.formula, GraphEmissionPure.conj, CoreSyntax.Expr.app2,
      encode, levels, bind, pure, Option.bind_some] at he
    simp only [Option.bind_eq_some_iff, Option.some.injEq] at he
    obtain ⟨_, ⟨rp, hp, rfl⟩, rq, hq, rfl⟩ := he
    have h := Denotes.app (Denotes.app
      (Denotes.const (ρ := ρ) (cval := m.cval) (φ := φ) (us := [])
        pr.and_lookup (by simpa using pr.and_levels.symm))
      (ihp hu hm ha rp hp)) (ihq hu hm ha rq hq)
    rw [pr.and_law] at h
    exact h
  | @ex s Γ p ih =>
    obtain ⟨ar, har, hAr⟩ := hm.carrier s
    simp only [GraphEmissionPure.formula, GraphEmissionPure.ex, CoreSyntax.Expr.app2,
      encode, levels, hu, har, bind, pure, Option.bind_some] at he
    simp only [Option.bind_eq_some_iff, Option.some.injEq] at he
    obtain ⟨_, ⟨br, hbr, rfl⟩, rfl⟩ := he
    let P : V → Prop := fun x => ∃ hx : x ∈ˢ S.carrier s,
      p.eval (interpretation S L) (η.extend (⟨x, hx⟩ : (interpretation S L).Carrier s))
    have hb (x : V) (hx : x ∈ˢ S.carrier s) :
        Denotes m.cval env φ (push x ρ) br (truthVal (P x)) := by
      have h := ih (em := em.shift) hu (hm.shift x) (assignment_extend ha ⟨x, hx⟩) br hbr
      have heq : P x = p.eval (interpretation S L) (η.extend (⟨x, hx⟩ : (interpretation S L).Carrier s)) :=
        propext ⟨fun ⟨_, hp⟩ => hp, fun hp => ⟨hx, hp⟩⟩
      rw [heq]
      exact h
    have h := Denotes.app (Denotes.app
      (Denotes.const (ρ := ρ) (cval := m.cval) (φ := φ) (us := [u])
        pr.exists_lookup (by simpa using pr.exists_levels.symm)) hAr)
      (Denotes.lam hAr hb)
    rw [pr.exists_law _ P (L.carrier_mem s)] at h
    have heq : (GraphTarget.Formula.ex p).eval (interpretation S L) η =
        (∃ x, x ∈ˢ S.carrier s ∧ P x) := by
      apply propext
      constructor
      · rintro ⟨x, hp⟩
        exact ⟨x.val, x.property, x.property, hp⟩
      · rintro ⟨x, _, hx, hp⟩
        exact ⟨⟨x, hx⟩, hp⟩
    rw [heq]
    exact h

theorem formula_comparison {S : Setting V} {L : Laws S u φ} {ρ : Nat → V}
    {em : GraphEmissionPure.Model} {a : GraphEmissionPure.Assignment Γ}
    {η : SquareKit.Internal.Env (interpretation S L) Γ}
    (pr : GraphAdapter.Primitives m u φ) (hu : U.encode em.level = some u)
    (hm : Compatible (m := m) (φ := φ) S ρ em)
    (ha : AssignmentCompatible (m := m) S L ρ a η)
    (p : GraphTarget.Formula Γ) (r : ConLeche.Expr) (P : V)
    (he : encode (GraphEmissionPure.formula em a p) = some r)
    (hd : Denotes m.cval env φ ρ r P) :
    (pt : V) ∈ˢ P ↔ p.eval (interpretation S L) η := by
  obtain rfl := Denotes_functional hd (formula_denotes pr hu hm ha p r he)
  simp only [mem_truthVal, and_true]

theorem code_comparison {S : Setting V} {L : Laws S u φ} {ρ : Nat → V}
    {em : GraphEmissionPure.Model} {a : GraphEmissionPure.Assignment Γ}
    {η : SquareKit.Internal.Env (interpretation S L) Γ}
    (pr : GraphAdapter.Primitives m u φ) (hu : U.encode em.level = some u)
    (hm : Compatible (m := m) (φ := φ) S ρ em)
    (ha : AssignmentCompatible (m := m) S L ρ a η)
    {p q : GraphTarget.Formula Γ} (d : GraphTarget.Code p q)
    (rp rq : ConLeche.Expr) (P Q : V)
    (hep : encode (GraphEmissionPure.formula em a p) = some rp)
    (heq : encode (GraphEmissionPure.formula em a q) = some rq)
    (hp : Denotes m.cval env φ ρ rp P) (hq : Denotes m.cval env φ ρ rq Q) :
    (pt : V) ∈ˢ P → (pt : V) ∈ˢ Q := by
  rw [formula_comparison pr hu hm ha p rp P hep hp,
    formula_comparison pr hu hm ha q rq Q heq hq]
  exact GraphTarget.sound (interpretation S L) d η

theorem source_comparison {S : Setting V} {L : Laws S u φ} {ρ : Nat → V}
    {em : GraphEmissionPure.Model} {a : GraphEmissionPure.Assignment Γ}
    {η : SquareKit.Internal.Env (interpretation S L) Γ}
    (pr : GraphAdapter.Primitives m u φ) (hu : U.encode em.level = some u)
    (hm : Compatible (m := m) (φ := φ) S ρ em)
    (ha : AssignmentCompatible (m := m) S L ρ a η)
    (p : GraphTarget.SourceFormula Γ) (r : ConLeche.Expr) (P : V)
    (he : encode (GraphEmissionPure.formula em a (GraphTarget.translateFormula p)) = some r)
    (hd : Denotes m.cval env φ ρ r P) :
    (pt : V) ∈ˢ P ↔ p.eval (interpretation S L) η :=
  (formula_comparison pr hu hm ha _ r P he hd).trans
    (GraphTarget.formula_comparison (interpretation S L) η p)

/-- Join the native producer contract, exact artifact encoding, and relative
formula observation. Checker acceptance and model construction are separate. -/
theorem emission_comparison {S : Setting V} {L : Laws S u φ} {ρ : Nat → V}
    (d : GraphTarget.Declaration) (em : GraphEmissionPure.Model)
    (a : GraphEmissionPure.Assignment d.context)
    (η : SquareKit.Internal.Env (interpretation S L) d.context)
    (pr : GraphAdapter.Primitives m u φ) (hu : U.encode em.level = some u)
    (hm : Compatible (m := m) (φ := φ) S ρ em)
    (ha : AssignmentCompatible (m := m) S L ρ a η)
    (ty body rp rq : ConLeche.Expr) (P Q : V)
    (ht : encode (GraphEmissionPure.emitCore d).1 = some ty)
    (hb : encode (GraphEmissionPure.emitCore d).2 = some body)
    (hep : encode (GraphEmissionPure.formula em a d.premise) = some rp)
    (heq : encode (GraphEmissionPure.formula em a d.conclusion) = some rq)
    (hp : Denotes m.cval env φ ρ rp P) (hq : Denotes m.cval env φ ρ rq Q) :
    (GraphEmissionPure.ArtifactTyped (GraphEmissionPure.emit d) ∧
      GraphEmissionPure.ArtifactDenotes.{w} (GraphEmissionPure.emit d) (GraphTarget.Declaration.denote.{w} d)) ∧
    ((decode ty).map CoreSyntax.Expr.toLean = some (GraphEmissionPure.emit d).1 ∧
      (decode body).map CoreSyntax.Expr.toLean = some (GraphEmissionPure.emit d).2) ∧
    ((pt : V) ∈ˢ P → (pt : V) ∈ˢ Q) :=
  ⟨⟨GraphEmissionPure.emit_typed d, GraphEmissionPure.emit_denotes d⟩,
    emitted_identity d ty body ht hb,
    code_comparison pr hu hm ha d.code rp rq P Q hep heq hp hq⟩

end EmissionSemantics
#audit_graph_module

