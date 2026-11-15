import Applications.Languages.IndexedCompositional

/-! Exact rewrites retain selected witnesses in arbitrary finite constructor contexts. -/
namespace LanguageWitnesses
universe u v
variable {α : Type u}

def Iso.refl (A : Type u) : Iso A A where
  forward := id
  backward := id
  backward_forward _ := rfl
  forward_backward _ := rfl

def Iso.trans {A B C : Type u} (e : Iso A B) (f : Iso B C) : Iso A C where
  forward := f.forward ∘ e.forward
  backward := e.backward ∘ f.backward
  backward_forward a := by simp only [Function.comp_apply, f.backward_forward, e.backward_forward]
  forward_backward c := by simp only [Function.comp_apply, e.forward_backward, f.forward_backward]

theorem Decision.map_refl {A : Type u} (d : Decision A) : d.map (Iso.refl A) = d := by
  cases d <;> rfl

theorem Decision.map_trans {A B C : Type u} (e : Iso A B) (f : Iso B C) (d : Decision A) :
    (d.map e).map f = d.map (e.trans f) := by cases d <;> rfl

namespace WitnessTrie
variable {P Q R : Language α}

theorem transport_refl {n} (t : WitnessTrie P n) : transport (fun w => Iso.refl (P w)) t = t := by
  induction n generalizing P with
  | zero => cases t; simp only [transport, Decision.map_refl]
  | succ n ih =>
    cases t
    simp only [transport, Decision.map_refl]
    congr 1
    funext a
    exact ih _

theorem transport_trans (e : ∀ w, Iso (P w) (Q w)) (f : ∀ w, Iso (Q w) (R w))
    {n} (t : WitnessTrie P n) :
    transport f (transport e t) = transport (fun w => (e w).trans (f w)) t := by
  induction n generalizing P Q R with
  | zero => cases t; simp only [transport, Decision.map_trans]
  | succ n ih =>
    cases t
    simp only [transport, Decision.map_trans]
    congr 1
    funext a
    exact ih _ _ _
end WitnessTrie

namespace Parser
variable [DecidableEq α] {P Q R : Language α}

theorem parse_transport_refl (p : Parser P) (w : List α) :
    (Parser.transport (fun w => Iso.refl (P w)) p).parse w = p.parse w := by
  have h := congrArg (fun t : WitnessTrie P w.length => t.lookup w (Nat.le_refl _))
    (WitnessTrie.transport_refl (WitnessTrie.unfold p w.length))
  rw [← WitnessTrie.unfold_transport, WitnessTrie.lookup_unfold, WitnessTrie.lookup_unfold] at h
  exact h

theorem parse_transport_trans (e : ∀ w, Iso (P w) (Q w)) (f : ∀ w, Iso (Q w) (R w))
    (p : Parser P) (w : List α) :
    (Parser.transport f (.transport e p)).parse w =
      (Parser.transport (fun w => (e w).trans (f w)) p).parse w := by
  have h := congrArg (fun t : WitnessTrie R w.length => t.lookup w (Nat.le_refl _))
    (WitnessTrie.transport_trans e f (WitnessTrie.unfold p w.length))
  rw [← WitnessTrie.unfold_transport, ← WitnessTrie.unfold_transport,
    ← WitnessTrie.unfold_transport, WitnessTrie.lookup_unfold, WitnessTrie.lookup_unfold] at h
  exact h
end Parser

namespace IndexedCompositional
open SquareKit.IndexedCompositional

/-- Leaves are typed holes. They may occur zero, once, or many times in the context.
Equality is required only at each hole's declared depth. -/
theorem contextual_exact [DecidableEq α] {X : Index α → Type v}
    (lhs rhs : ∀ j, X j → Term signature Source j)
    (h : ∀ j x w (_hw : w.length ≤ j.2),
      (Term.fold sourceAlgebra (fun _ p => p) (lhs j x)).parse w =
      (Term.fold sourceAlgebra (fun _ p => p) (rhs j x)).parse w)
    {P : Language α} {n} (context : Term signature X (P,n))
    (w : List α) (hw : w.length ≤ n) :
    (Term.fold sourceAlgebra (fun _ p => p) (context.bind lhs)).parse w =
      (Term.fold sourceAlgebra (fun _ p => p) (context.bind rhs)).parse w := by
  rw [← recovered (bound := hw), ← recovered (bound := hw)]
  have holes : (fun j x => Term.fold targetAlgebra unfold (lhs j x)) =
      (fun j x => Term.fold targetAlgebra unfold (rhs j x)) := by
    funext j x
    apply WitnessTrie.ext_lookup
    intro word bound
    rw [recovered, recovered]
    exact h j x word bound
  rw [Term.fold_bind, Term.fold_bind, holes]

/-- The same local obligation recovers native trie observations after replacement. -/
theorem contextual_tree [DecidableEq α] {X : Index α → Type v}
    (lhs rhs : ∀ j, X j → Term signature Source j)
    (h : ∀ j x w (_hw : w.length ≤ j.2),
      (Term.fold sourceAlgebra (fun _ p => p) (lhs j x)).parse w =
      (Term.fold sourceAlgebra (fun _ p => p) (rhs j x)).parse w)
    {P : Language α} {n} (context : Term signature X (P,n)) :
    Term.fold targetAlgebra unfold (context.bind lhs) =
      Term.fold targetAlgebra unfold (context.bind rhs) := by
  apply WitnessTrie.ext_lookup
  intro w hw
  rw [recovered, recovered]
  exact contextual_exact lhs rhs h context w hw

def identityTransport : (j : Index α) → Source j → Term signature Source j
  | (P,n), p => .node (.transport P P n (fun w => Iso.refl (P w))) (fun _ => .leaf p)

/-- Identity transport can be eliminated at every leaf in any supported context. -/
theorem contextual_transport_refl [DecidableEq α] {P : Language α} {n}
    (context : Term signature Source (P,n)) (w : List α) (hw : w.length ≤ n) :
    (Term.fold sourceAlgebra (fun _ p => p) (context.bind identityTransport)).parse w =
      (Term.fold sourceAlgebra (fun _ p => p) context).parse w := by
  have h := contextual_exact identityTransport (fun _ p => Term.leaf p)
    (fun j p word _ => by
      rcases j with ⟨Q,m⟩
      exact Parser.parse_transport_refl p word) context w hw
  simpa only [Term.bind_leaf] using h

/-- A rewrite site records its intermediate witness types and both isomorphisms. -/
structure TransportPair (j : Index α) where
  P : Language α
  Q : Language α
  first : ∀ w, Iso (P w) (Q w)
  second : ∀ w, Iso (Q w) (j.1 w)
  parser : Parser P

def TransportPair.expanded (j : Index α) (site : TransportPair j) : Term signature Source j :=
  .node (.transport site.Q j.1 j.2 site.second) (fun _ =>
    .node (.transport site.P site.Q j.2 site.first) (fun _ => .leaf site.parser))

def TransportPair.fused (j : Index α) (site : TransportPair j) : Term signature Source j :=
  .node (.transport site.P j.1 j.2 (fun w => (site.first w).trans (site.second w)))
    (fun _ => .leaf site.parser)

/-- Fusion is valid under all seven constructors, including star and depth restriction. -/
theorem contextual_transport_trans [DecidableEq α] {P : Language α} {n}
    (context : Term signature TransportPair (P,n)) (w : List α) (hw : w.length ≤ n) :
    (Term.fold sourceAlgebra (fun _ p => p) (context.bind TransportPair.expanded)).parse w =
      (Term.fold sourceAlgebra (fun _ p => p) (context.bind TransportPair.fused)).parse w :=
  contextual_exact TransportPair.expanded TransportPair.fused (fun j site word _ => by
    rcases j with ⟨R,m⟩
    exact Parser.parse_transport_trans site.first site.second site.parser word) context w hw

end IndexedCompositional
end LanguageWitnesses
