import Squares
import SquareKit.Relations

/-! Optional evidence, proof and realization capabilities. These are connections
at a chosen signature; a signature category and its functor laws are additional
structure, not hidden assumptions of this interface. -/
namespace SquareKit.Institutions
universe u v w

structure Setting where
  Sentence : Type u
  Model : Type v
  Evidence : Model → Sentence → Type w

/-- Sentences travel forward, models backward, and selected evidence forward. -/
structure Connection (A B : Setting.{u, v, w}) where
  sentence : A.Sentence → B.Sentence
  reduct : B.Model → A.Model
  evidence : ∀ m p, A.Evidence (reduct m) p → B.Evidence m (sentence p)

namespace Connection
variable {A B C D : Setting.{u, v, w}}
def identity (A : Setting.{u, v, w}) : Connection A A := ⟨id, id, fun _ _ => id⟩
def comp (g : Connection B C) (f : Connection A B) : Connection A C where
  sentence := g.sentence ∘ f.sentence
  reduct := f.reduct ∘ g.reduct
  evidence m p := g.evidence m (f.sentence p) ∘ f.evidence (g.reduct m) p

theorem comp_assoc (h : Connection C D) (g : Connection B C) (f : Connection A B) :
    h.comp (g.comp f) = (h.comp g).comp f := rfl
theorem identity_comp (f : Connection A B) : (identity B).comp f = f := by cases f; rfl
theorem comp_identity (f : Connection A B) : f.comp (identity A) = f := by cases f; rfl

/-- Inhabitation reflection is additional to forward evidence transport. -/
structure Reflects (f : Connection A B) : Prop where
  reflects : ∀ m p, Nonempty (B.Evidence m (f.sentence p)) →
    Nonempty (A.Evidence (f.reduct m) p)

theorem satisfaction (f : Connection A B) (r : f.Reflects) (m) (p) :
    Nonempty (A.Evidence (f.reduct m) p) ↔ Nonempty (B.Evidence m (f.sentence p)) :=
  ⟨fun ⟨x⟩ => ⟨f.evidence m p x⟩, r.reflects m p⟩
theorem Reflects.comp {f : Connection A B} {g : Connection B C}
    (s : g.Reflects) (r : f.Reflects) : (g.comp f).Reflects :=
  ⟨fun m p h => r.reflects (g.reduct m) p (s.reflects m (f.sentence p) h)⟩
end Connection

structure Proofs (A : Setting.{u, v, w}) where
  Proof : A.Sentence → Type w
  interpret : ∀ m p, Proof p → A.Evidence m p

structure ProofMap {A B : Setting.{u, v, w}} (f : Connection A B) (P : Proofs A) (Q : Proofs B) where
  map : ∀ p, P.Proof p → Q.Proof (f.sentence p)
  commutes : ∀ m p t, Q.interpret m _ (map p t) = f.evidence m p (P.interpret _ p t)

def ProofMap.comp {A B C : Setting.{u, v, w}} {f : Connection A B} {g : Connection B C}
    {P : Proofs A} {Q : Proofs B} {R : Proofs C} (b : ProofMap g Q R) (a : ProofMap f P Q) :
    ProofMap (g.comp f) P R where
  map p := b.map _ ∘ a.map p
  commutes m p t := by
    dsimp [Function.comp_def, Connection.comp]
    rw [b.commutes, a.commutes]

/-- A representation need not be executable. Execution is a further property
of its chosen operations, not a consequence of semantic preservation. -/
structure Realization (A : Setting.{u, v, w}) where
  Carrier : A.Model → A.Sentence → Type w
  decode : ∀ m p, Carrier m p → A.Evidence m p

structure RealizationMap {A B : Setting.{u, v, w}} (f : Connection A B)
    (R : Realization A) (S : Realization B) where
  map : ∀ m p, R.Carrier (f.reduct m) p → S.Carrier m (f.sentence p)
  commutes : ∀ m p r, S.decode m _ (map m p r) = f.evidence m p (R.decode _ p r)

def RealizationMap.square {A B : Setting.{u, v, w}} {f : Connection A B}
    {R : Realization A} {S : Realization B} (c : RealizationMap f R S) (m) (p) :
    Squares.Square ⟨_, _, R.decode (f.reduct m) p⟩ ⟨_, _, S.decode m (f.sentence p)⟩ :=
  ⟨c.map m p, f.evidence m p, c.commutes m p⟩

def RealizationMap.comp {A B C : Setting.{u, v, w}} {f : Connection A B} {g : Connection B C}
    {R : Realization A} {S : Realization B} {T : Realization C}
    (b : RealizationMap g S T) (a : RealizationMap f R S) : RealizationMap (g.comp f) R T where
  map m p := b.map m _ ∘ a.map (g.reduct m) p
  commutes m p r := (Squares.compose (b.square m _) (a.square (g.reduct m) p)).commutes r

/-- A wrapper of separately constructed capabilities cannot choose a second
meaning comparison for computation. -/
structure Compatible {A B : Setting.{u, v, w}} (f : Connection A B)
    (P : Proofs A) (Q : Proofs B) (R : Realization A) (S : Realization B) where
  proof : ProofMap f P Q
  realization : RealizationMap f R S

def Compatible.comp {A B C : Setting.{u, v, w}} {f : Connection A B} {g : Connection B C}
    {P : Proofs A} {Q : Proofs B} {U : Proofs C}
    {R : Realization A} {S : Realization B} {T : Realization C}
    (b : Compatible g Q U S T) (a : Compatible f P Q R S) : Compatible (g.comp f) P U R T :=
  ⟨b.proof.comp a.proof, b.realization.comp a.realization⟩

/-- Relational meanings have no selected decoder. The evidence remains a
parameter of the relation rather than being chosen from it. -/
structure RelRealization (A : Setting.{u, v, w}) where
  Carrier : A.Model → A.Sentence → Type w
  relates : ∀ m p, Carrier m p → A.Evidence m p → Prop
structure RelRealizationMap {A B : Setting.{u, v, w}} (f : Connection A B)
    (R : RelRealization A) (S : RelRealization B) where
  map : ∀ m p, R.Carrier (f.reduct m) p → S.Carrier m (f.sentence p)
  preserves : ∀ m p r e, R.relates _ p r e → S.relates m _ (map m p r) (f.evidence m p e)
def RelRealizationMap.comp {A B C : Setting.{u, v, w}} {f : Connection A B} {g : Connection B C}
    {R : RelRealization A} {S : RelRealization B} {T : RelRealization C}
    (b : RelRealizationMap g S T) (a : RelRealizationMap f R S) :
    RelRealizationMap (g.comp f) R T :=
  ⟨fun m p => b.map m _ ∘ a.map (g.reduct m) p,
    fun m p r e h => b.preserves m _ _ _ (a.preserves _ p r e h)⟩

def Realization.relational {A : Setting.{u, v, w}} (R : Realization A) : RelRealization A :=
  ⟨R.Carrier, fun m p r e => R.decode m p r = e⟩
def RealizationMap.relational {A B : Setting.{u, v, w}} {f : Connection A B}
    {R : Realization A} {S : Realization B} (c : RealizationMap f R S) :
    RelRealizationMap f R.relational S.relational :=
  ⟨c.map, fun m p r _e h => (c.commutes m p r).trans (congrArg (f.evidence m p) h)⟩

/-- Relational preservation is a common local abstraction: ordinary satisfaction
is a relation between models and sentences. It does not reconstruct the indices
or the selected evidence of a connection from that relation. -/
def Connection.satisfactionSquare {A B : Setting.{u, v, w}} (f : Connection A B)
    (m : B.Model) : Relational.RelSquare
      ⟨PUnit, A.Sentence, fun _ p => Nonempty (A.Evidence (f.reduct m) p)⟩
      ⟨PUnit, B.Sentence, fun _ p => Nonempty (B.Evidence m p)⟩ where
  impl := id
  spec := f.sentence
  preserves := fun {_r} {p} ⟨e⟩ => ⟨f.evidence m p e⟩

end SquareKit.Institutions

namespace SquareKit.Institutions
universe u v w
variable {A B C D : Setting.{u,v,w}}

def ProofMap.identity (P : Proofs A) : ProofMap (Connection.identity A) P P :=
  ⟨fun _ => id, fun _ _ _ => rfl⟩
def RealizationMap.identity (R : Realization A) : RealizationMap (Connection.identity A) R R :=
  ⟨fun _ _ => id, fun _ _ _ => rfl⟩

theorem ProofMap.comp_assoc {f : Connection A B} {g : Connection B C} {h : Connection C D}
    {P : Proofs A} {Q : Proofs B} {R : Proofs C} {S : Proofs D}
    (c : ProofMap h R S) (b : ProofMap g Q R) (a : ProofMap f P Q) :
    c.comp (b.comp a) = (c.comp b).comp a := rfl

theorem RealizationMap.comp_assoc {f : Connection A B} {g : Connection B C} {h : Connection C D}
    {P : Realization A} {Q : Realization B} {R : Realization C} {S : Realization D}
    (c : RealizationMap h R S) (b : RealizationMap g Q R) (a : RealizationMap f P Q) :
    c.comp (b.comp a) = (c.comp b).comp a := rfl

/-- Convert a pre-existing square only after checking its chosen lower arrow. -/
def RealizationMap.ofSquares {f : Connection A B} {R : Realization A} {S : Realization B}
    (sq : ∀ m p, Squares.Square ⟨_,_,R.decode (f.reduct m) p⟩ ⟨_,_,S.decode m (f.sentence p)⟩)
    (compatible : ∀ m p e, (sq m p).spec e = f.evidence m p e) : RealizationMap f R S :=
  ⟨fun m p => (sq m p).impl,
    fun m p r => ((sq m p).commutes r).trans (compatible m p (R.decode _ p r))⟩

/-- Proof interpretation itself gives a representation, without claiming that
its semantic evaluator is executable. -/
def Proofs.realization (P : Proofs A) : Realization A :=
  ⟨fun _ p => P.Proof p, P.interpret⟩
def ProofMap.realization {f : Connection A B} {P : Proofs A} {Q : Proofs B}
    (p : ProofMap f P Q) : RealizationMap f P.realization Q.realization :=
  ⟨fun _ => p.map, p.commutes⟩

end SquareKit.Institutions
