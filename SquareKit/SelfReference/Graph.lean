import SquareKit.SelfReference.Native

/-! Finite named self-reference graphs. Edges are data, not recursive evaluation. -/
namespace SquareKit.SelfReference

inductive Tag where
  | truth | provability
  deriving DecidableEq, Repr

/-- Nodes for a selected sentence, its quotation, unary application, implication
and target parameter. Payload stores the external parameter sentence. -/
inductive Node where
  | selected | quotation | unary | implication | parameter
  deriving DecidableEq, Repr

inductive Edge where
  | reference | argument | antecedent | consequent | definition
  deriving DecidableEq, Repr

/-- Edge labels distinguish the reference cycle from formula syntax. -/
def endpoints : Edge → Node × Node
  | .reference => (.quotation, .selected)
  | .argument => (.unary, .quotation)
  | .antecedent => (.implication, .unary)
  | .consequent => (.implication, .parameter)
  | .definition => (.selected, .implication)

structure UntaggedGraph where
  selectedName : Nat
  parameter : Formula
  edge : Edge → Node × Node

structure TaggedGraph extends UntaggedGraph where
  tag : Tag

def selfReferenceGraph (t : Tag) (name : Nat) (A : Formula) : TaggedGraph :=
  ⟨⟨name, A, endpoints⟩, t⟩

def TaggedGraph.erase (g : TaggedGraph) : UntaggedGraph := g.toUntaggedGraph

@[simp] theorem erase_name (g : TaggedGraph) : g.erase.selectedName = g.selectedName := rfl
@[simp] theorem erase_parameter (g : TaggedGraph) : g.erase.parameter = g.parameter := rfl
@[simp] theorem erase_edge (g : TaggedGraph) (e : Edge) : g.erase.edge e = g.edge e := rfl

theorem reference_retained (t : Tag) (name : Nat) (A : Formula) :
    (selfReferenceGraph t name A).erase.edge .reference = (.quotation, .selected) := rfl

theorem tags_have_same_erasure (name : Nat) (A : Formula) :
    (selfReferenceGraph .truth name A).erase =
      (selfReferenceGraph .provability name A).erase := rfl

theorem tags_distinct (name : Nat) (A : Formula) :
    selfReferenceGraph .truth name A ≠ selfReferenceGraph .provability name A := by
  intro h
  have := congrArg TaggedGraph.tag h
  cases this

/-- No restoration function can recover both original tags from erased data. -/
theorem no_tag_recovery : ¬ ∃ restore : UntaggedGraph → TaggedGraph,
    ∀ t name A, restore (selfReferenceGraph t name A).erase = selfReferenceGraph t name A := by
  rintro ⟨restore, h⟩
  exact tags_distinct 0 .bot ((h .truth 0 .bot).symm.trans (h .provability 0 .bot))

/-- Connect the finite graph's selected name to an actual diagonal witness.
The graph alone supplies neither of the witness's derivations. -/
structure NamedConstruction (T : Theory) (A : Formula) where
  name : Nat
  diagonal : Diagonal T A
  named : diagonal.sentence = .atom name

def NamedConstruction.graph {T A} (c : NamedConstruction T A) (t : Tag) : TaggedGraph :=
  selfReferenceGraph t c.name A

theorem NamedConstruction.selected_retained {T A} (c : NamedConstruction T A) (t : Tag) :
    c.diagonal.sentence = .atom (c.graph t).erase.selectedName := c.named

end SquareKit.SelfReference
