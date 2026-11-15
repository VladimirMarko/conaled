import Examples.SchreierDiagrams

/-! JSON observation of the checked finite rows. Mathematical labels remain
separate from vertex display strings and generator indices. -/

open Lean Schreier.FiniteDiagram SchreierDiagrams
namespace SchreierDiagramDriver

/-- Serialization is an executable observation; its runtime behavior is tested
against independent fixtures, separately from the edge correspondence theorem. -/
def diagram {G X : Type} [Group G] [MulAction G X] {n m : Nat}
    (name : String) (vertices : Fin n ≃ X) (generators : Fin m → G)
    (vertexText : X → String) (observeLabel : G → Json) : Json :=
  Json.mkObj [
    ("name", toJson name),
    ("vertices", toJson ((List.finRange n).map fun v => Json.mkObj [
      ("id", toJson v.val), ("label", toJson (vertexText (vertices v)))])),
    ("generators", toJson ((List.finRange m).map fun s => Json.mkObj [
      ("id", toJson s.val), ("label", observeLabel (generators s))])),
    ("edges", toJson ((rows vertices generators).map fun r => Json.mkObj [
      ("id", toJson s!"{r.source.val}:{r.generator.val}"),
      ("source", toJson r.source.val), ("target", toJson r.target.val),
      ("generator", toJson r.generator.val), ("label", observeLabel r.label)]))]

def permutationLabel (p : SchreierExamples.S3) : Json :=
  toJson ((List.finRange 3).map fun i => (p i).val)

def examples : Json := toJson [
  diagram "c3" cyclicVertices cyclicGenerator (fun x => toString x.toAdd.val)
    (fun g => toJson g.toAdd.val),
  diagram "s3-natural" (Equiv.refl (Fin 3)) permutations (fun x => toString x.val)
    permutationLabel,
  diagram "s3-trivial" unitVertices permutations (fun _ => "*") permutationLabel]

def run : IO Unit := do
  (← IO.getStdout).putStrLn examples.compress

end SchreierDiagramDriver
