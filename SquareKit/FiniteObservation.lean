import SquareKit.IndexedCompositional

/-! A typed observation path with a public result type. The endpoint decoder
retains the client's promised data without exposing endpoint index casts. -/
namespace SquareKit.IndexedCompositional.Behavior
universe i o a x y r
variable {I : Type i} (B : Behavior.{i,o,a} I)

structure Observation (j : I) (Result : Type r) where
  endpoint : I
  path : B.Path j endpoint
  decode : B.Output endpoint → Result

namespace Observation
variable {B} {X : I → Type x} {Y : I → Type y} {j : I} {Result : Type r}
def read (p : B.Observation j Result) (c : B.Coalgebra X) (x : X j) : Result :=
  p.decode (B.observe c p.path x)

theorem read_morphism (p : B.Observation j Result)
    (c : B.Coalgebra X) (d : B.Coalgebra Y) (f : ∀ j, X j → Y j)
    (h : B.Morphism c d f) (x : X j) : p.read d (f j x) = p.read c x :=
  congrArg p.decode (B.observe_morphism c d f h p.path x)
end Observation
end SquareKit.IndexedCompositional.Behavior
