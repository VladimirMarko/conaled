import SquareKit.WitnessSetoidsErasure

namespace Examples.WitnessSetoids
open SquareKit SquareKit.WitnessSetoids

/-- Every pair has two different witnesses; no coherence equations collapse them. -/
def tagged : Obj := ⟨Bool, fun _ _ => Bool, fun _ => false, id, fun h _ => h⟩
def keep : Hom tagged tagged := ⟨id, id⟩
def flipWitness : Hom tagged tagged := ⟨id, Bool.not⟩

example : keep.congr (x := false) (y := true) true = true := rfl
example : flipWitness.congr (x := false) (y := true) true = false := rfl
example : keep ≠ flipWitness := by
  intro h
  have q := congrArg (fun f : Hom tagged tagged => f.congr (x := false) (y := true) true) h
  cases q
example : eraseHom keep = eraseHom flipWitness := rfl
example : (ops.comp flipWitness flipWitness).congr (x := false) (y := true) true = true := rfl

/-- Pointwise hom witnesses remain distinguishable after category congruence. -/
def yes : equiv.Rel keep keep := fun _ => true
def no : equiv.Rel keep keep := fun _ => false
example : yes ≠ no := by
  intro h
  have q := congrArg (fun f => f false) h
  cases q
example : congr.comp yes no false = true := rfl
example : (products.pair keep flipWitness).congr (x := false) (y := true) true =
    (true,false) := rfl
example : (coproducts.copair keep flipWitness).congr
    (x := Sum.inr false) (y := Sum.inr true) true = false := rfl
example : ((closed.curry (products.fst (a := tagged) (b := tagged))).toFun false).congr
    (x := false) (y := true) true = false := rfl
example : (distribution.distribute (a := tagged) (b := tagged) (c := tagged)).congr
    (x := (false,Sum.inr false)) (y := (true,Sum.inr true)) (true,false) =
    (true,false) := rfl
example : (rightDistribution.distribute (a := tagged) (b := tagged) (c := tagged)).congr
    (x := (Sum.inl false,false)) (y := (Sum.inl true,true)) (true,false) =
    (true,false) := rfl

end Examples.WitnessSetoids
