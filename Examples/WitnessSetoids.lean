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

/-- Direct universal-property operations retain the supplied Boolean witnesses. -/
example : (product_universal.forward
    (fun _ => (true,false) : equiv.Rel (products.pair keep keep) (products.pair keep keep))).1 false = true := rfl
example : coproduct_universal.backward (k := coproducts.copair keep keep)
    (f := keep) (g := keep) ⟨yes,no⟩
    (Sum.inr false) = false := rfl
example {A B C D : Obj} (h : Hom C D) (g : Hom B C) (f : Hom A B) :
    SetoidCategory.equiv.Rel (eraseHom (ops.comp (ops.comp h g) f))
      (eraseHom (ops.comp h (ops.comp g f))) := erase_relation (laws.assoc h g f)

/-- An existing generic derived Cartesian operation specializes without re-proving its law. -/
example (f g : Hom tagged tagged) :
    equiv.Rel (ops.comp (SquareKit.Cartesian.swap products)
      (products.pair f g)) (products.pair g f) :=
  WitnessEquivalence.Cartesian.swap_pair congr laws product_congr product_laws f g

end Examples.WitnessSetoids
