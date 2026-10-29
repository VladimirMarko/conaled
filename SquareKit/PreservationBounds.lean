import SquareKit.InteractionContracts

/-! Ordered observations specialize covered relational preservation. No resource
algebra, execution model, existence or progress premise is implicit. -/
namespace Interaction
universe u v w x

/-- Transfer an upper bound in the source-to-target direction. Target coverage
is essential: an empty relation cannot justify a nonempty target behavior set. -/
theorem Refines.bound {S : Type u} {T : Type v} {K : Type w} {L : Type x}
    [Preorder K] [Preorder L] {r : S → T → Prop} {source : Set S} {target : Set T}
    (covered : Refines r source target) (sourceCost : S → K) (targetCost : T → L)
    (h : K → L) (mono : Monotone h)
    (comparison : ∀ s t, r s t → targetCost t ≤ h (sourceCost s))
    (budget : K) (bounded : ∀ s ∈ source, sourceCost s ≤ budget) :
    ∀ t ∈ target, targetCost t ≤ h budget :=
  covered.property bounded (fun s t related hs => (comparison s t related).trans (mono hs))

end Interaction

namespace SquareKit.PreservationBounds
universe u v w x y z

/-- Observation comparisons compose along the actual intermediate witness. -/
theorem comparison_comp {S : Type u} {T : Type v} {U : Type w}
    {K : Type x} {L : Type y} {M : Type z}
    [Preorder L] [Preorder M] {r : S → T → Prop} {q : T → U → Prop}
    (a : S → K) (b : T → L) (c : U → M) (h : K → L) (k : L → M)
    (mono : Monotone k)
    (first : ∀ s t, r s t → b t ≤ h (a s))
    (second : ∀ t z, q t z → c z ≤ k (b t)) :
    ∀ s z, Relation.Comp r q s z → c z ≤ k (h (a s)) := by
  rintro s z ⟨t, hst, htz⟩
  exact (second t z htz).trans (mono (first s t hst))

/-- Component bounds compose only with a compatible observation operation.
The target operation may include boundary storage or administrative overhead.
The caller must separately justify that it bounds the actual composite. -/
theorem combine {K : Type u} {L : Type v} [Preorder L]
    (sourceOp : K → K → K) (targetOp : L → L → L) (h : K → L)
    (mono : ∀ {a b c d}, a ≤ b → c ≤ d → targetOp a c ≤ targetOp b d)
    (compatible : ∀ a b, targetOp (h a) (h b) ≤ h (sourceOp a b))
    {x y : L} {a b : K} (hx : x ≤ h a) (hy : y ≤ h b) :
    targetOp x y ≤ h (sourceOp a b) :=
  (mono hx hy).trans (compatible a b)

end SquareKit.PreservationBounds
