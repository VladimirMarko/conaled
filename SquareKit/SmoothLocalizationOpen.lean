import SquareKit.SmoothLocalizationPoints
import SquareKit.SmoothOpenFunctions
import SquareKit.SmoothInverseGraph

/-! Experimental identification of principal smooth localization with the full
ordinary smooth-function algebra on its open locus. Extension choices disappear
in the quotient by the exact analytic kernel theorem. -/
noncomputable section
open Set
open scoped ContDiff
namespace SquareKit.SmoothAlgebra.Localization
variable {n : ℕ}

def locus (f : Free n) : Set (Fin n → ℝ) := {x | f.val x ≠ 0}
abbrev Functions (f : Free n) := OpenFunctions.Carrier (locus f)

/-- Restriction to the inverse graph, valued in all ordinary smooth functions. -/
def graphRestriction (f : Free n) : Hom (Free (n+1)) (Functions f) where
  toFun H := ⟨fun x => H.val (SmoothInverseGraph.graph f.val x.val), by
    apply (OpenFunctions.representative_iff _ (fun x => H.val (SmoothInverseGraph.graph f.val x)) (fun _ => rfl)).mpr
    exact (show ContDiff ℝ ∞ H.val from H.property).comp_contDiffOn
      (SmoothInverseGraph.graph_smoothOn f.property)⟩
  map_act _ _ := rfl

theorem relation_apply (f : Free n) (z : Fin (n+1) → ℝ) :
    (relation (fun _ : Fin 1 => f) 0).val z = SmoothInverseGraph.relation f.val z := rfl

theorem graphRestriction_relation (f : Free n) : graphRestriction f (relation (fun _ : Fin 1 => f) 0) = 0 := by
  apply OpenFunctions.ext
  intro x
  exact SmoothInverseGraph.relation_graph x.property

theorem graphRestriction_surjective (f : Free n) : Function.Surjective (graphRestriction f) := by
  intro g
  obtain ⟨H,hH,he⟩ := SmoothInverseGraph.extension (show ContDiff ℝ ∞ f.val from f.property)
    (OpenFunctions.extendZero (locus f) g.val) g.property
  refine ⟨⟨H,hH⟩,?_⟩
  apply OpenFunctions.ext
  intro x
  exact (he x.val x.property).trans (OpenFunctions.extendZero_mem g.val x)

theorem principal_ideal (f : Free n) : ideal (fun _ : Fin 1 => f) =
    Ideal.span {relation (fun _ : Fin 1 => f) 0} := by
  unfold ideal
  congr 1
  ext p
  constructor
  · rintro ⟨i,rfl⟩
    have hi : i=0 := Subsingleton.elim _ _
    subst i
    rfl
  · intro hp
    exact ⟨0,hp.symm⟩

/-- Exact kernel, proved by global smooth divisibility rather than point detection. -/
theorem graphRestriction_kernel (f : Free n) (H : Free (n+1)) :
    graphRestriction f H = 0 ↔ H ∈ ideal (fun _ : Fin 1 => f) := by
  rw [principal_ideal,Ideal.mem_span_singleton]
  constructor
  · intro hh
    obtain ⟨Q,hQ,he⟩ := SmoothInverseGraph.divisibility (show ContDiff ℝ ∞ f.val from f.property)
      (show ContDiff ℝ ∞ H.val from H.property) (fun x hx => by
        exact congrArg (fun g : Functions f => g.val ⟨x,hx⟩) hh)
    refine ⟨⟨Q,hQ⟩,?_⟩
    apply Subtype.ext
    funext z
    exact (he z).symm
  · rintro ⟨Q,hQ⟩
    rw [hQ,(graphRestriction f).map_mul,graphRestriction_relation]
    exact zero_mul _

def toOpen (f : Free n) : Hom (Principal f) (Functions f) :=
  Quotient.lift (ideal (fun _ : Fin 1 => f)) (graphRestriction f)
    (fun H hH => (graphRestriction_kernel f H).mpr hH)

@[simp] theorem toOpen_projection (f : Free n) (H : Free (n+1)) :
    toOpen f (Quotient.projection (ideal (fun _ : Fin 1 => f)) H) = graphRestriction f H := rfl

theorem toOpen_bijective (f : Free n) : Function.Bijective (toOpen f) := by
  constructor
  · intro a b hab
    obtain ⟨A,rfl⟩ := Ideal.Quotient.mk_surjective a
    obtain ⟨B,rfl⟩ := Ideal.Quotient.mk_surjective b
    apply (Ideal.Quotient.mk_eq_mk_iff_sub_mem _ _).mpr
    apply (graphRestriction_kernel f (A-B)).mp
    change (graphRestriction f).toAlgHom (A-B) = 0
    rw [map_sub,sub_eq_zero]
    exact hab
  · intro g
    obtain ⟨H,hH⟩ := graphRestriction_surjective f g
    exact ⟨Quotient.projection _ H,hH⟩

/-- The inverse is independent of the extension chosen to represent a function. -/
def openEquiv (f : Free n) : Principal f ≃ Functions f := Equiv.ofBijective (toOpen f) (toOpen_bijective f)

def fromOpen (f : Free n) : Hom (Functions f) (Principal f) where
  toFun := (openEquiv f).symm
  map_act op g := by
    apply (toOpen_bijective f).injective
    change openEquiv f ((openEquiv f).symm _) = toOpen f (act op (fun i => (openEquiv f).symm (g i)))
    rw [(openEquiv f).apply_symm_apply,(toOpen f).map_act]
    congr 1
    funext i
    exact ((openEquiv f).apply_symm_apply (g i)).symm

theorem toOpen_fromOpen (f : Free n) : Hom.comp (toOpen f) (fromOpen f) = Hom.ident :=
  Hom.ext (openEquiv f).apply_symm_apply

theorem fromOpen_toOpen (f : Free n) : Hom.comp (fromOpen f) (toOpen f) = Hom.ident :=
  Hom.ext (openEquiv f).symm_apply_apply

theorem extension_independent (f : Free n) (A B : Free (n+1))
    (he : graphRestriction f A = graphRestriction f B) :
    Quotient.projection (ideal (fun _ : Fin 1 => f)) A = Quotient.projection (ideal (fun _ : Fin 1 => f)) B :=
  (toOpen_bijective f).injective he

@[simp] theorem toOpen_base (f H : Free n) (x : locus f) :
    (toOpen f (principalBase f H)).val x = H.val x.val := by
  change H.val (fun i => SmoothInverseGraph.graph f.val x.val (Fin.castAdd 1 i)) = _
  exact congrArg H.val (SmoothInverseGraph.base_graph f.val x.val)

@[simp] theorem toOpen_inverse (f : Free n) (x : locus f) :
    (toOpen f (inverse f)).val x = (f.val x.val)⁻¹ := by
  exact SmoothInverseGraph.graph_last _ _

/-- The algebra comparison agrees with the previously constructed real-point UP. -/
theorem toOpen_realPoint (f : Free n) (x : locus f) (q : Principal f) :
    (toOpen f q).val x = (realPoints f).symm x q := by
  let ev : Hom (Functions f) ℝ := {toFun := fun g => g.val x, map_act := fun _ _ => rfl}
  have he : Hom.comp ev (toOpen f) = (realPoints f).symm x := by
    apply principal_unique f
    apply Hom.ext
    intro H
    change (toOpen f (principalBase f H)).val x = _
    rw [toOpen_base]
    exact (congrArg (fun h : Hom (Free n) ℝ => h H)
      (lift_base (fun _ : Fin 1 => f) (evaluate x.val)
        (fun _ => isUnit_iff_ne_zero.mpr x.property))).symm
  exact congrArg (fun h : Hom (Principal f) ℝ => h q) he

/-- Restricting to the intersection uses the existing iterated/product maps. -/
def nestedMap (f g : Free n) : Hom (Principal f) (Principal (f*g)) :=
  Hom.comp (iteratedToProduct f g) (first f g)

theorem nestedMap_base (f g : Free n) : Hom.comp (nestedMap f g) (principalBase f) = principalBase (f*g) := by
  unfold nestedMap
  rw [← Hom.comp_assoc,first_base,iteratedToProduct_base]

theorem locus_product_subset (f g : Free n) : locus (f*g) ⊆ locus f := by
  intro x hx
  exact left_ne_zero_of_mul (show f.val x*g.val x ≠ 0 from hx)

theorem restriction_naturality (f g : Free n) :
    Hom.comp (toOpen (f*g)) (nestedMap f g) =
      Hom.comp (OpenFunctions.restrict (locus_product_subset f g)) (toOpen f) := by
  apply principal_unique f
  apply Hom.ext
  intro H
  apply OpenFunctions.ext
  intro x
  have he := congrArg (fun h : Hom (Free n) (Principal (f*g)) => h H) (nestedMap_base f g)
  change (toOpen (f*g) (nestedMap f g (principalBase f H))).val x =
    (toOpen f (principalBase f H)).val ⟨x.val,locus_product_subset f g x.property⟩
  change nestedMap f g (principalBase f H) = principalBase (f*g) H at he
  rw [he,toOpen_base,toOpen_base]

end SquareKit.SmoothAlgebra.Localization
