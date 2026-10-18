import SquareKit.SmoothOpenMaps

/-! Experimental contravariant duality between principal open domains and their
full smooth-function algebras. Real points reconstruct ordinary maps; equality
of localized elements uses the proved full function-algebra comparison. -/
noncomputable section
open scoped ContDiff
namespace SquareKit.SmoothAlgebra.Localization
open OpenFunctions
variable {n m k : ℕ} {f : Free n} {g : Free m} {q : Free k}

abbrev OpenMap (f : Free n) (g : Free m) := Map (locus f) (locus g)

def evaluation (f : Free n) (x : locus f) : Hom (Functions f) ℝ where
  toFun a := a.val x
  map_act _ _ := rfl

def pullback (h : OpenMap f g) : Hom (Principal g) (Principal f) :=
  (fromOpen f).comp (h.pullback.comp (toOpen g))

@[simp] theorem pullback_apply (h : OpenMap f g) (a : Principal g) (x : locus f) :
    (toOpen f (pullback h a)).val x = (toOpen g a).val (h x) := by
  exact congrArg (fun b : Functions f => b.val x) ((openEquiv f).apply_symm_apply _)

/-- Every algebra map determines a target point from its coordinate images. -/
def reconstruct (h : Hom (Principal g) (Principal f)) : OpenMap f g where
  toFun x := realPoints g ((evaluation f x).comp ((toOpen f).comp h))
  smooth i := by
    change ContDiffOn ℝ ∞ (extendZero (locus f)
      (fun x => (toOpen f (h (principalBase g (generator i)))).val x)) (locus f)
    exact (toOpen f (h (principalBase g (generator i)))).property

@[simp] theorem reconstruct_coordinate (h : Hom (Principal g) (Principal f))
    (x : locus f) (i : Fin m) :
    (reconstruct h x).val i = (toOpen f (h (principalBase g (generator i)))).val x := rfl

theorem reconstruct_value (h : Hom (Principal g) (Principal f)) (a : Principal g) (x : locus f) :
    (toOpen g a).val (reconstruct h x) = (toOpen f (h a)).val x := by
  rw [toOpen_realPoint]
  exact congrArg (fun e : Hom (Principal g) ℝ => e a) ((realPoints g).symm_apply_apply _)

theorem reconstruct_pullback (h : OpenMap f g) : reconstruct (pullback h) = h := by
  apply Map.ext
  intro x
  apply Subtype.ext
  funext i
  rw [reconstruct_coordinate,pullback_apply,toOpen_base]
  rfl

theorem pullback_reconstruct (h : Hom (Principal g) (Principal f)) : pullback (reconstruct h) = h := by
  apply Hom.ext
  intro a
  apply (toOpen_bijective f).injective
  apply OpenFunctions.ext
  intro x
  rw [pullback_apply,reconstruct_value]

/-- All algebra morphisms, not just those induced by globally smooth ambient maps. -/
def mapEquiv (f : Free n) (g : Free m) : OpenMap f g ≃ Hom (Principal g) (Principal f) where
  toFun := pullback
  invFun := reconstruct
  left_inv := reconstruct_pullback
  right_inv := pullback_reconstruct

/-- Existence and uniqueness for every smooth algebra homomorphism. -/
theorem unique_pullback (h : Hom (Principal g) (Principal f)) :
    ∃! a : OpenMap f g, pullback a = h := by
  refine ⟨reconstruct h,pullback_reconstruct h,?_⟩
  intro a ha
  exact (mapEquiv f g).injective (ha.trans (pullback_reconstruct h).symm)

theorem pullback_ident (f : Free n) : pullback (Map.ident (locus f)) = Hom.ident := by
  apply Hom.ext
  intro a
  exact (openEquiv f).symm_apply_apply a

theorem pullback_comp (a : OpenMap f g) (b : OpenMap g q) :
    pullback (Map.comp b a) = (pullback a).comp (pullback b) := by
  apply Hom.ext
  intro z
  apply (toOpen_bijective f).injective
  apply OpenFunctions.ext
  intro x
  rw [pullback_apply]
  change (toOpen q z).val (b (a x)) = (toOpen f (pullback a (pullback b z))).val x
  rw [pullback_apply,pullback_apply]

end SquareKit.SmoothAlgebra.Localization
