import SquareKit.SheafGroupoidChartPresentation

/-! The actual represented groupoid of an object atlas. Its object sheaf is the
atlas itself; its arrows include arrows between different lifts. -/
noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option warningAsError true
namespace SquareKit.SheafGroupoid.Chart
open CategoryTheory Limits
universe u v
variable {C : Type u} [Category.{v} C] {J : GrothendieckTopology C}
variable {G : Operations J} {U : Sheaf J (Type (max u v))}
variable {p : U ⟶ G.objects} (D : Chart G p p)

/-- Unit on the atlas, constructed through its arrow pullback. -/
def atlasUnit : U ⟶ D.coordinates := (ident D (𝟙 U)).val

/-- Inverse on the atlas retains and exchanges both endpoint lifts. -/
def atlasInverse : D.coordinates ⟶ D.coordinates :=
  (D.inverse D (⟨𝟙 _, by simp, by simp⟩ : D.Arrow D.source D.target)).val

/-- Composition on the actual pullback of composable atlas arrows. -/
def atlasComp : pullback D.target D.source ⟶ D.coordinates :=
  (D.comp D D
    (⟨pullback.fst _ _, rfl, rfl⟩ : D.Arrow
      (pullback.fst _ _ ≫ D.source) (pullback.fst _ _ ≫ D.target))
    (⟨pullback.snd _ _, (pullback.condition).symm, rfl⟩ : D.Arrow
      (pullback.fst _ _ ≫ D.target) (pullback.snd _ _ ≫ D.target))).val

/-- No covering or action presentation is needed to form an atlas groupoid. -/
def atlasOperations : Operations J where
  objects := U
  arrows := D.coordinates
  source := D.source
  target := D.target
  unit := D.atlasUnit
  inverse := D.atlasInverse
  comp := D.atlasComp
  unit_source := (ident D (𝟙 U)).property.1
  unit_target := (ident D (𝟙 U)).property.2
  inverse_source := (D.inverse D
    (⟨𝟙 _, by simp, by simp⟩ : D.Arrow D.source D.target)).property.1
  inverse_target := (D.inverse D
    (⟨𝟙 _, by simp, by simp⟩ : D.Arrow D.source D.target)).property.2
  comp_source := (D.comp D D
    (⟨pullback.fst _ _, rfl, rfl⟩ : D.Arrow
      (pullback.fst _ _ ≫ D.source) (pullback.fst _ _ ≫ D.target))
    (⟨pullback.snd _ _, (pullback.condition).symm, rfl⟩ : D.Arrow
      (pullback.fst _ _ ≫ D.target) (pullback.snd _ _ ≫ D.target))).property.1
  comp_target := (D.comp D D
    (⟨pullback.fst _ _, rfl, rfl⟩ : D.Arrow
      (pullback.fst _ _ ≫ D.source) (pullback.fst _ _ ≫ D.target))
    (⟨pullback.snd _ _, (pullback.condition).symm, rfl⟩ : D.Arrow
      (pullback.fst _ _ ≫ D.target) (pullback.snd _ _ ≫ D.target))).property.2

variable {X : Sheaf J (Type (max u v))}

def atlasArrowEquiv (m n : D.atlasOperations.Object X) :
    D.atlasOperations.Arrow m n ≃ D.Arrow m.map n.map where
  toFun f := ⟨f.map, f.source, f.target⟩
  invFun f := ⟨f.val, f.property.1, f.property.2⟩
  left_inv _ := rfl
  right_inv _ := rfl

@[simp] theorem atlasArrowEquiv_ident (m : D.atlasOperations.Object X) :
    D.atlasArrowEquiv m m (.ident _ m) = ident D m.map := by
  apply Subtype.ext
  have h := congrArg Subtype.val (restrict_ident D m.map (𝟙 U))
  simpa [atlasArrowEquiv, Operations.Arrow.ident, Operations.Arrow.inverse,
    atlasOperations, atlasUnit, atlasInverse, restrict, ident, inverse, arrowEquiv] using h

@[simp] theorem atlasArrowEquiv_inverse {m n : D.atlasOperations.Object X}
    (f : D.atlasOperations.Arrow m n) :
    D.atlasArrowEquiv n m (f.inverse _) = D.inverse D (D.atlasArrowEquiv m n f) := by
  apply Subtype.ext
  have h := congrArg Subtype.val (D.restrict_inverse D f.map
    (⟨𝟙 _, by simp, by simp⟩ : D.Arrow D.source D.target))
  dsimp [restrict] at h
  have hs : f.map ≫ D.source = m.map := f.source
  have ht : f.map ≫ D.target = n.map := f.target
  simpa [hs, ht, atlasArrowEquiv, Operations.Arrow.ident, Operations.Arrow.inverse,
    atlasOperations, atlasUnit, atlasInverse, restrict, ident, inverse, arrowEquiv] using h

@[simp] theorem atlasArrowEquiv_comp {m n q : D.atlasOperations.Object X}
    (f : D.atlasOperations.Arrow m n) (g : D.atlasOperations.Arrow n q) :
    D.atlasArrowEquiv m q (f.comp _ g) =
      D.comp D D (D.atlasArrowEquiv m n f) (D.atlasArrowEquiv n q g) := by
  apply Subtype.ext
  have h := congrArg Subtype.val (D.restrict_comp D D
    (pullback.lift f.map g.map (f.target.trans g.source.symm))
    (⟨pullback.fst _ _, rfl, rfl⟩ : D.Arrow
      (pullback.fst _ _ ≫ D.source) (pullback.fst _ _ ≫ D.target))
    (⟨pullback.snd _ _, (pullback.condition).symm, rfl⟩ : D.Arrow
      (pullback.fst _ _ ≫ D.target) (pullback.snd _ _ ≫ D.target)))
  dsimp [restrict] at h
  have hs : f.map ≫ D.source = m.map := f.source
  have ht : g.map ≫ D.target = q.map := g.target
  simpa [hs, ht, atlasArrowEquiv, Operations.Arrow.comp, atlasOperations, atlasComp,
    comp, arrowEquiv] using h

instance atlasLaws [G.Laws] : D.atlasOperations.Laws where
  id_comp f := (D.atlasArrowEquiv _ _).injective (by
    rw [atlasArrowEquiv_comp, atlasArrowEquiv_ident]
    exact D.ident_comp D _)
  comp_id f := (D.atlasArrowEquiv _ _).injective (by
    rw [atlasArrowEquiv_comp, atlasArrowEquiv_ident]
    exact D.comp_ident D _)
  assoc f g h := (D.atlasArrowEquiv _ _).injective (by
    simp only [atlasArrowEquiv_comp]
    exact D.assoc D D D D D _ _ _)
  inv_comp f := (D.atlasArrowEquiv _ _).injective (by
    rw [atlasArrowEquiv_comp, atlasArrowEquiv_inverse, atlasArrowEquiv_ident]
    exact D.inverse_comp D D _)
  comp_inv f := (D.atlasArrowEquiv _ _).injective (by
    rw [atlasArrowEquiv_comp, atlasArrowEquiv_inverse, atlasArrowEquiv_ident]
    exact D.comp_inverse D D _)

end SquareKit.SheafGroupoid.Chart
