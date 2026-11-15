import SquareKit.SheafCoverCech

/-! Commuting squares act on actual Čech overlaps and preserve all projections. -/
noncomputable section
namespace SquareKit.SheafCoverCech
open CategoryTheory CategoryTheory.Limits
universe u v w
variable {C : Type u} [Category.{v} C] {J : GrothendieckTopology C}
variable {X Y X' Y' : Sheaf J (Type w)} {f : Y ⟶ X} {k : Y' ⟶ X'}
variable (u : X' ⟶ X) (v : Y' ⟶ Y) (square : v ≫ f = k ≫ u)

def mapDouble : double k ⟶ double f :=
  pullback.lift (first k ≫ v) (second k ≫ v) (by
    simp only [Category.assoc, square]
    exact congrArg (fun m => m ≫ u) (pullback.condition (f := k) (g := k)))

@[simp, reassoc] theorem mapDouble_first : mapDouble u v square ≫ first f = first k ≫ v :=
  pullback.lift_fst _ _ _
@[simp, reassoc] theorem mapDouble_second : mapDouble u v square ≫ second f = second k ≫ v :=
  pullback.lift_snd _ _ _

theorem mapDouble_diagonal : diagonal k ≫ mapDouble u v square = v ≫ diagonal f := by
  apply pullback.hom_ext <;> simp [Category.assoc, ← Category.assoc (diagonal k)]

def mapTriple : triple k ⟶ triple f :=
  pullback.lift (firstSecond k ≫ mapDouble u v square) (third k ≫ v) (by
    simp only [Category.assoc, mapDouble_first_assoc, square]
    have h := congrArg (fun m => m ≫ u)
      (pullback.condition (f := first k ≫ k) (g := k))
    simpa only [Category.assoc] using h)

@[simp, reassoc] theorem mapTriple_firstSecond :
    mapTriple u v square ≫ firstSecond f = firstSecond k ≫ mapDouble u v square :=
  pullback.lift_fst _ _ _
@[simp, reassoc] theorem mapTriple_third : mapTriple u v square ≫ third f = third k ≫ v :=
  pullback.lift_snd _ _ _

theorem mapTriple_firstThird :
    mapTriple u v square ≫ firstThird f = firstThird k ≫ mapDouble u v square := by
  apply pullback.hom_ext
  · simp only [Category.assoc, firstThird_first, mapDouble_first,
      mapTriple_firstSecond_assoc]
    simp only [← Category.assoc, firstThird_first]
  · simp only [Category.assoc, firstThird_second, mapTriple_third, mapDouble_second]
    simp only [← Category.assoc, firstThird_second]

theorem mapTriple_secondThird :
    mapTriple u v square ≫ secondThird f = secondThird k ≫ mapDouble u v square := by
  apply pullback.hom_ext
  · simp only [Category.assoc, secondThird_first, mapDouble_first,
      mapTriple_firstSecond_assoc, mapDouble_second]
    simp only [← Category.assoc, secondThird_first]
  · simp only [Category.assoc, secondThird_second, mapTriple_third, mapDouble_second]
    simp only [← Category.assoc, secondThird_second]

theorem mapDouble_id : mapDouble (f := f) (k := f) (𝟙 X) (𝟙 Y) (by simp) =
    𝟙 (double f) := by
  apply pullback.hom_ext <;> simp

theorem mapTriple_id : mapTriple (f := f) (k := f) (𝟙 X) (𝟙 Y) (by simp) =
    𝟙 (triple f) := by
  apply pullback.hom_ext <;> simp [mapDouble_id]

variable {X'' Y'' : Sheaf J (Type w)} {l : Y'' ⟶ X''}
variable (u' : X'' ⟶ X') (v' : Y'' ⟶ Y') (square' : v' ≫ k = l ≫ u')

theorem mapDouble_comp : mapDouble u' v' square' ≫ mapDouble u v square =
    mapDouble (u' ≫ u) (v' ≫ v) (by
      rw [Category.assoc, square, ← Category.assoc v', square', Category.assoc]) := by
  apply pullback.hom_ext <;> simp [Category.assoc, mapDouble_first_assoc, mapDouble_second_assoc]

theorem mapTriple_comp : mapTriple u' v' square' ≫ mapTriple u v square =
    mapTriple (u' ≫ u) (v' ≫ v) (by
      rw [Category.assoc, square, ← Category.assoc v', square', Category.assoc]) := by
  apply pullback.hom_ext
  · simp only [Category.assoc, mapTriple_firstSecond, mapTriple_firstSecond_assoc,
      Category.assoc, mapDouble_comp]
  · simp [Category.assoc, mapTriple_third_assoc]

end SquareKit.SheafCoverCech
