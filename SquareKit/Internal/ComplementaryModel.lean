import Mathlib.Order.Disjoint
import Mathlib.CategoryTheory.Discrete.Basic
import Mathlib.CategoryTheory.Equivalence

/-! Models of the finite propositional theory in a bounded distributive lattice.
Morphisms preserve both predicates. Discreteness is a consequence of those
preservation requirements and complementarity, not part of the definition. -/
set_option autoImplicit false
namespace SquareKit.Internal.ComplementaryModel
open CategoryTheory
universe u
variable {L : Type u} [DistribLattice L] [BoundedOrder L]

structure Model (parameter : L) where
  p : L
  q : L
  complementary : IsCompl p q
  bounded : p ≤ parameter

@[ext] theorem Model.ext {u : L} {M N : Model u} (hp : M.p = N.p) (hq : M.q = N.q) :
    M = N := by
  cases M; cases N; cases hp; cases hq; rfl

/-- Preservation of both named predicates, with no reflection requirement. -/
structure Hom {u : L} (M N : Model u) : Prop where
  p_le : M.p ≤ N.p
  q_le : M.q ≤ N.q

/-- Complementarity forces any model homomorphism to identify its endpoints. -/
theorem Hom.eq {u : L} {M N : Model u} (f : Hom M N) : M = N := by
  apply Model.ext
  · exact le_antisymm f.p_le (M.complementary.symm.Antitone N.complementary.symm f.q_le)
  · exact le_antisymm f.q_le (M.complementary.Antitone N.complementary f.p_le)

instance (u : L) : Category (Model u) where
  Hom M N := PLift (Hom M N)
  id M := ⟨⟨le_rfl, le_rfl⟩⟩
  comp f g := ⟨⟨f.down.p_le.trans g.down.p_le, f.down.q_le.trans g.down.q_le⟩⟩

instance {u : L} (M N : Model u) : Subsingleton (M ⟶ N) := inferInstanceAs (Subsingleton (PLift _))

/-- The comparison maps a homomorphism to the equality proved from its laws. -/
def toDiscrete (u : L) : Model u ⥤ Discrete (Model u) where
  obj := Discrete.mk
  map f := Discrete.eqToHom f.down.eq

/-- The reverse comparison uses identities after equality transport. -/
def fromDiscrete (u : L) : Discrete (Model u) ⥤ Model u :=
  Discrete.functor id

/-- This theory, specifically, has a discrete model category. -/
def discreteEquivalence (u : L) : Model u ≌ Discrete (Model u) where
  functor := toDiscrete u
  inverse := fromDiscrete u
  unitIso := NatIso.ofComponents (fun _ => Iso.refl _) (by intros; apply Subsingleton.elim)
  counitIso := NatIso.ofComponents (fun _ => Iso.refl _) (by intros; apply Subsingleton.elim)

/-- The always-right model satisfies the bound even when the parameter is bottom. -/
def rightModel (u : L) : Model u := ⟨⊥, ⊤, isCompl_bot_top, bot_le⟩

/-- The always-left model exists at the full parameter. -/
def leftModel : Model (⊤ : L) := ⟨⊤, ⊥, isCompl_bot_top.symm, le_rfl⟩

/-- Distinct complementary partitions have no homomorphism between them. -/
theorem no_left_to_right [Nontrivial L] :
    ¬ Nonempty ((leftModel : Model (⊤ : L)) ⟶ rightModel ⊤) := by
  rintro ⟨f⟩
  exact top_ne_bot (le_antisymm f.down.p_le bot_le)

end SquareKit.Internal.ComplementaryModel
