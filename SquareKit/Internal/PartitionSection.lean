import Mathlib.CategoryTheory.Extensive
import Mathlib.CategoryTheory.Discrete.Basic
import Mathlib.CategoryTheory.Equivalence

/-! Complementary subterminal predicates and sections of `u ⨿ 1` in an
extensive category. Predicates retain chosen carriers and their inclusions;
morphisms preserve both predicates. The coproduct universal property expresses
coverage and disjointness together. -/
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
set_option autoImplicit false
namespace SquareKit.Internal.PartitionSection
open CategoryTheory CategoryTheory.Limits
universe v u
variable {C : Type u} [Category.{v} C] [HasTerminal C] [FinitaryExtensive C]
variable {U : C} (u : U ⟶ ⊤_ C) [Mono u]

/-- A complementary pair of subterminal predicates, with the left predicate bounded by `u`. -/
structure Model where
  P : C
  Q : C
  p : P ⟶ ⊤_ C
  q : Q ⟶ ⊤_ C
  bound : P ⟶ U
  bound_over : bound ≫ u = p
  partition : IsColimit (BinaryCofan.mk p q)

namespace Model
variable {u}

instance (M : Model u) : Mono M.p :=
  FinitaryExtensive.mono_inl_of_isColimit M.partition
instance (M : Model u) : Mono M.q :=
  FinitaryExtensive.mono_inr_of_isColimit M.partition

/-- Both maps are inclusions over the terminal object. -/
structure Hom (M N : Model u) where
  left : M.P ⟶ N.P
  right : M.Q ⟶ N.Q
  left_over : left ≫ N.p = M.p
  right_over : right ≫ N.q = M.q

@[ext] theorem Hom.ext {M N : Model u} (f g : Hom M N) : f = g := by
  have hp : f.left = g.left := (cancel_mono N.p).mp (f.left_over.trans g.left_over.symm)
  have hq : f.right = g.right := (cancel_mono N.q).mp (f.right_over.trans g.right_over.symm)
  cases f; cases g; cases hp; cases hq; rfl

instance : Category (Model u) where
  Hom := Hom
  id M := ⟨𝟙 _, 𝟙 _, by simp, by simp⟩
  comp f g := ⟨f.left ≫ g.left, f.right ≫ g.right,
    by rw [Category.assoc, g.left_over, f.left_over],
    by rw [Category.assoc, g.right_over, f.right_over]⟩
  id_comp f := Hom.ext _ _
  comp_id f := Hom.ext _ _
  assoc f g h := Hom.ext _ _

instance (M N : Model u) : Subsingleton (M ⟶ N) := ⟨Hom.ext⟩

/-- Assemble a section from the partition and the bound. -/
def toSection (M : Model u) : ⊤_ C ⟶ U ⨿ ⊤_ C :=
  M.partition.desc (BinaryCofan.mk (M.bound ≫ coprod.inl) (M.q ≫ coprod.inr))

@[reassoc (attr := simp)] theorem p_section (M : Model u) :
    M.p ≫ M.toSection = M.bound ≫ coprod.inl :=
  M.partition.fac _ ⟨WalkingPair.left⟩

@[reassoc (attr := simp)] theorem q_section (M : Model u) :
    M.q ≫ M.toSection = M.q ≫ coprod.inr :=
  M.partition.fac _ ⟨WalkingPair.right⟩

/-- A predicate-preserving homomorphism also preserves the map into the parameter. -/
theorem Hom.bound {M N : Model u} (f : M ⟶ N) : f.left ≫ N.bound = M.bound := by
  apply (cancel_mono u).mp
  rw [Category.assoc, N.bound_over, f.left_over, M.bound_over]

/-- Model homomorphisms preserve the assembled section. -/
theorem section_natural {M N : Model u} (f : M ⟶ N) : M.toSection = N.toSection := by
  apply M.partition.hom_ext
  rintro ⟨j⟩
  cases j
  · change M.p ≫ M.toSection = M.p ≫ N.toSection
    rw [p_section, ← f.left_over, Category.assoc, p_section, ← Category.assoc, Hom.bound]
  · change M.q ≫ M.toSection = M.q ≫ N.toSection
    rw [q_section, ← f.right_over]
    simp only [Category.assoc, q_section]

/-- Extensivity identifies the predicates as actual pullbacks of the summand inclusions. -/
theorem section_pullbacks (M : Model u) :
    IsPullback M.p M.bound M.toSection (coprod.inl : U ⟶ U ⨿ ⊤_ C) ∧
    IsPullback M.q M.q M.toSection (coprod.inr : ⊤_ C ⟶ U ⨿ ⊤_ C) :=
  ((BinaryCofan.isVanKampen_iff _).mp
    (FinitaryExtensive.vanKampen _ (coprodIsCoprod U (⊤_ C)))
    (BinaryCofan.mk M.p M.q) M.bound M.q M.toSection
    (M.p_section.symm) (M.q_section.symm)).mp ⟨M.partition⟩

/-- Equality of sections determines the maps of both predicates. -/
def homOfSection {M N : Model u} (e : M.toSection = N.toSection) : M ⟶ N where
  left := N.section_pullbacks.1.lift M.p M.bound (by rw [← e, p_section])
  right := N.section_pullbacks.2.lift M.q M.q (by rw [← e, q_section])
  left_over := IsPullback.lift_fst _ _ _ _
  right_over := IsPullback.lift_fst _ _ _ _
end Model

variable [HasPullbacks C]

/-- Recover the two actual predicates by pulling back the two summand inclusions. -/
def ofSection (s : ⊤_ C ⟶ U ⨿ ⊤_ C) : Model u where
  P := pullback s coprod.inl
  Q := pullback s coprod.inr
  p := pullback.fst _ _
  q := pullback.fst _ _
  bound := pullback.snd _ _
  bound_over := terminal.hom_ext _ _
  partition :=
    (((BinaryCofan.isVanKampen_iff _).mp
      (FinitaryExtensive.vanKampen _ (coprodIsCoprod U (⊤_ C)))
      (BinaryCofan.mk (pullback.fst s coprod.inl) (pullback.fst s coprod.inr))
      (pullback.snd s coprod.inl) (pullback.snd s coprod.inr) s
      (pullback.condition).symm (pullback.condition).symm).mpr
      ⟨IsPullback.of_hasPullback _ _, IsPullback.of_hasPullback _ _⟩).some

/-- Assembling the pulled-back predicates returns exactly the given section. -/
theorem ofSection_section (s : ⊤_ C ⟶ U ⨿ ⊤_ C) : (ofSection u s).toSection = s := by
  apply (ofSection u s).partition.hom_ext
  rintro ⟨j⟩
  cases j
  · change (ofSection u s).p ≫ (ofSection u s).toSection = _
    rw [Model.p_section]
    exact (pullback.condition).symm
  · change (ofSection u s).q ≫ (ofSection u s).toSection = _
    rw [Model.q_section]
    have ht : pullback.fst s (coprod.inr : ⊤_ C ⟶ U ⨿ ⊤_ C) = pullback.snd s coprod.inr :=
      terminal.hom_ext _ _
    change pullback.fst s coprod.inr ≫ coprod.inr = pullback.fst s coprod.inr ≫ s
    calc
      _ = pullback.snd s coprod.inr ≫ coprod.inr := congrArg (fun k => k ≫ coprod.inr) ht
      _ = _ := (pullback.condition).symm

/-- Classification of complementary partitions, including their morphisms. -/
def sectionEquivalence : Model u ≌ Discrete (⊤_ C ⟶ U ⨿ ⊤_ C) where
  functor := {
    obj M := Discrete.mk M.toSection
    map f := Discrete.eqToHom (Model.section_natural f) }
  inverse := Discrete.functor (fun s => ofSection u s)
  unitIso := NatIso.ofComponents (fun M => {
    hom := Model.homOfSection (ofSection_section u M.toSection).symm
    inv := Model.homOfSection (ofSection_section u M.toSection)
    hom_inv_id := Subsingleton.elim _ _
    inv_hom_id := Subsingleton.elim _ _ }) (by intros; apply Subsingleton.elim)
  counitIso := NatIso.ofComponents
    (fun s => Discrete.eqToIso (ofSection_section u s.as)) (by intros; apply Subsingleton.elim)
end SquareKit.Internal.PartitionSection
