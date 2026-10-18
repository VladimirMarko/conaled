import Mathlib.CategoryTheory.Elements
import Mathlib.CategoryTheory.Sites.Sheaf

/-! Experimental site of elements of an arbitrary type-valued presheaf.
Mathlib's elements category has the restriction direction; its opposite is the
site. A covering sieve is exactly a base covering sieve lifted along sections. -/
namespace SquareKit.ElementSite
open CategoryTheory Opposite
universe u v w
variable {C : Type u} [Category.{v} C] (F : Cᵒᵖ ⥤ Type w)

abbrev Site := F.Elementsᵒᵖ
abbrev projection : Site F ⥤ C := (Functor.Elements.π F).leftOp
abbrev point (U : C) (x : F.obj (op U)) : Site F := op (F.elementsMk (op U) x)

/-- The unique restriction arrow over a given base map. -/
abbrev arrow {U V : C} (f : V ⟶ U) (x : F.obj (op U)) :
    point F V (F.map f.op x) ⟶ point F U x := (Functor.Elements.homMk f.op rfl).op

/-- Every element-site sieve comes from a base sieve. Existential source
sections avoid imposing equality of distinct presentations of a restriction. -/
def down {X : Site F} (S : Sieve X) : Sieve ((projection F).obj X) where
  arrows {V} f := ∃ (y : F.obj (op V)) (h : F.map f.op X.unop.val = y),
    S ((Functor.Elements.homMk (x := X.unop) (y := F.elementsMk (op V) y) f.op h).op)
  downward_closed := by
    rintro V W f ⟨y, h, hs⟩ g
    refine ⟨F.map g.op y, ?_, ?_⟩
    · rw [← h, op_comp, F.map_comp]
      rfl
    · exact S.downward_closed hs (arrow F g y)

/-- Lift a sieve through the section-forgetting functor. -/
def up {X : Site F} (R : Sieve ((projection F).obj X)) : Sieve X :=
  R.functorPullback (projection F)

@[simp] theorem up_apply {X Y : Site F} (R : Sieve ((projection F).obj X)) (f : Y ⟶ X) :
    up F R f ↔ R ((projection F).map f) := Iff.rfl

@[simp] theorem down_up {X : Site F} (R : Sieve ((projection F).obj X)) :
    down F (up F R) = R := by
  ext V f
  constructor
  · rintro ⟨y, h, hs⟩
    exact hs
  · intro hf
    exact ⟨_, rfl, hf⟩

@[simp] theorem up_down {X : Site F} (S : Sieve X) : up F (down F S) = S := by
  ext Y f
  constructor
  · rintro ⟨y, h, hs⟩
    have hy : y = Y.unop.val := h.symm.trans f.unop.map_val
    cases hy
    exact hs
  · intro hf
    exact ⟨Y.unop.val, f.unop.map_val, hf⟩

theorem up_injective {X : Site F} : Function.Injective (up F (X := X)) := by
  intro R S h
  have := congrArg (down F) h
  simpa using this

@[simp] theorem down_top (X : Site F) : down F (⊤ : Sieve X) = ⊤ := by
  ext V f
  constructor
  · intro _; trivial
  · intro _; exact ⟨_, rfl, trivial⟩

@[simp] theorem up_pullback {X Y : Site F} (R : Sieve ((projection F).obj X)) (f : Y ⟶ X) :
    up F (R.pullback ((projection F).map f)) = (up F R).pullback f := rfl

@[simp] theorem down_pullback {X Y : Site F} (S : Sieve X) (f : Y ⟶ X) :
    down F (S.pullback f) = (down F S).pullback ((projection F).map f) := by
  apply up_injective F
  rw [up_down, up_pullback, up_down]

/-- The topology inherited through unique restrictions of sections. -/
def topology (J : GrothendieckTopology C) : GrothendieckTopology (Site F) where
  sieves X := {S | down F S ∈ J ((projection F).obj X)}
  top_mem' X := by simp
  pullback_stable' := by
    intro X Y S f hS
    simpa using J.pullback_stable ((projection F).map f) hS
  transitive' := by
    intro X S hS R hR
    apply J.transitive hS (down F R)
    rintro V f ⟨y, h, hs⟩
    have hc := hR hs
    simpa using hc

@[simp] theorem covering_iff (J : GrothendieckTopology C) {X : Site F} (S : Sieve X) :
    S ∈ topology F J X ↔ down F S ∈ J ((projection F).obj X) := Iff.rfl

@[simp] theorem up_covering_iff (J : GrothendieckTopology C) {X : Site F}
    (R : Sieve ((projection F).obj X)) : up F R ∈ topology F J X ↔ R ∈ J _ := by
  rw [covering_iff, down_up]

end SquareKit.ElementSite
