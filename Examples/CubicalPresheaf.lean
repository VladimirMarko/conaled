import SquareKit.Internal.Cubical.Presheaf
import SquareKit.Internal.Cubical.DimensionModels

/-! Varying fibers and simultaneous substitutions through constructed cubical
presheaf comprehension. These do not yet test fibrancy or higher identities. -/
namespace Examples.CubicalPresheaf
open CategoryTheory SquareKit.Cubical SquareKit.Cubical.Presheaf

abbrev naturals : Context := (Functor.const Cubeᵒᵖ).obj ℕ

/-- The fiber over n contains exactly n+1 elements. -/
abbrev finiteFiber : Family naturals where
  obj e := Fin (Nat.succ e.val)
  map f := TypeCat.ofHom (Fin.cast (congrArg Nat.succ f.map_val))
  map_id _ := rfl
  map_comp _ _ := rfl

/-- A coherent section chooses the last element, rather than erasing the index. -/
def lastElement : Term finiteFiber where
  val e := Fin.last e.val
  property f := Fin.ext f.map_val

def successor : naturals ⟶ naturals where
  app _ := TypeCat.ofHom Nat.succ
  naturality _ _ _ := rfl

def twice : naturals ⟶ naturals where
  app _ := TypeCat.ofHom (fun n => 2 * n)
  naturality _ _ _ := rfl

/-- Repeated substitution includes the varying fiber Fin(2n+2). -/
theorem lastElement_twice :
    Term.reindex (Term.reindex lastElement successor) twice =
      Term.reindex lastElement (twice ≫ successor) :=
  Term.reindex_comp lastElement successor twice

/-- The independently calculated value at n=2 is 5 in a six-element fiber. -/
theorem lastElement_at_two :
    (Term.reindex (Term.reindex lastElement successor) twice).val
      (naturals.elementsMk (Opposite.op ⟨0⟩) (2 : ℕ)) = (5 : Fin 6) := by
  rw [lastElement_twice]
  rfl

/-- The same substitutions enter the comprehension pairing theorem. -/
theorem pair_twice :
    twice ≫ pair successor (Term.reindex lastElement successor) =
      pair (twice ≫ successor) (Term.reindex lastElement (twice ≫ successor)) :=
  pair_reindex successor (Term.reindex lastElement successor) twice

/-- Forgetting the varying index cannot produce an equivalence of these fibers. -/
theorem fibers_not_constant :
    ¬ Nonempty (finiteFiber.obj (naturals.elementsMk (Opposite.op ⟨0⟩) (0 : ℕ)) ≃
      finiteFiber.obj (naturals.elementsMk (Opposite.op ⟨0⟩) (1 : ℕ))) := by
  rintro ⟨e⟩
  change Fin 1 ≃ Fin 2 at e
  have h := Fintype.card_congr e
  simp at h

/-- Every assembled context map retains its selected dependent component. -/
theorem selected_component_retained :
    Term.reindex (generic finiteFiber)
      (pair successor (Term.reindex lastElement successor)) =
      Term.reindex lastElement successor :=
  generic_pair successor (Term.reindex lastElement successor)

/-- The represented interval remembers cube substitutions, not just endpoints. -/
abbrev interval : Context := yoneda.obj (Cube.mk 1)

abbrev coordinateFamily : Family interval :=
  Functor.Elements.π interval ⋙ interval

def coordinate : Term coordinateFamily where
  val e := e.val
  property f := f.map_val

/-- Restriction of a selected coordinate follows actual contravariant cube action. -/
theorem coordinate_connection_zero :
    (total coordinateFamily).map (@Quiver.Hom.op Cube _ ⟨1⟩ ⟨2⟩ (Cube.face false))
      ⟨Cube.connection, coordinate.val (interval.elementsMk (Opposite.op ⟨2⟩) Cube.connection)⟩ =
    ⟨Cube.zeroLine, Cube.zeroLine⟩ := by
  change (⟨Cube.comp (Cube.face false) Cube.connection,
    Cube.comp (Cube.face false) Cube.connection⟩ :
    Σ x : Cube.Hom ⟨1⟩ ⟨1⟩, Cube.Hom ⟨1⟩ ⟨1⟩) = _
  rw [Cube.face_zero_connection]

/-- The other face preserves the full variable line in both components. -/
theorem coordinate_connection_one :
    (total coordinateFamily).map (@Quiver.Hom.op Cube _ ⟨1⟩ ⟨2⟩ (Cube.face true))
      ⟨Cube.connection, coordinate.val (interval.elementsMk (Opposite.op ⟨2⟩) Cube.connection)⟩ =
    ⟨Cube.identity ⟨1⟩, Cube.identity ⟨1⟩⟩ := by
  change (⟨Cube.comp (Cube.face true) Cube.connection,
    Cube.comp (Cube.face true) Cube.connection⟩ :
    Σ x : Cube.Hom ⟨1⟩ ⟨1⟩, Cube.Hom ⟨1⟩ ⟨1⟩) = _
  rw [Cube.face_one_connection]

end Examples.CubicalPresheaf
