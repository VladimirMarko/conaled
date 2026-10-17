import SquareKit.FirstOrderNaturality
import SquareKit.MatrixDoubling

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

namespace Examples.MatrixCompilerPreservation
open SquareKit FirstOrderCompiler MatrixDoubling
open FirstOrderNaturality

abbrev sourceObjects := objects (sourceTerminal true) (sourceProducts true)
  (⟨oneCoordinate⟩ : Source true)

/-- A primitive is an actual finite matrix, with its source and result coordinates. -/
abbrev Prim (a b : Ty) := (sourceOps true).Hom (sourceObjects a) (sourceObjects b)

def sourceModel : Model (sourceOps true) Prim sourceObjects :=
  cartesian (sourceTerminal true) (sourceProducts true) ⟨oneCoordinate⟩ (fun p => p)

def doubledModel : Model M Prim (doublingMap.obj ∘ sourceObjects) :=
  image doublingMap (sourceTerminal true) (sourceProducts true)
    (MatrixCategory.terminal Nat) P ⟨oneCoordinate⟩ doublingTerminal doublingProducts
    (fun p => duplicate p)

/-- Primitive compatibility is equality of matrices, with no function observation. -/
theorem primitive_preserved {a b : Ty} (p : Prim a b) :
    doublingMap.map p = doubledModel.primitive p := rfl

/-- All source programs, including let and products, commute with matrix doubling. -/
theorem compile_doubled (t : Term Prim Γ a) :
    duplicate (compile sourceModel t) = compile doubledModel t :=
  cartesian_naturality doublingMap_laws (equalityCongr M)
    (MatrixCategory.productCongr Nat) doublingTerminal doublingProducts
    doublingTerminal_laws doublingProducts_laws ⟨oneCoordinate⟩
    (fun p => p) (fun p => duplicate p) primitive_preserved t

/-- Forgetting the source tag is the identity interpretation from the comma example. -/
def identityModel : Model M Prim (fun a => ⟨(sourceObjects a).coordinates⟩) where
  terminal := sourceModel.terminal
  fst := sourceModel.fst
  snd := sourceModel.snd
  pair := sourceModel.pair
  primitive := sourceModel.primitive

def retag : RawMap (sourceOps true) (sourceOps false) where
  obj a := ⟨a.coordinates⟩
  map f := f

def identityInterpretation := retag.comp identityMap

theorem identity_laws : MapLaws identityInterpretation (equality _) (equality _) where
  congr := by intros; subst_vars; rfl
  ident := rfl
  comp _ _ := rfl

theorem compile_identity (t : Term Prim Γ a) :
    compile sourceModel t = compile identityModel t :=
  naturality identity_laws (equalityCongr M)
    (show ModelCongr (equality M) identityModel from ⟨by intros; subst_vars; rfl⟩)
    (show Preserves identityInterpretation (equality M) sourceModel identityModel from
      ⟨rfl, rfl, rfl, fun _ _ => rfl, fun _ => rfl⟩) t

theorem compile_interpretations (t : Term Prim Γ a) :
    duplicate (compile identityModel t) = compile doubledModel t := by
  rw [← compile_identity]
  exact compile_doubled t

/-- The compiled interpretations form the actual identity/doubling comma square. -/
theorem compiled_square (t : Term Prim Γ a) :
    M.comp (embed (sourceObjects a).coordinates).connector (compile identityModel t) =
      M.comp (compile doubledModel t) (embed (sourceObjects (context Γ)).coordinates).connector := by
  rw [← compile_interpretations]
  exact (embedArrow (a := (sourceObjects (context Γ)).coordinates)
    (b := (sourceObjects a).coordinates) (compile identityModel t)).commutes

def tripleTerm : Term Prim [.base] .base :=
  .letE (.pair (.var .here) (.var .here))
    (.prim (fun _ _ => 3) (.fst (.var .here)))

/-- A nonidentity primitive under a captured let is compiled in both matrix models. -/
theorem triple_doubled :
    duplicate (compile identityModel tripleTerm) = compile doubledModel tripleTerm :=
  compile_interpretations tripleTerm

/-- The first copy has coefficient three; there is no cross-copy coefficient. -/
theorem triple_entries :
    (compile doubledModel tripleTerm (.inl (0 : Fin 1)) (.inl (.inr (0 : Fin 1))),
      compile doubledModel tripleTerm (.inr (0 : Fin 1)) (.inl (.inr (0 : Fin 1)))) = (3, 0) := by
  rw [← triple_doubled]
  decide

end Examples.MatrixCompilerPreservation
