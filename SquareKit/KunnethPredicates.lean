import Mathlib.CategoryTheory.Monoidal.Cartesian.InfSemilattice
import Mathlib.CategoryTheory.Monoidal.Braided.Basic
import Mathlib.CategoryTheory.Adjunction.Basic
import Mathlib.CategoryTheory.Bicategory.Functor.LocallyDiscrete
import Mathlib.CategoryTheory.Category.Cat
import Mathlib.Data.Set.Lattice.Order
import SquareKit.KunnethIndexed
import SquareKit.KunnethTransport
import Mathlib.CategoryTheory.Limits.Types.Pullbacks
open CategoryTheory MonoidalCategory Opposite
open scoped CategoryTheory.SemilatticeInf CategoryTheory.Bicategory
universe u
/-! Predicate families indexed by types, with a retained coefficient-color index.
Surjective base maps satisfy the projection formula. -/
namespace SquareKit.Kunneth.Predicates
/-- A coefficient predicate indexed by a base point and a color. -/
abbrev Fiber (I X : Type u) := Set (X × I)
/-- Reindex the base point while retaining its coefficient color. -/
def pull (I : Type u) {X Y : Type u} (f : X ⟶ Y) : Fiber I Y ⥤ Fiber I X where
 obj A := {xi | (f xi.1, xi.2) ∈ A}
 map h := homOfLE (fun _ hx => leOfHom h hx)
/-- Universal quantification over the actual fiber of a base map. -/
def push (I : Type u) {X Y : Type u} (f : X ⟶ Y) : Fiber I X ⥤ Fiber I Y where
 obj A := {yi | ∀ x, f x = yi.1 → (x,yi.2) ∈ A}
 map h := homOfLE (fun _ hx x e => leOfHom h (hx x e))
/-- Preimage is left adjoint to fiberwise universal quantification. -/
def adj (I : Type u) {X Y : Type u} (f : X ⟶ Y) : pull I f ⊣ push I f :=
 Adjunction.mkOfHomEquiv {
 homEquiv := fun A B => {
   toFun := fun h => homOfLE (fun yi hy x e => leOfHom h (by simpa [pull, e] using hy))
   invFun := fun h => homOfLE (fun xi hx => leOfHom h hx xi.1 rfl)
   left_inv := fun _ => Subsingleton.elim _ _
   right_inv := fun _ => Subsingleton.elim _ _ }
 homEquiv_naturality_left_symm := by intros; apply Subsingleton.elim
 homEquiv_naturality_right := by intros; apply Subsingleton.elim }
noncomputable instance (I : Type u) {X Y : Type u} (f : X ⟶ Y) : (pull I f).Braided where
 ε := homOfLE (by intro x h; trivial)
 μ _ _ := homOfLE (fun _ h => h)
 η := homOfLE (by intro x h; trivial)
 δ _ _ := homOfLE (fun _ h => h)

/-- The indexed category with explicit identity and composition coherence. -/
noncomputable def fibers (I : Type u) : LocallyDiscrete (Type u)ᵒᵖ ⥤ᵖ Cat :=
 LocallyDiscrete.mkPseudofunctor
  (fun X => Cat.of (Fiber I X.unop))
  (fun f => (pull I f.unop).toCatHom)
  (fun X => Cat.Hom.isoMk (NatIso.ofComponents (fun A => Iso.refl _) (by intros; rfl)))
  (fun f g => Cat.Hom.isoMk (NatIso.ofComponents (fun A => Iso.refl _) (by intros; rfl)))
  (by intros; ext; exact Subsingleton.elim (α := ULift (PLift _)) _ _)
  (by intros; ext; exact Subsingleton.elim (α := ULift (PLift _)) _ _)
  (by intros; ext; exact Subsingleton.elim (α := ULift (PLift _)) _ _)


/-- The monoidal indexed provider, with the constructed chosen adjunctions. -/
noncomputable def indexed (I : Type u) : Indexed (Type u) where
 fibers := fibers I
 monoidal X := inferInstanceAs (MonoidalCategory (Fiber I X))
 symmetric X := inferInstanceAs (SymmetricCategory (Fiber I X))
 pullBraided f := inferInstanceAs ((pull I f).Braided)
 push f := push I f
 adj f := adj I f

instance (I X : Type u) : Preorder ((indexed I).Fiber X) :=
  inferInstanceAs (Preorder (Fiber I X))
instance (I X : Type u) (A B : (indexed I).Fiber X) : Subsingleton (A ⟶ B) :=
  inferInstanceAs (Subsingleton (ULift (PLift _)))

/-- The reverse PF map requires a point in each base fiber. -/
theorem projection_isIso (I : Type u) {X Y : Type u} (f : X ⟶ Y)
    (hf : Function.Surjective f) (A : Fiber I X) (B : Fiber I Y) :
    IsIso (projection (adj I f) A B) := by
  refine ⟨⟨homOfLE ?_, Subsingleton.elim _ _, Subsingleton.elim _ _⟩⟩
  intro yi h
  obtain ⟨x, hx⟩ := hf yi.1
  exact ⟨fun z hz => (h z hz).1, by simpa [pull, hx] using (h x hx).2⟩

/-- Pullback universal quantification satisfies BC for every actual pullback. -/
theorem baseChange_isIso (I : Type u)
    {W X Y S : Type u} {p : W ⟶ X} {q : W ⟶ Y} {f : X ⟶ S} {g : Y ⟶ S}
    (h : IsPullback p q f g) (B : Fiber I Y) :
    IsIso (baseChange ((indexed I).adj g) ((indexed I).adj p)
      ((indexed I).square h.w).hom B) := by
  refine ⟨⟨homOfLE ?_, Subsingleton.elim _ _, Subsingleton.elim _ _⟩⟩
  intro xi hx y hy
  obtain ⟨w, hw, hq⟩ := CategoryTheory.Limits.Types.exists_of_isPullback h xi.1 y hy.symm
  have := hx w hw
  change (q w, xi.2) ∈ B at this
  simpa [hq] using this

/-- Surjections supply nonempty fibers, hence the projection formula. -/
noncomputable def proper (I : Type u) : (indexed I).Proper where
 coherent := {
   composition := fun _ _ => { unit := Subsingleton.elim _ _, tensor := fun _ _ => Subsingleton.elim _ _ }
   identity := fun _ => { unit := Subsingleton.elim _ _, tensor := fun _ _ => Subsingleton.elim _ _ } }
 admissible f := Function.Surjective f
 identity X := fun x => ⟨x,rfl⟩
 composition hf hg := hg.comp hf
 pullback := by
   intro W X Y S p q f g h hg x
   obtain ⟨y, hy⟩ := hg (f x)
   obtain ⟨w, hw, _⟩ := CategoryTheory.Limits.Types.exists_of_isPullback h x y hy.symm
   exact ⟨w,hw⟩
 projection f hf A B := projection_isIso I f hf A B
 baseChange h _ B := baseChange_isIso I h B

/-- Change the coefficient-color index by precomposition. Duplicating one
color into two gives the nonidentity route used in the examples. -/
def recolor {I J : Type u} (r : J → I) (X : Type u) : Fiber I X ⥤ Fiber J X where
 obj A := {xj | (xj.1, r xj.2) ∈ A}
 map h := homOfLE (fun _ hx => leOfHom h hx)

noncomputable instance {I J : Type u} (r : J → I) (X : Type u) : (recolor r X).Braided where
 ε := homOfLE (by intro x h; trivial)
 μ _ _ := homOfLE (fun _ h => h)
 η := homOfLE (by intro x h; trivial)
 δ _ _ := homOfLE (fun _ h => h)

/-- Actual pullback comparison for the route. -/
def pullRoute {I J X Y : Type u} (r : J → I) (f : X ⟶ Y) :
    recolor r Y ⋙ pull J f ≅ pull I f ⋙ recolor r X :=
  NatIso.ofComponents (fun _ => Iso.refl _) (by intros; apply Subsingleton.elim)

/-- Actual pushforward comparison; its equality with the mate is checked below. -/
def pushRoute {I J X Y : Type u} (r : J → I) (f : X ⟶ Y) :
    push I f ⋙ recolor r Y ≅ recolor r X ⋙ push J f :=
  NatIso.ofComponents (fun _ => Iso.refl _) (by intros; apply Subsingleton.elim)

theorem pushRoute_eq_mate {I J X Y : Type u} (r : J → I) (f : X ⟶ Y) :
    (pushRoute r f).hom = mateEquiv (adj I f) (adj J f) (pullRoute r f).hom := by
  ext A
  apply Subsingleton.elim

/-- Counit compatibility (C) of the specified comparison. -/
theorem route_counit {I J X Y : Type u} (r : J → I) (f : X ⟶ Y) (A : Fiber I X) :
    (pull J f).map ((pushRoute r f).hom.app A) ≫
        (adj J f).counit.app ((recolor r X).obj A) =
      (pullRoute r f).hom.app ((push I f).obj A) ≫
        (recolor r X).map ((adj I f).counit.app A) := by
  rw [pushRoute_eq_mate]
  exact mateEquiv_counit (adj I f) (adj J f) (pullRoute r f).hom A

/-- Composite pullback comparison used for the tensor transpose. -/
def compositeRoute {I J W X S : Type u} (r : J → I) (p : W ⟶ X) (f : X ⟶ S) :
    recolor r S ⋙ (pull J f ⋙ pull J p) ⟶
      (pull I f ⋙ pull I p) ⋙ recolor r W where
  app _ := 𝟙 _
  naturality _ _ _ := Subsingleton.elim _ _

instance {I J W X S : Type u} (r : J → I) (p : W ⟶ X) (f : X ⟶ S) :
    NatTrans.IsMonoidal (compositeRoute r p f) where
  unit := Subsingleton.elim _ _
  tensor _ _ := Subsingleton.elim _ _

/-- The tensor comparison preserves both transported coefficient objects. -/
def inputIso {I J X Y S : Type u} (r : J → I) (f : X ⟶ S) (g : Y ⟶ S)
    (A : Fiber I X) (B : Fiber I Y) :
    (recolor r S).obj ((push I f).obj A ⊗ (push I g).obj B) ≅
      (push J f).obj ((recolor r X).obj A) ⊗ (push J g).obj ((recolor r Y).obj B) :=
  Iso.refl _

/-- Output conversion for the iterated pushforward and external tensor. -/
def outputIso {I J W X Y S : Type u} (r : J → I)
    (p : W ⟶ X) (q : W ⟶ Y) (f : X ⟶ S) (A : Fiber I X) (B : Fiber I Y) :
    (recolor r S).obj ((push I p ⋙ push I f).obj
      ((pull I p).obj A ⊗ (pull I q).obj B)) ≅
    (push J p ⋙ push J f).obj
      ((pull J p).obj ((recolor r X).obj A) ⊗ (pull J q).obj ((recolor r Y).obj B)) :=
  Iso.refl _

/-- Transport of the independently constructed canonical local maps, obtained
from the shared tensor/counit proof. Thinness discharges structural model laws;
it does not replace invocation of the transport theorem. -/
theorem map_transport {I J W X Y S : Type u} (r : J → I)
    {p : W ⟶ X} {q : W ⟶ Y} {f : X ⟶ S} {g : Y ⟶ S}
    (h : IsPullback p q f g) (A : Fiber I X) (B : Fiber I Y) :
    (inputIso r f g A B).inv ≫
      (recolor r S).map (Kunneth.map (adj I f) (adj I g) (adj I p)
        ((indexed I).square h.w).hom A B) ≫ (outputIso r p q f A B).hom =
    Kunneth.map (adj J f) (adj J g) (adj J p) ((indexed J).square h.w).hom
      ((recolor r X).obj A) ((recolor r Y).obj B) := by
  erw [map_eq_tensorTranspose, map_eq_tensorTranspose]
  apply tensorTranspose_transport_conjugate _ _ (compositeRoute r p f)
    (tensorCompatible_of_monoidal _)
    _ _ _ _ ((pushRoute r f).hom.app A) ((pushRoute r g).hom.app B)
    ((pullRoute r p).inv.app A) ((pullRoute r q).inv.app B)
    (Subsingleton.elim _ _) (Subsingleton.elim _ _)
    (inputIso r f g A B) (outputIso r p q f A B)
    (Subsingleton.elim _ _) (Subsingleton.elim _ _)

/-- Endpoint conversion for the chosen, rather than iterated, pushforward. -/
def indexedOutputIso {I J W X Y S : Type u} (r : J → I)
    (p : W ⟶ X) (q : W ⟶ Y) (f : X ⟶ S) (A : Fiber I X) (B : Fiber I Y) :
    (recolor r S).obj ((push I (p ≫ f)).obj
      ((pull I p).obj A ⊗ (pull I q).obj B)) ≅
    (push J (p ≫ f)).obj
      ((pull J p).obj ((recolor r X).obj A) ⊗ (pull J q).obj ((recolor r Y).obj B)) :=
  Iso.refl _

/-- The chosen-adjoint endpoint conversion commutes with the route. -/
theorem output_composition {I J W X Y S : Type u} (r : J → I)
    (p : W ⟶ X) (q : W ⟶ Y) (f : X ⟶ S) (A : Fiber I X) (B : Fiber I Y) :
    (recolor r S).map (((indexed I).pushComp p f).hom.app
      ((pull I p).obj A ⊗ (pull I q).obj B)) ≫ (indexedOutputIso r p q f A B).hom =
    (outputIso r p q f A B).hom ≫ ((indexed J).pushComp p f).hom.app
      ((pull J p).obj ((recolor r X).obj A) ⊗ (pull J q).obj ((recolor r Y).obj B)) :=
  Subsingleton.elim _ _

set_option backward.isDefEq.respectTransparency false in
/-- Transport (T) includes the chosen composite adjoint and its conversion. -/
theorem indexed_transport {I J W X Y S : Type u} (r : J → I)
    {p : W ⟶ X} {q : W ⟶ Y} {f : X ⟶ S} {g : Y ⟶ S}
    (h : IsPullback p q f g) (A : Fiber I X) (B : Fiber I Y) :
    (inputIso r f g A B).inv ≫
      (recolor r S).map (Indexed.kunneth (D := indexed I) h A B) ≫
        (indexedOutputIso r p q f A B).hom =
    Indexed.kunneth (D := indexed J) h ((recolor r X).obj A) ((recolor r Y).obj B) := by
  change (inputIso r f g A B).inv ≫
    (recolor r S).map (Kunneth.map (adj I f) (adj I g) (adj I p)
      ((indexed I).square h.w).hom A B ≫ ((indexed I).pushComp p f).hom.app
        ((pull I p).obj A ⊗ (pull I q).obj B)) ≫ (indexedOutputIso r p q f A B).hom =
    Kunneth.map (adj J f) (adj J g) (adj J p) ((indexed J).square h.w).hom
      ((recolor r X).obj A) ((recolor r Y).obj B) ≫ ((indexed J).pushComp p f).hom.app
        ((pull J p).obj ((recolor r X).obj A) ⊗ (pull J q).obj ((recolor r Y).obj B))
  simp only [Functor.map_comp, Category.assoc]
  erw [output_composition r p q f A B]
  have ht := map_transport r h A B
  have he := congrArg (fun t => t ≫ ((indexed J).pushComp p f).hom.app
    ((pull J p).obj ((recolor r X).obj A) ⊗ (pull J q).obj ((recolor r Y).obj B))) ht
  simpa only [Category.assoc] using he

/-- Pullback comparisons compose in the actual order of reindexing. -/
theorem pullRoute_composition {I J X Y Z : Type u} (r : J → I)
    (f : X ⟶ Y) (g : Y ⟶ Z) (A : Fiber I Z) :
    (pullRoute r (f ≫ g)).hom.app A =
      (pull J f).map ((pullRoute r g).hom.app A) ≫
        (pullRoute r f).hom.app ((pull I g).obj A) := Subsingleton.elim _ _

end SquareKit.Kunneth.Predicates
