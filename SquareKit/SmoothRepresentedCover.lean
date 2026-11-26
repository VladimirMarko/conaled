import SquareKit.SheafCoproductLocal
import SquareKit.SmoothOrdinaryQuotient
import SquareKit.SheafCoverCech
import SquareKit.SheafActionQuotientDescent
import Mathlib.CategoryTheory.Limits.Types.Pullbacks

/-! Explicit representable charts and intersections over a sheaf parameter.
Representability and covering are geometric inputs, not descent conclusions. -/
noncomputable section
namespace SquareKit.SmoothRepresentedCover
open CategoryTheory CategoryTheory.Limits Opposite EuclideanOpen SmoothOpenSite

structure Atlas (X : Sheaf topology Type) (I : Type) where
  domain : I → Domain
  chart : ∀ i, embedding.obj (domain i) ⟶ X
  covering : ∀ (V : SmoothPresentationSite.Site) (x : X.obj.obj (op V)),
    SheafCoproductLocal.liftSieve (fun i => embedding.obj (domain i)) chart x ∈ topology V
  pair : I → I → Domain
  left : ∀ i j, pair i j ⟶ domain i
  right : ∀ i j, pair i j ⟶ domain j
  square : ∀ i j, IsPullback (embedding.map (left i j)) (embedding.map (right i j)) (chart i) (chart j)
  triple : I → I → I → Domain
  firstSecond : ∀ i j k, triple i j k ⟶ pair i j
  third : ∀ i j k, triple i j k ⟶ domain k
  triple_isPullback : ∀ i j k, IsPullback (embedding.map (firstSecond i j k))
    (embedding.map (third i j k)) (embedding.map (left i j) ≫ chart i) (chart k)

namespace Atlas
variable {X : Sheaf topology Type} {I : Type} (A : Atlas X I)

abbrev family : I → Sheaf topology Type := fun i => embedding.obj (A.domain i)
abbrev total := SheafCoproductLocal.total A.family
abbrev inclusion (i : I) : embedding.obj (A.domain i) ⟶ A.total :=
  SheafCoproductLocal.inclusion A.family i
abbrev cover : A.total ⟶ X := SheafCoproductLocal.desc A.family A.chart

instance cover_isLocallySurjective : Presheaf.IsLocallySurjective topology A.cover.hom :=
  SheafCoproductLocal.isLocallySurjective_desc A.family A.chart A.covering

@[simp, reassoc] theorem inclusion_cover (i : I) : A.inclusion i ≫ A.cover = A.chart i :=
  SheafCoproductLocal.inclusion_desc A.family A.chart i

def diagonal (i : I) : A.domain i ⟶ A.pair i i :=
  (homEquiv _ _).symm ((A.square i i).lift (𝟙 _) (𝟙 _) (by simp))

theorem diagonal_map (i : I) : embedding.map (A.diagonal i) =
    (A.square i i).lift (𝟙 _) (𝟙 _) (by simp) := forward_inverse _

@[simp, reassoc] theorem diagonal_left (i : I) : A.diagonal i ≫ A.left i i = 𝟙 _ := by
  apply (homEquiv _ _).injective
  change embedding.map (_ ≫ _) = embedding.map (𝟙 _)
  rw [Functor.map_comp, diagonal_map]
  simp

@[simp, reassoc] theorem diagonal_right (i : I) : A.diagonal i ≫ A.right i i = 𝟙 _ := by
  apply (homEquiv _ _).injective
  change embedding.map (_ ≫ _) = embedding.map (𝟙 _)
  rw [Functor.map_comp, diagonal_map]
  simp

def reverse (i j : I) : A.pair i j ⟶ A.pair j i :=
  (homEquiv _ _).symm ((A.square j i).lift (embedding.map (A.right i j))
    (embedding.map (A.left i j)) (A.square i j).w.symm)

theorem reverse_map (i j : I) : embedding.map (A.reverse i j) =
    (A.square j i).lift (embedding.map (A.right i j))
      (embedding.map (A.left i j)) (A.square i j).w.symm := forward_inverse _

@[simp, reassoc] theorem reverse_left (i j : I) : A.reverse i j ≫ A.left j i = A.right i j := by
  apply (homEquiv _ _).injective
  change embedding.map (_ ≫ _) = embedding.map _
  rw [Functor.map_comp, reverse_map]
  simp

@[simp, reassoc] theorem reverse_right (i j : I) : A.reverse i j ≫ A.right j i = A.left i j := by
  apply (homEquiv _ _).injective
  change embedding.map (_ ≫ _) = embedding.map _
  rw [Functor.map_comp, reverse_map]
  simp

def firstThird (i j k : I) : A.triple i j k ⟶ A.pair i k :=
  (homEquiv _ _).symm ((A.square i k).lift
    (embedding.map (A.firstSecond i j k) ≫ embedding.map (A.left i j))
    (embedding.map (A.third i j k)) (by
      simpa only [Category.assoc] using (A.triple_isPullback i j k).w))

def secondThird (i j k : I) : A.triple i j k ⟶ A.pair j k :=
  (homEquiv _ _).symm ((A.square j k).lift
    (embedding.map (A.firstSecond i j k) ≫ embedding.map (A.right i j))
    (embedding.map (A.third i j k)) (by
      rw [Category.assoc, ← (A.square i j).w]
      exact (A.triple_isPullback i j k).w))

theorem firstThird_map (i j k : I) : embedding.map (A.firstThird i j k) =
    (A.square i k).lift
      (embedding.map (A.firstSecond i j k) ≫ embedding.map (A.left i j))
      (embedding.map (A.third i j k)) (by
        simpa only [Category.assoc] using (A.triple_isPullback i j k).w) := forward_inverse _

theorem secondThird_map (i j k : I) : embedding.map (A.secondThird i j k) =
    (A.square j k).lift
      (embedding.map (A.firstSecond i j k) ≫ embedding.map (A.right i j))
      (embedding.map (A.third i j k)) (by
        rw [Category.assoc, ← (A.square i j).w]
        exact (A.triple_isPullback i j k).w) := forward_inverse _

@[simp, reassoc] theorem firstThird_left (i j k : I) :
    A.firstThird i j k ≫ A.left i k = A.firstSecond i j k ≫ A.left i j := by
  apply (homEquiv _ _).injective
  change embedding.map (_ ≫ _) = embedding.map (_ ≫ _)
  rw [Functor.map_comp, firstThird_map, Functor.map_comp]
  simp

@[simp, reassoc] theorem firstThird_right (i j k : I) :
    A.firstThird i j k ≫ A.right i k = A.third i j k := by
  apply (homEquiv _ _).injective
  change embedding.map (_ ≫ _) = embedding.map _
  rw [Functor.map_comp, firstThird_map]
  simp

@[simp, reassoc] theorem secondThird_left (i j k : I) :
    A.secondThird i j k ≫ A.left j k = A.firstSecond i j k ≫ A.right i j := by
  apply (homEquiv _ _).injective
  change embedding.map (_ ≫ _) = embedding.map (_ ≫ _)
  rw [Functor.map_comp, secondThird_map, Functor.map_comp]
  simp

@[simp, reassoc] theorem secondThird_right (i j k : I) :
    A.secondThird i j k ≫ A.right j k = A.third i j k := by
  apply (homEquiv _ _).injective
  change embedding.map (_ ≫ _) = embedding.map _
  rw [Functor.map_comp, secondThird_map]
  simp

/-- Pair charts map into the actual double overlap of the coproduct cover. -/
def pairMap (i j : I) : embedding.obj (A.pair i j) ⟶ SheafCoverCech.double A.cover :=
  pullback.lift (embedding.map (A.left i j) ≫ A.inclusion i)
    (embedding.map (A.right i j) ≫ A.inclusion j) (by simp [Category.assoc, (A.square i j).w])

@[simp, reassoc] theorem pairMap_first (i j : I) :
    A.pairMap i j ≫ SheafCoverCech.first A.cover = embedding.map (A.left i j) ≫ A.inclusion i :=
  pullback.lift_fst _ _ _

@[simp, reassoc] theorem pairMap_second (i j : I) :
    A.pairMap i j ≫ SheafCoverCech.second A.cover = embedding.map (A.right i j) ≫ A.inclusion j :=
  pullback.lift_snd _ _ _

/-- Pair intersections cover the actual sheaf double overlap. -/
theorem pairMap_cover (V : SmoothPresentationSite.Site)
    (z : (SheafCoverCech.double A.cover).obj.obj (op V)) :
    SheafCoproductLocal.liftSieve (fun ij : I × I => embedding.obj (A.pair ij.1 ij.2))
      (fun ij => A.pairMap ij.1 ij.2) z ∈ topology V := by
  let a := (SheafCoverCech.first A.cover).hom.app (op V) z
  let b := (SheafCoverCech.second A.cover).hom.app (op V) z
  apply topology.superset_covering _ (topology.intersection_covering
    (SheafCoproductLocal.liftSieve_cover A.family a)
    (SheafCoproductLocal.liftSieve_cover A.family b))
  intro W k hk
  obtain ⟨⟨i,x,hx⟩,⟨j,y,hy⟩⟩ := hk
  have hxy : (A.chart i).hom.app (op W) x = (A.chart j).hom.app (op W) y := by
    have hi := congrArg (fun f : embedding.obj (A.domain i) ⟶ X => f.hom.app (op W) x)
      (A.inclusion_cover i)
    have hj := congrArg (fun f : embedding.obj (A.domain j) ⟶ X => f.hom.app (op W) y)
      (A.inclusion_cover j)
    change A.cover.hom.app (op W) ((A.inclusion i).hom.app (op W) x) = _ at hi
    change A.cover.hom.app (op W) ((A.inclusion j).hom.app (op W) y) = _ at hj
    rw [← hi, ← hj, hx, hy, ← NatTrans.naturality_apply, ← NatTrans.naturality_apply]
    exact congrArg (fun f : SheafCoverCech.double A.cover ⟶ X =>
      f.hom.app (op W) ((SheafCoverCech.double A.cover).obj.map k.op z))
      (pullback.condition (f := A.cover) (g := A.cover))
  obtain ⟨w,hw₁,hw₂⟩ := Types.exists_of_isPullback
    ((A.square i j).map (sheafToPresheaf topology Type ⋙ (evaluation _ _).obj (op W))) x y hxy
  change (embedding.map (A.left i j)).hom.app (op W) w = x at hw₁
  change (embedding.map (A.right i j)).hom.app (op W) w = y at hw₂
  refine ⟨(i,j),w,?_⟩
  apply Types.ext_of_isPullback
    ((IsPullback.of_hasPullback A.cover A.cover).map
      (sheafToPresheaf topology Type ⋙ (evaluation _ _).obj (op W)))
  · have hp := congrArg (fun f : embedding.obj (A.pair i j) ⟶ A.total => f.hom.app (op W) w)
      (A.pairMap_first i j)
    change (SheafCoverCech.first A.cover).hom.app (op W) ((A.pairMap i j).hom.app (op W) w) =
      (A.inclusion i).hom.app (op W) ((embedding.map (A.left i j)).hom.app (op W) w) at hp
    change (SheafCoverCech.first A.cover).hom.app (op W) ((A.pairMap i j).hom.app (op W) w) =
      (SheafCoverCech.first A.cover).hom.app (op W) ((SheafCoverCech.double A.cover).obj.map k.op z)
    rw [hp, hw₁, hx]
    exact (NatTrans.naturality_apply (SheafCoverCech.first A.cover).hom k.op z).symm
  · have hp := congrArg (fun f : embedding.obj (A.pair i j) ⟶ A.total => f.hom.app (op W) w)
      (A.pairMap_second i j)
    change (SheafCoverCech.second A.cover).hom.app (op W) ((A.pairMap i j).hom.app (op W) w) =
      (A.inclusion j).hom.app (op W) ((embedding.map (A.right i j)).hom.app (op W) w) at hp
    change (SheafCoverCech.second A.cover).hom.app (op W) ((A.pairMap i j).hom.app (op W) w) =
      (SheafCoverCech.second A.cover).hom.app (op W) ((SheafCoverCech.double A.cover).obj.map k.op z)
    rw [hp, hw₂, hy]
    exact (NatTrans.naturality_apply (SheafCoverCech.second A.cover).hom k.op z).symm

abbrev pairFamily : (I × I) → Sheaf topology Type := fun ij => embedding.obj (A.pair ij.1 ij.2)
abbrev pairCover : SheafCoproductLocal.total A.pairFamily ⟶ SheafCoverCech.double A.cover :=
  SheafCoproductLocal.desc A.pairFamily (fun ij => A.pairMap ij.1 ij.2)

instance pairCover_isLocallySurjective : Presheaf.IsLocallySurjective topology A.pairCover.hom :=
  SheafCoproductLocal.isLocallySurjective_desc A.pairFamily (fun ij => A.pairMap ij.1 ij.2) A.pairMap_cover

/-- Any family of maps from represented pair intersections agrees where its
images in the actual double overlap agree. Summand indices are retained locally. -/
theorem pairHom_compatible {N : Sheaf topology Type}
    (m : ∀ i j, embedding.obj (A.pair i j) ⟶ N)
    (V : SmoothPresentationSite.Site) (i j k l : I)
    (x : (embedding.obj (A.pair i j)).obj.obj (op V))
    (y : (embedding.obj (A.pair k l)).obj.obj (op V))
    (h : (A.pairMap i j).hom.app (op V) x = (A.pairMap k l).hom.app (op V) y) :
    (m i j).hom.app (op V) x = (m k l).hom.app (op V) y := by
  let xi := (embedding.map (A.left i j)).hom.app (op V) x
  let xj := (embedding.map (A.right i j)).hom.app (op V) x
  let yk := (embedding.map (A.left k l)).hom.app (op V) y
  let yl := (embedding.map (A.right k l)).hom.app (op V) y
  have hl : (A.inclusion i).hom.app (op V) xi = (A.inclusion k).hom.app (op V) yk := by
    have h₁ := congrArg (fun f : embedding.obj (A.pair i j) ⟶ A.total => f.hom.app (op V) x)
      (A.pairMap_first i j)
    have h₂ := congrArg (fun f : embedding.obj (A.pair k l) ⟶ A.total => f.hom.app (op V) y)
      (A.pairMap_first k l)
    exact h₁.symm.trans ((congrArg ((SheafCoverCech.first A.cover).hom.app (op V)) h).trans h₂)
  have hr : (A.inclusion j).hom.app (op V) xj = (A.inclusion l).hom.app (op V) yl := by
    have h₁ := congrArg (fun f : embedding.obj (A.pair i j) ⟶ A.total => f.hom.app (op V) x)
      (A.pairMap_second i j)
    have h₂ := congrArg (fun f : embedding.obj (A.pair k l) ⟶ A.total => f.hom.app (op V) y)
      (A.pairMap_second k l)
    exact h₁.symm.trans ((congrArg ((SheafCoverCech.second A.cover).hom.app (op V)) h).trans h₂)
  let R := Presheaf.equalizerSieve (F := SheafCoproductLocal.coordinates A.family) ⟨i,xi⟩ ⟨k,yk⟩
  let S := Presheaf.equalizerSieve (F := SheafCoproductLocal.coordinates A.family) ⟨j,xj⟩ ⟨l,yl⟩
  have hR : R ∈ topology V := SheafCoproductLocal.inclusion_locally_equal A.family i k xi yk hl
  have hS : S ∈ topology V := SheafCoproductLocal.inclusion_locally_equal A.family j l xj yl hr
  apply (((isSheaf_iff_isSheaf_of_type _ _).mp N.property) (R ⊓ S)
    (topology.intersection_covering hR hS)).isSeparatedFor.ext
  intro W f hf
  have hx : (⟨i, (A.family i).obj.map f.op xi⟩ : Σ a, (A.family a).obj.obj (op W)) =
      ⟨k, (A.family k).obj.map f.op yk⟩ := hf.1
  have hy : (⟨j, (A.family j).obj.map f.op xj⟩ : Σ a, (A.family a).obj.obj (op W)) =
      ⟨l, (A.family l).obj.map f.op yl⟩ := hf.2
  have hi : i = k := congrArg Sigma.fst hx
  have hj : j = l := congrArg Sigma.fst hy
  subst k
  subst l
  have hx' := eq_of_heq (Sigma.mk.inj_iff.mp hx).2
  have hy' := eq_of_heq (Sigma.mk.inj_iff.mp hy).2
  have he : (embedding.obj (A.pair i j)).obj.map f.op x =
      (embedding.obj (A.pair i j)).obj.map f.op y := by
    apply Types.ext_of_isPullback
      ((A.square i j).map (sheafToPresheaf topology Type ⋙ (evaluation _ _).obj (op W)))
    · change (embedding.map (A.left i j)).hom.app (op W) _ =
        (embedding.map (A.left i j)).hom.app (op W) _
      rw [NatTrans.naturality_apply, NatTrans.naturality_apply]
      exact hx'
    · change (embedding.map (A.right i j)).hom.app (op W) _ =
        (embedding.map (A.right i j)).hom.app (op W) _
      rw [NatTrans.naturality_apply, NatTrans.naturality_apply]
      exact hy'
  rw [← NatTrans.naturality_apply, ← NatTrans.naturality_apply, he]

/-- Assemble arbitrary represented overlap maps using the proved sheaf cover. -/
def pairHom {N : Sheaf topology Type} (m : ∀ i j, embedding.obj (A.pair i j) ⟶ N) :
    SheafCoverCech.double A.cover ⟶ N :=
  SheafActionQuotient.Descent.descendMap A.pairCover
    (SheafCoproductLocal.desc A.pairFamily (fun ij => m ij.1 ij.2)) (fun U x y h =>
      SheafCoproductLocal.desc_fiber_constant A.pairFamily
        (fun ij => A.pairMap ij.1 ij.2) (fun ij => m ij.1 ij.2)
        (fun V ij kl x y h => A.pairHom_compatible m V ij.1 ij.2 kl.1 kl.2 x y h)
        U.unop x y h)

@[simp, reassoc] theorem pairHom_fac {N : Sheaf topology Type}
    (m : ∀ i j, embedding.obj (A.pair i j) ⟶ N) (i j : I) :
    A.pairMap i j ≫ A.pairHom m = m i j := by
  have h := SheafActionQuotient.Descent.descendMap_fac A.pairCover
    (SheafCoproductLocal.desc A.pairFamily (fun ij => m ij.1 ij.2))
    (fun U x y h => SheafCoproductLocal.desc_fiber_constant A.pairFamily
      (fun ij => A.pairMap ij.1 ij.2) (fun ij => m ij.1 ij.2)
      (fun V ij kl x y h => A.pairHom_compatible m V ij.1 ij.2 kl.1 kl.2 x y h) U.unop x y h)
  change A.pairCover ≫ A.pairHom m = _ at h
  have hi := congrArg (fun f => SheafCoproductLocal.inclusion A.pairFamily (i,j) ≫ f) h
  simpa only [← Category.assoc, SheafCoproductLocal.inclusion_desc] using hi

theorem pairHom_ext {N : Sheaf topology Type} (f g : SheafCoverCech.double A.cover ⟶ N)
    (h : ∀ i j, A.pairMap i j ≫ f = A.pairMap i j ≫ g) : f = g := by
  apply (cancel_epi A.pairCover).mp
  apply colimit.hom_ext
  intro ⟨i,j⟩
  simpa only [← Category.assoc, SheafCoproductLocal.inclusion_desc] using h i j

/-- The complete maps, not just their point observations, are recovered. -/
def pairHomEquiv (N : Sheaf topology Type) :
    (SheafCoverCech.double A.cover ⟶ N) ≃ (∀ i j, embedding.obj (A.pair i j) ⟶ N) where
  toFun f i j := A.pairMap i j ≫ f
  invFun := A.pairHom
  left_inv f := A.pairHom_ext _ f (fun i j => A.pairHom_fac _ i j)
  right_inv m := funext (fun i => funext (fun j => A.pairHom_fac m i j))

/-- Represented triples map to the actual triple overlap. -/
def tripleMap (i j k : I) : embedding.obj (A.triple i j k) ⟶ SheafCoverCech.triple A.cover :=
  pullback.lift (embedding.map (A.firstSecond i j k) ≫ A.pairMap i j)
    (embedding.map (A.third i j k) ≫ A.inclusion k) (by
      simp only [Category.assoc, pairMap_first_assoc, inclusion_cover]
      exact (A.triple_isPullback i j k).w)

@[simp, reassoc] theorem tripleMap_firstSecond (i j k : I) :
    A.tripleMap i j k ≫ SheafCoverCech.firstSecond A.cover =
      embedding.map (A.firstSecond i j k) ≫ A.pairMap i j := pullback.lift_fst _ _ _

@[simp, reassoc] theorem tripleMap_third (i j k : I) :
    A.tripleMap i j k ≫ SheafCoverCech.third A.cover =
      embedding.map (A.third i j k) ≫ A.inclusion k := pullback.lift_snd _ _ _

@[simp, reassoc] theorem tripleMap_firstThird (i j k : I) :
    A.tripleMap i j k ≫ SheafCoverCech.firstThird A.cover =
      embedding.map (A.firstThird i j k) ≫ A.pairMap i k := by
  apply pullback.hom_ext
  · simp only [Category.assoc, SheafCoverCech.firstThird_first,
      tripleMap_firstSecond_assoc, pairMap_first]
    simpa only [Functor.map_comp, Category.assoc] using
      congrArg (fun f => embedding.map f ≫ A.inclusion i) (A.firstThird_left i j k).symm
  · simp only [Category.assoc, SheafCoverCech.firstThird_second, tripleMap_third,
      pairMap_second]
    rw [← Category.assoc, ← Functor.map_comp, firstThird_right]

@[simp, reassoc] theorem tripleMap_secondThird (i j k : I) :
    A.tripleMap i j k ≫ SheafCoverCech.secondThird A.cover =
      embedding.map (A.secondThird i j k) ≫ A.pairMap j k := by
  apply pullback.hom_ext
  · simp only [Category.assoc, SheafCoverCech.secondThird_first,
      tripleMap_firstSecond_assoc, pairMap_second, pairMap_first]
    simpa only [Functor.map_comp, Category.assoc] using
      congrArg (fun f => embedding.map f ≫ A.inclusion j) (A.secondThird_left i j k).symm
  · simp only [Category.assoc, SheafCoverCech.secondThird_second, tripleMap_third,
      pairMap_second]
    rw [← Category.assoc, ← Functor.map_comp, secondThird_right]

theorem tripleMap_cover (V : SmoothPresentationSite.Site)
    (z : (SheafCoverCech.triple A.cover).obj.obj (op V)) :
    SheafCoproductLocal.liftSieve
      (fun ijk : (I × I) × I => embedding.obj (A.triple ijk.1.1 ijk.1.2 ijk.2))
      (fun ijk => A.tripleMap ijk.1.1 ijk.1.2 ijk.2) z ∈ topology V := by
  let a := (SheafCoverCech.firstSecond A.cover).hom.app (op V) z
  let b := (SheafCoverCech.third A.cover).hom.app (op V) z
  apply topology.superset_covering _ (topology.intersection_covering
    (A.pairMap_cover V a) (SheafCoproductLocal.liftSieve_cover A.family b))
  intro W r hr
  obtain ⟨⟨⟨i,j⟩,x,hx⟩,⟨k,y,hy⟩⟩ := hr
  have hxy : (embedding.map (A.left i j) ≫ A.chart i).hom.app (op W) x =
      (A.chart k).hom.app (op W) y := by
    have hi := congrArg (fun f : embedding.obj (A.pair i j) ⟶ X => f.hom.app (op W) x)
      (show A.pairMap i j ≫ (SheafCoverCech.first A.cover ≫ A.cover) =
        embedding.map (A.left i j) ≫ A.chart i by
          rw [← Category.assoc, A.pairMap_first, Category.assoc, A.inclusion_cover])
    have hj := congrArg (fun f : embedding.obj (A.domain k) ⟶ X => f.hom.app (op W) y)
      (A.inclusion_cover k)
    change (SheafCoverCech.first A.cover ≫ A.cover).hom.app (op W)
      ((A.pairMap i j).hom.app (op W) x) = _ at hi
    change A.cover.hom.app (op W) ((A.inclusion k).hom.app (op W) y) = _ at hj
    rw [← hi, ← hj, hx, hy, ← NatTrans.naturality_apply, ← NatTrans.naturality_apply]
    exact congrArg (fun f : SheafCoverCech.triple A.cover ⟶ X =>
      f.hom.app (op W) ((SheafCoverCech.triple A.cover).obj.map r.op z))
      (pullback.condition (f := SheafCoverCech.first A.cover ≫ A.cover) (g := A.cover))
  obtain ⟨w,hw₁,hw₂⟩ := Types.exists_of_isPullback
    ((A.triple_isPullback i j k).map (sheafToPresheaf topology Type ⋙ (evaluation _ _).obj (op W))) x y hxy
  change (embedding.map (A.firstSecond i j k)).hom.app (op W) w = x at hw₁
  change (embedding.map (A.third i j k)).hom.app (op W) w = y at hw₂
  refine ⟨((i,j),k),w,?_⟩
  apply Types.ext_of_isPullback
    ((IsPullback.of_hasPullback (SheafCoverCech.first A.cover ≫ A.cover) A.cover).map
      (sheafToPresheaf topology Type ⋙ (evaluation _ _).obj (op W)))
  · have hp := congrArg (fun f : embedding.obj (A.triple i j k) ⟶ SheafCoverCech.double A.cover =>
        f.hom.app (op W) w) (A.tripleMap_firstSecond i j k)
    change (SheafCoverCech.firstSecond A.cover).hom.app (op W) ((A.tripleMap i j k).hom.app (op W) w) =
      (A.pairMap i j).hom.app (op W) ((embedding.map (A.firstSecond i j k)).hom.app (op W) w) at hp
    change (SheafCoverCech.firstSecond A.cover).hom.app (op W) ((A.tripleMap i j k).hom.app (op W) w) =
      (SheafCoverCech.firstSecond A.cover).hom.app (op W) ((SheafCoverCech.triple A.cover).obj.map r.op z)
    rw [hp, hw₁, hx]
    exact (NatTrans.naturality_apply (SheafCoverCech.firstSecond A.cover).hom r.op z).symm
  · have hp := congrArg (fun f : embedding.obj (A.triple i j k) ⟶ A.total => f.hom.app (op W) w)
      (A.tripleMap_third i j k)
    change (SheafCoverCech.third A.cover).hom.app (op W) ((A.tripleMap i j k).hom.app (op W) w) =
      (A.inclusion k).hom.app (op W) ((embedding.map (A.third i j k)).hom.app (op W) w) at hp
    change (SheafCoverCech.third A.cover).hom.app (op W) ((A.tripleMap i j k).hom.app (op W) w) =
      (SheafCoverCech.third A.cover).hom.app (op W) ((SheafCoverCech.triple A.cover).obj.map r.op z)
    rw [hp, hw₂, hy]
    exact (NatTrans.naturality_apply (SheafCoverCech.third A.cover).hom r.op z).symm

/-- Represented triples jointly detect complete maps from the actual triple overlap. -/
theorem tripleHom_ext {N : Sheaf topology Type}
    (f g : SheafCoverCech.triple A.cover ⟶ N)
    (h : ∀ i j k, A.tripleMap i j k ≫ f = A.tripleMap i j k ≫ g) : f = g := by
  let F := fun ijk : (I × I) × I => embedding.obj (A.triple ijk.1.1 ijk.1.2 ijk.2)
  let j := fun ijk : (I × I) × I => A.tripleMap ijk.1.1 ijk.1.2 ijk.2
  have : Presheaf.IsLocallySurjective topology (SheafCoproductLocal.desc F j).hom :=
    SheafCoproductLocal.isLocallySurjective_desc F j A.tripleMap_cover
  apply (cancel_epi (SheafCoproductLocal.desc F j)).mp
  apply colimit.hom_ext
  intro ⟨⟨i,j⟩,k⟩
  simpa only [← Category.assoc, SheafCoproductLocal.inclusion_desc] using h i j k

@[simp, reassoc] theorem diagonal_pairMap (i : I) :
    embedding.map (A.diagonal i) ≫ A.pairMap i i =
      A.inclusion i ≫ SheafCoverCech.diagonal A.cover := by
  apply pullback.hom_ext
  · simp only [Category.assoc, pairMap_first, SheafCoverCech.diagonal_first,
      Category.comp_id]
    rw [← Category.assoc, ← Functor.map_comp, diagonal_left, embedding.map_id,
      Category.id_comp]
  · simp only [Category.assoc, pairMap_second, SheafCoverCech.diagonal_second,
      Category.comp_id]
    rw [← Category.assoc, ← Functor.map_comp, diagonal_right, embedding.map_id,
      Category.id_comp]

end Atlas
end SquareKit.SmoothRepresentedCover
