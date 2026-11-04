import Mathlib.Data.Quot
import Mathlib.Logic.Equiv.Defs
import SquareKit.ObservationExtension

/-! The two-sorted set-model fixture of #287. Sort extensions are specified by
 their defining axioms; canonical recipes discharge them for every old model. -/
namespace SquareKit.RepresentationExtension
universe u v

structure Model where
  A : Type u
  B : Type u
  inhabitedA : Nonempty A
  inhabitedB : Nonempty B
  relation : Setoid A
  predicate : A → Prop

attribute [instance] Model.inhabitedA Model.inhabitedB

structure Hom (M N : Model.{u}) where
  onA : M.A → N.A
  onB : M.B → N.B
  relation : ∀ {a b}, M.relation.r a b → N.relation.r (onA a) (onA b)
  predicate : ∀ {a}, M.predicate a → N.predicate (onA a)

namespace Hom
variable {M N K : Model.{u}}
def id (M : Model.{u}) : Hom M M := ⟨_root_.id, _root_.id, fun h => h, fun h => h⟩
def comp (g : Hom N K) (f : Hom M N) : Hom M K :=
  ⟨g.onA ∘ f.onA, g.onB ∘ f.onB, fun h => g.relation (f.relation h),
    fun h => g.predicate (f.predicate h)⟩
end Hom

structure ProductSort (M : Model.{u}) where
  C : Type u
  fst : C → M.A
  snd : C → M.B
  pair_unique : ∀ a b, ∃! c, fst c = a ∧ snd c = b

namespace ProductSort
variable {M N : Model.{u}}
def canonical (M : Model.{u}) : ProductSort M where
  C := M.A × M.B
  fst := Prod.fst
  snd := Prod.snd
  pair_unique a b := ⟨(a,b), ⟨rfl,rfl⟩, fun _ h => Prod.ext h.1 h.2⟩

instance (S : ProductSort M) : Nonempty S.C := by
  obtain ⟨a⟩ := M.inhabitedA
  obtain ⟨b⟩ := M.inhabitedB
  obtain ⟨c, _⟩ := S.pair_unique a b
  exact ⟨c⟩

theorem coordinates_injective (S : ProductSort M) :
    Function.Injective (fun c => (S.fst c, S.snd c)) := by
  intro c d h
  obtain ⟨z, _, hz⟩ := S.pair_unique (S.fst c) (S.snd c)
  exact (hz c ⟨rfl,rfl⟩).trans (hz d ⟨(congrArg Prod.fst h).symm,
    (congrArg Prod.snd h).symm⟩).symm

noncomputable def comparison (S : ProductSort M) : S.C ≃ M.A × M.B :=
  Equiv.ofBijective (fun c => (S.fst c, S.snd c))
    ⟨S.coordinates_injective, fun ⟨a,b⟩ => by
      obtain ⟨c,h,_⟩ := S.pair_unique a b
      exact ⟨c, Prod.ext h.1 h.2⟩⟩

structure Map (f : Hom M N) (S : ProductSort M) (T : ProductSort N) where
  toFun : S.C → T.C
  fst_comm : ∀ c, T.fst (toFun c) = f.onA (S.fst c)
  snd_comm : ∀ c, T.snd (toFun c) = f.onB (S.snd c)

noncomputable def map (f : Hom M N) (S : ProductSort M) (T : ProductSort N) :
    Map f S T where
  toFun c := T.comparison.symm (f.onA (S.fst c), f.onB (S.snd c))
  fst_comm _ := congrArg Prod.fst (T.comparison.apply_symm_apply _)
  snd_comm _ := congrArg Prod.snd (T.comparison.apply_symm_apply _)

theorem map_unique (f : Hom M N) (S : ProductSort M) (T : ProductSort N)
    (g h : Map f S T) : g.toFun = h.toFun := by
  funext c
  apply T.coordinates_injective
  exact Prod.ext ((g.fst_comm c).trans (h.fst_comm c).symm)
    ((g.snd_comm c).trans (h.snd_comm c).symm)

theorem comparison_natural (f : Hom M N) (S : ProductSort M) (T : ProductSort N)
    (h : Map f S T) (c : S.C) :
    T.comparison (h.toFun c) = Prod.map f.onA f.onB (S.comparison c) :=
  Prod.ext (h.fst_comm c) (h.snd_comm c)

/-- Direct coordinate action agrees with the uniquely determined lifted map. -/
theorem canonical_map (f : Hom M N) (c : M.A × M.B) :
    (map f (canonical M) (canonical N)).toFun c = Prod.map f.onA f.onB c :=
  comparison_natural f (canonical M) (canonical N) (map f _ _) c
end ProductSort

structure QuotientSort (M : Model.{u}) where
  Q : Type u
  q : M.A → Q
  kernel : ∀ a b, q a = q b ↔ M.relation.r a b
  surjective : Function.Surjective q

namespace QuotientSort
variable {M N : Model.{u}}
def canonical (M : Model.{u}) : QuotientSort M where
  Q := Quotient M.relation
  q := Quotient.mk M.relation
  kernel _ _ := ⟨Quotient.exact, Quotient.sound⟩
  surjective := Quotient.mk_surjective

instance (S : QuotientSort M) : Nonempty S.Q := by
  obtain ⟨a⟩ := M.inhabitedA
  exact ⟨S.q a⟩

/-- The quotient eliminator, independent of a choice of representatives. -/
def fromCanonical (S : QuotientSort M) : Quotient M.relation → S.Q :=
  Quotient.lift S.q (fun a b h => (S.kernel a b).mpr h)

noncomputable def comparison (S : QuotientSort M) : S.Q ≃ Quotient M.relation :=
  (Equiv.ofBijective S.fromCanonical ⟨by
    intro x y
    induction x using Quotient.inductionOn with | _ a =>
      induction y using Quotient.inductionOn with | _ b =>
        intro h
        exact Quotient.sound ((S.kernel a b).mp h), by
    intro z
    obtain ⟨a,rfl⟩ := S.surjective z
    exact ⟨Quotient.mk _ a,rfl⟩⟩).symm

@[simp] theorem comparison_q (S : QuotientSort M) (a : M.A) :
    S.comparison (S.q a) = Quotient.mk M.relation a :=
  S.comparison.apply_symm_apply (Quotient.mk _ a)

structure Map (f : Hom M N) (S : QuotientSort M) (T : QuotientSort N) where
  toFun : S.Q → T.Q
  q_comm : ∀ a, toFun (S.q a) = T.q (f.onA a)

noncomputable def map (f : Hom M N) (S : QuotientSort M) (T : QuotientSort N) :
    Map f S T where
  toFun z := Quotient.lift (fun a => T.q (f.onA a))
    (fun a b h => (T.kernel _ _).mpr (f.relation h)) (S.comparison z)
  q_comm a := by simp only [comparison_q, Quotient.lift_mk]

theorem map_unique (f : Hom M N) (S : QuotientSort M) (T : QuotientSort N)
    (g h : Map f S T) : g.toFun = h.toFun := by
  funext z
  obtain ⟨a,rfl⟩ := S.surjective z
  exact (g.q_comm a).trans (h.q_comm a).symm

theorem comparison_natural (f : Hom M N) (S : QuotientSort M) (T : QuotientSort N)
    (h : Map f S T) (z : S.Q) :
    T.comparison (h.toFun z) = Quotient.map f.onA (fun _ _ r => f.relation r)
      (S.comparison z) := by
  obtain ⟨a,rfl⟩ := S.surjective z
  simp only [h.q_comm, comparison_q, Quotient.map_mk]

/-- Exact observers extend to every admitted quotient presentation. -/
noncomputable def observe (S : QuotientSort M) {Y : Type v} (o : M.A → Y)
    (h : ObservationExtension.Compatible M.relation o) : S.Q → Y :=
  ObservationExtension.descend M.relation o h ∘ S.comparison

@[simp] theorem observe_q (S : QuotientSort M) {Y : Type v} (o : M.A → Y)
    (h : ObservationExtension.Compatible M.relation o) (a : M.A) :
    S.observe o h (S.q a) = o a := by
  simp only [observe, Function.comp_apply, comparison_q, ObservationExtension.descend_mk]
end QuotientSort

/-- Stage one retains its entire old model as its reduct. -/
structure ProductModel where
  reduct : Model.{u}
  product : ProductSort reduct

/-- Stage two retains stage one, including its possibly noncanonical product. -/
structure ExtendedModel where
  reduct : ProductModel.{u}
  quotient : QuotientSort reduct.reduct

def expandProduct (M : Model.{u}) : ProductModel := ⟨M, ProductSort.canonical M⟩
def expandQuotient (N : ProductModel.{u}) : ExtendedModel :=
  ⟨N, QuotientSort.canonical N.reduct⟩
def expand (M : Model.{u}) : ExtendedModel := expandQuotient (expandProduct M)

@[simp] theorem reduct_expand (M : Model.{u}) : (expand M).reduct.reduct = M := rfl

structure ExtendedHom (S T : ExtendedModel.{u}) where
  old : Hom S.reduct.reduct T.reduct.reduct
  product : ProductSort.Map old S.reduct.product T.reduct.product
  quotient : QuotientSort.Map old S.quotient T.quotient

structure ProductHom (S T : ProductModel.{u}) where
  old : Hom S.reduct T.reduct
  product : ProductSort.Map old S.product T.product

noncomputable def expandProductHom {M N : Model.{u}} (f : Hom M N) :
    ProductHom (expandProduct M) (expandProduct N) :=
  ⟨f, ProductSort.map f _ _⟩

/-- Quotient expansion preserves a supplied product-stage map as well as its
 entire product presentation. The new map needs only forward R-preservation. -/
noncomputable def expandQuotientHom {S T : ProductModel.{u}} (f : ProductHom S T) :
    ExtendedHom (expandQuotient S) (expandQuotient T) :=
  ⟨f.old, f.product, QuotientSort.map f.old _ _⟩

noncomputable def expandHom {M N : Model.{u}} (f : Hom M N) :
    ExtendedHom (expand M) (expand N) := expandQuotientHom (expandProductHom f)

namespace ExtendedHom
variable {S T U : ExtendedModel.{u}}
def id (S : ExtendedModel.{u}) : ExtendedHom S S where
  old := Hom.id _
  product := ⟨_root_.id, fun _ => rfl, fun _ => rfl⟩
  quotient := ⟨_root_.id, fun _ => rfl⟩

def comp (g : ExtendedHom T U) (f : ExtendedHom S T) : ExtendedHom S U where
  old := g.old.comp f.old
  product := ⟨g.product.toFun ∘ f.product.toFun, fun c => by
    simp only [Function.comp_apply, g.product.fst_comm, f.product.fst_comm, Hom.comp],
    fun c => by
    simp only [Function.comp_apply, g.product.snd_comm, f.product.snd_comm, Hom.comp]⟩
  quotient := ⟨g.quotient.toFun ∘ f.quotient.toFun, fun a => by
    simp only [Function.comp_apply, f.quotient.q_comm, g.quotient.q_comm, Hom.comp]⟩
end ExtendedHom

/-- The certificate contains the defining-sort axioms, not unproved expansion
 or preservation claims. The recipes above build it for every admitted model. -/
noncomputable def liftHom (S T : ExtendedModel.{u})
    (f : Hom S.reduct.reduct T.reduct.reduct) : ExtendedHom S T :=
  ⟨f, ProductSort.map f _ _, QuotientSort.map f _ _⟩

@[ext] theorem ExtendedHom.ext {S T : ExtendedModel.{u}} (f g : ExtendedHom S T)
    (h : f.old = g.old) : f = g := by
  cases f with | mk fo fp fq =>
    cases g with | mk go gp gq =>
      dsimp at h
      cases h
      have hp := ProductSort.map_unique fo _ _ fp gp
      have hq := QuotientSort.map_unique fo _ _ fq gq
      cases fp; cases gp; cases fq; cases gq
      dsimp at hp hq
      cases hp; cases hq
      rfl

theorem liftHom_id (S : ExtendedModel.{u}) : liftHom S S (Hom.id _) = ExtendedHom.id S :=
  ExtendedHom.ext _ _ rfl

theorem liftHom_comp (S T U : ExtendedModel.{u})
    (f : Hom S.reduct.reduct T.reduct.reduct)
    (g : Hom T.reduct.reduct U.reduct.reduct) :
    liftHom S U (g.comp f) = (liftHom T U g).comp (liftHom S T f) :=
  ExtendedHom.ext _ _ rfl

theorem expandHom_id (M : Model.{u}) : expandHom (Hom.id M) = ExtendedHom.id (expand M) :=
  ExtendedHom.ext _ _ rfl

theorem expandHom_comp {M N K : Model.{u}} (f : Hom M N) (g : Hom N K) :
    expandHom (g.comp f) = (expandHom g).comp (expandHom f) :=
  ExtendedHom.ext _ _ rfl

/-- Comparison fixes both old carriers, and is bijective on both new sorts. -/
noncomputable def comparison (S : ExtendedModel.{u}) :
    ExtendedHom S (expand S.reduct.reduct) := liftHom _ _ (Hom.id _)

theorem comparison_bijective (S : ExtendedModel.{u}) :
    Function.Bijective (comparison S).product.toFun ∧
    Function.Bijective (comparison S).quotient.toFun := by
  have hp : (comparison S).product.toFun = S.reduct.product.comparison := by
    funext c
    exact ProductSort.comparison_natural (Hom.id _) _ _ (comparison S).product c
  have hq : (comparison S).quotient.toFun = S.quotient.comparison := by
    funext z
    obtain ⟨a,rfl⟩ := S.quotient.surjective z
    rw [(comparison S).quotient.q_comm, QuotientSort.comparison_q]
    rfl
  exact ⟨hp ▸ S.reduct.product.comparison.bijective,
    hq ▸ S.quotient.comparison.bijective⟩

theorem comparison_natural {S T : ExtendedModel.{u}} (f : ExtendedHom S T) :
    (comparison T).comp f =
      (liftHom (expand S.reduct.reduct) (expand T.reduct.reduct) f.old).comp
        (comparison S) := ExtendedHom.ext _ _ rfl

/-- The inverse comparison is also the unique lift of the old identity. -/
noncomputable def comparisonInverse (S : ExtendedModel.{u}) :
    ExtendedHom (expand S.reduct.reduct) S := liftHom _ _ (Hom.id _)

theorem comparison_inverse_left (S : ExtendedModel.{u}) :
    (comparisonInverse S).comp (comparison S) = ExtendedHom.id S :=
  ExtendedHom.ext _ _ rfl

theorem comparison_inverse_right (S : ExtendedModel.{u}) :
    (comparison S).comp (comparisonInverse S) = ExtendedHom.id (expand S.reduct.reduct) :=
  ExtendedHom.ext _ _ rfl

end SquareKit.RepresentationExtension
