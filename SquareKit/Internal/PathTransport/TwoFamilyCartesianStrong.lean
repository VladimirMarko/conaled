import SquareKit.Internal.PathTransport.TwoFamilyCoherentLift
import SquareKit.Internal.PathTransport.TwoStrongData
namespace SquareKit.Internal.PathTransport.TwoFamily
open CategoryTheory Bicategory
universe u v w uE vE wE
variable {Γ : Type u} [Bicategory.{w,v} Γ] [Strict Γ]
variable (E : Family.{u,v,w,uE,vE,wE} Γ)
private theorem boundary_heq {C : Type*} [Category C] {a b c d : C}
    (h : a = c) (e : a = b) (e' : c = d) : HEq (eqToHom e) (eqToHom e') := by
  cases e; cases h; cases e'; rfl

def EqualityHomFiber {x y : Total E} (p : x ⟶ y) : Prop :=
  ∃ e : (E.map p.base).obj x.fiber = y.fiber, p.fiber = eqToHom e

theorem equalityHomFiber_ext {x y : Total E} {p q : x ⟶ y}
    (hb : p.base = q.base) (hp : EqualityHomFiber E p) (hq : EqualityHomFiber E q) : p = q := by
  obtain ⟨ep,hp⟩ := hp
  obtain ⟨eq,hq⟩ := hq
  apply Pseudofunctor.CoGrothendieck.ext hb
  rw [hp,hq]
  exact boundary_heq (congrArg (fun f => (E.map f).obj x.fiber) hb) ep eq

theorem equalityHomFiber_hext {x y x' y' : Total E} (hx : x = x') (hy : y = y')
    {p : x ⟶ y} {q : x' ⟶ y'} (hb : HEq p.base q.base)
    (hp : EqualityHomFiber E p) (hq : EqualityHomFiber E q) : HEq p q := by
  cases hx; cases hy
  exact heq_of_eq (equalityHomFiber_ext E (eq_of_heq hb) hp hq)

theorem equalityFiber_hext {x y x' y' : Total E} (hx : x = x') (hy : y = y')
    {p q : x ⟶ y} {p' q' : x' ⟶ y'} (hp : HEq p p') (hq : HEq q q')
    {α : p ⟶ q} {β : p' ⟶ q'} (hb : HEq α.base β.base)
    (hα : EqualityFiber E α) (hβ : EqualityFiber E β) : HEq α β := by
  cases hx; cases hy
  cases eq_of_heq hp; cases eq_of_heq hq
  exact heq_of_eq (equalityFiber_ext E (eq_of_heq hb) hα hβ)

variable {A : Type*} [Bicategory A]
theorem cartesianStrong_hext {F G F' G' : StrictPseudofunctor A (Total E)}
    (eF : F = F') (eG : G = G')
    (η : Pseudofunctor.StrongTrans F.toPseudofunctor G.toPseudofunctor)
    (θ : Pseudofunctor.StrongTrans F'.toPseudofunctor G'.toPseudofunctor)
    (hab : ∀x, HEq (η.app x).base (θ.app x).base)
    (haf : ∀x, EqualityHomFiber E (η.app x))
    (hbf : ∀x, EqualityHomFiber E (θ.app x))
    (hnb : ∀{x y} (p : x ⟶ y), HEq ((η.naturality p).hom).base ((θ.naturality p).hom).base)
    (hnf : ∀{x y} (p : x ⟶ y), EqualityFiber E (η.naturality p).hom)
    (hmf : ∀{x y} (p : x ⟶ y), EqualityFiber E (θ.naturality p).hom) : HEq η θ := by
  cases eF; cases eG
  have ha (x : A) : η.app x = θ.app x := equalityHomFiber_ext E (eq_of_heq (hab x)) (haf x) (hbf x)
  apply heq_of_eq
  apply strongTrans_ext _ _ ha
  intro x y p
  exact equalityFiber_hext E rfl rfl
    (heq_of_eq (congrArg (fun a => F.map p ≫ a) (ha y)))
    (heq_of_eq (congrArg (fun a => a ≫ G.map p) (ha x))) (hnb p) (hnf p) (hmf p)
theorem equalityHomFiber_identity (x : Total E) : EqualityHomFiber E (𝟙 x) :=
  ⟨congrArg (fun K => K.obj x.fiber) (E.map_id x.base), rfl⟩
theorem equalityHomFiber_cartesian {x y : Γ} (f : x ⟶ y) (a : E.obj x) :
    EqualityHomFiber E (cartesianLift E f a) := ⟨rfl, rfl⟩

theorem identityStrong_equalityFiber (H : StrictPseudofunctor A (Total E))
    {x y : A} (p : x ⟶ y) :
    EqualityFiber E ((Pseudofunctor.StrongTrans.id H.toPseudofunctor).naturality p).hom := by
  simp only [Pseudofunctor.StrongTrans.id, Iso.trans_hom, Iso.symm_hom,
    Strict.rightUnitor_eqToIso, Strict.leftUnitor_eqToIso, eqToIso.hom, eqToIso.inv]
  exact equalityFiber_comp E (equalityFiber_cast E _) (equalityFiber_cast E _)

variable [Strict A] (i : StrictPseudofunctor A Γ)
theorem identityReindex_comparison_base {x y : Total (reindex i E)} (p : x ⟶ y) :
    HEq (((Pseudofunctor.StrongTrans.id (reindexHigher E i).toPseudofunctor).naturality p).hom).base
      ((Pseudofunctor.StrongTrans.id i.toPseudofunctor).naturality p.base).hom := by
  simp only [Pseudofunctor.StrongTrans.id, Iso.trans_hom, Iso.symm_hom,
    Strict.rightUnitor_eqToIso, Strict.leftUnitor_eqToIso, eqToIso.hom, eqToIso.inv]
  simp only [eqToHom_trans]
  erw [total_eqToHom_base E]
  rfl

end SquareKit.Internal.PathTransport.TwoFamily
