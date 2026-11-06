import SquareKit.Internal.PathTransport.TwoStrongTransport
namespace SquareKit.Internal.PathTransport
open CategoryTheory Bicategory
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option backward.defeqAttrib.useBackward true
set_option maxHeartbeats 200000
universe u v w uB vB wB uC vC wC
variable {A : Type u} [Bicategory.{w,v} A] [Strict A]
variable {B : Type uB} [Bicategory.{wB,vB} B] [Strict B]
variable {C : Type uC} [Bicategory.{wC,vC} C] [Strict C]
variable {F G : StrictPseudofunctor A B} (H : StrictPseudofunctor B C)
variable (a : ∀x, F.obj x ⟶ G.obj x)
variable (n : ∀ {x y} (p : x ⟶ y), F.map p ≫ a y ≅ a x ≫ G.map p)
def mappedStrongNaturality {x y} (p : x ⟶ y) :
    (F.comp H).map p ≫ H.map (a y) ≅ H.map (a x) ≫ (G.comp H).map p :=
  (H.mapComp (F.map p) (a y)).symm ≪≫ H.map₂Iso (n p) ≪≫ H.mapComp (a x) (G.map p)

def strongReflect (hc : ∀{x y : B} {p q : x ⟶ y}, Function.Injective (H.map₂ (f := p) (g := q)))
    (θ : Pseudofunctor.StrongTrans (F.comp H).toPseudofunctor (G.comp H).toPseudofunctor)
    (ha : (fun x => H.map (a x)) = θ.app)
    (hn : ∀ {x y : A} (p : x ⟶ y), HEq (mappedStrongNaturality H a n p).hom (θ.naturality p).hom) :
    Pseudofunctor.StrongTrans F.toPseudofunctor G.toPseudofunctor := by
  rcases θ with ⟨θa, θn, θh, θi, θc⟩
  dsimp only at ha hn
  cases ha
  have hnat : (fun {x y : A} (p : x ⟶ y) => mappedStrongNaturality H a n p) = @θn := by
    funext x y p
    apply Iso.ext
    exact eq_of_heq (hn p)
  cases hnat
  refine { app := a, naturality := n, naturality_naturality := ?_, naturality_id := ?_, naturality_comp := ?_ }
  · intro x y f g α
    apply hc
    have k := congrArg (fun z => eqToHom (H.map_comp (F.map f) (a y)) ≫ z ≫
      eqToHom (H.map_comp (a x) (G.map g)).symm) (θh α)
    simp only [mappedStrongNaturality, Iso.trans_hom, Iso.symm_hom, Functor.mapIso_hom,
      PrelaxFunctor.map₂_comp, Pseudofunctor.map₂_whisker_left, Pseudofunctor.map₂_whisker_right,
      H.mapComp_eq_eqToIso, eqToIso.hom, eqToIso.inv, Category.assoc,
      eqToHom_trans_assoc, eqToHom_trans, eqToHom_refl, Category.id_comp, Category.comp_id] at k ⊢
    convert k using 1 <;> rfl
  · intro x
    apply hc
    have e : H.map (a x ≫ 𝟙 (G.obj x)) = H.map (a x) ≫ 𝟙 (H.obj (G.obj x)) := by simp
    have k := congrArg (fun z => eqToHom (H.map_comp (F.map (𝟙 x)) (a x)) ≫ z ≫ eqToHom e.symm) (θi x)
    simp only [mappedStrongNaturality, PrelaxFunctor.map₂_comp, F.mapId_eq_eqToIso, G.mapId_eq_eqToIso,
      H.mapComp_eq_eqToIso, (F.comp H).mapId_eq_eqToIso, (G.comp H).mapId_eq_eqToIso,
      Iso.trans_hom, Iso.symm_hom, Functor.mapIso_hom, eqToIso.hom, eqToIso.inv,
      Strict.leftUnitor_eqToIso, Strict.rightUnitor_eqToIso,
      whiskerLeft_eqToHom, eqToHom_whiskerRight,
      PrelaxFunctor.map₂_eqToHom, Category.assoc, eqToHom_trans_assoc,
      eqToHom_trans, eqToHom_refl, Category.id_comp, Category.comp_id] at k ⊢
    convert k using 1 <;> rfl
  · intro x y z f g
    apply hc
    have e : H.map (a x ≫ (G.map f ≫ G.map g)) =
        H.map (a x) ≫ (H.map (G.map f) ≫ H.map (G.map g)) := by rw [H.map_comp, H.map_comp]
    have k := congrArg (fun cell => eqToHom (H.map_comp (F.map (f ≫ g)) (a z)) ≫ cell ≫ eqToHom e.symm) (θc f g)
    simp only [mappedStrongNaturality, PrelaxFunctor.map₂_comp, F.mapComp_eq_eqToIso, G.mapComp_eq_eqToIso,
      H.mapComp_eq_eqToIso, (F.comp H).mapComp_eq_eqToIso, (G.comp H).mapComp_eq_eqToIso,
      Iso.trans_hom, Iso.symm_hom, Functor.mapIso_hom, eqToIso.hom, eqToIso.inv,
      Strict.associator_eqToIso, whiskerLeft_eqToHom, eqToHom_whiskerRight,
      Pseudofunctor.map₂_whisker_left, Pseudofunctor.map₂_whisker_right,
      whiskerLeft_comp, comp_whiskerRight,
      PrelaxFunctor.map₂_eqToHom, Category.assoc, eqToHom_trans_assoc,
      eqToHom_trans, eqToHom_refl, Category.id_comp, Category.comp_id] at k ⊢
    convert k using 1 <;> rfl

variable (hc : ∀{x y : B} {p q : x ⟶ y}, Function.Injective (H.map₂ (f := p) (g := q)))
variable (θ : Pseudofunctor.StrongTrans (F.comp H).toPseudofunctor (G.comp H).toPseudofunctor)
variable (ha : (fun x => H.map (a x)) = θ.app)
variable (hn : ∀ {x y : A} (p : x ⟶ y), HEq (mappedStrongNaturality H a n p).hom (θ.naturality p).hom)
theorem strongReflect_app : (strongReflect H a n (@hc) θ ha hn).app = a := by
  rcases θ with ⟨θa, θn, θh, θi, θc⟩
  dsimp only at ha hn
  cases ha
  have hnat : (fun {x y : A} (p : x ⟶ y) => mappedStrongNaturality H a n p) = @θn := by
    funext x y p
    apply Iso.ext
    exact eq_of_heq (hn p)
  cases hnat
  rfl

theorem strongReflect_naturality : HEq (@(strongReflect H a n (@hc) θ ha hn).naturality) (@n) := by
  rcases θ with ⟨θa, θn, θh, θi, θc⟩
  dsimp only at ha hn
  cases ha
  have hnat : (fun {x y : A} (p : x ⟶ y) => mappedStrongNaturality H a n p) = @θn := by
    funext x y p
    apply Iso.ext
    exact eq_of_heq (hn p)
  cases hnat
  rfl

theorem strongReflect_postcomp : strongPostcomp (strongReflect H a n (@hc) θ ha hn) H = θ := by
  rcases θ with ⟨θa, θn, θh, θi, θc⟩
  dsimp only at ha hn
  cases ha
  have hnat : (fun {x y : A} (p : x ⟶ y) => mappedStrongNaturality H a n p) = @θn := by
    funext x y p
    apply Iso.ext
    exact eq_of_heq (hn p)
  cases hnat
  rfl
end SquareKit.Internal.PathTransport
