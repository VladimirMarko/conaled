import SquareKit.SheafGroupoidBibundleStack
import SquareKit.StackDescentTransformationComposition

/-! Tensoring principal bundles as a strong transformation of stacks. -/
noncomputable section
set_option autoImplicit false
set_option warningAsError true
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
namespace SquareKit.SheafGroupoid.Bibundle
open CategoryTheory Opposite SquareKit SquareKit.SheafGroupoid
open SquareKit.SheafGroupoid.Bundle
open SquareKit.SheafGroupoid.Bundle SquareKit.SheafGroupoid.Bibundle SquareKit.SheafGroupoid.Bundle.BalancedFactorization
open SquareKit.SheafGroupoid.Bundle.BalancedAction SquareKit.SheafGroupoid.Bundle.BalancedProduct SquareKit.SheafGroupoid.Bibundle
open scoped CategoryTheory.Pseudofunctor.StrongTrans
universe u v
variable {C : Type u} [Category.{v} C] {J : GrothendieckTopology C}
variable {G H : Operations J} [G.Laws] [H.Laws]
variable (P : Bibundle G H) {X Y Z : Sheaf J (Type (max u v))}

theorem tensor_bundle_map_ext (T : Principal G X) {R : Principal H X}
    (a b : Bundle.Map (compositionRightBundle T P.right P.left) R)
    (h : ∀ (x : X.obj.Elements) (m : G.Section x.obj)
      (t : Fiber G X T.family x m) (k : H.Section x.obj)
      (p : Fiber H G.objects P.right.family (atSection m) k),
      a.hom.app (point H X x k) (tensorPoint T P.right P.left x m t k p) =
      b.hom.app (point H X x k) (tensorPoint T P.right P.left x m t k p)) : a = b := by
  apply Bundle.Map.ext
  apply SplitSheaf.totalMap_injective
  apply (cancel_epi (balancedMap T P.right P.left)).mp
  apply Sheaf.hom_ext
  ext U z
  rcases z with ⟨⟨⟨x,m⟩,t⟩,⟨⟨⟨m',k⟩,p⟩,e⟩⟩
  change m' = m at e
  subst m'
  exact congrArg (Sigma.mk (x,k)) (h (X.obj.elementsMk U x) ⟨m⟩ t ⟨k⟩ p)

def tensorComponent : Principal G X ⥤ Principal H X where
  obj T := compositionRightBundle T P.right P.left
  map f := tensorMap P.right P.left f
  map_id T := by
    apply tensor_bundle_map_ext
    intro x m t k p
    exact tensorMapFamily_tensorPoint P.right P.left (Bundle.Map.ident T) x m t k p
  map_comp f g := by
    apply tensor_bundle_map_ext
    intro x m t k p
    change (tensorMap P.right P.left (f.comp g)).hom.app _ _ =
      (tensorMap P.right P.left g).hom.app _ ((tensorMap P.right P.left f).hom.app _ _)
    simp only [tensorMap, tensorMapFamily_tensorPoint]
    rfl

def tensorBaseChange (r : Y ⟶ X) :
    Bundle.restriction r ⋙ tensorComponent P ≅ tensorComponent P ⋙ Bundle.restriction r :=
  NatIso.ofComponents (fun T => baseChangeIso T P.right P.left r) (by
    intro T R f
    apply tensor_bundle_map_ext
    intro y m t k p
    change (baseChangeFamily R P.right P.left r).app _
      ((tensorMapFamily P.right P.left (f.reindex r)).app _ _) =
        (tensorMapFamily P.right P.left f).app _ ((baseChangeFamily T P.right P.left r).app _ _)
    have ht := tensorMapFamily_tensorPoint P.right P.left (f.reindex r) y m t k p
    have hb := baseChangeFamily_tensorPoint R P.right P.left r y m
      ((f.reindex r).hom.app (point G Y y m) t) k p
    have hc := baseChangeFamily_tensorPoint T P.right P.left r y m t k p
    have hm := tensorMapFamily_tensorPoint P.right P.left f (r.hom.mapElements.obj y) m t k p
    exact (congrArg ((baseChangeFamily R P.right P.left r).app (point H Y y k)) ht).trans
      (hb.trans ((congrArg ((tensorMapFamily P.right P.left f).app
        (point H X (r.hom.mapElements.obj y) k)) hc).trans hm).symm))

theorem tensorBaseChange_comp (T : Principal G X) (r : Y ⟶ X) (s : Z ⟶ Y) :
    baseChangeMap T P.right P.left (s ≫ r) =
      (baseChangeMap (Bundle.reindex T r) P.right P.left s).comp
        ((baseChangeMap T P.right P.left r).reindex s) := by
  apply tensor_bundle_map_ext P (Bundle.reindex T (s ≫ r))
  intro x m t k p
  have h₁ := baseChangeFamily_tensorPoint (Bundle.reindex T r) P.right P.left s x m t k p
  have h₂ := baseChangeFamily_tensorPoint T P.right P.left r (s.hom.mapElements.obj x) m t k p
  have h₃ := baseChangeFamily_tensorPoint T P.right P.left (s ≫ r) x m t k p
  exact h₃.trans ((congrArg ((baseChangeFamily T P.right P.left r).app
    (point H Y (s.hom.mapElements.obj x) k)) h₁).trans h₂).symm

def tensorTransformation : Bundle.pseudofunctor G ⟶ Bundle.pseudofunctor H where
  app X := (tensorComponent P (X := X.as.unop)).toCatHom
  naturality r := Cat.Hom.isoMk (tensorBaseChange P r.as.unop)
  naturality_naturality := by
    intro X Y f g h
    obtain rfl := LocallyDiscrete.eq_of_hom h
    have hh : h = 𝟙 f := Subsingleton.elim _ _
    subst h
    simp only [PrelaxFunctor.map₂_id]
    apply Cat.Hom₂.ext
    ext T
    simp
  naturality_id X := by
    cases X
    apply Cat.Hom₂.ext
    apply NatTrans.ext
    funext T
    apply tensor_bundle_map_ext P T
    intro x m t k p
    change (baseChangeFamily T P.right P.left (𝟙 _)).app _ _ =
      (tensorMapFamily P.right P.left (Bundle.Map.ident T)).app _ _
    exact (baseChangeFamily_tensorPoint T P.right P.left (𝟙 _) x m t k p).trans
      (tensorMapFamily_tensorPoint P.right P.left (Bundle.Map.ident T) x m t k p).symm
  naturality_comp f g := by
    apply Cat.Hom₂.ext
    apply NatTrans.ext
    funext T
    let A := Bundle.reindex T (g.as.unop ≫ f.as.unop)
    let b := (baseChangeMap (Bundle.reindex T f.as.unop) P.right P.left g.as.unop).comp
      ((baseChangeMap T P.right P.left f.as.unop).reindex g.as.unop)
    have hid := (tensorComponent P).map_id A
    change tensorMap P.right P.left (Bundle.Map.ident A) = Bundle.Map.ident _ at hid
    exact (tensorBaseChange_comp P T f.as.unop g.as.unop).trans
      (congrArg (fun a : Bundle.Map (compositionRightBundle A P.right P.left)
        (compositionRightBundle A P.right P.left) => a.comp b) hid.symm)


end SquareKit.SheafGroupoid.Bibundle
