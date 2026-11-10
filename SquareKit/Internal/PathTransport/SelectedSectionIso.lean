import SquareKit.Internal.PathTransport.SelectedLiftIso
import Mathlib.CategoryTheory.EqToHom

/-! Coherence of the selected isomorphism between strict sections of a fully
faithful projection. -/
noncomputable section
namespace SquareKit.Internal.PathTransport
open CategoryTheory CategoryTheory.Functor
universe u v
variable {A B A' B' : Type u} [Category.{v} A] [Category.{v} B]
  [Category.{v} A'] [Category.{v} B']

/-- The unique isomorphism above the identity, with endpoint transports. -/
def selectedSectionIso (P : B ⥤ A) [P.Full] [P.Faithful]
    (I J : A ⥤ B) (hI : I ⋙ P = 𝟭 A) (hJ : J ⋙ P = 𝟭 A) : I ≅ J :=
  fullyFaithfulCancelRight P (eqToIso hI ≪≫ (eqToIso hJ).symm)

@[simp] theorem selectedSectionIso_map (P : B ⥤ A) [P.Full] [P.Faithful]
    (I J : A ⥤ B) (hI : I ⋙ P = 𝟭 A) (hJ : J ⋙ P = 𝟭 A) (x : A) :
    P.map ((selectedSectionIso P I J hI hJ).hom.app x) =
      eqToHom (congrArg (fun K => K.obj x) hI) ≫
      eqToHom (congrArg (fun K => K.obj x) hJ.symm) := by
  simp [selectedSectionIso]

theorem selectedSectionIso_square (P : B ⥤ A) [P.Full] [P.Faithful]
    (Q : B' ⥤ A') [Q.Full] [Q.Faithful]
    (I J : A ⥤ B) (I' J' : A' ⥤ B')
    (hI : I ⋙ P = 𝟭 A) (hJ : J ⋙ P = 𝟭 A)
    (hI' : I' ⋙ Q = 𝟭 A') (hJ' : J' ⋙ Q = 𝟭 A')
    (s : A' ⥤ A) (t : B' ⥤ B) (ht : t ⋙ P = Q ⋙ s)
    (hi : s ⋙ I = I' ⋙ t) (hj : s ⋙ J = J' ⋙ t) :
    isoWhiskerLeft s (selectedSectionIso P I J hI hJ) ≪≫ eqToIso hj =
      eqToIso hi ≪≫ isoWhiskerRight (selectedSectionIso Q I' J' hI' hJ') t := by
  ext x
  apply P.map_injective
  have hn := (eqToHom ht).naturality ((selectedSectionIso Q I' J' hI' hJ').hom.app x)
  simp only [Functor.comp_map] at hn
  have hh := congrArg (fun k => k ≫ eqToHom
    (congrArg (fun K => K.obj (J'.obj x)) ht.symm)) hn
  simp only [Category.assoc, eqToHom_app, eqToHom_trans, eqToHom_refl,
    Category.comp_id] at hh
  simp only [Iso.trans_hom, NatTrans.comp_app, isoWhiskerLeft_hom, isoWhiskerRight_hom,
    whiskerLeft_app, whiskerRight_app, eqToIso.hom, Functor.map_comp]
  rw [hh]
  simp [selectedSectionIso_map, eqToHom_map]

/-- Postcomposition transports a selected square across a strictly commuting
square of target functors. All endpoint identifications are explicit. -/
theorem isoSquare_postcompose {E E' : Type u} [Category.{v} E] [Category.{v} E']
    {I J : A ⥤ B} {I' J' : A' ⥤ B'}
    (s : A' ⥤ A) (t : B' ⥤ B) (r : E' ⥤ E)
    (K : B ⥤ E) (K' : B' ⥤ E') (ht : t ⋙ K = K' ⋙ r)
    (hi : s ⋙ I = I' ⋙ t) (hj : s ⋙ J = J' ⋙ t)
    (e : I ≅ J) (e' : I' ≅ J')
    (h : isoWhiskerLeft s e ≪≫ eqToIso hj = eqToIso hi ≪≫ isoWhiskerRight e' t)
    (hiK : s ⋙ (I ⋙ K) = (I' ⋙ K') ⋙ r)
    (hjK : s ⋙ (J ⋙ K) = (J' ⋙ K') ⋙ r) :
    isoWhiskerLeft s (isoWhiskerRight e K) ≪≫ eqToIso hjK =
      eqToIso hiK ≪≫ isoWhiskerRight (isoWhiskerRight e' K') r := by
  ext x
  have hh := congrArg (fun z => K.map (z.hom.app x)) h
  simp only [Iso.trans_hom, NatTrans.comp_app, isoWhiskerLeft_hom, isoWhiskerRight_hom,
    whiskerLeft_app, whiskerRight_app, eqToIso.hom, Functor.map_comp, eqToHom_app,
    eqToHom_map] at hh ⊢
  have hn := (eqToHom ht).naturality (e'.hom.app x)
  simp only [Functor.comp_map, eqToHom_app] at hn
  have hn' := congrArg (fun k => k ≫ eqToHom
    (congrArg (fun T => T.obj (J'.obj x)) ht.symm)) hn
  simp only [Category.assoc, eqToHom_trans, eqToHom_refl, Category.comp_id] at hn'
  rw [hn'] at hh
  have hfinal := congrArg (fun k => k ≫ eqToHom
    (show K.obj ((J' ⋙ t).obj x) = ((J' ⋙ K') ⋙ r).obj x from
      congrArg (fun T => T.obj (J'.obj x)) ht)) hh
  simpa [Category.assoc] using hfinal

theorem isoSquare_relabel {I J L R : A ⥤ B} {I' J' L' R' : A' ⥤ B'}
    (s : A' ⥤ A) (t : B' ⥤ B)
    (e : I ≅ J) (e' : I' ≅ J')
    (hI : I = L) (hJ : J = R) (hI' : I' = L') (hJ' : J' = R')
    (hi : s ⋙ I = I' ⋙ t) (hj : s ⋙ J = J' ⋙ t)
    (hl : s ⋙ L = L' ⋙ t) (hr : s ⋙ R = R' ⋙ t)
    (h : isoWhiskerLeft s e ≪≫ eqToIso hj = eqToIso hi ≪≫ isoWhiskerRight e' t) :
    isoWhiskerLeft s ((eqToIso hI).symm ≪≫ e ≪≫ eqToIso hJ) ≪≫ eqToIso hr =
      eqToIso hl ≪≫ isoWhiskerRight ((eqToIso hI').symm ≪≫ e' ≪≫ eqToIso hJ') t := by
  cases hI; cases hJ; cases hI'; cases hJ'
  simpa using h

end SquareKit.Internal.PathTransport
