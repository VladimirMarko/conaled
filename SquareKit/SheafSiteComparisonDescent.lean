import SquareKit.SheafSiteComparisonQuotient
import SquareKit.SheafFamilyDescent

/-! Site comparison commutes with full covering descent and recovery. -/
noncomputable section
set_option autoImplicit false
set_option warningAsError true
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
namespace SquareKit.SheafSiteComparison
open CategoryTheory Opposite
universe u
section
variable {A₀ A₁ B₀ B₁ C₀ C₁ D₀ D₁ : Type*}
  [Category A₀] [Category A₁] [Category B₀] [Category B₁]
  [Category C₀] [Category C₁] [Category D₀] [Category D₁]

/-- Compose recovery, parameter restriction and canonical descent comparison squares. -/
private def recoveryRestrictionSquare
    (R₀ : B₀ ⥤ A₀) (R₁ : B₁ ⥤ A₁) (H₀ : A₀ ⥤ C₀) (H₁ : A₁ ⥤ C₁)
    (T₀ : C₀ ⥤ D₀) (T₁ : C₁ ⥤ D₁)
    (P : B₀ ⥤ B₁) (p : A₀ ⥤ A₁) (q : C₀ ⥤ C₁) (Q : D₀ ⥤ D₁)
    (hR : P ⋙ R₁ ≅ R₀ ⋙ p) (hH : p ⋙ H₁ ≅ H₀ ⋙ q)
    (hT : T₀ ⋙ Q ≅ q ⋙ T₁) :
    P ⋙ (R₁ ⋙ (H₁ ⋙ T₁)) ≅ (R₀ ⋙ (H₀ ⋙ T₀)) ⋙ Q :=
  (Functor.associator _ _ _).symm ≪≫
    Functor.isoWhiskerRight hR _ ≪≫
    Functor.associator _ _ _ ≪≫
    Functor.isoWhiskerLeft _ ((Functor.associator _ _ _).symm ≪≫
      Functor.isoWhiskerRight hH _ ≪≫
      Functor.associator _ _ _ ≪≫
      Functor.isoWhiskerLeft _ hT.symm ≪≫
      (Functor.associator _ _ _).symm) ≪≫
    (Functor.associator _ _ _).symm
end

variable {C D : Type u} [Category.{u} C] [Category.{u} D]
variable (J : GrothendieckTopology C) (K : GrothendieckTopology D) (F : C ⥤ D)
variable [F.Full] [F.Faithful] [F.IsDenseSubsite J K]
variable (G : Sheaf K GrpCat.{u}) {M X : Sheaf K (Type u)}
variable {I : Type u} {Y : I → Sheaf K (Type u)}
variable (f : ∀ i, Y i ⟶ X) (hf : SheafFamilyCover.JointlyLocallySurjective f)

omit [F.Full] [F.Faithful] [F.IsDenseSubsite J K] in
private theorem torsorCanonicalTransition (P : SheafTorsor.Torsor G X)
    {W : Sheaf K (Type u)} (q : W ⟶ X) {i j : I} (l : W ⟶ Y i) (r : W ⟶ Y j)
    (hl : l ≫ f i = q) (hr : r ≫ f j = q) :
    (((SheafTorsor.Stack.pseudofunctor G).toDescentData f).obj P).hom q l r hl hr =
      eqToHom (show SheafTorsor.reindex (SheafTorsor.reindex P (f i)) l =
        SheafTorsor.reindex (SheafTorsor.reindex P (f j)) r from
          congrArg (SheafTorsor.reindex P) (hl.trans hr.symm)) := by
  simp [Pseudofunctor.toDescentData, Pseudofunctor.DescentData.ofObj,
    Pseudofunctor.mapComp', SheafTorsor.Stack.pseudofunctor, Functor.toPseudofunctor',
    pseudofunctorOfIsLocallyDiscrete]
  exact Category.id_comp _

omit [F.Full] [F.Faithful] in
private theorem torsorCanonicalTransition_map (P : SheafTorsor.Torsor G X)
    {W : Sheaf K (Type u)} (q : W ⟶ X) {i j : I} (l : W ⟶ Y i) (r : W ⟶ Y j)
    (hl : l ≫ f i = q) (hr : r ≫ f j = q) :
    (torsorFunctor J K F).map
        ((((SheafTorsor.Stack.pseudofunctor G).toDescentData f).obj P).hom q l r hl hr) =
      (((SheafTorsor.Stack.pseudofunctor (group J K F G)).toDescentData
        (fun i => map J K F (f i))).obj (torsor J K F P)).hom
        (map J K F q) (map J K F l) (map J K F r)
        (congrArg (map J K F) hl) (congrArg (map J K F) hr) := by
  rw [torsorCanonicalTransition, torsorCanonicalTransition, eqToHom_map]

/-- Compare all descent objects and all compatible arrows using effective recovery.
The local comparison below identifies this with componentwise site restriction. -/
def torsorDescentEquivalence :
    (SheafTorsor.Stack.pseudofunctor G).DescentData f ≌
      (SheafTorsor.Stack.pseudofunctor (group J K F G)).DescentData (fun i => map J K F (f i)) :=
  (SheafFamilyDescent.torsorEquivalence G f hf).symm.trans
    ((torsorEquivalence J K F).trans
      (SheafFamilyDescent.torsorEquivalence (group J K F G) _ (joint_cover J K F f hf)))

/-- The square of canonical descent functors commutes as a natural isomorphism. -/
def torsorDescentSquare :
    (SheafTorsor.Stack.pseudofunctor G).toDescentData f ⋙
      (torsorDescentEquivalence J K F G f hf).functor ≅
    torsorFunctor J K F ⋙
      (SheafTorsor.Stack.pseudofunctor (group J K F G)).toDescentData
        (fun i => map J K F (f i)) :=
  (Functor.associator _ _ _).symm ≪≫
    Functor.isoWhiskerRight (SheafFamilyDescent.torsorEquivalence G f hf).unitIso.symm _ ≪≫
      Functor.leftUnitor _

/-- Recovering changed-site descent data agrees with changing the recovered torsor's site. -/
def torsorDescentRecovery :
    (torsorDescentEquivalence J K F G f hf).functor ⋙
      (SheafFamilyDescent.torsorEquivalence (group J K F G) _ (joint_cover J K F f hf)).inverse ≅
    (SheafFamilyDescent.torsorEquivalence G f hf).inverse ⋙ torsorFunctor J K F :=
  Functor.isoWhiskerRight (Functor.associator _ _ _).symm _ ≪≫
    Functor.associator _ _ _ ≪≫
      Functor.isoWhiskerLeft _
        (SheafFamilyDescent.torsorEquivalence (group J K F G) _ (joint_cover J K F f hf)).unitIso.symm ≪≫
          Functor.rightUnitor _

/-- Each local object is the actual restricted original object, up to the recovery component. -/
def torsorDescentLocalComparison
    (d : (SheafTorsor.Stack.pseudofunctor G).DescentData f) (i : I) :
    ((torsorDescentEquivalence J K F G f hf).functor.obj d).obj i ≅
      (torsorFunctor J K F).obj (d.obj i) :=
  (torsorFunctor J K F).mapIso (SheafTorsor.Arrow.toIso
    (((SheafFamilyDescent.torsorEquivalence G f hf).counitIso.app d).hom.hom i))

theorem torsorDescentLocalComparison_natural
    {d e : (SheafTorsor.Stack.pseudofunctor G).DescentData f} (h : d ⟶ e) (i : I) :
    ((torsorDescentEquivalence J K F G f hf).functor.map h).hom i ≫
      (torsorDescentLocalComparison J K F G f hf e i).hom =
    (torsorDescentLocalComparison J K F G f hf d i).hom ≫
      (torsorFunctor J K F).map (h.hom i) := by
  have hh := congrArg (fun k => k.hom i)
    ((SheafFamilyDescent.torsorEquivalence G f hf).counitIso.hom.naturality h)
  apply SheafTorsor.Arrow.ext
  ext x p
  exact congrArg (fun k => k.iso.hom.app ((elements K F (Y i)).obj x) p) hh

omit [F.Full] [F.Faithful] in
private theorem torsorLocalTransition
    (P : SheafTorsor.Torsor G X)
    (d : (SheafTorsor.Stack.pseudofunctor G).DescentData f)
    (t : ((SheafTorsor.Stack.pseudofunctor G).toDescentData f).obj P ⟶ d)
    {W : Sheaf K (Type u)} (q : W ⟶ X) {i j : I}
    (l : W ⟶ Y i) (r : W ⟶ Y j) (hl : l ≫ f i = q) (hr : r ≫ f j = q) :
    (SheafTorsor.restriction (map J K F l)).map
        ((torsorFunctor J K F).map (t.hom i)) ≫
      (torsorFunctor J K F).map (d.hom q l r hl hr) =
    (((SheafTorsor.Stack.pseudofunctor (group J K F G)).toDescentData
        (fun i => map J K F (f i))).obj (torsor J K F P)).hom
        (map J K F q) (map J K F l) (map J K F r)
        (congrArg (map J K F) hl) (congrArg (map J K F) hr) ≫
      (SheafTorsor.restriction (map J K F r)).map
        ((torsorFunctor J K F).map (t.hom j)) := by
  have hc := congrArg (fun k => (torsorFunctor J K F).map k) (t.comm q l r hl hr)
  rw [Functor.map_comp, Functor.map_comp, torsorCanonicalTransition_map] at hc
  exact hc

/-- Local recovery comparisons commute with every overlap transition. -/
theorem torsorDescentLocalComparison_transition
    (d : (SheafTorsor.Stack.pseudofunctor G).DescentData f)
    {W : Sheaf K (Type u)} (q : W ⟶ X) {i j : I}
    (l : W ⟶ Y i) (r : W ⟶ Y j) (hl : l ≫ f i = q) (hr : r ≫ f j = q) :
    (SheafTorsor.restriction (map J K F l)).map
        (torsorDescentLocalComparison J K F G f hf d i).hom ≫
      (torsorFunctor J K F).map (d.hom q l r hl hr) =
    ((torsorDescentEquivalence J K F G f hf).functor.obj d).hom
        (map J K F q) (map J K F l) (map J K F r)
        (congrArg (map J K F) hl) (congrArg (map J K F) hr) ≫
      (SheafTorsor.restriction (map J K F r)).map
        (torsorDescentLocalComparison J K F G f hf d j).hom :=
  torsorLocalTransition J K F G f _ d
    ((SheafFamilyDescent.torsorEquivalence G f hf).counitIso.app d).hom q l r hl hr

variable {G} (a : SheafActionQuotient.Action G M)

omit [F.Full] [F.Faithful] [F.IsDenseSubsite J K] in
private theorem quotientCanonicalTransition (P : SheafActionQuotient.Object a X)
    {W : Sheaf K (Type u)} (q : W ⟶ X) {i j : I} (l : W ⟶ Y i) (r : W ⟶ Y j)
    (hl : l ≫ f i = q) (hr : r ≫ f j = q) :
    (((SheafActionQuotient.Stack.pseudofunctor a).toDescentData f).obj P).hom q l r hl hr =
      eqToHom (show SheafActionQuotient.reindex (SheafActionQuotient.reindex P (f i)) l =
        SheafActionQuotient.reindex (SheafActionQuotient.reindex P (f j)) r from
          congrArg (SheafActionQuotient.reindex P) (hl.trans hr.symm)) := by
  simp [Pseudofunctor.toDescentData, Pseudofunctor.DescentData.ofObj,
    Pseudofunctor.mapComp', SheafActionQuotient.Stack.pseudofunctor, Functor.toPseudofunctor',
    pseudofunctorOfIsLocallyDiscrete]
  exact Category.id_comp _

omit [F.Full] [F.Faithful] in
private theorem quotientCanonicalTransition_map (P : SheafActionQuotient.Object a X)
    {W : Sheaf K (Type u)} (q : W ⟶ X) {i j : I} (l : W ⟶ Y i) (r : W ⟶ Y j)
    (hl : l ≫ f i = q) (hr : r ≫ f j = q) :
    (quotientFunctor J K F a).map
        ((((SheafActionQuotient.Stack.pseudofunctor a).toDescentData f).obj P).hom q l r hl hr) =
      (((SheafActionQuotient.Stack.pseudofunctor (action J K F a)).toDescentData
        (fun i => map J K F (f i))).obj (quotientObject J K F a P)).hom
        (map J K F q) (map J K F l) (map J K F r)
        (congrArg (map J K F) hl) (congrArg (map J K F) hr) := by
  rw [quotientCanonicalTransition, quotientCanonicalTransition, eqToHom_map]

/-- Quotient descent comparison retains the equivariant target and stabilizers. -/
def quotientDescentEquivalence :
    (SheafActionQuotient.Stack.pseudofunctor a).DescentData f ≌
      (SheafActionQuotient.Stack.pseudofunctor (action J K F a)).DescentData
        (fun i => map J K F (f i)) :=
  (SheafFamilyDescent.quotientEquivalence a f hf).symm.trans
    ((quotientEquivalence J K F a).trans
      (SheafFamilyDescent.quotientEquivalence (action J K F a) _ (joint_cover J K F f hf)))

def quotientDescentSquare :
    (SheafActionQuotient.Stack.pseudofunctor a).toDescentData f ⋙
      (quotientDescentEquivalence J K F f hf a).functor ≅
    quotientFunctor J K F a ⋙
      (SheafActionQuotient.Stack.pseudofunctor (action J K F a)).toDescentData
        (fun i => map J K F (f i)) :=
  (Functor.associator _ _ _).symm ≪≫
    Functor.isoWhiskerRight (SheafFamilyDescent.quotientEquivalence a f hf).unitIso.symm _ ≪≫
      Functor.leftUnitor _

def quotientDescentRecovery :
    (quotientDescentEquivalence J K F f hf a).functor ⋙
      (SheafFamilyDescent.quotientEquivalence (action J K F a) _ (joint_cover J K F f hf)).inverse ≅
    (SheafFamilyDescent.quotientEquivalence a f hf).inverse ⋙ quotientFunctor J K F a :=
  Functor.isoWhiskerRight (Functor.associator _ _ _).symm _ ≪≫
    Functor.associator _ _ _ ≪≫
      Functor.isoWhiskerLeft _
        (SheafFamilyDescent.quotientEquivalence (action J K F a) _ (joint_cover J K F f hf)).unitIso.symm ≪≫
          Functor.rightUnitor _

def quotientDescentLocalComparison
    (d : (SheafActionQuotient.Stack.pseudofunctor a).DescentData f) (i : I) :
    ((quotientDescentEquivalence J K F f hf a).functor.obj d).obj i ≅
      (quotientFunctor J K F a).obj (d.obj i) :=
  (quotientFunctor J K F a).mapIso (SheafActionQuotient.Arrow.toIso
    (((SheafFamilyDescent.quotientEquivalence a f hf).counitIso.app d).hom.hom i))

theorem quotientDescentLocalComparison_natural
    {d e : (SheafActionQuotient.Stack.pseudofunctor a).DescentData f} (h : d ⟶ e) (i : I) :
    ((quotientDescentEquivalence J K F f hf a).functor.map h).hom i ≫
      (quotientDescentLocalComparison J K F f hf a e i).hom =
    (quotientDescentLocalComparison J K F f hf a d i).hom ≫
      (quotientFunctor J K F a).map (h.hom i) := by
  have hh := congrArg (fun k => k.hom i)
    ((SheafFamilyDescent.quotientEquivalence a f hf).counitIso.hom.naturality h)
  apply SheafActionQuotient.Arrow.ext
  apply SheafTorsor.Arrow.ext
  ext x p
  exact congrArg (fun k => k.torsorArrow.iso.hom.app ((elements K F (Y i)).obj x) p) hh

omit [F.Full] [F.Faithful] in
private theorem quotientLocalTransition
    (P : SheafActionQuotient.Object a X)
    (d : (SheafActionQuotient.Stack.pseudofunctor a).DescentData f)
    (t : ((SheafActionQuotient.Stack.pseudofunctor a).toDescentData f).obj P ⟶ d)
    {W : Sheaf K (Type u)} (q : W ⟶ X) {i j : I}
    (l : W ⟶ Y i) (r : W ⟶ Y j) (hl : l ≫ f i = q) (hr : r ≫ f j = q) :
    (SheafActionQuotient.restriction (map J K F l)).map
        ((quotientFunctor J K F a).map (t.hom i)) ≫
      (quotientFunctor J K F a).map (d.hom q l r hl hr) =
    (((SheafActionQuotient.Stack.pseudofunctor (action J K F a)).toDescentData
        (fun i => map J K F (f i))).obj (quotientObject J K F a P)).hom
        (map J K F q) (map J K F l) (map J K F r)
        (congrArg (map J K F) hl) (congrArg (map J K F) hr) ≫
      (SheafActionQuotient.restriction (map J K F r)).map
        ((quotientFunctor J K F a).map (t.hom j)) := by
  have hc := congrArg (fun k => (quotientFunctor J K F a).map k) (t.comm q l r hl hr)
  rw [Functor.map_comp, Functor.map_comp, quotientCanonicalTransition_map] at hc
  exact hc

theorem quotientDescentLocalComparison_transition
    (d : (SheafActionQuotient.Stack.pseudofunctor a).DescentData f)
    {W : Sheaf K (Type u)} (q : W ⟶ X) {i j : I}
    (l : W ⟶ Y i) (r : W ⟶ Y j) (hl : l ≫ f i = q) (hr : r ≫ f j = q) :
    (SheafActionQuotient.restriction (map J K F l)).map
        (quotientDescentLocalComparison J K F f hf a d i).hom ≫
      (quotientFunctor J K F a).map (d.hom q l r hl hr) =
    ((quotientDescentEquivalence J K F f hf a).functor.obj d).hom
        (map J K F q) (map J K F l) (map J K F r)
        (congrArg (map J K F) hl) (congrArg (map J K F) hr) ≫
      (SheafActionQuotient.restriction (map J K F r)).map
        (quotientDescentLocalComparison J K F f hf a d j).hom :=
  quotientLocalTransition J K F f a _ d
    ((SheafFamilyDescent.quotientEquivalence a f hf).counitIso.app d).hom q l r hl hr

end SquareKit.SheafSiteComparison

namespace SquareKit.SheafSiteComparison
open CategoryTheory Opposite
universe u
variable {C D : Type u} [Category.{u} C] [Category.{u} D]
variable (J : GrothendieckTopology C) (K : GrothendieckTopology D) (F : C ⥤ D)
variable [F.Full] [F.Faithful] [F.IsDenseSubsite J K]
variable {G : Sheaf K GrpCat.{u}} {M X X' : Sheaf K (Type u)}
variable {I I' : Type u} {Y : I → Sheaf K (Type u)} {Y' : I' → Sheaf K (Type u)}
variable (f : ∀ i, Y i ⟶ X) (hf : SheafFamilyCover.JointlyLocallySurjective f)
variable (g : ∀ i, Y' i ⟶ X') (hg : SheafFamilyCover.JointlyLocallySurjective g)
variable (r : I' → I) (p : X' ⟶ X) (b : ∀ i, Y' i ⟶ Y (r i))
variable (w : ∀ i, b i ≫ f (r i) = g i ≫ p)

/-- Changing site commutes with every covering refinement and change of parameter. -/
def torsorDescentRefinement (G : Sheaf K GrpCat.{u}) :
    Pseudofunctor.DescentData.pullFunctor (SheafTorsor.Stack.pseudofunctor G) w ⋙
      (torsorDescentEquivalence J K F G g hg).functor ≅
    (torsorDescentEquivalence J K F G f hf).functor ⋙
      Pseudofunctor.DescentData.pullFunctor
        (SheafTorsor.Stack.pseudofunctor (group J K F G))
        (f := fun i => map J K F (f i)) (f' := fun i => map J K F (g i))
        (p := map J K F p) (α := r) (p' := fun i => map J K F (b i))
        (fun i => congrArg (map J K F) (w i)) := by
  have := ((SheafTorsor.Stack.pseudofunctor G).isStackFor_ofArrows_iff _).mp
    (SheafFamilyDescent.torsor_isStackFor G f hf)
  have := ((SheafTorsor.Stack.pseudofunctor G).isStackFor_ofArrows_iff _).mp
    (SheafFamilyDescent.torsor_isStackFor G g hg)
  exact recoveryRestrictionSquare _ _ _ _ _ _ _ _ _ _
    (SheafFamilyDescent.recoveryNaturality (SheafTorsor.Stack.pseudofunctor G) r p b w)
    (torsorRestrictionComparison J K F p)
    (Pseudofunctor.DescentData.toDescentDataCompPullFunctorIso
      (SheafTorsor.Stack.pseudofunctor (group J K F G))
      (f := fun i => map J K F (f i)) (f' := fun i => map J K F (g i))
        (p := map J K F p) (α := r) (p' := fun i => map J K F (b i))
        (fun i => congrArg (map J K F) (w i)))

/-- The refinement square preserves equivariant targets and all descent arrows. -/
def quotientDescentRefinement (a : SheafActionQuotient.Action G M) :
    Pseudofunctor.DescentData.pullFunctor (SheafActionQuotient.Stack.pseudofunctor a) w ⋙
      (quotientDescentEquivalence J K F g hg a).functor ≅
    (quotientDescentEquivalence J K F f hf a).functor ⋙
      Pseudofunctor.DescentData.pullFunctor
        (SheafActionQuotient.Stack.pseudofunctor (action J K F a))
        (f := fun i => map J K F (f i)) (f' := fun i => map J K F (g i))
        (p := map J K F p) (α := r) (p' := fun i => map J K F (b i))
        (fun i => congrArg (map J K F) (w i)) := by
  have := ((SheafActionQuotient.Stack.pseudofunctor a).isStackFor_ofArrows_iff _).mp
    (SheafFamilyDescent.quotient_isStackFor a f hf)
  have := ((SheafActionQuotient.Stack.pseudofunctor a).isStackFor_ofArrows_iff _).mp
    (SheafFamilyDescent.quotient_isStackFor a g hg)
  exact recoveryRestrictionSquare _ _ _ _ _ _ _ _ _ _
    (SheafFamilyDescent.recoveryNaturality (SheafActionQuotient.Stack.pseudofunctor a) r p b w)
    (quotientRestrictionComparison J K F a p)
    (Pseudofunctor.DescentData.toDescentDataCompPullFunctorIso
      (SheafActionQuotient.Stack.pseudofunctor (action J K F a))
      (f := fun i => map J K F (f i)) (f' := fun i => map J K F (g i))
        (p := map J K F p) (α := r) (p' := fun i => map J K F (b i))
        (fun i => congrArg (map J K F) (w i)))

end SquareKit.SheafSiteComparison

namespace SquareKit.SheafSiteComparison
open CategoryTheory Opposite
universe u
variable {C D : Type u} [Category.{u} C] [Category.{u} D]
variable (J : GrothendieckTopology C) (K : GrothendieckTopology D) (F : C ⥤ D)
variable [F.Full] [F.Faithful] [F.IsDenseSubsite J K]
variable {G : Sheaf K GrpCat.{u}} {M X X' X'' : Sheaf K (Type u)}
variable {I I' I'' : Type u}
variable {Y : I → Sheaf K (Type u)} {Y' : I' → Sheaf K (Type u)}
variable {Y'' : I'' → Sheaf K (Type u)}
variable (f : ∀ i, Y i ⟶ X) (hf : SheafFamilyCover.JointlyLocallySurjective f)
variable (g : ∀ i, Y' i ⟶ X') (h : ∀ i, Y'' i ⟶ X'')
variable (hh : SheafFamilyCover.JointlyLocallySurjective h)
variable (r : I' → I) (p : X' ⟶ X) (b : ∀ i, Y' i ⟶ Y (r i))
variable (w : ∀ i, b i ≫ f (r i) = g i ≫ p)
variable (s : I'' → I') (q : X'' ⟶ X') (c : ∀ i, Y'' i ⟶ Y' (s i))
variable (v : ∀ i, c i ≫ g (s i) = h i ≫ q)

/-- Two successive refinements commute with site change, using the comparison
with their composite on both sites. -/
def torsorDescentRefinementComp (G : Sheaf K GrpCat.{u}) :
    (Pseudofunctor.DescentData.pullFunctor (SheafTorsor.Stack.pseudofunctor G) w ⋙
      Pseudofunctor.DescentData.pullFunctor (SheafTorsor.Stack.pseudofunctor G) v) ⋙
        (torsorDescentEquivalence J K F G h hh).functor ≅
    (torsorDescentEquivalence J K F G f hf).functor ⋙
      (Pseudofunctor.DescentData.pullFunctor
        (SheafTorsor.Stack.pseudofunctor (group J K F G))
        (f := fun i => map J K F (f i)) (f' := fun i => map J K F (g i))
        (p := map J K F p) (α := r) (p' := fun i => map J K F (b i))
        (fun i => congrArg (map J K F) (w i)) ⋙
      Pseudofunctor.DescentData.pullFunctor
        (SheafTorsor.Stack.pseudofunctor (group J K F G))
        (f := fun i => map J K F (g i)) (f' := fun i => map J K F (h i))
        (p := map J K F q) (α := s) (p' := fun i => map J K F (c i))
        (fun i => congrArg (map J K F) (v i))) := by
  let wc : ∀ i, (c i ≫ b (s i)) ≫ f (r (s i)) = h i ≫ (q ≫ p) :=
    fun i => by rw [Category.assoc, w, ← Category.assoc, v, Category.assoc]
  exact Functor.isoWhiskerRight
      (Pseudofunctor.DescentData.pullFunctorCompIso
        (SheafTorsor.Stack.pseudofunctor G) w v (q ≫ p)
        (r' := fun i => c i ≫ b (s i)) rfl (fun _ => rfl)) _ ≪≫
    torsorDescentRefinement J K F f hf h hh (r ∘ s) (q ≫ p)
      (fun i => c i ≫ b (s i)) wc G ≪≫
    Functor.isoWhiskerLeft _
      (Pseudofunctor.DescentData.pullFunctorCompIso
        (SheafTorsor.Stack.pseudofunctor (group J K F G))
        (f := fun i => map J K F (f i)) (f' := fun i => map J K F (g i))
        (f'' := fun i => map J K F (h i))
        (p := map J K F p) (α := r) (p' := fun i => map J K F (b i))
        (q := map J K F q) (β := s) (q' := fun i => map J K F (c i))
        (fun i => congrArg (map J K F) (w i))
        (fun i => congrArg (map J K F) (v i))
        (map J K F (q ≫ p)) (r' := fun i => map J K F (c i ≫ b (s i)))
        rfl (fun _ => rfl)).symm
/-- Two successive refinements commute with site change, using the comparison
with their composite on both sites. -/
def quotientDescentRefinementComp (a : SheafActionQuotient.Action G M) :
    (Pseudofunctor.DescentData.pullFunctor (SheafActionQuotient.Stack.pseudofunctor a) w ⋙
      Pseudofunctor.DescentData.pullFunctor (SheafActionQuotient.Stack.pseudofunctor a) v) ⋙
        (quotientDescentEquivalence J K F h hh a).functor ≅
    (quotientDescentEquivalence J K F f hf a).functor ⋙
      (Pseudofunctor.DescentData.pullFunctor
        (SheafActionQuotient.Stack.pseudofunctor (action J K F a))
        (f := fun i => map J K F (f i)) (f' := fun i => map J K F (g i))
        (p := map J K F p) (α := r) (p' := fun i => map J K F (b i))
        (fun i => congrArg (map J K F) (w i)) ⋙
      Pseudofunctor.DescentData.pullFunctor
        (SheafActionQuotient.Stack.pseudofunctor (action J K F a))
        (f := fun i => map J K F (g i)) (f' := fun i => map J K F (h i))
        (p := map J K F q) (α := s) (p' := fun i => map J K F (c i))
        (fun i => congrArg (map J K F) (v i))) := by
  let wc : ∀ i, (c i ≫ b (s i)) ≫ f (r (s i)) = h i ≫ (q ≫ p) :=
    fun i => by rw [Category.assoc, w, ← Category.assoc, v, Category.assoc]
  exact Functor.isoWhiskerRight
      (Pseudofunctor.DescentData.pullFunctorCompIso
        (SheafActionQuotient.Stack.pseudofunctor a) w v (q ≫ p)
        (r' := fun i => c i ≫ b (s i)) rfl (fun _ => rfl)) _ ≪≫
    quotientDescentRefinement J K F f hf h hh (r ∘ s) (q ≫ p)
      (fun i => c i ≫ b (s i)) wc a ≪≫
    Functor.isoWhiskerLeft _
      (Pseudofunctor.DescentData.pullFunctorCompIso
        (SheafActionQuotient.Stack.pseudofunctor (action J K F a))
        (f := fun i => map J K F (f i)) (f' := fun i => map J K F (g i))
        (f'' := fun i => map J K F (h i))
        (p := map J K F p) (α := r) (p' := fun i => map J K F (b i))
        (q := map J K F q) (β := s) (q' := fun i => map J K F (c i))
        (fun i => congrArg (map J K F) (w i))
        (fun i => congrArg (map J K F) (v i))
        (map J K F (q ≫ p)) (r' := fun i => map J K F (c i ≫ b (s i)))
        rfl (fun _ => rfl)).symm
end SquareKit.SheafSiteComparison
