import SquareKit.Internal.Cubical.CartesianFunctionPaths
import SquareKit.Internal.Cubical.CartesianWitnesses
import SquareKit.Internal.Cubical.CartesianEquivalenceExtension
import SquareKit.Internal.Cubical.CartesianLargeFamilyConstructors

/-! Native proposition and set witnesses retain coherent paths at every stage. -/
set_option autoImplicit false
set_option warningAsError true
namespace SquareKit.Cubical.Cartesian.HomotopyLevels
open CategoryTheory EquivalenceFamilies
universe u

/-- Every point is a center, with a coherent path to every other point. -/
def isProp {Γ : Context.{u}} (A : Family Γ) : Family Γ :=
  pi A (contractions A)

/-- Every native identity family is a proposition. -/
def isSet {Γ : Context.{u}} (A : Family Γ) : Family Γ :=
  pi A (pi (reindex A (projection A)) (isProp (contractionPaths A)))

def contractionPathsReindexIso {Γ Δ : Context.{u}} (A : Family Γ) (σ : Δ ⟶ Γ) :
    reindex (contractionPaths A)
      (liftSub (reindex A (projection A)) (liftSub A σ)) ≅
      contractionPaths (reindex A σ) :=
  pathReindexIso
    (reindex (reindex (reindex A (projection A)) (projection (reindex A (projection A))))
      (projection (interval (total (reindex A (projection A))))))
    (Term.reindex (generic A) (projection (reindex A (projection A))))
    (generic (reindex A (projection A)))
    (liftSub (reindex A (projection A)) (liftSub A σ))

def contractionsReindexIso {Γ Δ : Context.{u}} (A : Family Γ) (σ : Δ ⟶ Γ) :
    reindex (contractions A) (liftSub A σ) ≅ contractions (reindex A σ) :=
  piReindexIso _ _ (liftSub A σ) ≪≫ piSecondIso _ (contractionPathsReindexIso A σ)

def isPropReindexIso {Γ Δ : Context.{u}} (A : Family Γ) (σ : Δ ⟶ Γ) :
    reindex (isProp A) σ ≅ isProp (reindex A σ) :=
  piReindexIso _ _ σ ≪≫ piSecondIso _ (contractionsReindexIso A σ)

def reindexProp {Γ Δ : Context.{u}} {A : Family Γ}
    (p : Term (isProp A)) (σ : Δ ⟶ Γ) : Term (isProp (reindex A σ)) :=
  Term.map (isPropReindexIso A σ).hom (Term.reindex p σ)

/-- An inhabited native proposition has its supplied point as center. -/
noncomputable def contractible {Γ : Context.{u}} {A : Family Γ}
    (p : Term (isProp A)) (a : Term A) : Contractible A :=
  Contractible.ofContraction a (app (Term.map (contractionsAtIso A a).hom
    (Term.reindex (app p) (pair (𝟙 Γ) a))))

noncomputable def path {Γ : Context.{u}} {A : Family Γ} (p : Term (isProp A)) (a b : Term A) :
    Term (homogeneousPath A a b) := (contractible p a).pathTo b

/-- Change a proposition's presentation without erasing its selected paths. -/
noncomputable def mapProp {Γ : Context.{u}} {A B : Family Γ} (e : A ≅ B)
    (p : Term (isProp A)) : Term (isProp B) := by
  apply lam
  apply lam
  let σ := projection (reindex B (projection B)) ≫ projection B
  let i := Functor.whiskerLeft σ.mapElements e.hom
  let j := Functor.whiskerLeft σ.mapElements e.inv
  let a := Term.reindex (generic B) (projection (reindex B (projection B)))
  let b := generic (reindex B (projection B))
  let q := homogeneousPathMap i (path (reindexProp p σ) (Term.map j a) (Term.map j b))
  refine pathLam (pathApp q) ?_ ?_
  · exact (pathApp_zero q).trans (Term.ext (fun x => e.inv_hom_id_app_apply _ _))
  · exact (pathApp_one q).trans (Term.ext (fun x => e.inv_hom_id_app_apply _ _))

noncomputable def reindexSet {Γ Δ : Context.{u}} {A : Family Γ}
    (s : Term (isSet A)) (σ : Δ ⟶ Γ) : Term (isSet (reindex A σ)) :=
  lam (lam (mapProp (contractionPathsReindexIso A σ)
    (reindexProp (app (app s)) (liftSub (reindex A (projection A)) (liftSub A σ)))))

noncomputable def contractionPathsFilling {Γ : Context.{u}} {A : Family Γ}
    (F : Filling A) (hF : F.Lawful) : Filling (contractionPaths A) :=
  pathFilling (F.reindex (projection (interval (total (reindex A (projection A)))) ≫
    projection (reindex A (projection A)) ≫ projection A)) (hF.reindex _) _ _

theorem contractionPathsFilling_lawful {Γ : Context.{u}} {A : Family Γ}
    (F : Filling A) (hF : F.Lawful) : (contractionPathsFilling F hF).Lawful :=
  pathFilling_lawful _ (hF.reindex _) _ _

noncomputable def contractionsFilling {Γ : Context.{u}} {A : Family Γ}
    (F : Filling A) (hF : F.Lawful) : Filling (contractions A) :=
  piFilling (F.reindex (projection A)) (hF.reindex _) (contractionPathsFilling F hF)

theorem contractionsFilling_lawful {Γ : Context.{u}} {A : Family Γ}
    (F : Filling A) (hF : F.Lawful) : (contractionsFilling F hF).Lawful :=
  piFilling_lawful _ (hF.reindex _) _ (contractionPathsFilling_lawful F hF)

noncomputable def isPropFilling {Γ : Context.{u}} {A : Family Γ}
    (F : Filling A) (hF : F.Lawful) : Filling (isProp A) :=
  piFilling F hF (contractionsFilling F hF)

theorem isPropFilling_lawful {Γ : Context.{u}} {A : Family Γ}
    (F : Filling A) (hF : F.Lawful) : (isPropFilling F hF).Lawful :=
  piFilling_lawful F hF _ (contractionsFilling_lawful F hF)

noncomputable def isSetFilling {Γ : Context.{u}} {A : Family Γ}
    (F : Filling A) (hF : F.Lawful) : Filling (isSet A) :=
  piFilling F hF (piFilling (F.reindex (projection A)) (hF.reindex _)
    (isPropFilling (contractionPathsFilling F hF) (contractionPathsFilling_lawful F hF)))

theorem isSetFilling_lawful {Γ : Context.{u}} {A : Family Γ}
    (F : Filling A) (hF : F.Lawful) : (isSetFilling F hF).Lawful :=
  piFilling_lawful F hF _ (piFilling_lawful _ (hF.reindex _) _
    (isPropFilling_lawful _ (contractionPathsFilling_lawful F hF)))

/-- Sethood supplies proposition data for the whole generic path family. -/
def pathIsProp {Γ : Context.{u}} {A : Family Γ} (s : Term (isSet A)) :
    Term (isProp (contractionPaths A)) := app (app s)

/-- Pointwise subsingletons supply native proposition witnesses without choosing a point. -/
def ofSubsingleton {Γ : Context.{u}} (A : Family Γ)
    (h : ∀ x, Subsingleton (A.obj x)) : Term (isProp A) := by
  apply lam
  apply lam
  let a := Term.reindex (generic A) (projection (reindex A (projection A)))
  refine pathLam (Term.reindex a (projection (interval _))) rfl ?_
  apply Term.ext
  intro x
  exact @Subsingleton.elim _ (h _) _ _

private def smallReindex {Γ Δ : Context.{u+1}} {A : Family Γ}
    (P : SmallUniverse.SmallPresentation.Data A) (σ : Δ ⟶ Γ) :
    SmallUniverse.SmallPresentation.Data (reindex A σ) where
  fiber x := P.fiber (σ.mapElements.obj x)
  equiv x := P.equiv (σ.mapElements.obj x)

noncomputable def pathsPresentation {Γ : Context.{u+1}} {A : Family Γ}
    (P : SmallUniverse.SmallPresentation.Data A) :
    SmallUniverse.SmallPresentation.Data (contractionPaths A) :=
  SmallUniverse.SmallPresentation.Data.path _
    (smallReindex P (projection (interval _) ≫ projection _ ≫ projection A)) _ _

noncomputable def isPropPresentation {Γ : Context.{u+1}} {A : Family Γ}
    (P : SmallUniverse.SmallPresentation.Data A) :
    SmallUniverse.SmallPresentation.Data (isProp A) :=
  P.pi ((smallReindex P (projection A)).pi (pathsPresentation P))

noncomputable def isSetPresentation {Γ : Context.{u+1}} {A : Family Γ}
    (P : SmallUniverse.SmallPresentation.Data A) :
    SmallUniverse.SmallPresentation.Data (isSet A) :=
  P.pi ((smallReindex P (projection A)).pi (isPropPresentation (pathsPresentation P)))

namespace PiContractibility
variable {Γ : Context.{u}} {A : Family Γ} {B : Family (total A)}
  (c : Contractible B) (F : Filling B) (hF : F.Lawful)
  {Δ : Context.{u}} (σ : Δ ⟶ Γ) (φ : Subcontext Δ)
  (s : PartialSection (reindex (pi A B) σ) φ)

noncomputable def body : Term (reindex B (liftSub A σ)) :=
  (c.reindex (liftSub A σ)).extend (F.reindex (liftSub A σ))
    ((s.map (piReindex A B σ)).app)

noncomputable def extend : Term (reindex (pi A B) σ) :=
  Term.map (piReindexIso A B σ).inv (lam (body c F σ φ s))

include hF in
theorem boundary (x : Δ.Elements) (hx : φ.holds x) :
    (extend c F σ φ s).val x = s.val x hx := by
  let i := piReindexIso A B σ
  let p := s.map i.hom
  have h : (lam (body c F σ φ s)).val x = p.val x hx := by
    apply PiElement.ext
    intro y g v
    have hb := (c.reindex (liftSub A σ)).extend_boundary (F.reindex (liftSub A σ))
      (hF.reindex _) p.app (extendObj (reindex A σ) y v) (φ.natural g hx)
    have hp := congrArg (fun k => k.val (𝟙 y) v) (p.natural g hx)
    refine hb.trans ?_
    change (p.val x hx).val (g ≫ 𝟙 y) v =
      (p.val y (φ.natural g hx)).val (𝟙 y) v at hp
    change (p.val y (φ.natural g hx)).val (𝟙 y) v = (p.val x hx).val g v
    simpa only [Category.comp_id] using hp.symm
  exact (congrArg (i.inv.app x) h).trans
    (congrArg (fun m => m.app x (s.val x hx)) i.hom_inv_id)

end PiContractibility

/-- Pointwise contractions yield a contraction of the native dependent function family. -/
noncomputable def piContractible {Γ : Context.{u}} {A : Family Γ}
    {B : Family (total A)} (c : Contractible B) (F : Filling B) (hF : F.Lawful) :
    Contractible (pi A B) :=
  Contractible.ofExtensions (PiContractibility.extend c F)
    (PiContractibility.boundary c F hF)

/-- A contraction and lawful filling connect any two supplied points. -/
noncomputable def pathOfContractible {Γ : Context.{u}} {A : Family Γ}
    (c : Contractible A) (F : Filling A) (hF : F.Lawful) (a b : Term A) :
    Term (homogeneousPath A a b) :=
  (contractAt a (fun σ _ s => (c.reindex σ).extend (F.reindex σ) s)
    (fun σ _ s => (c.reindex σ).extend_boundary (F.reindex σ) (hF.reindex σ) s)).pathTo b

/-- Contractibility supplies native proposition witnesses. -/
noncomputable def ofContractible {Γ : Context.{u}} {A : Family Γ}
    (c : Contractible A) (F : Filling A) (hF : F.Lawful) : Term (isProp A) := by
  apply lam
  apply lam
  let σ := projection (reindex A (projection A)) ≫ projection A
  exact pathOfContractible (c.reindex σ) (F.reindex σ) (hF.reindex σ)
    (Term.reindex (generic A) (projection (reindex A (projection A))))
    (generic (reindex A (projection A)))

/-- Dependent functions into native propositions form a native proposition. -/
noncomputable def piIsProp {Γ : Context.{u}} {A : Family Γ} {B : Family (total A)}
    (p : Term (isProp B)) (FA : Filling A) (hFA : FA.Lawful)
    (F : Filling B) (hF : F.Lawful) : Term (isProp (pi A B)) := by
  apply lam
  apply lam
  let P := pi A B
  let σ := projection (reindex P (projection P)) ≫ projection P
  let f := Term.reindex (generic P) (projection (reindex P (projection P)))
  let g := generic (reindex P (projection P))
  let τ := liftSub A σ
  let d := contractible (reindexProp p τ) (app (Term.map (piReindex A B σ) f))
  let c := Contractible.map (piReindexIso A B σ).symm (piContractible d (F.reindex τ) (hF.reindex τ))
  let K := (piFilling FA hFA F).reindex σ
  exact pathOfContractible c K ((piFilling_lawful FA hFA F hF).reindex σ) f g

/-- Contractible fibers over a contractible base give a contractible dependent total. -/
noncomputable def sigmaContractible {Γ : Context.{u}} {A : Family Γ}
    {B : Family (total A)} (cA : Contractible A) (cB : Contractible B)
    (FA : Filling A) (hFA : FA.Lawful) (FB : Filling B) (hFB : FB.Lawful) :
    Contractible (sigma A B) := by
  let extend {Δ : Context.{u}} (σ : Δ ⟶ Γ) (φ : Subcontext Δ)
      (s : PartialSection (reindex (sigma A B) σ) φ) : Term (reindex (sigma A B) σ) := by
    let a := (cA.reindex σ).extend (FA.reindex σ) (s.sigmaFst (B := reindex B (liftSub A σ)))
    have ha := (cA.reindex σ).extend_boundary (FA.reindex σ) (hFA.reindex σ) (s.sigmaFst (B := reindex B (liftSub A σ)))
    let t := (s.sigmaSnd (B := reindex B (liftSub A σ)) a ha)
    exact sigmaIntro (B := reindex B (liftSub A σ)) a ((cB.reindex (pair σ a)).extend (FB.reindex (pair σ a)) t)
  refine Contractible.ofExtensions extend ?_
  intro Δ σ φ s x hx
  let a := (cA.reindex σ).extend (FA.reindex σ) (s.sigmaFst (B := reindex B (liftSub A σ)))
  have ha := (cA.reindex σ).extend_boundary (FA.reindex σ) (hFA.reindex σ) (s.sigmaFst (B := reindex B (liftSub A σ)))
  have hb := (cB.reindex (pair σ a)).extend_boundary (FB.reindex (pair σ a))
    (hFB.reindex (pair σ a)) ((s.sigmaSnd (B := reindex B (liftSub A σ)) a ha)) x hx
  exact Sigma.ext (ha x hx) ((heq_of_eq hb).trans (PartialSection.sigmaSnd_val (B := reindex B (liftSub A σ)) s a ha x hx))

/-- A pair of native propositions is a native proposition. -/
noncomputable def productIsProp {Γ : Context.{u}} {A B : Family Γ}
    (pA : Term (isProp A)) (pB : Term (isProp B))
    (FA : Filling A) (hFA : FA.Lawful) (FB : Filling B) (hFB : FB.Lawful) :
    Term (isProp (sigma A (reindex B (projection A)))) := by
  apply lam
  apply lam
  let P := sigma A (reindex B (projection A))
  let σ := projection (reindex P (projection P)) ≫ projection P
  let f := Term.reindex (generic P) (projection (reindex P (projection P)))
  let g := generic (reindex P (projection P))
  let a := sigmaFst (B := reindex (reindex B (projection A)) (liftSub A σ)) f
  let b : Term (reindex B σ) := sigmaSnd (B := reindex (reindex B (projection A)) (liftSub A σ)) f
  let cA := contractible (reindexProp pA σ) a
  let cB := contractible (reindexProp pB σ) b
  let π := projection (reindex A σ)
  let c := sigmaContractible cA (cB.reindex π) (FA.reindex σ) (hFA.reindex σ)
    (FB.reindex (π ≫ σ)) (hFB.reindex (π ≫ σ))
  exact pathOfContractible c
    ((sigmaFilling FA hFA (FB.reindex (projection A))).reindex σ)
    ((sigmaFilling_lawful FA hFA (FB.reindex (projection A)) (hFB.reindex _)).reindex σ) f g

private theorem constant_path_value {Γ : Context.{u}} {S : Type u}
    {a b : Term (constantFamily Γ S)} {x : Γ.Elements}
    (p : (homogeneousPath (constantFamily Γ S) a b).obj x)
    {y : Γ.Elements} (f : x ⟶ y) (r : (interval Γ).obj y) :
    p.val.val f r = a.val y := by
  let P := homogeneousPath (constantFamily Γ S) a b
  let τ := projection P
  let t := Term.map (homogeneousReindexIso (constantFamily Γ S) a b τ).hom (generic P)
  let z := extendObj P y (P.map f p)
  have h := constant_section_interval (pathApp t) z r ((endpoint (total P) false).val z)
  have hz := congrArg (fun s => s.val z) (pathApp_zero t)
  have hh := h.trans hz
  change p.val.val (f ≫ 𝟙 y) r = a.val y at hh
  simpa only [Category.comp_id] using hh

/-- Every constant family is a native set, without a finiteness assumption. -/
def constantIsSet {Γ : Context.{u}} (S : Type u) : Term (isSet (constantFamily Γ S)) := by
  apply lam
  apply lam
  apply ofSubsingleton
  intro x
  constructor
  intro p q
  apply Subtype.ext
  apply PiElement.ext
  intro y f r
  exact (constant_path_value p f r).trans (constant_path_value q f r).symm

/-- Product paths retain both component paths, including their interiors. -/
def productPathIso {Γ : Context.{u}} {A B : Family Γ}
    (a b : Term (sigma A (reindex B (projection A)))) :
    homogeneousPath (sigma A (reindex B (projection A))) a b ≅
      sigma (homogeneousPath A (sigmaFst a) (sigmaFst b))
        (reindex (homogeneousPath B (sigmaSnd a) (sigmaSnd b))
          (projection (homogeneousPath A (sigmaFst a) (sigmaFst b)))) := by
  let e (x : Γ.Elements) :
      (homogeneousPath (sigma A (reindex B (projection A))) a b).obj x ≃
      (sigma (homogeneousPath A (sigmaFst a) (sigmaFst b))
        (reindex (homogeneousPath B (sigmaSnd a) (sigmaSnd b))
          (projection (homogeneousPath A (sigmaFst a) (sigmaFst b))))).obj x := {
    toFun := fun p => ⟨
      ⟨{ val := fun f r => (p.val.val f r).1
         naturality := fun f g r => congrArg Sigma.fst (p.val.naturality f g r) },
       fun f => ⟨congrArg Sigma.fst (p.property f).1, congrArg Sigma.fst (p.property f).2⟩⟩,
      ⟨{ val := fun f r => (p.val.val f r).2
         naturality := fun f g r => eq_of_heq (Sigma.mk.inj (p.val.naturality f g r)).2 },
       fun {y} f => by
         constructor
         · change (p.val.val f ((endpoint Γ false).val y)).2 = (a.val y).2
           exact eq_of_heq (Sigma.mk.inj (p.property f).1).2
         · change (p.val.val f ((endpoint Γ true).val y)).2 = (b.val y).2
           exact eq_of_heq (Sigma.mk.inj (p.property f).2).2⟩⟩
    invFun := fun q => ⟨{
      val := fun f r => ⟨q.1.val.val f r, q.2.val.val f r⟩
      naturality := fun f g r => by
        apply Sigma.ext (q.1.val.naturality f g r)
        exact heq_of_eq (q.2.val.naturality f g r) }, fun f => by
      constructor
      · exact Sigma.ext (q.1.property f).1 (heq_of_eq (q.2.property f).1)
      · exact Sigma.ext (q.1.property f).2 (heq_of_eq (q.2.property f).2)⟩
    left_inv := fun p => by
      apply Subtype.ext
      apply PiElement.ext
      intro y f r
      rfl
    right_inv := fun q => by
      apply Sigma.ext
      · apply Subtype.ext
        apply PiElement.ext
        intro y f r
        rfl
      · apply heq_of_eq
        apply Subtype.ext
        apply PiElement.ext
        intro y f r
        rfl }
  exact NatIso.ofComponents (fun x => (e x).toIso) (by
    intro x y f
    apply ConcreteCategory.hom_ext
    intro p
    rfl)

/-- Sethood specializes to arbitrary chosen endpoints. -/
noncomputable def pathIsPropAt {Γ : Context.{u}} {A : Family Γ} (s : Term (isSet A)) (a b : Term A) :
    Term (isProp (homogeneousPath A a b)) :=
by
  let σ := pair (A := reindex A (projection A)) (pair (𝟙 Γ) a) b
  let C := reindex (reindex A (projection A)) (projection (reindex A (projection A)))
  let x := Term.reindex (generic A) (projection (reindex A (projection A)))
  let y := generic (reindex A (projection A))
  let i := homogeneousReindexIso C x y σ
  let j : homogeneousPath (reindex C σ) (Term.reindex x σ) (Term.reindex y σ) ≅
      homogeneousPath A a b := {
    hom := {
      app := fun _ => TypeCat.ofHom (fun p => ⟨{
        val := fun f r => p.val.val f r
        naturality := fun f g r => p.val.naturality f g r }, fun f => p.property f⟩)
      naturality := fun _ _ _ => rfl }
    inv := {
      app := fun _ => TypeCat.ofHom (fun p => ⟨{
        val := fun f r => p.val.val f r
        naturality := fun f g r => p.val.naturality f g r }, fun f => p.property f⟩)
      naturality := fun _ _ _ => rfl }
    hom_inv_id := by
      ext x p
      apply Subtype.ext
      apply PiElement.ext
      intro y f r
      rfl
    inv_hom_id := by
      ext x p
      apply Subtype.ext
      apply PiElement.ext
      intro y f r
      rfl }
  exact mapProp (i ≪≫ j) (reindexProp (pathIsProp s) σ)

/-- A product of native sets is a native set. -/
noncomputable def productIsSet {Γ : Context.{u}} {A B : Family Γ}
    (sA : Term (isSet A)) (sB : Term (isSet B))
    (FA : Filling A) (hFA : FA.Lawful) (FB : Filling B) (hFB : FB.Lawful) :
    Term (isSet (sigma A (reindex B (projection A)))) := by
  apply lam
  apply lam
  let P := sigma A (reindex B (projection A))
  let σ := projection (reindex P (projection P)) ≫ projection P
  let a := Term.reindex (generic P) (projection (reindex P (projection P)))
  let b := generic (reindex P (projection P))
  let a₁ := sigmaFst (B := reindex (reindex B (projection A)) (liftSub A σ)) a
  let b₁ := sigmaFst (B := reindex (reindex B (projection A)) (liftSub A σ)) b
  let a₂ : Term (reindex B σ) := sigmaSnd (B := reindex (reindex B (projection A)) (liftSub A σ)) a
  let b₂ : Term (reindex B σ) := sigmaSnd (B := reindex (reindex B (projection A)) (liftSub A σ)) b
  let pA := pathIsPropAt (reindexSet sA σ) a₁ b₁
  let pB := pathIsPropAt (reindexSet sB σ) a₂ b₂
  exact mapProp (productPathIso (A := reindex A σ) (B := reindex B σ) a b).symm (productIsProp pA pB
    (pathFilling ((FA.reindex σ).reindex (projection (interval _)))
      ((hFA.reindex σ).reindex _) a₁ b₁)
    (pathFilling_lawful ((FA.reindex σ).reindex (projection (interval _))) ((hFA.reindex σ).reindex (projection (interval _))) a₁ b₁)
    (pathFilling ((FB.reindex σ).reindex (projection (interval _)))
      ((hFB.reindex σ).reindex _) a₂ b₂)
    (pathFilling_lawful ((FB.reindex σ).reindex (projection (interval _))) ((hFB.reindex σ).reindex (projection (interval _))) a₂ b₂))

/-- Paths between points of a contractible family are contractible. -/
noncomputable def pathContractible {Γ : Context.{u}} {A : Family Γ}
    (c : Contractible A) (F : Filling A) (hF : F.Lawful) (a b : Term A) :
    Contractible (homogeneousPath A a b) := by
  let extend {Δ : Context.{u}} (σ : Δ ⟶ Γ) (φ : Subcontext Δ)
      (s : PartialSection (reindex (homogeneousPath A a b) σ) φ) :
      Term (reindex (homogeneousPath A a b) σ) :=
    let i := homogeneousReindexIso A a b σ
    Term.map i.inv (ContractiblePaths.extend (c.reindex σ) (F.reindex σ)
      (hF.reindex σ) (s.map i.hom))
  refine Contractible.ofExtensions extend ?_
  intro Δ σ φ s x hx
  let i := homogeneousReindexIso A a b σ
  have h := ContractiblePaths.extend_boundary (c.reindex σ) (F.reindex σ)
    (hF.reindex σ) (s.map i.hom) x hx
  exact (congrArg (i.inv.app x) h).trans (i.hom_inv_id_app_apply x (s.val x hx))

/-- Any native map between contractible families is a homotopy equivalence. -/
noncomputable def equivalenceOfContractible {Γ : Context.{u}} {A B : Family Γ}
    (f : A ⟶ B) (cA : Contractible A) (cB : Contractible B)
    (FA : Filling A) (hFA : FA.Lawful) (FB : Filling B) (hFB : FB.Lawful) :
    HomotopyEquivalence f := by
  let A' := reindex A (projection B)
  let σ := projection A' ≫ projection B
  let a := Term.map (Functor.whiskerLeft σ.mapElements f) (generic A')
  let b := Term.reindex (generic B) (projection A')
  exact ⟨sigmaContractible (cA.reindex (projection B))
    (pathContractible (cB.reindex σ) (FB.reindex σ) (hFB.reindex σ) a b)
    (FA.reindex (projection B)) (hFA.reindex _)
    (pathFilling (FB.reindex (projection (interval _) ≫ σ)) (hFB.reindex _) a b)
    (pathFilling_lawful (FB.reindex (projection (interval _) ≫ σ)) (hFB.reindex _) a b)⟩

/-- A native homotopy equivalence carries contractibility to its target. -/
noncomputable def targetContractible {Γ : Context.{u}} {A B : Family Γ} {f : A ⟶ B}
    (e : HomotopyEquivalence f) (c : Contractible A)
    (F : Filling B) (hF : F.Lawful) : Contractible B := by
  let g := EquivalenceFamilies.decodeMap (lam (sigmaFst e.fibers.center))
  let h := Homotopy.fiberPath (Functor.whiskerLeft (projection B).mapElements f)
    (generic B) e.fibers.center
  exact c.retract F hF f g h


def pathMap {Γ : Context.{u}} {A B : Family Γ} (f : A ⟶ B) (a b : Term A) :
    homogeneousPath A a b ⟶ homogeneousPath B (Term.map f a) (Term.map f b) where
  app _ := TypeCat.ofHom (fun p => ⟨{
    val := fun {y} g r => f.app y (p.val.val g r)
    naturality := fun {_ z} g k r => (f.naturality_apply k _).symm.trans
      (congrArg (f.app z) (p.val.naturality g k r)) },
    fun g => ⟨congrArg (f.app _) (p.property g).1, congrArg (f.app _) (p.property g).2⟩⟩)
  naturality _ _ _ := rfl

def pathCongr {Γ : Context.{u}} {A B : Family Γ} (e : A ≅ B) (a b : Term A) :
    homogeneousPath A a b ≅ homogeneousPath B (Term.map e.hom a) (Term.map e.hom b) where
  hom := pathMap e.hom a b
  inv := {
    app := fun _ => TypeCat.ofHom (fun p => ⟨{
      val := fun {y} g r => e.inv.app y (p.val.val g r)
      naturality := fun {_ z} g k r => (e.inv.naturality_apply k _).symm.trans
        (congrArg (e.inv.app z) (p.val.naturality g k r)) }, fun {y} g => by
          constructor
          · exact (congrArg (e.inv.app y) (p.property g).1).trans (e.hom_inv_id_app_apply y _)
          · exact (congrArg (e.inv.app y) (p.property g).2).trans (e.hom_inv_id_app_apply y _)⟩)
    naturality := fun _ _ _ => rfl }
  hom_inv_id := by
    ext x p
    apply Subtype.ext
    apply PiElement.ext
    intro y g r
    exact e.hom_inv_id_app_apply y _
  inv_hom_id := by
    ext x p
    apply Subtype.ext
    apply PiElement.ext
    intro y g r
    exact e.inv_hom_id_app_apply y _


/-- Dependent functions into native sets form a native set. -/
noncomputable def piIsSet {Γ : Context.{u}} {A : Family Γ} {B : Family (total A)}
    (s : Term (isSet B)) (FA : Filling A) (hFA : FA.Lawful)
    (FB : Filling B) (hFB : FB.Lawful) : Term (isSet (pi A B)) := by
  apply lam
  apply lam
  let P := pi A B
  let σ := projection (reindex P (projection P)) ≫ projection P
  let f := Term.reindex (generic P) (projection (reindex P (projection P)))
  let g := generic (reindex P (projection P))
  let τ := liftSub A σ
  let i := piReindexIso A B σ
  let f' := Term.map i.hom f
  let g' := Term.map i.hom g
  let p := pathIsPropAt (reindexSet s τ) (app f') (app g')
  let K := pathFilling (FB.reindex (projection (interval _) ≫ τ))
    (hFB.reindex _) (app f') (app g')
  have hK : K.Lawful := pathFilling_lawful (FB.reindex (projection (interval _) ≫ τ)) (hFB.reindex (projection (interval _) ≫ τ)) (app f') (app g')
  exact mapProp ((pathCongr i f g) ≪≫ FunctionPaths.decomposition f' g').symm
    (piIsProp p (FA.reindex σ) (hFA.reindex σ) K hK)

/-- Smallness retains the center and every native contraction path. -/
noncomputable def contrPresentation {Γ : Context.{u+1}} {A : Family Γ}
    (P : SmallUniverse.SmallPresentation.Data A) :
    SmallUniverse.SmallPresentation.Data (contr A) :=
  P.sigma ((smallReindex P (projection A)).pi (pathsPresentation P))

noncomputable def fiberPresentation {Γ : Context.{u+1}} {A B : Family Γ}
    (PA : SmallUniverse.SmallPresentation.Data A)
    (PB : SmallUniverse.SmallPresentation.Data B) (f : A ⟶ B) (b : Term B) :
    SmallUniverse.SmallPresentation.Data (Homotopy.fiber f b) :=
  PA.sigma (SmallUniverse.SmallPresentation.Data.path _
    (smallReindex PB (projection (interval _) ≫ projection A)) _ _)

noncomputable def isEquivPresentation {Γ : Context.{u+1}} {A B : Family Γ}
    (PA : SmallUniverse.SmallPresentation.Data A)
    (PB : SmallUniverse.SmallPresentation.Data B) (f : A ⟶ B) :
    SmallUniverse.SmallPresentation.Data (isEquiv f) :=
  PB.pi (contrPresentation (fiberPresentation
    (smallReindex PA (projection B)) (smallReindex PB (projection B))
    (Functor.whiskerLeft (projection B).mapElements f) (generic B)))

/-- A small native equivalence family includes its chosen contractible-fiber witnesses. -/
noncomputable def equivPresentation {Γ : Context.{u+1}} {A B : Family Γ}
    (PA : SmallUniverse.SmallPresentation.Data A)
    (PB : SmallUniverse.SmallPresentation.Data B) :
    SmallUniverse.SmallPresentation.Data (equiv A B) :=
  (PA.pi (smallReindex PB (projection A))).sigma
    (isEquivPresentation (smallReindex PA (projection (maps A B)))
      (smallReindex PB (projection (maps A B))) (universalMap A B))

/-- A native proposition has proposition-valued native identity families. -/
noncomputable def propIsSet {Γ : Context.{u}} {A : Family Γ}
    (p : Term (isProp A)) (F : Filling A) (hF : F.Lawful) : Term (isSet A) := by
  apply lam
  apply lam
  let σ := projection (reindex A (projection A)) ≫ projection A
  let a := Term.reindex (generic A) (projection (reindex A (projection A)))
  let b := generic (reindex A (projection A))
  let c := contractible (reindexProp p σ) a
  let K := pathFilling (F.reindex (projection (interval _) ≫ σ)) (hF.reindex _) a b
  exact ofContractible (pathContractible c (F.reindex σ) (hF.reindex σ) a b)
    K (pathFilling_lawful (F.reindex (projection (interval _) ≫ σ)) (hF.reindex (projection (interval _) ≫ σ)) a b)

private noncomputable def isPropIsPropOfProp {Γ : Context.{u}} {A : Family Γ}
    (p : Term (isProp A)) (F : Filling A) (hF : F.Lawful) : Term (isProp (isProp A)) :=
  piIsProp
    (piIsProp (pathIsProp (propIsSet p F hF)) (F.reindex (projection A)) (hF.reindex _)
      (contractionPathsFilling F hF) (contractionPathsFilling_lawful F hF))
    F hF (contractionsFilling F hF) (contractionsFilling_lawful F hF)

/-- Being a native proposition is itself a native proposition. -/
noncomputable def isPropIsProp {Γ : Context.{u}} {A : Family Γ}
    (F : Filling A) (hF : F.Lawful) : Term (isProp (isProp A)) := by
  apply lam
  apply lam
  let P := isProp A
  let σ := projection (reindex P (projection P)) ≫ projection P
  let p := Term.reindex (generic P) (projection (reindex P (projection P)))
  let q := generic (reindex P (projection P))
  let i := isPropReindexIso A σ
  let h := isPropIsPropOfProp (Term.map i.hom p) (F.reindex σ) (hF.reindex σ)
  exact path (mapProp i.symm h) p q

/-- Being a native set is itself a native proposition, retaining the path witnesses. -/
noncomputable def isSetIsProp {Γ : Context.{u}} {A : Family Γ}
    (F : Filling A) (hF : F.Lawful) : Term (isProp (isSet A)) :=
  piIsProp
    (piIsProp (isPropIsProp (contractionPathsFilling F hF) (contractionPathsFilling_lawful F hF))
      (F.reindex (projection A)) (hF.reindex _)
      (isPropFilling (contractionPathsFilling F hF) (contractionPathsFilling_lawful F hF))
      (isPropFilling_lawful _ _))
    F hF
    (piFilling (F.reindex (projection A)) (hF.reindex _)
      (isPropFilling (contractionPathsFilling F hF) (contractionPathsFilling_lawful F hF)))
    (piFilling_lawful _ (hF.reindex _) _ (isPropFilling_lawful _ _))

/-- Decode a reindexed native sethood witness without requiring a global witness. -/
noncomputable def reindexSetTerm {Γ Δ : Context.{u}} (A : Family Γ) (σ : Δ ⟶ Γ)
    (s : Term (reindex (isSet A) σ)) : Term (isSet (reindex A σ)) := by
  let τ := liftSub A σ
  let υ := liftSub (reindex A (projection A)) τ
  let s₁ := app (Term.map (piReindexIso A
    (pi (reindex A (projection A)) (isProp (contractionPaths A))) σ).hom s)
  let s₂ := app (Term.map (piReindexIso (reindex A (projection A))
    (isProp (contractionPaths A)) τ).hom s₁)
  exact lam (lam (mapProp (contractionPathsReindexIso A σ)
    (Term.map (isPropReindexIso (contractionPaths A) υ).hom s₂)))

end SquareKit.Cubical.Cartesian.HomotopyLevels
