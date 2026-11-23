import SquareKit.Internal.Cubical.FiberwiseHomotopyRetracts
import SquareKit.Internal.Cubical.NativeStructureDescriptions
import SquareKit.Internal.Cubical.PiDomainIso
import SquareKit.Internal.Cubical.SelectedInverse
import SquareKit.Internal.Cubical.HomotopyLevels
import SquareKit.Internal.Cubical.FunctionPaths
import SquareKit.Internal.Cubical.EquivalenceFamilyReindex
import SquareKit.Internal.Cubical.NativePathSingleton

/-! Native structure maps act on every generalized argument of a function field.
The two carrier maps are kept explicit so contravariance does not discard the
inverse selected by a supplied equivalence. -/
set_option autoImplicit false
set_option warningAsError true
namespace SquareKit.Cubical.Presheaf.StructureIdentity.Native
open CategoryTheory SquareKit.StructureIdentity
universe u
variable {Γ : Context.{u+1}}

def productMap {A B C D : Family Γ} (f : A ⟶ B) (g : C ⟶ D) :
    sigma A (reindex C (projection A)) ⟶ sigma B (reindex D (projection B)) where
  app x := TypeCat.ofHom (fun z => ⟨f.app x z.1, g.app x z.2⟩)
  naturality x y h := by
    apply ConcreteCategory.hom_ext
    intro z
    exact congrArg₂ (fun (a : B.obj y) (c : D.obj y) =>
      (⟨a,c⟩ : (sigma B (reindex D (projection B))).obj y))
      (f.naturality_apply h z.1) (g.naturality_apply h z.2)

def functionMap {A B C D : Family Γ} (f : B ⟶ A) (g : C ⟶ D) :
    pi A (reindex C (projection A)) ⟶ pi B (reindex D (projection B)) where
  app x := TypeCat.ofHom (fun p => {
    val := fun {y} h b => g.app y (p.val h (f.app y b))
    naturality := fun {y z} h k b => by
      change D.map k (g.app y (p.val h (f.app y b))) =
        g.app z (p.val (h ≫ k) (f.app z (B.map k b)))
      exact (g.naturality_apply k _).symm.trans
        (congrArg (g.app z) ((p.naturality h k (f.app y b)).trans
          (congrArg (fun a : A.obj z => (show C.obj z from p.val (h ≫ k) a))
            (f.naturality_apply k b).symm))) })
  naturality x y h := by
    apply ConcreteCategory.hom_ext
    intro p
    apply PiElement.ext
    intro z k b
    rfl

/-- Both variances are structural. No path or univalence operation defines this map. -/
def action (D : Description.{u}) {A B : Family Γ} (f : A ⟶ B) (g : B ⟶ A) :
    family D A ⟶ family D B :=
  match D with
  | .carrier => f
  | .fixed _ => 𝟙 _
  | .product D E => productMap (action D f g) (action E f g)
  | .function D E => functionMap (action D g f) (action E f g)

theorem action_id (D : Description.{u}) (A : Family Γ) : action D (𝟙 A) (𝟙 A) = 𝟙 _ := by
  induction D with
  | carrier => rfl
  | fixed _ => rfl
  | product D E hD hE =>
    simp only [action, hD, hE]
    rfl
  | function D E hD hE =>
    simp only [action, hD, hE]
    rfl

theorem action_comp (D : Description.{u}) {A B C : Family Γ}
    (f : A ⟶ B) (g : B ⟶ A) (h : B ⟶ C) (k : C ⟶ B) :
    action D (f ≫ h) (k ≫ g) = action D f g ≫ action D h k := by
  induction D generalizing A B C with
  | carrier => rfl
  | fixed _ => rfl
  | product D E hD hE =>
    simp only [action, hD, hE]
    rfl
  | function D E hD hE =>
    simp only [action, hD, hE]
    rfl

def actionIso (D : Description.{u}) {A B : Family Γ} (e : A ≅ B) : family D A ≅ family D B where
  hom := action D e.hom e.inv
  inv := action D e.inv e.hom
  hom_inv_id := by rw [← action_comp, e.hom_inv_id, action_id]
  inv_hom_id := by rw [← action_comp, e.inv_hom_id, action_id]

/-- The actual native inverse is recovered from the supplied fiber centers. -/
def equivalenceAction (D : Description.{u}) {A B : Family Γ} {f : A ⟶ B}
    (e : HomotopyEquivalence f) : family D A ⟶ family D B :=
  action D f e.selectedInverse

def productCongr {A B C D : Family Γ} (i : A ≅ B) (j : C ≅ D) :
    sigma A (reindex C (projection A)) ≅ sigma B (reindex D (projection B)) where
  hom := productMap i.hom j.hom
  inv := productMap i.inv j.inv
  hom_inv_id := by
    ext x z
    exact congrArg₂ (fun (a : A.obj x) (c : C.obj x) =>
      (⟨a,c⟩ : (sigma A (reindex C (projection A))).obj x))
      (i.hom_inv_id_app_apply x z.1) (j.hom_inv_id_app_apply x z.2)
  inv_hom_id := by
    ext x z
    exact congrArg₂ (fun (b : B.obj x) (d : D.obj x) =>
      (⟨b,d⟩ : (sigma B (reindex D (projection B))).obj x))
      (i.inv_hom_id_app_apply x z.1) (j.inv_hom_id_app_apply x z.2)

def functionCongr {A B C D : Family Γ} (i : A ≅ B) (j : C ≅ D) :
    pi A (reindex C (projection A)) ≅ pi B (reindex D (projection B)) where
  hom := functionMap i.inv j.hom
  inv := functionMap i.hom j.inv
  hom_inv_id := by
    ext x p
    apply PiElement.ext
    intro y h a
    change j.inv.app y (j.hom.app y (p.val h (i.inv.app y (i.hom.app y a)))) = p.val h a
    exact (j.hom_inv_id_app_apply y _).trans
      (congrArg (fun a : A.obj y => (show C.obj y from p.val h a)) (i.hom_inv_id_app_apply y a))
  inv_hom_id := by
    ext x p
    apply PiElement.ext
    intro y h b
    change j.hom.app y (j.inv.app y (p.val h (i.hom.app y (i.inv.app y b)))) = p.val h b
    exact (j.inv_hom_id_app_apply y _).trans
      (congrArg (fun b : B.obj y => (show D.obj y from p.val h b)) (i.inv_hom_id_app_apply y b))

/-- Reindexing compares whole native function fields, including their generalized arguments. -/
def reindexIso (D : Description.{u}) (A : Family Γ) {Δ : Context.{u+1}} (σ : Δ ⟶ Γ) :
    reindex (family D A) σ ≅ family D (reindex A σ) :=
  match D with
  | .carrier => Iso.refl _
  | .fixed _ => Iso.refl _
  | .product D E => productCongr (reindexIso D A σ) (reindexIso E A σ)
  | .function D E =>
    piReindexIso (family D A) (reindex (family E A) (projection (family D A))) σ ≪≫
      functionCongr (reindexIso D A σ) (reindexIso E A σ)

def reindexTerm (D : Description.{u}) {A : Family Γ} (s : Term (family D A))
    {Δ : Context.{u+1}} (σ : Δ ⟶ Γ) : Term (family D (reindex A σ)) :=
  Term.map (reindexIso D A σ).hom (s.reindex σ)

def applyTerm {A B : Family Γ} (f : Term (pi A (reindex B (projection A)))) (a : Term A) : Term B :=
  (app f).reindex (pair (𝟙 Γ) a)

def applyOver {A B : Family Γ} (f : Term (pi A (reindex B (projection A))))
    {Δ : Context.{u+1}} (σ : Δ ⟶ Γ) (a : Term (reindex A σ)) : Term (reindex B σ) :=
  applyTerm (Term.map (piReindex A (reindex B (projection A)) σ) (f.reindex σ)) a

abbrev pathMap := @HomotopyLevels.pathMap
abbrev pathCongr := @HomotopyLevels.pathCongr

/-- Structure preservation compares points, both product fields, and the
application of functions at every generalized source argument. -/
def preserves (D : Description.{u}) {Γ : Context.{u+1}} {A B : Family Γ} (f : A ⟶ B) (g : B ⟶ A)
    (s : Term (family D A)) (t : Term (family D B)) : Family Γ :=
  match D with
  | .carrier => homogeneousPath B (Term.map f s) t
  | .fixed S => homogeneousPath (constantFamily Γ (ULift.{u+1} S)) s t
  | .product D E =>
    let p := preserves D f g (sigmaFst s) (sigmaFst t)
    sigma p (reindex (preserves E f g (sigmaSnd s) (sigmaSnd t)) (projection p))
  | .function D E =>
    let π := projection (family D A)
    let a := generic (family D A)
    let b := Term.map (Functor.whiskerLeft π.mapElements (action D f g)) a
    pi (family D A) (preserves (Γ := total (family D A)) E (Functor.whiskerLeft π.mapElements f)
      (Functor.whiskerLeft π.mapElements g)
      (Term.map (reindexIso E A π).hom (applyOver s π a))
      (Term.map (reindexIso E B π).hom (applyOver t π b)))

noncomputable def preservesFilling (D : Description.{u}) {Γ : Context.{u+1}}
    {A B : Family Γ} (f : A ⟶ B) (g : B ⟶ A)
    (s : Term (family D A)) (t : Term (family D B))
    (FA : Filling A) (hFA : FA.Lawful) (FB : Filling B) (hFB : FB.Lawful) :
    {F : Filling (preserves D f g s t) // F.Lawful} :=
  match D with
  | .carrier =>
    ⟨pathFilling (FB.reindex (projection (interval Γ))) (hFB.reindex _) (Term.map f s) t,
      pathFilling_lawful _ (hFB.reindex _) _ _⟩
  | .fixed S =>
    let F := filling (.fixed S) FB hFB
    ⟨pathFilling (F.1.reindex (projection (interval Γ))) (F.2.reindex _) s t,
      pathFilling_lawful _ (F.2.reindex _) _ _⟩
  | .product D E =>
    let d := preservesFilling D f g (sigmaFst s) (sigmaFst t) FA hFA FB hFB
    let e := preservesFilling E f g (sigmaSnd s) (sigmaSnd t) FA hFA FB hFB
    ⟨sigmaFilling d.1 d.2 (e.1.reindex (projection _)),
      sigmaFilling_lawful d.1 d.2 _ (e.2.reindex _)⟩
  | .function D E =>
    let π := projection (family D A)
    let a := generic (family D A)
    let b := Term.map (Functor.whiskerLeft π.mapElements (action D f g)) a
    let d := filling D FA hFA
    let e := preservesFilling E (Γ := total (family D A))
      (Functor.whiskerLeft π.mapElements f) (Functor.whiskerLeft π.mapElements g)
      (Term.map (reindexIso E A π).hom (applyOver s π a))
      (Term.map (reindexIso E B π).hom (applyOver t π b))
      (FA.reindex π) (hFA.reindex π) (FB.reindex π) (hFB.reindex π)
    ⟨piFilling d.1 d.2 e.1, piFilling_lawful d.1 d.2 e.1 e.2⟩

noncomputable def preservesPresentation (D : Description.{u}) {Γ : Context.{u+1}}
    {A B : Family Γ} (f : A ⟶ B) (g : B ⟶ A)
    (s : Term (family D A)) (t : Term (family D B))
    (PA : SmallUniverse.SmallPresentation.Data A) (PB : SmallUniverse.SmallPresentation.Data B) :
    SmallUniverse.SmallPresentation.Data (preserves D f g s t) :=
  match D with
  | .carrier => SmallUniverse.SmallPresentation.Data.path _
      (smallReindex PB (projection (interval Γ))) (Term.map f s) t
  | .fixed S => SmallUniverse.SmallPresentation.Data.path _
      (smallReindex (presentation (.fixed S) PB) (projection (interval Γ))) s t
  | .product D E =>
    let d := preservesPresentation D f g (sigmaFst s) (sigmaFst t) PA PB
    let e := preservesPresentation E f g (sigmaSnd s) (sigmaSnd t) PA PB
    d.sigma (smallReindex e _)
  | .function D E =>
    let π := projection (family D A)
    let a := generic (family D A)
    let b := Term.map (Functor.whiskerLeft π.mapElements (action D f g)) a
    (presentation D PA).pi (preservesPresentation E (Γ := total (family D A))
      (Functor.whiskerLeft π.mapElements f) (Functor.whiskerLeft π.mapElements g)
      (Term.map (reindexIso E A π).hom (applyOver s π a))
      (Term.map (reindexIso E B π).hom (applyOver t π b))
      (smallReindex PA π) (smallReindex PB π))

/-- At the identity carrier map, recursive preservation is exactly a native
path of all fields. Function paths retain every generalized argument. -/
def identityPathIso (D : Description.{u}) {Γ : Context.{u+1}} {A : Family Γ}
    (s t : Term (family D A)) :
    preserves D (𝟙 A) (𝟙 A) s t ≅ homogeneousPath (family D A) s t :=
  match D with
  | .carrier => Iso.refl _
  | .fixed _ => Iso.refl _
  | .product D E =>
    productCongr (identityPathIso D (sigmaFst s) (sigmaFst t))
      (identityPathIso E (sigmaSnd s) (sigmaSnd t)) ≪≫
      (HomotopyLevels.productPathIso s t).symm
  | .function D E => by
    dsimp only [preserves]
    rw [action_id]
    let π := projection (family D A)
    let a := generic (family D A)
    let cs := applyOver s π a
    let ct := applyOver t π a
    let e := reindexIso E A π
    exact EquivalenceFamilies.piSecondIso (family D A)
      (identityPathIso E (Term.map e.hom cs) (Term.map e.hom ct) ≪≫
        (pathCongr e cs ct).symm) ≪≫ (FunctionPaths.decomposition s t).symm


variable {Δ Θ : Context.{u+1}}

private theorem inv_square {A B C D : Family Γ} (i : A ≅ B) (j : C ≅ D)
    (f : A ⟶ C) (g : B ⟶ D) (h : f ≫ j.hom = i.hom ≫ g) :
    i.inv ≫ f = g ≫ j.inv := by
  calc
    i.inv ≫ f = (i.inv ≫ f ≫ j.hom) ≫ j.inv := by simp
    _ = (i.inv ≫ i.hom ≫ g) ≫ j.inv := by rw [h]
    _ = g ≫ j.inv := by simp

theorem action_reindex (D : Description.{u}) {A B : Family Γ} (f : A ⟶ B) (g : B ⟶ A)
    (σ : Δ ⟶ Γ) :
    Functor.whiskerLeft σ.mapElements (action D f g) ≫ (reindexIso D B σ).hom =
      (reindexIso D A σ).hom ≫ action D (Functor.whiskerLeft σ.mapElements f)
        (Functor.whiskerLeft σ.mapElements g) := by
  induction D generalizing A B with
  | carrier => rfl
  | fixed _ => rfl
  | product D E hD hE =>
    ext x z
    apply Sigma.ext
    · exact congrArg (fun m => m.app x z.1) (hD f g)
    · exact heq_of_eq (congrArg (fun m => m.app x z.2) (hE f g))
  | function D E hD hE =>
    ext x p
    apply PiElement.ext
    intro y h b
    let i := reindexIso D B σ
    let j := reindexIso D A σ
    let f' := Functor.whiskerLeft σ.mapElements (action D g f)
    let g' := action D (Functor.whiskerLeft σ.mapElements g) (Functor.whiskerLeft σ.mapElements f)
    have hd := inv_square i j f' g' (hD g f)
    have he := congrArg (fun m => m.app y
      (p.val (σ.mapElements.map h) ((action D g f).app (σ.mapElements.obj y)
        ((reindexIso D B σ).inv.app y b)))) (hE f g)
    exact he.trans (congrArg
      (fun a => (action E (Functor.whiskerLeft σ.mapElements f)
        (Functor.whiskerLeft σ.mapElements g)).app y
        ((reindexIso E A σ).hom.app y (p.val (σ.mapElements.map h) a)))
      (congrArg (fun m => m.app y b) hd))
theorem reindexIso_comp (D : Description.{u}) (A : Family Γ)
    (σ : Δ ⟶ Γ) (τ : Θ ⟶ Δ) :
    Functor.whiskerLeft τ.mapElements (reindexIso D A σ).hom ≫
      (reindexIso D (reindex A σ) τ).hom = (reindexIso D A (τ ≫ σ)).hom := by
  induction D with
  | carrier => rfl
  | fixed _ => rfl
  | product D E hD hE =>
    ext x z
    apply Sigma.ext
    · exact congrArg (fun m => m.app x z.1) hD
    · exact heq_of_eq (congrArg (fun m => m.app x z.2) hE)
  | function D E hD hE =>
    have hi : Functor.isoWhiskerLeft τ.mapElements (reindexIso D A σ) ≪≫
        reindexIso D (reindex A σ) τ = reindexIso D A (τ ≫ σ) := Iso.ext hD
    have hdi := congrArg Iso.inv hi
    ext x p
    apply PiElement.ext
    intro y h a
    have he := congrArg (fun m => m.app y
      (p.val (σ.mapElements.map (τ.mapElements.map h))
        ((reindexIso D A σ).inv.app (τ.mapElements.obj y)
          ((reindexIso D (reindex A σ) τ).inv.app y a)))) hE
    exact he.trans (congrArg
      (fun b => (reindexIso E A (τ ≫ σ)).hom.app y (p.val ((τ ≫ σ).mapElements.map h) b))
      (congrArg (fun m => m.app y a) hdi))

theorem reindexTerm_comp (D : Description.{u}) {A : Family Γ} (s : Term (family D A))
    (σ : Δ ⟶ Γ) (τ : Θ ⟶ Δ) :
    reindexTerm D (reindexTerm D s σ) τ = reindexTerm D s (τ ≫ σ) := by
  apply Term.ext
  intro x
  exact congrArg (fun m => m.app x (s.val ((τ ≫ σ).mapElements.obj x)))
    (reindexIso_comp D A σ τ)

theorem reindexIso_id (D : Description.{u}) (A : Family Γ) :
    reindexIso D A (𝟙 Γ) = Iso.refl (family D A) := by
  induction D with
  | carrier => rfl
  | fixed _ => rfl
  | product D E hD hE =>
    simp only [reindexIso, hD, hE]
    rfl
  | function D E hD hE =>
    apply Iso.ext
    simp only [reindexIso, hD, hE]
    rfl

theorem reindexTerm_id (D : Description.{u}) {A : Family Γ} (s : Term (family D A)) :
    reindexTerm D s (𝟙 Γ) = s := by
  unfold reindexTerm
  rw [reindexIso_id]
  rfl
theorem reindexIso_comp_map (D : Description.{u}) {A : Family Γ}
    (σ : Δ ⟶ Γ) (τ : Θ ⟶ Δ) (s : Term (reindex (family D A) σ)) :
    reindexTerm D (Term.map (reindexIso D A σ).hom s) τ =
      Term.map (reindexIso D A (τ ≫ σ)).hom (s.reindex τ) := by
  apply Term.ext
  intro x
  exact congrArg (fun m => m.app x (s.val (τ.mapElements.obj x))) (reindexIso_comp D A σ τ)

theorem applyOver_reindexTerm (D E : Description.{u}) {A : Family Γ}
    (f : Term (family (.function D E) A)) (σ : Δ ⟶ Γ) (τ : Θ ⟶ Δ)
    (a : Term (reindex (family D (reindex A σ)) τ)) :
    applyOver (reindexTerm (.function D E) f σ) τ a =
      Term.map (Functor.whiskerLeft τ.mapElements (reindexIso E A σ).hom)
        (applyOver f (τ ≫ σ)
          (Term.map (Functor.whiskerLeft τ.mapElements (reindexIso D A σ).inv) a)) := rfl

theorem applyOver_reindex {A B : Family Γ} (f : Term (pi A (reindex B (projection A))))
    (σ : Δ ⟶ Γ) (τ : Θ ⟶ Δ) (a : Term (reindex A σ)) :
    Term.reindex (applyOver f σ a) τ = applyOver f (τ ≫ σ) (Term.reindex a τ) := rfl

/-- Substitution preserves every field of the independent preservation relation. -/
noncomputable def preservesReindexIso (D : Description.{u}) {Γ Δ : Context.{u+1}}
    {A B : Family Γ} (f : A ⟶ B) (g : B ⟶ A)
    (s : Term (family D A)) (t : Term (family D B)) (σ : Δ ⟶ Γ) :
    reindex (preserves D f g s t) σ ≅
      preserves D (Functor.whiskerLeft σ.mapElements f) (Functor.whiskerLeft σ.mapElements g)
        (reindexTerm D s σ) (reindexTerm D t σ) :=
  match D with
  | .carrier => EquivalenceFamilies.homogeneousReindexIso B (Term.map f s) t σ
  | .fixed S => EquivalenceFamilies.homogeneousReindexIso (constantFamily Γ (ULift.{u+1} S)) s t σ
  | .product D E => productCongr
      (preservesReindexIso D f g (sigmaFst s) (sigmaFst t) σ)
      (preservesReindexIso E f g (sigmaSnd s) (sigmaSnd t) σ)
  | .function D E => by
    let X := family D A
    let X' := family D (reindex A σ)
    let π := projection X
    let π' := projection X'
    let ρ := liftSub X σ
    let e := reindexIso D A σ
    let κ := PiDomain.baseMap e.hom
    let f' := Functor.whiskerLeft σ.mapElements f
    let g' := Functor.whiskerLeft σ.mapElements g
    let s0 := Term.map (reindexIso E A π).hom (applyOver s π (generic X))
    let t0 := Term.map (reindexIso E B π).hom (applyOver t π
      (Term.map (Functor.whiskerLeft π.mapElements (action D f g)) (generic X)))
    let s1 := Term.map (reindexIso E (reindex A σ) π').hom
      (applyOver (reindexTerm (.function D E) s σ) π' (generic X'))
    let t1 := Term.map (reindexIso E (reindex B σ) π').hom
      (applyOver (reindexTerm (.function D E) t σ) π'
        (Term.map (Functor.whiskerLeft π'.mapElements (action D f' g')) (generic X')))
    let j0 := preservesReindexIso E (Functor.whiskerLeft π.mapElements f)
      (Functor.whiskerLeft π.mapElements g) s0 t0 ρ
    let j1 := preservesReindexIso E (Functor.whiskerLeft π'.mapElements f')
      (Functor.whiskerLeft π'.mapElements g') s1 t1 κ
    have hs : reindexTerm E s0 ρ = reindexTerm E s1 κ := by
      dsimp only [s0, s1]
      rw [reindexIso_comp_map, reindexIso_comp_map]
      simp only [applyOver_reindexTerm]
      apply Term.ext
      intro x
      have hc := reindexIso_comp E A σ (κ ≫ π')
      have hd := e.hom_inv_id_app_apply ((projection (reindex X σ)).mapElements.obj x) x.val.2
      let y := (projection (reindex X σ)).mapElements.obj x
      let z := σ.mapElements.obj y
      have hv := congrArg (fun m => m.app x
        ((s.val z).val (𝟙 z) (e.inv.app y (e.hom.app y x.val.2)))) hc
      exact (congrArg (fun a => (reindexIso E A (ρ ≫ π)).hom.app x
        ((s.val z).val (𝟙 z) a)) hd.symm).trans hv.symm
    have ht : reindexTerm E t0 ρ = reindexTerm E t1 κ := by
      dsimp only [t0, t1]
      rw [reindexIso_comp_map, reindexIso_comp_map]
      simp only [applyOver_reindexTerm]
      apply Term.ext
      intro x
      let y := (projection (reindex X σ)).mapElements.obj x
      let z := σ.mapElements.obj y
      let j := reindexIso D B σ
      have hn := congrArg (fun m => m.app y x.val.2) (action_reindex D f g σ)
      have hd : j.inv.app y ((action D f' g').app y (e.hom.app y x.val.2)) =
          (action D f g).app z x.val.2 :=
        (congrArg (j.inv.app y) hn).symm.trans (j.hom_inv_id_app_apply y _)
      have hc := reindexIso_comp E B σ (κ ≫ π')
      have hv := congrArg (fun m => m.app x
        ((t.val z).val (𝟙 z) (j.inv.app y ((action D f' g').app y (e.hom.app y x.val.2))))) hc
      exact (congrArg (fun a => (reindexIso E B (ρ ≫ π)).hom.app x
        ((t.val z).val (𝟙 z) a)) hd.symm).trans hv.symm
    let P := preserves E (Functor.whiskerLeft π'.mapElements f')
      (Functor.whiskerLeft π'.mapElements g') s1 t1
    let j := j0 ≪≫ eqToIso (congrArg₂ (preserves E
      (Functor.whiskerLeft (ρ ≫ π).mapElements f)
      (Functor.whiskerLeft (ρ ≫ π).mapElements g)) hs ht) ≪≫ j1.symm
    exact piReindexIso X (preserves E (Functor.whiskerLeft π.mapElements f)
      (Functor.whiskerLeft π.mapElements g) s0 t0) σ ≪≫
      EquivalenceFamilies.piSecondIso (reindex X σ) j ≪≫ PiDomain.congr e P

/-- Decode the generic equivalence with all of its chosen fiber contractions. -/
noncomputable def genericEquivalence (A B : Family Γ) :
    Σ f : reindex A (projection (EquivalenceFamilies.equiv A B)) ⟶
        reindex B (projection (EquivalenceFamilies.equiv A B)), HomotopyEquivalence f :=
  let π := projection (EquivalenceFamilies.equiv A B)
  (EquivalenceFamilies.equivReindexSections A B π).symm
    (generic (EquivalenceFamilies.equiv A B))

theorem decodeEquivalence_reindex (A B : Family Γ) (σ : Δ ⟶ Γ) (τ : Θ ⟶ Δ)
    (s : Term (reindex (EquivalenceFamilies.equiv A B) σ)) :
    (EquivalenceFamilies.equivReindexSections A B (τ ≫ σ)).symm (Term.reindex s τ) =
      ⟨Functor.whiskerLeft τ.mapElements ((EquivalenceFamilies.equivReindexSections A B σ).symm s).1,
        ((EquivalenceFamilies.equivReindexSections A B σ).symm s).2.reindex τ⟩ := by
  apply (EquivalenceFamilies.equivReindexSections A B (τ ≫ σ)).injective
  exact (Equiv.apply_symm_apply _ _).trans
    ((congrArg (fun t => Term.reindex t τ)
      (Equiv.apply_symm_apply (EquivalenceFamilies.equivReindexSections A B σ) s)).symm.trans
      (EquivalenceFamilies.equivReindexSections_comp A B σ τ _ _).symm)

theorem genericEquivalence_at (A B : Family Γ) (f : A ⟶ B) (E : HomotopyEquivalence f) :
    let σ := pair (A := EquivalenceFamilies.equiv A B) (𝟙 Γ) (EquivalenceFamilies.equivSections A B ⟨f, E⟩)
    (⟨Functor.whiskerLeft σ.mapElements (genericEquivalence A B).1,
        (genericEquivalence A B).2.reindex σ⟩ : Σ g : A ⟶ B, HomotopyEquivalence g) = ⟨f,E⟩ := by
  let σ := pair (A := EquivalenceFamilies.equiv A B) (𝟙 Γ) (EquivalenceFamilies.equivSections A B ⟨f,E⟩)
  have h := decodeEquivalence_reindex A B (projection (EquivalenceFamilies.equiv A B)) σ
    (generic (EquivalenceFamilies.equiv A B))
  refine h.symm.trans ?_
  change (EquivalenceFamilies.equivReindexSections A B (𝟙 Γ)).symm
    (EquivalenceFamilies.equivSections A B ⟨f,E⟩) = ⟨f,E⟩
  rw [← EquivalenceFamilies.equivReindexSections_id A B f E]
  exact Equiv.symm_apply_apply _ _


/-- The field relation over the actual native family of carrier equivalences. -/
noncomputable def equivalenceFields (D : Description.{u}) {A B : Family Γ}
    (s : Term (family D A)) (t : Term (family D B)) :
    Family (total (EquivalenceFamilies.equiv A B)) :=
  let π := projection (EquivalenceFamilies.equiv A B)
  let e := genericEquivalence A B
  preserves D e.1 e.2.selectedInverse (reindexTerm D s π) (reindexTerm D t π)

/-- Structured equivalences carry the native equivalence and independently
defined preservation fields as separate data. -/
noncomputable def equivalences (D : Description.{u}) {A B : Family Γ}
    (s : Term (family D A)) (t : Term (family D B)) : Family Γ :=
  sigma (EquivalenceFamilies.equiv A B) (equivalenceFields D s t)

noncomputable def equivalenceFieldsFilling (D : Description.{u}) {A B : Family Γ}
    (s : Term (family D A)) (t : Term (family D B))
    (FA : Filling A) (hFA : FA.Lawful) (FB : Filling B) (hFB : FB.Lawful) :
    {F : Filling (equivalenceFields D s t) // F.Lawful} :=
  let π := projection (EquivalenceFamilies.equiv A B)
  let e := genericEquivalence A B
  preservesFilling D e.1 e.2.selectedInverse (reindexTerm D s π) (reindexTerm D t π)
    (FA.reindex π) (hFA.reindex π) (FB.reindex π) (hFB.reindex π)

noncomputable def equivalencesFilling (D : Description.{u}) {A B : Family Γ}
    (s : Term (family D A)) (t : Term (family D B))
    (FA : Filling A) (hFA : FA.Lawful) (FB : Filling B) (hFB : FB.Lawful) :
    {F : Filling (equivalences D s t) // F.Lawful} :=
  let e := EquivalenceFamilies.equivFilling FA hFA FB hFB
  let he := EquivalenceFamilies.equivFilling_lawful FA hFA FB hFB
  let p := equivalenceFieldsFilling D s t FA hFA FB hFB
  ⟨sigmaFilling e he p.1, sigmaFilling_lawful e he p.1 p.2⟩

/-- All target fields together with their independent preservation witnesses. -/
def preservationTargets (D : Description.{u}) {A B : Family Γ} (f : A ⟶ B) (g : B ⟶ A)
    (s : Term (family D A)) : Family Γ :=
  let T := family D B
  let π := projection T
  sigma T (preserves D (Functor.whiskerLeft π.mapElements f) (Functor.whiskerLeft π.mapElements g)
    (reindexTerm D s π) (Term.map (reindexIso D B π).hom (generic T)))

noncomputable def preservationTargetsFilling (D : Description.{u}) {A B : Family Γ}
    (f : A ⟶ B) (g : B ⟶ A) (s : Term (family D A))
    (FA : Filling A) (hFA : FA.Lawful) (FB : Filling B) (hFB : FB.Lawful) :
    {F : Filling (preservationTargets D f g s) // F.Lawful} :=
  let T := family D B
  let π := projection T
  let d := filling D FB hFB
  let p := preservesFilling D (Functor.whiskerLeft π.mapElements f)
    (Functor.whiskerLeft π.mapElements g) (reindexTerm D s π)
    (Term.map (reindexIso D B π).hom (generic T))
    (FA.reindex π) (hFA.reindex π) (FB.reindex π) (hFB.reindex π)
  ⟨sigmaFilling d.1 d.2 p.1, sigmaFilling_lawful d.1 d.2 p.1 p.2⟩

/-- The identity fiber contracts through complete field paths. -/
noncomputable def identityTargetsContractible (D : Description.{u}) {A : Family Γ}
    (s : Term (family D A)) : HomotopyContractible (preservationTargets D (𝟙 A) (𝟙 A) s) := by
  let T := family D A
  let π := projection T
  let i := reindexIso D A π
  let j := identityPathIso D (reindexTerm D s π) (Term.map i.hom (generic T)) ≪≫
    (pathCongr i (Term.reindex s π) (generic T)).symm
  exact (NativePathSingleton.contractible s).transport (sigmaSecondIso T j).symm

noncomputable def equivalenceFieldsPresentation (D : Description.{u}) {A B : Family Γ}
    (s : Term (family D A)) (t : Term (family D B))
    (PA : SmallUniverse.SmallPresentation.Data A) (PB : SmallUniverse.SmallPresentation.Data B) :
    SmallUniverse.SmallPresentation.Data (equivalenceFields D s t) :=
  let π := projection (EquivalenceFamilies.equiv A B)
  let e := genericEquivalence A B
  preservesPresentation D e.1 e.2.selectedInverse (reindexTerm D s π) (reindexTerm D t π)
    (smallReindex PA π) (smallReindex PB π)

noncomputable def equivalencesPresentation (D : Description.{u}) {A B : Family Γ}
    (s : Term (family D A)) (t : Term (family D B))
    (PA : SmallUniverse.SmallPresentation.Data A) (PB : SmallUniverse.SmallPresentation.Data B) :
    SmallUniverse.SmallPresentation.Data (equivalences D s t) :=
  (HomotopyLevels.equivPresentation PA PB).sigma (equivalenceFieldsPresentation D s t PA PB)

noncomputable def preservationTargetsPresentation (D : Description.{u}) {A B : Family Γ}
    (f : A ⟶ B) (g : B ⟶ A) (s : Term (family D A))
    (PA : SmallUniverse.SmallPresentation.Data A) (PB : SmallUniverse.SmallPresentation.Data B) :
    SmallUniverse.SmallPresentation.Data (preservationTargets D f g s) :=
  let T := family D B
  let π := projection T
  (presentation D PB).sigma (preservesPresentation D (Functor.whiskerLeft π.mapElements f)
    (Functor.whiskerLeft π.mapElements g) (reindexTerm D s π)
    (Term.map (reindexIso D B π).hom (generic T)) (smallReindex PA π) (smallReindex PB π))

/-- Native structured equivalences themselves have classifier codes and lawful decoders. -/
noncomputable def classifyEquivalences (D : Description.{u})
    (a b : Γ ⟶ smallFamilyCodes.{u})
    (s : Term (family D (SmallUniverse.liftedDecode a)))
    (t : Term (family D (SmallUniverse.liftedDecode b))) :
    SmallUniverse.LargeConstructors.Result (equivalences D s t) :=
  let F := equivalencesFilling D s t (SmallUniverse.NativeDecode.filling a)
    (SmallUniverse.NativeDecode.filling_lawful a) (SmallUniverse.NativeDecode.filling b)
    (SmallUniverse.NativeDecode.filling_lawful b)
  SmallUniverse.LargeConstructors.construct
    (equivalencesPresentation D s t (SmallUniverse.decodePresentation a)
      (SmallUniverse.decodePresentation b)) F.1 F.2

/-- Preservation with all target fields commutes with arbitrary substitution. -/
noncomputable def preservationTargetsReindexIso (D : Description.{u}) {A B : Family Γ}
    (f : A ⟶ B) (g : B ⟶ A) (s : Term (family D A)) (σ : Δ ⟶ Γ) :
    reindex (preservationTargets D f g s) σ ≅
      preservationTargets D (Functor.whiskerLeft σ.mapElements f)
        (Functor.whiskerLeft σ.mapElements g) (reindexTerm D s σ) := by
  let T := family D B
  let T' := family D (reindex B σ)
  let π := projection T
  let π' := projection T'
  let ρ := liftSub T σ
  let e := reindexIso D B σ
  let κ := PiDomain.baseMap e.hom
  let f' := Functor.whiskerLeft σ.mapElements f
  let g' := Functor.whiskerLeft σ.mapElements g
  let s0 := reindexTerm D s π
  let t0 := Term.map (reindexIso D B π).hom (generic T)
  let s1 := reindexTerm D (reindexTerm D s σ) π'
  let t1 := Term.map (reindexIso D (reindex B σ) π').hom (generic T')
  let j0 := preservesReindexIso D (Functor.whiskerLeft π.mapElements f)
    (Functor.whiskerLeft π.mapElements g) s0 t0 ρ
  let j1 := preservesReindexIso D (Functor.whiskerLeft π'.mapElements f')
    (Functor.whiskerLeft π'.mapElements g') s1 t1 κ
  have hs : reindexTerm D s0 ρ = reindexTerm D s1 κ := by
    dsimp only [s0,s1]
    rw [reindexTerm_comp, reindexTerm_comp]
    exact (reindexTerm_comp D s σ (κ ≫ π')).symm
  have ht : reindexTerm D t0 ρ = reindexTerm D t1 κ := by
    dsimp only [t0,t1]
    rw [reindexIso_comp_map, reindexIso_comp_map]
    apply Term.ext
    intro x
    exact (congrArg (fun m => m.app x x.val.2) (reindexIso_comp D B σ (κ ≫ π'))).symm
  let P := preserves D (Functor.whiskerLeft π'.mapElements f')
    (Functor.whiskerLeft π'.mapElements g') s1 t1
  let j := j0 ≪≫ eqToIso (congrArg₂ (preserves D
    (Functor.whiskerLeft (ρ ≫ π).mapElements f)
    (Functor.whiskerLeft (ρ ≫ π).mapElements g)) hs ht) ≪≫ j1.symm
  exact sigmaSecondIso (reindex T σ) j ≪≫ PiDomain.sigmaCongr e P

/-- The carrier projection from the full context of generic structured objects. -/
def objectBase (D : Description.{u}) (Γ : Context.{u+1}) :
    total (objects D Γ) ⟶ total (SmallUniverse.family Γ) :=
  FiberwiseHomotopyRetracts.totalPoint ≫ projection
    (family D (SmallUniverse.liftedDecode (SmallUniverse.code (generic (SmallUniverse.family Γ)))))

def objectCarrierCode (D : Description.{u}) (Γ : Context.{u+1}) :
    total (objects D Γ) ⟶ smallFamilyCodes.{u} :=
  objectBase D Γ ≫ SmallUniverse.code (generic (SmallUniverse.family Γ))

def objectCarrier (D : Description.{u}) (Γ : Context.{u+1}) : Family (total (objects D Γ)) :=
  SmallUniverse.liftedDecode (objectCarrierCode D Γ)

def objectStructure (D : Description.{u}) (Γ : Context.{u+1}) :
    Term (family D (objectCarrier D Γ)) :=
  let A := SmallUniverse.liftedDecode (SmallUniverse.code (generic (SmallUniverse.family Γ)))
  Term.map (reindexIso D A (objectBase D Γ)).hom
    (Term.reindex (generic (family D A)) FiberwiseHomotopyRetracts.totalPoint)

def objectOf (D : Description.{u}) (a : Γ ⟶ smallFamilyCodes.{u})
    (s : Term (family D (SmallUniverse.liftedDecode a))) : Term (objects D Γ) :=
  let A := SmallUniverse.liftedDecode (SmallUniverse.code (generic (SmallUniverse.family Γ)))
  let σ := pair (A := SmallUniverse.family Γ) (𝟙 Γ) (SmallUniverse.term a)
  sigmaIntro (SmallUniverse.term a) (Term.map (reindexIso D A σ).inv s)

theorem objectStructure_at (D : Description.{u}) (a : Γ ⟶ smallFamilyCodes.{u})
    (s : Term (family D (SmallUniverse.liftedDecode a))) :
    reindexTerm D (objectStructure D Γ) (pair (𝟙 Γ) (objectOf D a s)) = s := by
  apply Term.ext
  intro x
  let A := SmallUniverse.liftedDecode (SmallUniverse.code (generic (SmallUniverse.family Γ)))
  let σ := pair (A := SmallUniverse.family Γ) (𝟙 Γ) (SmallUniverse.term a)
  let κ := pair (A := objects D Γ) (𝟙 Γ) (objectOf D a s)
  let i := reindexIso D A σ
  have h := congrArg (fun m => m.app x (i.inv.app x (s.val x)))
    (reindexIso_comp D A (objectBase D Γ) κ)
  exact h.trans (i.inv_hom_id_app_apply x (s.val x))


/-- For a strict carrier isomorphism, independent preservation compares the
complete transported fields with the target structure. -/
def preservesActionPathIso (D : Description.{u}) {Γ : Context.{u+1}}
    {A B : Family Γ} (k : A ≅ B) (s : Term (family D A)) (t : Term (family D B)) :
    preserves D k.hom k.inv s t ≅
      homogeneousPath (family D B) (Term.map (actionIso D k).hom s) t :=
  match D with
  | .carrier => Iso.refl _
  | .fixed _ => Iso.refl _
  | .product D E =>
    productCongr (preservesActionPathIso D k (sigmaFst s) (sigmaFst t))
      (preservesActionPathIso E k (sigmaSnd s) (sigmaSnd t)) ≪≫
      (HomotopyLevels.productPathIso (Term.map (actionIso (.product D E) k).hom s) t).symm
  | .function D E => by
    let X := family D A
    let Y := family D B
    let π := projection X
    let e := actionIso D k
    let κ := PiDomain.baseMap e.hom
    let f := Term.map (actionIso (.function D E) k).hom s
    let C := reindex (family E B) (projection Y)
    let P := homogeneousPath C (app f) (app t)
    let i := reindexIso E B π
    let cs := Term.map (reindexIso E A π).hom (applyOver s π (generic X))
    let ct := Term.map i.hom (applyOver t π
      (Term.map (Functor.whiskerLeft π.mapElements e.hom) (generic X)))
    let j0 := preservesActionPathIso E (Functor.isoWhiskerLeft π.mapElements k) cs ct
    have hs : Term.map (actionIso E (Functor.isoWhiskerLeft π.mapElements k)).hom cs =
        Term.map i.hom (Term.reindex (app f) κ) := by
      apply Term.ext
      intro z
      let y := π.mapElements.obj z
      have ha := congrArg (fun m => m.app z ((s.val y).val (𝟙 y) z.val.2))
        (action_reindex E k.hom k.inv π)
      have hb := congrArg (fun a => i.hom.app z
        ((action E k.hom k.inv).app y ((s.val y).val (𝟙 y) a)))
        (e.hom_inv_id_app_apply y z.val.2)
      exact ha.symm.trans hb.symm
    have ht : ct = Term.map i.hom (Term.reindex (app t) κ) := rfl
    let j := j0 ≪≫ eqToIso (congrArg₂ (homogeneousPath (family E (reindex B π))) hs ht) ≪≫
      (pathCongr i (Term.reindex (app f) κ) (Term.reindex (app t) κ)).symm ≪≫
      (EquivalenceFamilies.homogeneousReindexIso C (app f) (app t) κ).symm
    exact EquivalenceFamilies.piSecondIso X j ≪≫ PiDomain.congr e P ≪≫
      (FunctionPaths.decomposition f t).symm

/-- Over a native set target, preservation is a native proposition. The
carrier maps remain arbitrary and the source requires no sethood witness. -/
noncomputable def preservesIsProp (D : Description.{u}) {Γ : Context.{u+1}} {A B : Family Γ}
    (f : A ⟶ B) (g : B ⟶ A) (s : Term (family D A)) (t : Term (family D B))
    (sB : Term (HomotopyLevels.isSet B))
    (FA : Filling A) (hFA : FA.Lawful) (FB : Filling B) (hFB : FB.Lawful) :
    Term (HomotopyLevels.isProp (preserves D f g s t)) :=
  match D with
  | .carrier => HomotopyLevels.pathIsPropAt sB (Term.map f s) t
  | .fixed S => HomotopyLevels.pathIsPropAt (HomotopyLevels.constantIsSet (ULift.{u+1} S)) s t
  | .product D E =>
    let d := preservesFilling D f g (sigmaFst s) (sigmaFst t) FA hFA FB hFB
    let e := preservesFilling E f g (sigmaSnd s) (sigmaSnd t) FA hFA FB hFB
    HomotopyLevels.productIsProp
      (preservesIsProp D f g (sigmaFst s) (sigmaFst t) sB FA hFA FB hFB)
      (preservesIsProp E f g (sigmaSnd s) (sigmaSnd t) sB FA hFA FB hFB)
      d.1 d.2 e.1 e.2
  | .function D E =>
    let π := projection (family D A)
    let a := generic (family D A)
    let b := Term.map (Functor.whiskerLeft π.mapElements (action D f g)) a
    let s' := Term.map (reindexIso E A π).hom (applyOver s π a)
    let t' := Term.map (reindexIso E B π).hom (applyOver t π b)
    let f' := Functor.whiskerLeft π.mapElements f
    let g' := Functor.whiskerLeft π.mapElements g
    let d := filling D FA hFA
    let e := preservesFilling E f' g' s' t' (FA.reindex π) (hFA.reindex π)
      (FB.reindex π) (hFB.reindex π)
    HomotopyLevels.piIsProp
      (preservesIsProp E f' g' s' t' (HomotopyLevels.reindexSet sB π)
        (FA.reindex π) (hFA.reindex π) (FB.reindex π) (hFB.reindex π))
      d.1 d.2 e.1 e.2

noncomputable def equivalenceFieldsIsProp (D : Description.{u}) {Γ : Context.{u+1}} {A B : Family Γ}
    (s : Term (family D A)) (t : Term (family D B))
    (sB : Term (HomotopyLevels.isSet B))
    (FA : Filling A) (hFA : FA.Lawful) (FB : Filling B) (hFB : FB.Lawful) :
    Term (HomotopyLevels.isProp (equivalenceFields D s t)) :=
  let π := projection (EquivalenceFamilies.equiv A B)
  let e := genericEquivalence A B
  preservesIsProp D e.1 e.2.selectedInverse (reindexTerm D s π) (reindexTerm D t π)
    (HomotopyLevels.reindexSet sB π) (FA.reindex π) (hFA.reindex π) (FB.reindex π) (hFB.reindex π)

/-- Specializing the native equivalence family retains the supplied map and
its complete contractible-fiber witness. -/
noncomputable def suppliedEquivalenceFiberIso (D : Description.{u}) {A B : Family Γ}
    (f : A ⟶ B) (E : HomotopyEquivalence f) (s : Term (family D A)) (t : Term (family D B)) :
    reindex (equivalenceFields D s t)
      (pair (A := EquivalenceFamilies.equiv A B) (𝟙 Γ) (EquivalenceFamilies.equivSections A B ⟨f,E⟩)) ≅
      preserves D f E.selectedInverse s t := by
  let π := projection (EquivalenceFamilies.equiv A B)
  let τ := pair (A := EquivalenceFamilies.equiv A B) (𝟙 Γ) (EquivalenceFamilies.equivSections A B ⟨f,E⟩)
  let e : Σ g : A ⟶ B, HomotopyEquivalence g :=
    ⟨Functor.whiskerLeft τ.mapElements (genericEquivalence A B).1,
      (genericEquivalence A B).2.reindex τ⟩
  have he : e = ⟨f,E⟩ := genericEquivalence_at A B f E
  have hi : e.2.selectedInverse =
      Functor.whiskerLeft τ.mapElements (genericEquivalence A B).2.selectedInverse := by
    ext x b
    rfl
  have hs : reindexTerm D (reindexTerm D s π) τ = s :=
    (reindexTerm_comp D s π τ).trans (reindexTerm_id D s)
  have ht : reindexTerm D (reindexTerm D t π) τ = t :=
    (reindexTerm_comp D t π τ).trans (reindexTerm_id D t)
  refine preservesReindexIso D (genericEquivalence A B).1 (genericEquivalence A B).2.selectedInverse
    (reindexTerm D s π) (reindexTerm D t π) τ ≪≫ eqToIso ?_
  refine (congrArg₂ (preserves D e.1
    (Functor.whiskerLeft τ.mapElements (genericEquivalence A B).2.selectedInverse)) hs ht).trans ?_
  exact (congrArg (fun g => preserves D e.1 g s t) hi.symm).trans
    (congrArg (fun e : Σ g : A ⟶ B, HomotopyEquivalence g => preserves D e.1 e.2.selectedInverse s t) he)

def objectsReindexIso (D : Description.{u}) (σ : Δ ⟶ Γ) :
    reindex (objects D Γ) σ ≅ objects D Δ :=
  sigmaSecondIso (SmallUniverse.family Δ)
    (reindexIso D (SmallUniverse.liftedDecode (SmallUniverse.code (generic (SmallUniverse.family Γ))))
      (liftSub (SmallUniverse.family Γ) σ))

theorem objectOf_reindex (D : Description.{u}) (a : Γ ⟶ smallFamilyCodes.{u})
    (s : Term (family D (SmallUniverse.liftedDecode a))) (σ : Δ ⟶ Γ) :
    Term.map (objectsReindexIso D σ).hom (Term.reindex (objectOf D a s) σ) =
      objectOf D (σ ≫ a) (reindexTerm D s σ) := by
  let U := SmallUniverse.family Γ
  let A := SmallUniverse.liftedDecode (SmallUniverse.code (generic U))
  let ρ := liftSub U σ
  let α := pair (A := U) (𝟙 Γ) (SmallUniverse.term a)
  let β := pair (A := SmallUniverse.family Δ) (𝟙 Δ) (SmallUniverse.term (σ ≫ a))
  let i := Functor.isoWhiskerLeft σ.mapElements (reindexIso D A α)
  let j := reindexIso D (reindex A ρ) β
  let h := Functor.whiskerLeft β.mapElements (reindexIso D A ρ).hom
  let k := (reindexIso D (SmallUniverse.liftedDecode a) σ).hom
  have sq : h ≫ j.hom = i.hom ≫ k :=
    (reindexIso_comp D A ρ β).trans (reindexIso_comp D A α σ).symm
  have q := inv_square i j h k sq
  apply Term.ext
  intro x
  apply Sigma.ext
  · rfl
  · exact heq_of_eq (congrArg (fun m => m.app x (s.val (σ.mapElements.obj x))) q)


theorem decodeEquivalence_reindexIso (A B : Family Γ) (σ : Δ ⟶ Γ) (τ : Θ ⟶ Δ)
    (s : Term (reindex (EquivalenceFamilies.equiv A B) (τ ≫ σ))) :
    (EquivalenceFamilies.equivReindexSections (reindex A σ) (reindex B σ) τ).symm
      (Term.map (Functor.whiskerLeft τ.mapElements (EquivalenceFamilies.equivReindexIso A B σ).hom) s) =
        (EquivalenceFamilies.equivReindexSections A B (τ ≫ σ)).symm s :=
  (congrArg (EquivalenceFamilies.equivReindexSections (reindex A σ) (reindex B σ) τ).symm
    (EquivalenceFamilies.equivReindexIso_hom_reindex_sections A B σ τ s)).trans
    (Equiv.symm_apply_apply _ _)

noncomputable def equivalencesReindexIso (D : Description.{u}) {A B : Family Γ}
    (s : Term (family D A)) (t : Term (family D B)) (σ : Δ ⟶ Γ) :
    reindex (equivalences D s t) σ ≅
      equivalences D (reindexTerm D s σ) (reindexTerm D t σ) := by
  let C := EquivalenceFamilies.equiv A B
  let C' := EquivalenceFamilies.equiv (reindex A σ) (reindex B σ)
  let π := projection C
  let π' := projection C'
  let π₀ := projection (reindex C σ)
  let ρ := liftSub C σ
  let e := EquivalenceFamilies.equivReindexIso A B σ
  let κ := PiDomain.baseMap e.hom
  let E := genericEquivalence A B
  let E' := genericEquivalence (reindex A σ) (reindex B σ)
  let E₀ : Σ f : reindex A (π₀ ≫ σ) ⟶ reindex B (π₀ ≫ σ), HomotopyEquivalence f :=
    ⟨Functor.whiskerLeft ρ.mapElements E.1, E.2.reindex ρ⟩
  let E₁ : Σ f : reindex A (π₀ ≫ σ) ⟶ reindex B (π₀ ≫ σ), HomotopyEquivalence f :=
    ⟨Functor.whiskerLeft κ.mapElements E'.1, E'.2.reindex κ⟩
  have h₀ : (EquivalenceFamilies.equivReindexSections A B (π₀ ≫ σ)).symm
      (generic (reindex C σ)) = E₀ :=
    decodeEquivalence_reindex A B π ρ (generic C)
  have h₁ : (EquivalenceFamilies.equivReindexSections (reindex A σ) (reindex B σ) π₀).symm
      (Term.map (Functor.whiskerLeft π₀.mapElements e.hom) (generic (reindex C σ))) = E₁ :=
    decodeEquivalence_reindex (reindex A σ) (reindex B σ) π' κ (generic C')
  have he : E₀ = E₁ := by
    have h := congrArg
      (EquivalenceFamilies.equivReindexSections (reindex A σ) (reindex B σ) π₀).symm
      (EquivalenceFamilies.equivReindexIso_hom_reindex_sections A B σ π₀ (generic (reindex C σ)))
    exact h₀.symm.trans ((h.trans (Equiv.symm_apply_apply _ _)).symm.trans h₁)
  have hi₀ : E₀.2.selectedInverse = Functor.whiskerLeft ρ.mapElements E.2.selectedInverse := by
    ext x b
    rfl
  have hi₁ : E₁.2.selectedInverse = Functor.whiskerLeft κ.mapElements E'.2.selectedInverse := by
    ext x b
    rfl
  let s₀ := reindexTerm D s π
  let t₀ := reindexTerm D t π
  let s₁ := reindexTerm D (reindexTerm D s σ) π'
  let t₁ := reindexTerm D (reindexTerm D t σ) π'
  have hs : reindexTerm D s₀ ρ = reindexTerm D s₁ κ := by
    dsimp only [s₀, s₁]
    rw [reindexTerm_comp, reindexTerm_comp]
    exact (reindexTerm_comp D s σ (κ ≫ π')).symm
  have ht : reindexTerm D t₀ ρ = reindexTerm D t₁ κ := by
    dsimp only [t₀, t₁]
    rw [reindexTerm_comp, reindexTerm_comp]
    exact (reindexTerm_comp D t σ (κ ≫ π')).symm
  let j₀ := preservesReindexIso D E.1 E.2.selectedInverse s₀ t₀ ρ
  let j₁ := preservesReindexIso D E'.1 E'.2.selectedInverse s₁ t₁ κ
  have hp : preserves D (Functor.whiskerLeft ρ.mapElements E.1)
        (Functor.whiskerLeft ρ.mapElements E.2.selectedInverse)
        (reindexTerm D s₀ ρ) (reindexTerm D t₀ ρ) =
      preserves D (Functor.whiskerLeft κ.mapElements E'.1)
        (Functor.whiskerLeft κ.mapElements E'.2.selectedInverse)
        (reindexTerm D s₁ κ) (reindexTerm D t₁ κ) := by
    rw [← hi₀, ← hi₁, hs, ht]
    exact congrArg (fun e : Σ f : reindex A (π₀ ≫ σ) ⟶ reindex B (π₀ ≫ σ), HomotopyEquivalence f =>
      preserves D e.1 e.2.selectedInverse (reindexTerm D s₁ κ) (reindexTerm D t₁ κ)) he
  exact sigmaSecondIso (reindex C σ) (j₀ ≪≫ eqToIso hp ≪≫ j₁.symm) ≪≫
    PiDomain.sigmaCongr e (equivalenceFields D (reindexTerm D s σ) (reindexTerm D t σ))

theorem objectOf_eta (D : Description.{u}) (z : Term (objects D Γ)) :
    let A := SmallUniverse.liftedDecode (SmallUniverse.code (generic (SmallUniverse.family Γ)))
    let τ := pair (A := SmallUniverse.family Γ) (𝟙 Γ) (sigmaFst z)
    objectOf D (SmallUniverse.code (sigmaFst z))
      (Term.map (reindexIso D A τ).hom (sigmaSnd z)) = z := by
  let A := SmallUniverse.liftedDecode (SmallUniverse.code (generic (SmallUniverse.family Γ)))
  let τ := pair (A := SmallUniverse.family Γ) (𝟙 Γ) (sigmaFst z)
  apply Term.ext
  intro x
  apply Sigma.ext
  · rfl
  · change HEq ((reindexIso D A τ).inv.app x
        ((reindexIso D A τ).hom.app x (z.val x).2)) (z.val x).2
    exact heq_of_eq ((reindexIso D A τ).hom_inv_id_app_apply x (z.val x).2)

end SquareKit.Cubical.Presheaf.StructureIdentity.Native
