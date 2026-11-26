import SquareKit.StructureIdentity.Descriptions
import SquareKit.Internal.Cubical.CartesianUniverse
import SquareKit.Internal.Cubical.CartesianLargeFamilyConstructors

/-! Native interpretation of structure descriptions, with fixed-small-universe
admission and recovery at explicitly presented carriers. -/
set_option autoImplicit false
set_option warningAsError true
namespace SquareKit.Cubical.Cartesian.StructureIdentity.Native
open CategoryTheory SquareKit.StructureIdentity SmallUniverse
universe u
variable {Γ : Context.{u+1}}

def family (D : Description.{u}) (A : Family Γ) : Family Γ :=
  match D with
  | .carrier => A
  | .fixed S => constantFamily Γ (ULift.{u+1} S)
  | .product D E => sigma (family D A) (reindex (family E A) (projection (family D A)))
  | .function D E => pi (family D A) (reindex (family E A) (projection (family D A)))

noncomputable def filling (D : Description.{u}) {A : Family Γ} (F : Filling A) (hF : F.Lawful) :
    {G : Filling (family D A) // G.Lawful} :=
  match D with
  | .carrier => ⟨F,hF⟩
  | .fixed _ => ⟨presentedFilling (Iso.refl _), presentedFilling_lawful (Iso.refl _)⟩
  | .product D E =>
    let d := filling D F hF
    let e := filling E F hF
    ⟨sigmaFilling d.1 d.2 (e.1.reindex (projection (family D A))),
      sigmaFilling_lawful d.1 d.2 _ (e.2.reindex _)⟩
  | .function D E =>
    let d := filling D F hF
    let e := filling E F hF
    ⟨piFilling d.1 d.2 (e.1.reindex (projection (family D A))),
      piFilling_lawful d.1 d.2 _ (e.2.reindex _)⟩

def smallReindex {Δ : Context.{u+1}} {A : Family Γ} (P : SmallPresentation.Data A)
    (σ : Δ ⟶ Γ) : SmallPresentation.Data (reindex A σ) where
  Fiber x := P.Fiber (σ.mapElements.obj x)
  equiv x := P.equiv (σ.mapElements.obj x)

noncomputable def presentation (D : Description.{u}) {A : Family Γ} (P : SmallPresentation.Data A) :
    SmallPresentation.Data (family D A) :=
  match D with
  | .carrier => P
  | .fixed S => ⟨fun _ => S, fun _ => Equiv.ulift.symm⟩
  | .product D E => (presentation D P).sigma (smallReindex (presentation E P) _)
  | .function D E => (presentation D P).pi (smallReindex (presentation E P) _)

def functionEquiv {A B : Family Γ} {S T : Type (u+1)}
    (i : A ≅ constantFamily Γ S) (j : B ≅ constantFamily Γ T) (x : Γ.Elements) :
    (pi A (reindex B (projection A))).obj x ≃ (S → T) where
  toFun p s := j.hom.app x (p.val (𝟙 x) (i.inv.app x s))
  invFun g := {
    val := fun {y} _ a => j.inv.app y (g (i.hom.app y a))
    naturality := fun {y z} f h a => by
      change B.map h (j.inv.app y (g (i.hom.app y a))) = j.inv.app z (g (i.hom.app z (A.map h a)))
      exact (j.inv.naturality_apply h _).symm.trans
        (congrArg (fun z => j.inv.app _ (g z)) (i.hom.naturality_apply h a).symm) }
  left_inv p := by
    apply PiElement.ext
    intro y f a
    let a₀ := i.inv.app x (i.hom.app y a)
    have ha : A.map f a₀ = a := by
      change A.map f (i.inv.app x (i.hom.app y a)) = a
      exact (i.inv.naturality_apply f _).symm.trans
        (congrArg (fun k => k.app y a) i.hom_inv_id)
    have hp := p.naturality (𝟙 x) f a₀
    change B.map f (p.val (𝟙 x) a₀) = p.val (𝟙 x ≫ f) (A.map f a₀) at hp
    rw [Category.id_comp, ha] at hp
    change j.inv.app y (j.hom.app x (p.val (𝟙 x) a₀)) = p.val f a
    exact (congrArg (j.inv.app y) (j.hom.naturality_apply f (p.val (𝟙 x) a₀)).symm).trans
      ((congrArg (fun k => k.app y (B.map f (p.val (𝟙 x) a₀))) j.hom_inv_id).trans hp)
  right_inv g := by
    funext s
    change j.hom.app x (j.inv.app x (g (i.hom.app x (i.inv.app x s)))) = g s
    have hi := congrArg (fun k => k.app x s) i.inv_hom_id
    have hj := congrArg (fun k => k.app x (g s)) j.inv_hom_id
    change i.hom.app x (i.inv.app x s) = s at hi
    rw [hi]
    exact hj

def functionIso {A B : Family Γ} {S T : Type (u+1)}
    (i : A ≅ constantFamily Γ S) (j : B ≅ constantFamily Γ T) :
    pi A (reindex B (projection A)) ≅ constantFamily Γ (S → T) :=
  NatIso.ofComponents (fun x => (functionEquiv i j x).toIso) (by
    intro x y f
    apply ConcreteCategory.hom_ext
    intro p
    funext s
    have hp := p.naturality (𝟙 x) f (i.inv.app x s)
    have hi := (i.inv.naturality_apply f s).symm
    change B.map f (p.val (𝟙 x) (i.inv.app x s)) =
      p.val (𝟙 x ≫ f) (A.map f (i.inv.app x s)) at hp
    rw [Category.id_comp, hi] at hp
    change j.hom.app y (p.val (f ≫ 𝟙 y) (i.inv.app y s)) = j.hom.app x (p.val (𝟙 x) (i.inv.app x s))
    rw [Category.comp_id]
    exact (congrArg (j.hom.app y) hp.symm).trans (j.hom.naturality_apply f _))

def constantIso {S T : Type (u+1)} (e : S ≃ T) :
    constantFamily Γ S ≅ constantFamily Γ T :=
  NatIso.ofComponents (fun _ => e.toIso) (fun _ => rfl)

def productEquiv {A B : Family Γ} {S T : Type u}
    (i : A ≅ constantFamily Γ (ULift.{u+1} S))
    (j : B ≅ constantFamily Γ (ULift.{u+1} T)) (x : Γ.Elements) :
    (sigma A (reindex B (projection A))).obj x ≃ ULift.{u+1} (S × T) where
  toFun z := ⟨(i.hom.app x z.1).down, (j.hom.app x z.2).down⟩
  invFun z := ⟨i.inv.app x ⟨z.down.1⟩, j.inv.app x ⟨z.down.2⟩⟩
  left_inv z := by
    apply Sigma.ext
    · exact congrArg (fun k => k.app x z.1) i.hom_inv_id
    · exact heq_of_eq (congrArg (fun k => k.app x z.2) j.hom_inv_id)
  right_inv z := by
    have hi := congrArg (fun k => k.app x (ULift.up z.down.1 : ULift.{u+1} S)) i.inv_hom_id
    have hj := congrArg (fun k => k.app x (ULift.up z.down.2 : ULift.{u+1} T)) j.inv_hom_id
    exact congrArg₂ (fun (s : ULift.{u+1} S) (t : ULift.{u+1} T) =>
      (ULift.up (s.down,t.down) : ULift.{u+1} (S × T))) hi hj

def productIso {A B : Family Γ} {S T : Type u}
    (i : A ≅ constantFamily Γ (ULift.{u+1} S))
    (j : B ≅ constantFamily Γ (ULift.{u+1} T)) :
    sigma A (reindex B (projection A)) ≅ constantFamily Γ (ULift.{u+1} (S × T)) :=
  NatIso.ofComponents (fun x => (productEquiv i j x).toIso) (by
    intro x y f
    apply ConcreteCategory.hom_ext
    intro z
    exact congrArg₂ (fun (s : ULift.{u+1} S) (t : ULift.{u+1} T) =>
      (ULift.up (s.down,t.down) : ULift.{u+1} (S × T)))
      (i.hom.naturality_apply f z.1) (j.hom.naturality_apply f z.2))

def presentedIso (D : Description.{u}) {A : Family Γ} {X : Type u}
    (i : A ≅ constantFamily Γ (ULift.{u+1} X)) :
    family D A ≅ constantFamily Γ (ULift.{u+1} (D.Data X)) :=
  match D with
  | .carrier => i
  | .fixed _ => Iso.refl _
  | .product D E => productIso (presentedIso D i) (presentedIso E i)
  | .function D E => functionIso (presentedIso D i) (presentedIso E i) ≪≫
    constantIso ((Equiv.arrowCongr Equiv.ulift Equiv.ulift).trans Equiv.ulift.symm)

noncomputable def classify (D : Description.{u}) (a : Γ ⟶ smallFamilyCodes.{u}) :
    LargeConstructors.Result (family D (liftedDecode a)) :=
  let F := filling D (NativeDecode.filling a) (NativeDecode.filling_lawful a)
  LargeConstructors.construct (presentation D (decodePresentation a)) F.1 F.2

/-- Structures over the generic small carrier; no constant presentation is assumed. -/
noncomputable def universal (D : Description.{u}) :
    LargeConstructors.Result (family D (liftedDecode (𝟙 smallFamilyCodes.{u}))) :=
  classify D (𝟙 _)

/-- The large total family contains a carrier code together with its structure.
It is not asserted to be a code in that same small universe. -/
def objects (D : Description.{u}) (Γ : Context.{u+1}) : Family Γ :=
  sigma (SmallUniverse.family Γ)
    (family D (liftedDecode (SmallUniverse.code (generic (SmallUniverse.family Γ)))))

noncomputable def objectsFilling (D : Description.{u}) (Γ : Context.{u+1}) :
    {F : Filling (objects D Γ) // F.Lawful} :=
  let c := SmallUniverse.code (generic (SmallUniverse.family Γ))
  let s := filling D (NativeDecode.filling c) (NativeDecode.filling_lawful c)
  ⟨sigmaFilling (SmallUniverse.filling Γ) (SmallUniverse.filling_lawful Γ) s.1,
    sigmaFilling_lawful _ (SmallUniverse.filling_lawful Γ) _ s.2⟩

end SquareKit.Cubical.Cartesian.StructureIdentity.Native
