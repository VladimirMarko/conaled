import SquareKit.Internal.PathTransport.ComparisonHorizontalSignature

/-! An ordinary groupoid cylinder for a selected signature isomorphism.
The projection is an equivalence; the signature being compared need not be. -/
noncomputable section
namespace SquareKit.Internal.PathTransport.GroupoidModel.Comparison
open CategoryTheory CategoryTheory.Functor
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
universe u

namespace SignatureCylinder
variable {C D : Grpd.{u,u}} (F : C ⥤ D)

structure Object where
  source : C
  target : D
  arrow : F.obj source ≅ target

abbrev Cylinder := InducedCategory C (Object.source (F := F))

def projection : Cylinder F ⥤ C := inducedFunctor _

def inclusion : C ⥤ Cylinder F where
  obj c := ⟨c, F.obj c, Iso.refl _⟩
  map f := InducedCategory.homMk f

def equivalence : Cylinder F ≌ C where
  functor := projection F
  inverse := inclusion F
  unitIso := NatIso.ofComponents (fun x => InducedCategory.isoMk (Iso.refl x.source))
  counitIso := Iso.refl _

instance : (projection F).IsEquivalence := (equivalence F).isEquivalence_functor

def evaluation : Cylinder F ⥤ D where
  obj x := x.target
  map {x y} f := x.arrow.inv ≫ F.map f.hom ≫ y.arrow.hom
  map_id x := by simp
  map_comp {x y z} f g := by simp

def endpoint {G : C ⥤ D} (η : F ≅ G) : C ⥤ Cylinder F where
  obj c := ⟨c, G.obj c, η.app c⟩
  map f := InducedCategory.homMk f

@[simp] theorem endpoint_projection {G : C ⥤ D} (η : F ≅ G) :
    endpoint F η ⋙ projection F = 𝟭 C := rfl

@[simp] theorem inclusion_projection : inclusion F ⋙ projection F = 𝟭 C := rfl

@[simp] theorem endpoint_evaluation {G : C ⥤ D} (η : F ≅ G) :
    endpoint F η ⋙ evaluation F = G := by
  fapply CategoryTheory.Functor.ext
  · intro c; rfl
  intro x y f
  dsimp [endpoint, evaluation]
  rw [η.hom.naturality f]
  simp

@[simp] theorem inclusion_evaluation : inclusion F ⋙ evaluation F = F := by
  fapply CategoryTheory.Functor.ext
  · intro c; rfl
  intro x y f
  simp [inclusion, evaluation]

/-- The unique cylinder arrow above the identity retains the supplied component. -/
def endpointIso {G : C ⥤ D} (η : F ≅ G) : inclusion F ≅ endpoint F η :=
  NatIso.ofComponents (fun c => InducedCategory.isoMk (Iso.refl c)) (by
    intro x y f
    apply InducedCategory.hom_ext
    simp [inclusion, endpoint])

@[simp] theorem endpointIso_evaluation {G : C ⥤ D} (η : F ≅ G) (c : C) :
    (evaluation F).map ((endpointIso F η).hom.app c) = η.hom.app c := by
  simp [evaluation, endpointIso, inclusion, endpoint]

variable (P : C ⥤ Type u) (Q : D ⥤ Type u) (α : P ⟶ F ⋙ Q)

def projectionSignature : Signature.{u} :=
  ⟨⟨Grpd.of (Cylinder F), C, projection F⟩, projection F ⋙ P, P, 𝟙 _⟩

def inclusionSignature : Signature.{u} :=
  ⟨⟨C, Grpd.of (Cylinder F), inclusion F⟩, P, projection F ⋙ P, 𝟙 _⟩

def endpointSignature {G : C ⥤ D} (η : F ≅ G) : Signature.{u} :=
  ⟨⟨C, Grpd.of (Cylinder F), endpoint F η⟩, P, projection F ⋙ P, 𝟙 _⟩

def evaluationFiber : projection F ⋙ P ⟶ evaluation F ⋙ Q where
  app x := α.app x.source ≫ Q.map x.arrow.hom
  naturality {x y} f := by
    change P.map f.hom ≫ (α.app y.source ≫ Q.map y.arrow.hom) =
      (α.app x.source ≫ Q.map x.arrow.hom) ≫
        Q.map (x.arrow.inv ≫ F.map f.hom ≫ y.arrow.hom)
    rw [← Category.assoc, α.naturality]
    simp only [Functor.comp_map, Q.map_comp, Category.assoc]
    rw [← Q.map_comp_assoc, x.arrow.hom_inv_id]
    simp

def evaluationSignature : Signature.{u} :=
  ⟨⟨Grpd.of (Cylinder F), D, evaluation F⟩, projection F ⋙ P, Q, evaluationFiber F P Q α⟩

theorem signature_eq {C D : Grpd.{u,u}} {P : C ⥤ Type u} {Q : D ⥤ Type u}
    {F G : C ⥤ D} {α : P ⟶ F ⋙ Q} {β : P ⟶ G ⋙ Q}
    (h : F = G) (hα : α ≫ eqToHom (congrArg (fun K => K ⋙ Q) h) = β) :
    (⟨⟨C, D, F⟩, P, Q, α⟩ : Signature) = ⟨⟨C, D, G⟩, P, Q, β⟩ := by
  cases h
  simp only [eqToHom_refl, Category.comp_id] at hα
  cases hα
  rfl

theorem inclusion_evaluation_signature :
    (inclusionSignature F P).horizontal (evaluationSignature F P Q α) rfl HEq.rfl =
      (⟨⟨C, D, F⟩, P, Q, α⟩ : Signature) := by
  apply signature_eq (inclusion_evaluation F)
  apply NatTrans.ext
  funext c
  simp [evaluationFiber, inclusion]

theorem endpoint_evaluation_signature {G : C ⥤ D} (η : F ≅ G) :
    (endpointSignature F P η).horizontal (evaluationSignature F P Q α) rfl HEq.rfl =
      (⟨⟨C, D, G⟩, P, Q, α ≫ whiskerRight η.hom Q⟩ : Signature) := by
  apply signature_eq (endpoint_evaluation F η)
  apply NatTrans.ext
  funext c
  simp [evaluationFiber, endpoint]

end SignatureCylinder
end SquareKit.Internal.PathTransport.GroupoidModel.Comparison
