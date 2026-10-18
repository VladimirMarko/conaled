import SquareKit.SmoothOpenDescent
import SquareKit.SmoothElementDescent

/-! Experimental arbitrary-family descent equivalences and smooth operation/base-map
laws. Shared sections, overlaps and transport retain the finite-family APIs. -/
noncomputable section
namespace SquareKit.SmoothAlgebra.OpenCover
open PresentedLocalization PrincipalCover
variable {n m u v : ℕ} {ι : Type*}

def glue (r : Fin m → Free n) (p : ι → Free n)
    (hs : Covers (fun i => Presentation.projection r (p i))) (a : Sections r p) : Presentation.Carrier r :=
  (exists_unique r p hs a.val a.property).choose

theorem glue_spec (r : Fin m → Free n) (p : ι → Free n)
    (hs : Covers (fun i => Presentation.projection r (p i))) (a : Sections r p) (i : ι) :
    base r (p i) (glue r p hs a) = a.val i := (exists_unique r p hs a.val a.property).choose_spec.1 i

def descentEquiv (r : Fin m → Free n) (p : ι → Free n)
    (hs : Covers (fun i => Presentation.projection r (p i))) : Presentation.Carrier r ≃ Sections r p where
  toFun := restrict r p
  invFun := glue r p hs
  left_inv a := separated r p hs _ _ (fun i => glue_spec r p hs (restrict r p a) i)
  right_inv a := Subtype.ext (funext (glue_spec r p hs a))

/-- Finite smooth operations act componentwise on compatible sections. -/

theorem glue_act (r : Fin m → Free n) (p : ι → Free n)
    (hs : Covers (fun i => Presentation.projection r (p i))) {l : ℕ}
    (f : Operation l) (a : Fin l → Sections r p) :
    glue r p hs (sectionAct r p f a) = act f (fun j => glue r p hs (a j)) := by
  apply separated r p hs
  intro i
  rw [glue_spec,(base r (p i)).map_act]
  change act f (fun j => (a j).val i) = _
  congr 1
  funext j
  exact (glue_spec r p hs (a j) i).symm

theorem transported_cover (r : Fin m → Free n) (p : ι → Free n) (t : Fin v → Free u) (q : ι → Free u)
    (h : Hom (Presentation.Carrier r) (Presentation.Carrier t))
    (he : ∀ i, h (Presentation.projection r (p i))=Presentation.projection t (q i))
    (hs : Covers (fun i => Presentation.projection r (p i))) : Covers (fun i => Presentation.projection t (q i)) := by
  simpa only [he] using map_covers h _ hs

/-- Descent commutes with every smooth map of the presented algebras. -/

theorem glue_natural (r : Fin m → Free n) (p : ι → Free n) (t : Fin v → Free u) (q : ι → Free u)
    (h : Hom (Presentation.Carrier r) (Presentation.Carrier t))
    (he : ∀ i, h (Presentation.projection r (p i))=Presentation.projection t (q i))
    (hs : Covers (fun i => Presentation.projection r (p i))) (a : Sections r p) :
    h (glue r p hs a) = glue t q (transported_cover r p t q h he hs) (transport r p t q h he a) := by
  apply separated t q (transported_cover r p t q h he hs)
  intro i
  rw [glue_spec]
  have hb := congrArg (fun k : Hom (Presentation.Carrier r) (Carrier t (q i)) => k (glue r p hs a))
    (map_base r (p i) t (q i) h (he i))
  change map r (p i) t (q i) h (he i) (base r (p i) (glue r p hs a)) = _ at hb
  rw [glue_spec] at hb
  exact hb.symm

private theorem rep_cover (r : Fin m → Free n) (s : ι → Presentation.Carrier r) (hs : Covers s) :
    Covers (fun i => Presentation.projection r (representative r (s i))) := by simpa using hs

/-- Scalar descent on all-element localizations and their actual overlaps. -/

def atDescentEquiv (r : Fin m → Free n) (s : ι → Presentation.Carrier r) (hs : Covers s) :
    Presentation.Carrier r ≃ AtSections r s :=
  (descentEquiv r (fun i => representative r (s i)) (rep_cover r s hs)).trans
    {toFun := fun a => ⟨a.val,(atCompatible_iff r s a.val).mpr a.property⟩
     invFun := fun a => ⟨a.val,(atCompatible_iff r s a.val).mp a.property⟩
     left_inv := fun _ => rfl
     right_inv := fun _ => rfl}

theorem at_glue_spec (r : Fin m → Free n) (s : ι → Presentation.Carrier r) (hs : Covers s)
    (a : AtSections r s) (i : ι) : atBase r (s i) ((atDescentEquiv r s hs).symm a)=a.val i :=
  glue_spec r (fun j => representative r (s j)) (rep_cover r s hs)
    ⟨a.val,(atCompatible_iff r s a.val).mp a.property⟩ i

theorem at_separated (r : Fin m → Free n) (s : ι → Presentation.Carrier r) (hs : Covers s)
    (a b : Presentation.Carrier r) (he : ∀ i, atBase r (s i) a=atBase r (s i) b) : a=b :=
  separated r (fun i => representative r (s i)) (rep_cover r s hs) a b he

theorem at_restrict_act (r : Fin m → Free n) (s : ι → Presentation.Carrier r) (hs : Covers s)
    {l : ℕ} (f : Operation l) (a : Fin l → Presentation.Carrier r) :
    atDescentEquiv r s hs (act f a) = atSectionAct r s f (fun j => atDescentEquiv r s hs (a j)) := by
  apply Subtype.ext
  funext i
  exact (atBase r (s i)).map_act f a

theorem at_glue_act (r : Fin m → Free n) (s : ι → Presentation.Carrier r) (hs : Covers s)
    {l : ℕ} (f : Operation l) (a : Fin l → AtSections r s) :
    (atDescentEquiv r s hs).symm (atSectionAct r s f a) =
      act f (fun j => (atDescentEquiv r s hs).symm (a j)) := by
  apply at_separated r s hs
  intro i
  rw [at_glue_spec,(atBase r (s i)).map_act]
  change act f (fun j => (a j).val i) = _
  congr 1
  funext j
  exact (at_glue_spec r s hs (a j) i).symm

theorem at_glue_natural (r : Fin m → Free n) (s : ι → Presentation.Carrier r) (hs : Covers s)
    (t : Fin v → Free u) (h : Hom (Presentation.Carrier r) (Presentation.Carrier t)) (a : AtSections r s) :
    h ((atDescentEquiv r s hs).symm a) =
      (atDescentEquiv t (fun i => h (s i)) (map_covers h s hs)).symm (atTransport r s t h a) := by
  apply at_separated t (fun i => h (s i)) (map_covers h s hs)
  intro i
  rw [at_glue_spec t (fun i => h (s i)) (map_covers h s hs) (atTransport r s t h a) i,atTransport_apply]
  have hb := congrArg (fun k : Hom (Presentation.Carrier r) (At t (h (s i))) => k ((atDescentEquiv r s hs).symm a))
    (map_base r (representative r (s i)) t (representative t (h (s i))) h (by simp))
  change atMap r (s i) t h (atBase r (s i) ((atDescentEquiv r s hs).symm a)) = _ at hb
  rw [at_glue_spec] at hb
  exact hb.symm

end SquareKit.SmoothAlgebra.OpenCover
