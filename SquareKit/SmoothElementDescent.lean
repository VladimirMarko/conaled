import SquareKit.SmoothDescentOperations

/-! Experimental scalar descent stated on arbitrary elements of a finite presentation.
Overlaps are the existing all-element localizations at the actual products. -/
noncomputable section
namespace SquareKit.SmoothAlgebra.PrincipalCover
open PresentedLocalization
variable {n m k : ℕ}

private theorem product_rep (r : Fin m → Free n) (s t : Presentation.Carrier r) :
    Presentation.projection r (representative r s*representative r t)=s*t := by
  rw [(Presentation.projection r).map_mul,representative_eq,representative_eq]

def productComparison (r : Fin m → Free n) (s t : Presentation.Carrier r) :
    Hom (Carrier r (representative r s*representative r t)) (At r (s*t)) :=
  toChosen r (s*t) _ (product_rep r s t)

def productComparisonInv (r : Fin m → Free n) (s t : Presentation.Carrier r) :
    Hom (At r (s*t)) (Carrier r (representative r s*representative r t)) :=
  fromChosen r (s*t) _ (product_rep r s t)

theorem productComparison_inv (r : Fin m → Free n) (s t : Presentation.Carrier r) :
    Hom.comp (productComparisonInv r s t) (productComparison r s t) = Hom.ident := chosen_inverse _ _ _ _
theorem productComparison_inv_rev (r : Fin m → Free n) (s t : Presentation.Carrier r) :
    Hom.comp (productComparison r s t) (productComparisonInv r s t) = Hom.ident := inverse_chosen _ _ _ _

def atLeft (r : Fin m → Free n) (s t : Presentation.Carrier r) : Hom (At r s) (At r (s*t)) :=
  Hom.comp (productComparison r s t) (overlapLeft r (representative r s) (representative r t))
def atRight (r : Fin m → Free n) (s t : Presentation.Carrier r) : Hom (At r t) (At r (s*t)) :=
  Hom.comp (productComparison r s t) (overlapRight r (representative r s) (representative r t))

theorem atLeft_base (r : Fin m → Free n) (s t : Presentation.Carrier r) :
    Hom.comp (atLeft r s t) (atBase r s)=atBase r (s*t) := by
  unfold atLeft atBase
  rw [← Hom.comp_assoc,overlapLeft_base]
  exact compare_base r (representative r s*representative r t) (representative r (s*t)) ((product_rep r s t).trans (representative_eq r (s*t)).symm)
theorem atRight_base (r : Fin m → Free n) (s t : Presentation.Carrier r) :
    Hom.comp (atRight r s t) (atBase r t)=atBase r (s*t) := by
  unfold atRight atBase
  rw [← Hom.comp_assoc,overlapRight_base]
  exact compare_base r (representative r s*representative r t) (representative r (s*t)) ((product_rep r s t).trans (representative_eq r (s*t)).symm)

/-- These actual product localizations are algebra pushouts, hence geometric pullbacks. -/
theorem at_overlap_pushout {B : Type*} [CommRing B] [Algebra ℝ B] [Structure B]
    (r : Fin m → Free n) (s t : Presentation.Carrier r) (u : Hom (At r s) B) (v : Hom (At r t) B)
    (hc : Hom.comp u (atBase r s)=Hom.comp v (atBase r t)) :
    ∃! h : Hom (At r (s*t)) B, Hom.comp h (atLeft r s t)=u ∧ Hom.comp h (atRight r s t)=v := by
  obtain ⟨h,hl,hr⟩ := overlap_pushout r (representative r s) (representative r t) u v hc
  refine ⟨Hom.comp h (productComparisonInv r s t),⟨?_,?_⟩,?_⟩
  · unfold atLeft
    rw [Hom.comp_assoc,← Hom.comp_assoc (productComparison r s t) (productComparisonInv r s t) h,productComparison_inv,Hom.comp_ident]
    exact hl.1
  · unfold atRight
    rw [Hom.comp_assoc,← Hom.comp_assoc (productComparison r s t) (productComparisonInv r s t) h,productComparison_inv,Hom.comp_ident]
    exact hl.2
  · intro j hj
    have he : Hom.comp j (productComparison r s t)=h := hr _ (by
      constructor
      · rw [← Hom.comp_assoc]; exact hj.1
      · rw [← Hom.comp_assoc]; exact hj.2)
    calc
      j = Hom.comp (Hom.comp j (productComparison r s t)) (productComparisonInv r s t) := by
        rw [← Hom.comp_assoc,productComparison_inv_rev,Hom.comp_ident]
      _ = _ := by rw [he]

def AtCompatible {ι : Type*} (r : Fin m → Free n) (s : ι → Presentation.Carrier r) (a : ∀ i, At r (s i)) : Prop :=
  ∀ i j, atLeft r (s i) (s j) (a i)=atRight r (s i) (s j) (a j)

theorem atCompatible_iff {ι : Type*} (r : Fin m → Free n) (s : ι → Presentation.Carrier r) (a : ∀ i, At r (s i)) :
    AtCompatible r s a ↔ Compatible r (fun i => representative r (s i)) a := by
  constructor
  · intro ha i j
    have he := congrArg (productComparisonInv r (s i) (s j)) (ha i j)
    have hi := congrArg (fun h : Hom (Carrier r (representative r (s i)*representative r (s j)))
      (Carrier r (representative r (s i)*representative r (s j))) => h)
      (productComparison_inv r (s i) (s j))
    exact congrArg (fun h => h (overlapLeft r (representative r (s i)) (representative r (s j)) (a i))) hi |>.symm.trans
      (he.trans (congrArg (fun h => h (overlapRight r (representative r (s i)) (representative r (s j)) (a j))) hi))
  · intro ha i j
    exact congrArg (productComparison r (s i) (s j)) (ha i j)

abbrev AtSections {ι : Type*} (r : Fin m → Free n) (s : ι → Presentation.Carrier r) :=
  {a : ∀ i, At r (s i) // AtCompatible r s a}

private theorem rep_cover (r : Fin m → Free n) (s : Fin k → Presentation.Carrier r) (hs : Covers s) :
    Covers (fun i => Presentation.projection r (representative r (s i))) := by simpa using hs

/-- Scalar descent on all-element localizations and their actual overlaps. -/
def atDescentEquiv (r : Fin m → Free n) (s : Fin k → Presentation.Carrier r) (hs : Covers s) :
    Presentation.Carrier r ≃ AtSections r s :=
  (descentEquiv r (fun i => representative r (s i)) (rep_cover r s hs)).trans
    {toFun := fun a => ⟨a.val,(atCompatible_iff r s a.val).mpr a.property⟩
     invFun := fun a => ⟨a.val,(atCompatible_iff r s a.val).mp a.property⟩
     left_inv := fun _ => rfl
     right_inv := fun _ => rfl}

theorem at_glue_spec (r : Fin m → Free n) (s : Fin k → Presentation.Carrier r) (hs : Covers s)
    (a : AtSections r s) (i : Fin k) : atBase r (s i) ((atDescentEquiv r s hs).symm a)=a.val i :=
  glue_spec r (fun j => representative r (s j)) (rep_cover r s hs)
    ⟨a.val,(atCompatible_iff r s a.val).mp a.property⟩ i

theorem at_separated (r : Fin m → Free n) (s : Fin k → Presentation.Carrier r) (hs : Covers s)
    (a b : Presentation.Carrier r) (he : ∀ i, atBase r (s i) a=atBase r (s i) b) : a=b :=
  separated r (fun i => representative r (s i)) (rep_cover r s hs) a b he

def atSectionAct {ι : Type*} (r : Fin m → Free n) (s : ι → Presentation.Carrier r) {l : ℕ}
    (f : Operation l) (a : Fin l → AtSections r s) : AtSections r s :=
  ⟨fun i => act f (fun j => (a j).val i),fun i j => by
    rw [(atLeft r (s i) (s j)).map_act,(atRight r (s i) (s j)).map_act]
    congr 1
    funext v
    exact (a v).property i j⟩

theorem at_restrict_act (r : Fin m → Free n) (s : Fin k → Presentation.Carrier r) (hs : Covers s)
    {l : ℕ} (f : Operation l) (a : Fin l → Presentation.Carrier r) :
    atDescentEquiv r s hs (act f a) = atSectionAct r s f (fun j => atDescentEquiv r s hs (a j)) := by
  apply Subtype.ext
  funext i
  exact (atBase r (s i)).map_act f a

theorem at_glue_act (r : Fin m → Free n) (s : Fin k → Presentation.Carrier r) (hs : Covers s)
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

variable {u v : ℕ}

def atTransport {ι : Type*} (r : Fin m → Free n) (s : ι → Presentation.Carrier r)
    (t : Fin v → Free u) (h : Hom (Presentation.Carrier r) (Presentation.Carrier t))
    (a : AtSections r s) : AtSections t (fun i => h (s i)) := by
  let b := transport r (fun i => representative r (s i)) t (fun i => representative t (h (s i))) h
    (fun i => by simp) ⟨a.val,(atCompatible_iff r s a.val).mp a.property⟩
  exact ⟨b.val,(atCompatible_iff t (fun i => h (s i)) b.val).mpr b.property⟩

theorem atTransport_apply {ι : Type*} (r : Fin m → Free n) (s : ι → Presentation.Carrier r)
    (t : Fin v → Free u) (h : Hom (Presentation.Carrier r) (Presentation.Carrier t))
    (a : AtSections r s) (i : ι) :
    (atTransport r s t h a).val i=atMap r (s i) t h (a.val i) := rfl

/-- Arbitrary smooth base maps commute with the all-element gluing equivalence. -/
theorem at_glue_natural (r : Fin m → Free n) (s : Fin k → Presentation.Carrier r) (hs : Covers s)
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


end SquareKit.SmoothAlgebra.PrincipalCover
