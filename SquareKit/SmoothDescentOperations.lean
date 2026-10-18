import SquareKit.SmoothPrincipalDescent

/-! Experimental smooth-operation and arbitrary-base-map laws for scalar descent. -/
noncomputable section
namespace SquareKit.SmoothAlgebra.PrincipalCover
open PresentedLocalization
variable {n m k : ℕ}

abbrev Sections (r : Fin m → Free n) (p : Fin k → Free n) :=
  {a : ∀ i, Carrier r (p i) // Compatible r p a}

def restrict (r : Fin m → Free n) (p : Fin k → Free n) (a : Presentation.Carrier r) : Sections r p :=
  ⟨fun i => base r (p i) a,fun i j => by
    exact (congrArg (fun h : Hom (Presentation.Carrier r) (Carrier r (p i*p j)) => h a)
      (overlapLeft_base r (p i) (p j))).trans
        (congrArg (fun h : Hom (Presentation.Carrier r) (Carrier r (p i*p j)) => h a)
          (overlapRight_base r (p i) (p j))).symm⟩

def glue (r : Fin m → Free n) (p : Fin k → Free n)
    (hs : Covers (fun i => Presentation.projection r (p i))) (a : Sections r p) : Presentation.Carrier r :=
  (exists_unique r p hs a.val a.property).choose

theorem glue_spec (r : Fin m → Free n) (p : Fin k → Free n)
    (hs : Covers (fun i => Presentation.projection r (p i))) (a : Sections r p) (i : Fin k) :
    base r (p i) (glue r p hs a) = a.val i := (exists_unique r p hs a.val a.property).choose_spec.1 i

def descentEquiv (r : Fin m → Free n) (p : Fin k → Free n)
    (hs : Covers (fun i => Presentation.projection r (p i))) : Presentation.Carrier r ≃ Sections r p where
  toFun := restrict r p
  invFun := glue r p hs
  left_inv a := separated r p hs _ _ (fun i => glue_spec r p hs (restrict r p a) i)
  right_inv a := Subtype.ext (funext (glue_spec r p hs a))

/-- Finite smooth operations act componentwise on compatible sections. -/
def sectionAct (r : Fin m → Free n) (p : Fin k → Free n) {l : ℕ}
    (f : Operation l) (a : Fin l → Sections r p) : Sections r p :=
  ⟨fun i => act f (fun j => (a j).val i),fun i j => by
    rw [(overlapLeft r (p i) (p j)).map_act,(overlapRight r (p i) (p j)).map_act]
    congr 1
    funext v
    exact (a v).property i j⟩

/-- Gluing preserves every finite-arity smooth operation, including nullary operations. -/
theorem glue_act (r : Fin m → Free n) (p : Fin k → Free n)
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

variable {u v : ℕ}

theorem map_overlapLeft (r : Fin m → Free n) (p q : Free n)
    (t : Fin v → Free u) (P Q : Free u) (h : Hom (Presentation.Carrier r) (Presentation.Carrier t))
    (hp : h (Presentation.projection r p)=Presentation.projection t P)
    (hq : h (Presentation.projection r q)=Presentation.projection t Q) :
    Hom.comp (map r (p*q) t (P*Q) h (by rw [(Presentation.projection r).map_mul,h.map_mul,hp,hq,(Presentation.projection t).map_mul]))
      (overlapLeft r p q) = Hom.comp (overlapLeft t P Q) (map r p t P h hp) := by
  apply unique r p
  rw [← Hom.comp_assoc,overlapLeft_base,map_base,← Hom.comp_assoc,map_base,Hom.comp_assoc,overlapLeft_base]

theorem map_overlapRight (r : Fin m → Free n) (p q : Free n)
    (t : Fin v → Free u) (P Q : Free u) (h : Hom (Presentation.Carrier r) (Presentation.Carrier t))
    (hp : h (Presentation.projection r p)=Presentation.projection t P)
    (hq : h (Presentation.projection r q)=Presentation.projection t Q) :
    Hom.comp (map r (p*q) t (P*Q) h (by rw [(Presentation.projection r).map_mul,h.map_mul,hp,hq,(Presentation.projection t).map_mul]))
      (overlapRight r p q) = Hom.comp (overlapRight t P Q) (map r q t Q h hq) := by
  apply unique r q
  rw [← Hom.comp_assoc,overlapRight_base,map_base,← Hom.comp_assoc,map_base,Hom.comp_assoc,overlapRight_base]

def transport (r : Fin m → Free n) (p : Fin k → Free n) (t : Fin v → Free u) (q : Fin k → Free u)
    (h : Hom (Presentation.Carrier r) (Presentation.Carrier t))
    (he : ∀ i, h (Presentation.projection r (p i))=Presentation.projection t (q i))
    (a : Sections r p) : Sections t q :=
  ⟨fun i => map r (p i) t (q i) h (he i) (a.val i),fun i j => by
    have hl := congrArg (fun k : Hom (Carrier r (p i)) (Carrier t (q i*q j)) => k (a.val i))
      (map_overlapLeft r (p i) (p j) t (q i) (q j) h (he i) (he j))
    have hr := congrArg (fun k : Hom (Carrier r (p j)) (Carrier t (q i*q j)) => k (a.val j))
      (map_overlapRight r (p i) (p j) t (q i) (q j) h (he i) (he j))
    exact hl.symm.trans ((congrArg _ (a.property i j)).trans hr)⟩

theorem transported_cover (r : Fin m → Free n) (p : Fin k → Free n) (t : Fin v → Free u) (q : Fin k → Free u)
    (h : Hom (Presentation.Carrier r) (Presentation.Carrier t))
    (he : ∀ i, h (Presentation.projection r (p i))=Presentation.projection t (q i))
    (hs : Covers (fun i => Presentation.projection r (p i))) : Covers (fun i => Presentation.projection t (q i)) := by
  simpa only [he] using map_covers h _ hs

/-- Descent commutes with every smooth map of the presented algebras. -/
theorem glue_natural (r : Fin m → Free n) (p : Fin k → Free n) (t : Fin v → Free u) (q : Fin k → Free u)
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

end SquareKit.SmoothAlgebra.PrincipalCover
