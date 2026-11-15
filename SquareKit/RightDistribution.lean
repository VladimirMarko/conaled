import SquareKit.DistributionMap

/-! Right distribution is left distribution for reversed product choices.
The chosen raw inverse stays separate from its laws. -/
namespace SquareKit
universe u v
variable {O : Type u} {C : CategoryOps.{u,v} O} {E : HomEquiv C}

namespace ProductOps

def reverse (P : ProductOps C) : ProductOps C where
  prod a b := P.prod b a
  fst := P.snd
  snd := P.fst
  pair f g := P.pair g f

theorem reverse_congr {P : ProductOps C} (PC : ProductCongr E P) :
    ProductCongr E P.reverse := ⟨fun hf hg => PC.pair hg hf⟩

theorem reverse_laws {P : ProductOps C} (PL : ProductLaws E P) :
    ProductLaws E P.reverse := ⟨fun f g => PL.snd_pair g f,
      fun f g => PL.fst_pair g f, fun f => PL.pair_eta f⟩

def swap (P : ProductOps C) {a b : O} : C.Hom (P.prod a b) (P.prod b a) :=
  P.pair P.snd P.fst

variable (P : ProductOps C) (CC : CategoryCongr C E) (CL : CategoryLaws C E)
variable (PC : ProductCongr E P) (PL : ProductLaws E P)

include CC CL PC PL in
theorem swap_pair {a b x : O} (f : C.Hom x a) (g : C.Hom x b) :
    E.Rel (C.comp P.swap (P.pair f g)) (P.pair g f) :=
  E.trans (PL.pair_comp CC CL PC _ _ _)
    (PC.pair (PL.snd_pair _ _) (PL.fst_pair _ _))

include CC CL PC PL in
theorem swap_swap (a b : O) :
    E.Rel (C.comp (P.swap (a := b) (b := a)) P.swap) C.ident := by
  apply E.trans (P.swap_pair CC CL PC PL _ _)
  exact E.trans (PC.pair (E.symm (CL.comp_id _)) (E.symm (CL.comp_id _)))
    (PL.pair_eta _)

def symmetry (a b : O) : Comparison C (P.prod a b) (P.prod b a) := ⟨P.swap, P.swap⟩

include CC CL PC PL in
theorem symmetry_laws (a b : O) : ComparisonLaws E (P.symmetry a b) :=
  ⟨P.swap_swap CC CL PC PL b a, P.swap_swap CC CL PC PL a b⟩
end ProductOps

/-- An independently selected inverse for `(b + c) × a`. -/
abbrev RightDistributionOps (P : ProductOps C) (S : CoproductOps C) :=
  DistributionOps C P.reverse S

abbrev collectRight (P : ProductOps C) (S : CoproductOps C) {a b c : O} :=
  collect C P.reverse S (a := a) (b := b) (c := c)

abbrev RightDistributionLaws (P : ProductOps C) (S : CoproductOps C)
    (d : RightDistributionOps P S) := DistributionLaws C E P.reverse S d

namespace DistributionOps
variable {P : ProductOps C} {S : CoproductOps C}

/-- Swap the input, distribute on the left, then swap each output branch. -/
def right (d : DistributionOps C P S) : RightDistributionOps P S where
  distribute := C.comp (S.map P.swap P.swap) (C.comp d.distribute P.swap)

variable (CC : CategoryCongr C E) (CL : CategoryLaws C E)
variable (PC : ProductCongr E P) (PL : ProductLaws E P)
variable (SC : CoproductCongr C E S) (SL : CoproductLaws C E S)

/- Canonical right collection is the conjugate of canonical left collection. -/
include CC CL PC PL SC SL in
theorem collectRight_eq (a b c : O) :
    E.Rel (collectRight P S (a := a) (b := b) (c := c))
      (C.comp P.swap (C.comp (collect C P S) (S.map P.swap P.swap))) := by
  apply E.symm
  apply E.trans (CC.comp (E.refl _) (DistributionMap.collect_map CC CL SC SL _ _))
  apply E.trans (SL.comp_copair CC CL SC _ _ _)
  apply SC.copair
  · apply E.trans (CC.comp (E.refl _) (PL.pair_comp CC CL PC _ _ _))
    apply E.trans (P.swap_pair CC CL PC PL _ _)
    exact PC.pair
      (E.trans (CL.assoc _ _ _) (CC.comp (E.refl _) (PL.snd_pair _ _)))
      (PL.fst_pair _ _)
  · apply E.trans (CC.comp (E.refl _) (PL.pair_comp CC CL PC _ _ _))
    apply E.trans (P.swap_pair CC CL PC PL _ _)
    exact PC.pair
      (E.trans (CL.assoc _ _ _) (CC.comp (E.refl _) (PL.snd_pair _ _)))
      (PL.fst_pair _ _)

include CC CL PC PL SC SL in
theorem right_laws {d : DistributionOps C P S} (D : DistributionLaws C E P S d) :
    RightDistributionLaws (E := E) P S d.right := by
  have h (a b c : O) : ComparisonLaws E
      (((P.symmetry (S.sum b c) a).comp
        (⟨d.distribute, collect C P S⟩ : Comparison C _ _)).comp
          (Comparison.coproduct S (P.symmetry a b) (P.symmetry a c))) :=
    Comparison.comp_laws CC CL
      (Comparison.comp_laws CC CL (P.symmetry_laws CC CL PC PL _ _)
        ⟨D.distribute_collect a b c, D.collect_distribute a b c⟩)
      (Comparison.coproduct_laws CC CL SC SL
        (P.symmetry_laws CC CL PC PL _ _) (P.symmetry_laws CC CL PC PL _ _))
  constructor
  · intro a b c
    apply E.trans (CC.comp (collectRight_eq CC CL PC PL SC SL a b c) (E.refl _))
    apply E.trans (CC.comp (E.symm (CL.assoc _ _ _)) (E.refl _))
    exact (h a b c).inv_hom
  · intro a b c
    apply E.trans (CC.comp (E.refl _) (collectRight_eq CC CL PC PL SC SL a b c))
    apply E.trans (CC.comp (E.refl _) (E.symm (CL.assoc _ _ _)))
    exact (h a b c).hom_inv

/- A separately supplied lawful right inverse agrees with the derived one
under semantic equivalence; raw representatives need not be equal. -/
include CC CL PC PL SC SL in
theorem right_unique {d : DistributionOps C P S} (D : DistributionLaws C E P S d)
    {r : RightDistributionOps P S}
    (R : ∀ a b c, E.Rel (C.comp (r.distribute (a := a) (b := b) (c := c))
      (collectRight P S)) C.ident) (a b c : O) :
    E.Rel (r.distribute (a := a) (b := b) (c := c)) d.right.distribute :=
  Comparison.inverse_unique CC CL (R a b c)
    ((right_laws CC CL PC PL SC SL D).collect_distribute a b c)
end DistributionOps

namespace ProductMap
universe w z
variable {Q : Type w} {D : CategoryOps.{w,z} Q} {F : RawMap C D}
variable {P : ProductOps C} {T : ProductOps D}

def reverse (i : ProductMap F P T) : ProductMap F P.reverse T.reverse := fun a b => i b a

theorem reverse_laws {H : HomEquiv D} {i : ProductMap F P T} (M : ProductMapLaws H i) :
    ProductMapLaws H i.reverse := ⟨M.snd, M.fst, fun f g => M.pair g f⟩
end ProductMap

namespace RightDistributionMap
universe w z
variable {Q : Type w} {D : CategoryOps.{w,z} Q} {F : RawMap C D} {H : HomEquiv D}
variable {P : ProductOps C} {T : ProductOps D} {S : CoproductOps C} {U : CoproductOps D}
variable {i : ProductMap F P T} {j : CoproductMap F S U}

/-- Lawful right choices are preserved by product and coproduct preservation.
No additional right-distribution field or reflection is needed. -/
theorem of_laws (DC : CategoryCongr D H) (DL : CategoryLaws D H)
    (TC : ProductCongr H T) (TL : ProductLaws H T)
    (UC : CoproductCongr D H U) (UL : CoproductLaws D H U)
    (L : MapLaws F E H) (M : ProductMapLaws H i) (N : CoproductMapLaws H j)
    (I : ∀ a b, ComparisonLaws H (i a b)) (J : ∀ a b, ComparisonLaws H (j a b))
    {d : RightDistributionOps P S} {e : RightDistributionOps T U}
    (V : RightDistributionLaws (E := E) P S d)
    (W : RightDistributionLaws (E := H) T U e) :
    DistributionMapLaws H i.reverse j d e :=
  DistributionMap.of_laws DC DL (ProductOps.reverse_congr TC) (ProductOps.reverse_laws TL)
    UC UL L (ProductMap.reverse_laws M) N (fun a b => I b a) J
    V.distribute_collect W.collect_distribute
end RightDistributionMap
end SquareKit
