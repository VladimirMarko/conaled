import SquareKit.CartesianInverses
import SquareKit.OptionalComparison

/-! Derived Cartesian preservation retains the selected comparison arrows. -/
namespace SquareKit.CartesianPreservation
universe u v w z
open Cartesian
variable {O : Type u} {Q : Type w} {C : CategoryOps.{u,v} O} {D : CategoryOps.{w,z} Q}
variable {E : HomEquiv C} {H : HomEquiv D} {F : RawMap C D}
variable {P : ProductOps C} {T : ProductOps D} {i : ProductMap F P T}
variable (DC : CategoryCongr D H) (DL : CategoryLaws D H)
variable (TC : ProductCongr H T) (TL : ProductLaws H T)
variable (FL : MapLaws F E H) (IL : ProductMapLaws H i)
local instance {a b : Q} : IsPreorder (D.Hom a b) H.Rel where
  refl := H.refl
  trans _ _ _ := H.trans
attribute [local gcongr] CategoryCongr.comp ProductCongr.pair Cartesian.tensor_congr
attribute [local refl] HomEquiv.refl

include DC FL in
theorem map_comp3 {a0 a1 a2 a3 : O} (f1 : C.Hom a0 a1) (f2 : C.Hom a1 a2) (f3 : C.Hom a2 a3) :
    H.Rel (F.map (C.comp f3 (C.comp f2 f1))) (D.comp (F.map f3) (D.comp (F.map f2) (F.map f1))) := by
  repeat grw [FL.comp]

include DC FL in
theorem map_comp4 {a0 a1 a2 a3 a4 : O} (f1 : C.Hom a0 a1) (f2 : C.Hom a1 a2) (f3 : C.Hom a2 a3) (f4 : C.Hom a3 a4) :
    H.Rel (F.map (C.comp f4 (C.comp f3 (C.comp f2 f1)))) (D.comp (F.map f4) (D.comp (F.map f3) (D.comp (F.map f2) (F.map f1)))) := by
  repeat grw [FL.comp]

include DC FL in
theorem map_comp5 {a0 a1 a2 a3 a4 a5 : O} (f1 : C.Hom a0 a1) (f2 : C.Hom a1 a2) (f3 : C.Hom a2 a3) (f4 : C.Hom a3 a4) (f5 : C.Hom a4 a5) :
    H.Rel (F.map (C.comp f5 (C.comp f4 (C.comp f3 (C.comp f2 f1))))) (D.comp (F.map f5) (D.comp (F.map f4) (D.comp (F.map f3) (D.comp (F.map f2) (F.map f1))))) := by
  repeat grw [FL.comp]

include DC FL in
theorem map_comp6 {a0 a1 a2 a3 a4 a5 a6 : O} (f1 : C.Hom a0 a1) (f2 : C.Hom a1 a2) (f3 : C.Hom a2 a3) (f4 : C.Hom a3 a4) (f5 : C.Hom a4 a5) (f6 : C.Hom a5 a6) :
    H.Rel (F.map (C.comp f6 (C.comp f5 (C.comp f4 (C.comp f3 (C.comp f2 f1)))))) (D.comp (F.map f6) (D.comp (F.map f5) (D.comp (F.map f4) (D.comp (F.map f3) (D.comp (F.map f2) (F.map f1)))))) := by
  repeat grw [FL.comp]

include DC DL TC TL FL IL in
theorem tensor_conjugate {a b c d : O} (f : C.Hom a c) (g : C.Hom b d) :
    H.Rel (F.map (tensor P f g))
      (D.comp (i c d).inv (D.comp (tensor T (F.map f) (F.map g)) (i a b).hom)) := by
  simp only [tensor]
  grw [IL.pair, FL.comp, FL.comp, IL.fst, IL.snd]
  apply H.symm
  grw [TL.pair_comp DC DL TC]
  grw [DL.assoc, DL.assoc]

include DC DL TC TL FL IL in
theorem first_conjugate {a b c : O} (f : C.Hom a c) :
    H.Rel (F.map (first P (b := b) f))
      (D.comp (i c b).inv (D.comp (first T (F.map f)) (i a b).hom)) := by
  change H.Rel (F.map (tensor P f C.ident)) _
  grw [tensor_conjugate DC DL TC TL FL IL, FL.ident]
  exact H.refl _

include DC DL TC TL FL IL in
theorem second_conjugate {a b d : O} (g : C.Hom b d) :
    H.Rel (F.map (second P (a := a) g))
      (D.comp (i a d).inv (D.comp (second T (F.map g)) (i a b).hom)) := by
  change H.Rel (F.map (tensor P C.ident g)) _
  grw [tensor_conjugate DC DL TC TL FL IL, FL.ident]
  exact H.refl _

include DC DL in
theorem remove_comparison {a b c d : Q} (j : Comparison D a b) (k : Comparison D c d)
    (JL : ComparisonLaws H j) {f : D.Hom a c} {g : D.Hom b d}
    (h : H.Rel f (D.comp k.inv (D.comp g j.hom))) :
    H.Rel (D.comp f j.inv) (D.comp k.inv g) := by
  grw [h, DL.assoc, DL.assoc, JL.hom_inv, DL.comp_id]

include DC DL TC TL FL IL in
theorem tensor_preserved (I : ∀ a b, ComparisonLaws H (i a b))
    {a b c d : O} (f : C.Hom a c) (g : C.Hom b d) :
    H.Rel (D.comp (F.map (tensor P f g)) (i a b).inv)
      (D.comp (i c d).inv (tensor T (F.map f) (F.map g))) :=
  remove_comparison DC DL _ _ (I a b) (tensor_conjugate DC DL TC TL FL IL f g)

include DC DL TC TL FL IL in
theorem first_preserved (I : ∀ a b, ComparisonLaws H (i a b))
    {a b c : O} (f : C.Hom a c) :
    H.Rel (D.comp (F.map (first P (b := b) f)) (i a b).inv)
      (D.comp (i c b).inv (first T (F.map f))) :=
  remove_comparison DC DL _ _ (I a b) (first_conjugate DC DL TC TL FL IL f)

include DC DL TC TL FL IL in
theorem second_preserved (I : ∀ a b, ComparisonLaws H (i a b))
    {a b d : O} (g : C.Hom b d) :
    H.Rel (D.comp (F.map (second P (a := a) g)) (i a b).inv)
      (D.comp (i a d).inv (second T (F.map g))) :=
  remove_comparison DC DL _ _ (I a b) (second_conjugate DC DL TC TL FL IL g)

include DC DL TC TL FL IL in
theorem assocLeft_conjugate (a b c : O) :
    H.Rel (F.map (assocLeft P (a := a) (b := b) (c := c)))
      (D.comp (i (P.prod a b) c).inv (D.comp (first T (i a b).inv)
        (D.comp (assocLeft T) (D.comp (second T (i b c).hom) (i a (P.prod b c)).hom)))) := by
  simp only [assocLeft, first, second, tensor]
  repeat first
    | grw [IL.pair]
    | grw [FL.comp]
    | grw [FL.ident]
    | grw [IL.fst]
    | grw [IL.snd]

    | grw [DL.assoc]

    | grw [DL.id_comp]

  apply H.symm
  repeat first

    | grw [TL.pair_comp DC DL TC]
    | grw [DL.assoc]
    | grw [TL.fst_pair]
    | grw [TL.snd_pair]
    | grw [DL.id_comp]

include DC DL TC TL FL IL in
theorem assocRight_conjugate (a b c : O) :
    H.Rel (F.map (assocRight P (a := a) (b := b) (c := c)))
      (D.comp (i a (P.prod b c)).inv (D.comp (second T (i b c).inv)
        (D.comp (assocRight T) (D.comp (first T (i a b).hom) (i (P.prod a b) c).hom)))) := by
  simp only [assocRight, first, second, tensor]
  repeat first
    | grw [IL.pair]
    | grw [FL.comp]
    | grw [FL.ident]
    | grw [IL.fst]
    | grw [IL.snd]

    | grw [DL.assoc]

    | grw [DL.id_comp]

  apply H.symm
  repeat first

    | grw [TL.pair_comp DC DL TC]
    | grw [DL.assoc]
    | grw [TL.fst_pair]
    | grw [TL.snd_pair]
    | grw [DL.id_comp]

include DC DL TC TL FL IL in
theorem assocLeft_preserved (I : ∀ a b, ComparisonLaws H (i a b)) (a b c : O) :
    H.Rel (D.comp (F.map (assocLeft P (a := a) (b := b) (c := c)))
      (D.comp (i a (P.prod b c)).inv (second T (i b c).inv)))
      (D.comp (i (P.prod a b) c).inv (D.comp (first T (i a b).inv) (assocLeft T))) := by
  grw [assocLeft_conjugate DC DL TC TL FL IL]
  repeat grw [DL.assoc]
  grw [DL.cancel_left DC (I _ _).hom_inv]
  grw [second_inverse DC DL TC TL (I b c).hom_inv, DL.comp_id]

include DC DL TC TL FL IL in
theorem assocRight_preserved (I : ∀ a b, ComparisonLaws H (i a b)) (a b c : O) :
    H.Rel (D.comp (F.map (assocRight P (a := a) (b := b) (c := c)))
      (D.comp (i (P.prod a b) c).inv (first T (i a b).inv)))
      (D.comp (i a (P.prod b c)).inv (D.comp (second T (i b c).inv) (assocRight T))) := by
  grw [assocRight_conjugate DC DL TC TL FL IL]
  repeat grw [DL.assoc]
  grw [DL.cancel_left DC (I _ _).hom_inv]
  grw [first_inverse DC DL TC TL (I a b).hom_inv, DL.comp_id]
include DC DL IL in
theorem fst_after_inverse (I : ∀ a b, ComparisonLaws H (i a b)) (a b : O) :
    H.Rel (D.comp (F.map (P.fst (a := a) (b := b))) (i a b).inv) T.fst := by
  grw [IL.fst, DL.assoc, (I a b).hom_inv, DL.comp_id]
include DC DL IL in
theorem snd_after_inverse (I : ∀ a b, ComparisonLaws H (i a b)) (a b : O) :
    H.Rel (D.comp (F.map (P.snd (a := a) (b := b))) (i a b).inv) T.snd := by
  grw [IL.snd, DL.assoc, (I a b).hom_inv, DL.comp_id]
include DC DL IL in
theorem pair_after_comparison (I : ∀ a b, ComparisonLaws H (i a b))
    {a b c : O} (f : C.Hom a b) (g : C.Hom a c) :
    H.Rel (D.comp (i b c).hom (F.map (P.pair f g))) (T.pair (F.map f) (F.map g)) := by
  grw [IL.pair, DL.cancel_left DC (I b c).hom_inv]

include DC DL in
theorem terminal_after_comparison {S : TerminalOps C} {U : TerminalOps D}
    {j : TerminalMap F S U} (J : ComparisonLaws H j) (JL : TerminalMapLaws H j) (a : O) :
    H.Rel (D.comp j.hom (F.map (S.terminal (a := a)))) U.terminal := by
  grw [JL.terminal, DL.cancel_left DC J.hom_inv]
end SquareKit.CartesianPreservation
