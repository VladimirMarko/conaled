import SquareKit.WitnessCartesianMap
import SquareKit.WitnessRewrite

namespace SquareKit.WitnessEquivalence.CartesianPreservation
universe u v w z
open SquareKit.Cartesian
open SquareKit.WitnessEquivalence.Cartesian
variable {O : Type u} {Q : Type w} {C : CategoryOps.{u,v} O} {D : CategoryOps.{w,z} Q}
variable {E : WitnessEquivalence C} {H : WitnessEquivalence D} {F : RawMap C D}
variable {P : ProductOps C} {T : ProductOps D} {i : ProductMap F P T}
variable (DC : Congr H) (DL : Laws H)
variable (TC : ProductCongr H T) (TL : ProductLaws H T)
variable (FL : Preservation F E H) (IL : ProductMapLaws H i)

include DC FL in
def map_comp3 {a0 a1 a2 a3 : O} (f1 : C.Hom a0 a1) (f2 : C.Hom a1 a2) (f3 : C.Hom a2 a3) :
    H.Rel (F.map (C.comp f3 (C.comp f2 f1))) (D.comp (F.map f3) (D.comp (F.map f2) (F.map f1))) := by
  repeat (witness_rewrite H, DC, TC, (FL.comp))
  all_goals exact H.refl _

include DC FL in
def map_comp4 {a0 a1 a2 a3 a4 : O} (f1 : C.Hom a0 a1) (f2 : C.Hom a1 a2) (f3 : C.Hom a2 a3) (f4 : C.Hom a3 a4) :
    H.Rel (F.map (C.comp f4 (C.comp f3 (C.comp f2 f1)))) (D.comp (F.map f4) (D.comp (F.map f3) (D.comp (F.map f2) (F.map f1)))) := by
  repeat (witness_rewrite H, DC, TC, (FL.comp))
  all_goals exact H.refl _

include DC FL in
def map_comp5 {a0 a1 a2 a3 a4 a5 : O} (f1 : C.Hom a0 a1) (f2 : C.Hom a1 a2) (f3 : C.Hom a2 a3) (f4 : C.Hom a3 a4) (f5 : C.Hom a4 a5) :
    H.Rel (F.map (C.comp f5 (C.comp f4 (C.comp f3 (C.comp f2 f1))))) (D.comp (F.map f5) (D.comp (F.map f4) (D.comp (F.map f3) (D.comp (F.map f2) (F.map f1))))) := by
  repeat (witness_rewrite H, DC, TC, (FL.comp))
  all_goals exact H.refl _

include DC FL in
def map_comp6 {a0 a1 a2 a3 a4 a5 a6 : O} (f1 : C.Hom a0 a1) (f2 : C.Hom a1 a2) (f3 : C.Hom a2 a3) (f4 : C.Hom a3 a4) (f5 : C.Hom a4 a5) (f6 : C.Hom a5 a6) :
    H.Rel (F.map (C.comp f6 (C.comp f5 (C.comp f4 (C.comp f3 (C.comp f2 f1)))))) (D.comp (F.map f6) (D.comp (F.map f5) (D.comp (F.map f4) (D.comp (F.map f3) (D.comp (F.map f2) (F.map f1)))))) := by
  repeat (witness_rewrite H, DC, TC, (FL.comp))
  all_goals exact H.refl _

include DC DL TC TL FL IL in
def tensor_conjugate {a b c d : O} (f : C.Hom a c) (g : C.Hom b d) :
    H.Rel (F.map (tensor P f g))
      (D.comp (i c d).inv (D.comp (tensor T (F.map f) (F.map g)) (i a b).hom)) := by
  simp only [tensor]
  (witness_rewrite H, DC, TC, (IL.pair); witness_rewrite H, DC, TC, (FL.comp); witness_rewrite H, DC, TC, (FL.comp); witness_rewrite H, DC, TC, (IL.fst); witness_rewrite H, DC, TC, (IL.snd))
  apply H.symm
  (witness_rewrite H, DC, TC, (TL.pair_comp DC DL TC))
  (witness_rewrite H, DC, TC, (DL.assoc); witness_rewrite H, DC, TC, (DL.assoc))
  all_goals exact H.refl _

include DC DL TC TL FL IL in
def first_conjugate {a b c : O} (f : C.Hom a c) :
    H.Rel (F.map (first P (b := b) f))
      (D.comp (i c b).inv (D.comp (first T (F.map f)) (i a b).hom)) := by
  change H.Rel (F.map (tensor P f C.ident)) _
  (witness_rewrite H, DC, TC, (tensor_conjugate DC DL TC TL FL IL); witness_rewrite H, DC, TC, (FL.ident))
  exact H.refl _

include DC DL TC TL FL IL in
def second_conjugate {a b d : O} (g : C.Hom b d) :
    H.Rel (F.map (second P (a := a) g))
      (D.comp (i a d).inv (D.comp (second T (F.map g)) (i a b).hom)) := by
  change H.Rel (F.map (tensor P C.ident g)) _
  (witness_rewrite H, DC, TC, (tensor_conjugate DC DL TC TL FL IL); witness_rewrite H, DC, TC, (FL.ident))
  exact H.refl _

include DC DL in
def remove_comparison {a b c d : Q} (j : Comparison D a b) (k : Comparison D c d)
    (JL : ComparisonLaws H j) {f : D.Hom a c} {g : D.Hom b d}
    (h : H.Rel f (D.comp k.inv (D.comp g j.hom))) :
    H.Rel (D.comp f j.inv) (D.comp k.inv g) := by
  (witness_rewrite H, DC, TC, (h); witness_rewrite H, DC, TC, (DL.assoc); witness_rewrite H, DC, TC, (DL.assoc); witness_rewrite H, DC, TC, (JL.hom_inv); witness_rewrite H, DC, TC, (DL.comp_id))
  all_goals exact H.refl _

include DC DL TC TL FL IL in
def tensor_preserved (I : ∀ a b, ComparisonLaws H (i a b))
    {a b c d : O} (f : C.Hom a c) (g : C.Hom b d) :
    H.Rel (D.comp (F.map (tensor P f g)) (i a b).inv)
      (D.comp (i c d).inv (tensor T (F.map f) (F.map g))) :=
  remove_comparison DC DL _ _ (I a b) (tensor_conjugate DC DL TC TL FL IL f g)

include DC DL TC TL FL IL in
def first_preserved (I : ∀ a b, ComparisonLaws H (i a b))
    {a b c : O} (f : C.Hom a c) :
    H.Rel (D.comp (F.map (first P (b := b) f)) (i a b).inv)
      (D.comp (i c b).inv (first T (F.map f))) :=
  remove_comparison DC DL _ _ (I a b) (first_conjugate DC DL TC TL FL IL f)

include DC DL TC TL FL IL in
def second_preserved (I : ∀ a b, ComparisonLaws H (i a b))
    {a b d : O} (g : C.Hom b d) :
    H.Rel (D.comp (F.map (second P (a := a) g)) (i a b).inv)
      (D.comp (i a d).inv (second T (F.map g))) :=
  remove_comparison DC DL _ _ (I a b) (second_conjugate DC DL TC TL FL IL g)

include DC DL TC TL FL IL in
def assocLeft_image_normal (a b c : O) :
    H.Rel (F.map (assocLeft P (a := a) (b := b) (c := c))) (D.comp (i (P.prod a b) c).inv
      (T.pair
        (D.comp (i a b).inv
          (T.pair (D.comp T.fst (i a (P.prod b c)).hom)
            (D.comp T.fst (D.comp (i b c).hom (D.comp T.snd (i a (P.prod b c)).hom)))))
        (D.comp T.snd (D.comp (i b c).hom (D.comp T.snd (i a (P.prod b c)).hom))))) := by
  simp only [assocLeft, second, tensor]
  repeat first
    | (witness_rewrite H, DC, TC, (IL.pair))
    | (witness_rewrite H, DC, TC, (FL.comp))
    | (witness_rewrite H, DC, TC, (FL.ident))
    | (witness_rewrite H, DC, TC, (IL.fst))
    | (witness_rewrite H, DC, TC, (IL.snd))

    | (witness_rewrite H, DC, TC, (DL.assoc))

    | (witness_rewrite H, DC, TC, (DL.id_comp))

  exact H.refl _
include DC DL TC TL FL IL in
def assocLeft_comparison_normal (a b c : O) :
    H.Rel (D.comp (i (P.prod a b) c).inv (D.comp (first T (i a b).inv)
        (D.comp (assocLeft T) (D.comp (second T (i b c).hom) (i a (P.prod b c)).hom)))) (D.comp (i (P.prod a b) c).inv
      (T.pair
        (D.comp (i a b).inv
          (T.pair (D.comp T.fst (i a (P.prod b c)).hom)
            (D.comp T.fst (D.comp (i b c).hom (D.comp T.snd (i a (P.prod b c)).hom)))))
        (D.comp T.snd (D.comp (i b c).hom (D.comp T.snd (i a (P.prod b c)).hom))))) := by
  simp only [assocLeft, first, second, tensor]
  repeat first

    | (witness_rewrite H, DC, TC, (TL.pair_comp DC DL TC))
    | (witness_rewrite H, DC, TC, (DL.assoc))
    | (witness_rewrite H, DC, TC, (TL.fst_pair))
    | (witness_rewrite H, DC, TC, (TL.snd_pair))
    | (witness_rewrite H, DC, TC, (DL.id_comp))
  all_goals exact H.refl _
include DC DL TC TL FL IL in
def assocLeft_conjugate (a b c : O) :
    H.Rel (F.map (assocLeft P (a := a) (b := b) (c := c)))
      (D.comp (i (P.prod a b) c).inv (D.comp (first T (i a b).inv)
        (D.comp (assocLeft T) (D.comp (second T (i b c).hom) (i a (P.prod b c)).hom)))) :=
  H.trans (assocLeft_image_normal DC DL TC FL IL a b c)
    (H.symm (assocLeft_comparison_normal DC DL TC TL a b c))

include DC DL TC TL FL IL in
def assocRight_conjugate (a b c : O) :
    H.Rel (F.map (assocRight P (a := a) (b := b) (c := c)))
      (D.comp (i a (P.prod b c)).inv (D.comp (second T (i b c).inv)
        (D.comp (assocRight T) (D.comp (first T (i a b).hom) (i (P.prod a b) c).hom)))) := by
  simp only [assocRight, first, second, tensor]
  repeat first
    | (witness_rewrite H, DC, TC, (IL.pair))
    | (witness_rewrite H, DC, TC, (FL.comp))
    | (witness_rewrite H, DC, TC, (FL.ident))
    | (witness_rewrite H, DC, TC, (IL.fst))
    | (witness_rewrite H, DC, TC, (IL.snd))

    | (witness_rewrite H, DC, TC, (DL.assoc))

    | (witness_rewrite H, DC, TC, (DL.id_comp))

  apply H.symm
  repeat first

    | (witness_rewrite H, DC, TC, (TL.pair_comp DC DL TC))
    | (witness_rewrite H, DC, TC, (DL.assoc))
    | (witness_rewrite H, DC, TC, (TL.fst_pair))
    | (witness_rewrite H, DC, TC, (TL.snd_pair))
    | (witness_rewrite H, DC, TC, (DL.id_comp))
  all_goals exact H.refl _

include DC DL TC TL FL IL in
def assocLeft_preserved (I : ∀ a b, ComparisonLaws H (i a b)) (a b c : O) :
    H.Rel (D.comp (F.map (assocLeft P (a := a) (b := b) (c := c)))
      (D.comp (i a (P.prod b c)).inv (second T (i b c).inv)))
      (D.comp (i (P.prod a b) c).inv (D.comp (first T (i a b).inv) (assocLeft T))) := by
  (witness_rewrite H, DC, TC, (assocLeft_conjugate DC DL TC TL FL IL))
  repeat (witness_rewrite H, DC, TC, (DL.assoc))
  (witness_rewrite H, DC, TC, (DL.cancel_left DC (I _ _).hom_inv))
  (witness_rewrite H, DC, TC, (second_inverse DC DL TC TL (I b c).hom_inv); witness_rewrite H, DC, TC, (DL.comp_id))
  all_goals exact H.refl _

include DC DL TC TL FL IL in
def assocRight_preserved (I : ∀ a b, ComparisonLaws H (i a b)) (a b c : O) :
    H.Rel (D.comp (F.map (assocRight P (a := a) (b := b) (c := c)))
      (D.comp (i (P.prod a b) c).inv (first T (i a b).inv)))
      (D.comp (i a (P.prod b c)).inv (D.comp (second T (i b c).inv) (assocRight T))) := by
  (witness_rewrite H, DC, TC, (assocRight_conjugate DC DL TC TL FL IL))
  repeat (witness_rewrite H, DC, TC, (DL.assoc))
  (witness_rewrite H, DC, TC, (DL.cancel_left DC (I _ _).hom_inv))
  (witness_rewrite H, DC, TC, (first_inverse DC DL TC TL (I a b).hom_inv); witness_rewrite H, DC, TC, (DL.comp_id))
  all_goals exact H.refl _

include DC DL IL in
def fst_after_inverse (I : ∀ a b, ComparisonLaws H (i a b)) (a b : O) :
    H.Rel (D.comp (F.map (P.fst (a := a) (b := b))) (i a b).inv) T.fst := by
  (witness_rewrite H, DC, TC, (IL.fst); witness_rewrite H, DC, TC, (DL.assoc); witness_rewrite H, DC, TC, ((I a b).hom_inv); witness_rewrite H, DC, TC, (DL.comp_id))
  all_goals exact H.refl _

include DC DL IL in
def snd_after_inverse (I : ∀ a b, ComparisonLaws H (i a b)) (a b : O) :
    H.Rel (D.comp (F.map (P.snd (a := a) (b := b))) (i a b).inv) T.snd := by
  (witness_rewrite H, DC, TC, (IL.snd); witness_rewrite H, DC, TC, (DL.assoc); witness_rewrite H, DC, TC, ((I a b).hom_inv); witness_rewrite H, DC, TC, (DL.comp_id))
  all_goals exact H.refl _

include DC DL IL in
def pair_after_comparison (I : ∀ a b, ComparisonLaws H (i a b))
    {a b c : O} (f : C.Hom a b) (g : C.Hom a c) :
    H.Rel (D.comp (i b c).hom (F.map (P.pair f g))) (T.pair (F.map f) (F.map g)) := by
  (witness_rewrite H, DC, TC, (IL.pair); witness_rewrite H, DC, TC, (DL.cancel_left DC (I b c).hom_inv))
  all_goals exact H.refl _

include DC DL in
def terminal_after_comparison {S : TerminalOps C} {U : TerminalOps D}
    {j : TerminalMap F S U} (J : ComparisonLaws H j) (JL : TerminalMapLaws H j) (a : O) :
    H.Rel (D.comp j.hom (F.map (S.terminal (a := a)))) U.terminal := by
  (witness_rewrite H, DC, TC, (JL.terminal); witness_rewrite H, DC, TC, (DL.cancel_left DC J.hom_inv))
  all_goals exact H.refl _

end SquareKit.WitnessEquivalence.CartesianPreservation
