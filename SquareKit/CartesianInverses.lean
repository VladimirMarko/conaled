import SquareKit.CartesianLaws
import SquareKit.OptionalComparison

/-! Selected left inverses are preserved without assuming two-sided inverses of the input arrows. -/
namespace SquareKit.Cartesian
universe u v
variable {O : Type u} {C : CategoryOps.{u,v} O} {E : HomEquiv C} {P : ProductOps C}
variable (CC : CategoryCongr C E) (CL : CategoryLaws C E)
variable (PC : ProductCongr E P) (PL : ProductLaws E P)

include CC CL PC PL in
theorem tensor_inverse {a b c d : O} {f : C.Hom a c} {fi : C.Hom c a}
    {g : C.Hom b d} {gi : C.Hom d b}
    (hf : E.Rel (C.comp fi f) C.ident) (hg : E.Rel (C.comp gi g) C.ident) :
    E.Rel (C.comp (tensor P fi gi) (tensor P f g)) C.ident :=
  E.trans (tensor_comp CC CL PC PL _ _ _ _)
    (E.trans (tensor_congr CC PC hf hg) (tensor_ident CL PC PL _ _))

include CC CL PC PL in
theorem first_inverse {a b c : O} {f : C.Hom a c} {fi : C.Hom c a}
    (hf : E.Rel (C.comp fi f) C.ident) :
    E.Rel (C.comp (first P (b := b) fi) (first P f)) C.ident :=
  tensor_inverse CC CL PC PL hf (CL.id_comp _)

include CC CL PC PL in
theorem second_inverse {a b d : O} {g : C.Hom b d} {gi : C.Hom d b}
    (hg : E.Rel (C.comp gi g) C.ident) :
    E.Rel (C.comp (second P (a := a) gi) (second P g)) C.ident :=
  tensor_inverse CC CL PC PL (CL.id_comp _) hg

include CC CL in
theorem conjugate_inverse {a a' b b' : O} (i : Comparison C a a') (j : Comparison C b b')
    (I : ComparisonLaws E i) (J : ComparisonLaws E j) {f : C.Hom a' b'} {fi : C.Hom b' a'}
    (hf : E.Rel (C.comp fi f) C.ident) :
    E.Rel (C.comp (Comparison.conjugate j i fi) (Comparison.conjugate i j f)) C.ident :=
  E.trans (Comparison.conjugate_comp CC CL i j i J _ _)
    (E.trans (Comparison.conjugate_congr CC i i hf) (Comparison.conjugate_id CC CL i I))

def assocComparison (P : ProductOps C) (a b c : O) :
    Comparison C (P.prod a (P.prod b c)) (P.prod (P.prod a b) c) :=
  ⟨assocLeft P,assocRight P⟩
include CC CL PC PL in
theorem assocComparison_laws (a b c : O) : ComparisonLaws E (assocComparison P a b c) :=
  ⟨assocLeft_assocRight CC CL PC PL _ _ _,assocRight_assocLeft CC CL PC PL _ _ _⟩

def assocComparisonRev (P : ProductOps C) (a b c : O) :
    Comparison C (P.prod (P.prod a b) c) (P.prod a (P.prod b c)) :=
  ⟨assocRight P,assocLeft P⟩
include CC CL PC PL in
theorem assocComparisonRev_laws (a b c : O) : ComparisonLaws E (assocComparisonRev P a b c) :=
  ⟨assocRight_assocLeft CC CL PC PL _ _ _,assocLeft_assocRight CC CL PC PL _ _ _⟩

include CC CL PC PL in
theorem inAssocLeft'_inverse {a b c a' b' c' : O}
    {f : C.Hom (P.prod (P.prod a b) c) (P.prod (P.prod a' b') c')}
    {fi : C.Hom (P.prod (P.prod a' b') c') (P.prod (P.prod a b) c)}
    (h : E.Rel (C.comp fi f) C.ident) :
    E.Rel (C.comp (inAssocLeft' P fi) (inAssocLeft' P f)) C.ident :=
  conjugate_inverse CC CL _ _ (assocComparison_laws CC CL PC PL _ _ _)
    (assocComparison_laws CC CL PC PL _ _ _) h

include CC CL PC PL in
theorem inAssocRight'_inverse {a b c a' b' c' : O}
    {f : C.Hom (P.prod a (P.prod b c)) (P.prod a' (P.prod b' c'))}
    {fi : C.Hom (P.prod a' (P.prod b' c')) (P.prod a (P.prod b c))}
    (h : E.Rel (C.comp fi f) C.ident) :
    E.Rel (C.comp (inAssocRight' P fi) (inAssocRight' P f)) C.ident :=
  conjugate_inverse CC CL _ _ (assocComparisonRev_laws CC CL PC PL _ _ _)
    (assocComparisonRev_laws CC CL PC PL _ _ _) h

include CC CL PC PL in
theorem inAssocLeft_inverse {a b c a' b' : O}
    {f : C.Hom (P.prod a b) (P.prod a' b')} {fi : C.Hom (P.prod a' b') (P.prod a b)}
    (h : E.Rel (C.comp fi f) C.ident) :
    E.Rel (C.comp (inAssocLeft P (c := c) fi) (inAssocLeft P f)) C.ident :=
  inAssocLeft'_inverse CC CL PC PL (first_inverse CC CL PC PL h)

include CC CL PC PL in
theorem inAssocRight_inverse {a b c b' c' : O}
    {f : C.Hom (P.prod b c) (P.prod b' c')} {fi : C.Hom (P.prod b' c') (P.prod b c)}
    (h : E.Rel (C.comp fi f) C.ident) :
    E.Rel (C.comp (inAssocRight P (a := a) fi) (inAssocRight P f)) C.ident :=
  inAssocRight'_inverse CC CL PC PL (second_inverse CC CL PC PL h)
end SquareKit.Cartesian
