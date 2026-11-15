import SquareKit.CartesianLaws

/-! Equational reasoning over raw arrows uses congruence separately from category laws. -/
namespace SquareKit.RawReasoning
universe u v
variable {O : Type u} {C : CategoryOps.{u,v} O} {E : HomEquiv C}
variable (CC : CategoryCongr C E) (CL : CategoryLaws C E)
local instance {a b : O} : IsPreorder (C.Hom a b) E.Rel where
  refl := E.refl
  trans _ _ _ := E.trans
attribute [local gcongr] CategoryCongr.comp
attribute [local refl] HomEquiv.refl

theorem symm_map {a b c d : O} {i j : C.Hom a b} {f g : C.Hom c d}
    (h : E.Rel i j → E.Rel f g) (k : E.Rel j i) : E.Rel g f := E.symm (h (E.symm k))

include CC CL in
theorem elim_left {a b : O} {i : C.Hom b b} (h : E.Rel i C.ident) (f : C.Hom a b) :
    E.Rel (C.comp i f) f := E.trans (CC.comp h (E.refl _)) (CL.id_comp _)
include CC CL in
theorem intro_left {a b : O} {i : C.Hom b b} (h : E.Rel i C.ident) (f : C.Hom a b) :
    E.Rel f (C.comp i f) := E.symm (elim_left CC CL h f)
include CC CL in
theorem elim_right {a b : O} {i : C.Hom a a} (h : E.Rel i C.ident) (f : C.Hom a b) :
    E.Rel (C.comp f i) f := E.trans (CC.comp (E.refl _) h) (CL.comp_id _)
include CC CL in
theorem intro_right {a b : O} {i : C.Hom a a} (h : E.Rel i C.ident) (f : C.Hom a b) :
    E.Rel f (C.comp f i) := E.symm (elim_right CC CL h f)
include CC CL in
theorem elim_center {a b c : O} {i : C.Hom b b} (h : E.Rel i C.ident)
    (f : C.Hom a b) (g : C.Hom b c) : E.Rel (C.comp g (C.comp i f)) (C.comp g f) :=
  CC.comp (E.refl _) (elim_left CC CL h f)
include CC CL in
theorem intro_center {a b c : O} {i : C.Hom b b} (h : E.Rel i C.ident)
    (f : C.Hom a b) (g : C.Hom b c) : E.Rel (C.comp g f) (C.comp g (C.comp i f)) :=
  E.symm (elim_center CC CL h f g)

include CC CL in
theorem assoc_pull_left {a b c d : O} (f : C.Hom a b) {g : C.Hom b c}
    {h : C.Hom c d} {k : C.Hom b d} (e : E.Rel (C.comp h g) k) :
    E.Rel (C.comp h (C.comp g f)) (C.comp k f) :=
  E.trans (E.symm (CL.assoc _ _ _)) (CC.comp e (E.refl _))
include CC CL in
theorem assoc_pull_right {a b c d : O} {f : C.Hom a b} {g : C.Hom b c}
    (k : C.Hom c d) {h : C.Hom a c} (e : E.Rel (C.comp g f) h) :
    E.Rel (C.comp (C.comp k g) f) (C.comp k h) :=
  E.trans (CL.assoc _ _ _) (CC.comp (E.refl _) e)
include CC CL in
theorem assoc_pull_left_right {a b c d e : O} (f : C.Hom a b)
    {g : C.Hom b c} {h : C.Hom c d} {i : C.Hom b e} {j : C.Hom e d}
    (eq : E.Rel (C.comp h g) (C.comp j i)) :
    E.Rel (C.comp h (C.comp g f)) (C.comp j (C.comp i f)) :=
  E.trans (assoc_pull_left CC CL f eq) (CL.assoc _ _ _)
include CC CL in
theorem assoc_pull_right_left {a b c d e : O} {f : C.Hom a b}
    {g : C.Hom b c} (h : C.Hom c d) {i : C.Hom a e} {j : C.Hom e c}
    (eq : E.Rel (C.comp g f) (C.comp j i)) :
    E.Rel (C.comp (C.comp h g) f) (C.comp (C.comp h j) i) :=
  E.trans (assoc_pull_right CC CL h eq) (E.symm (CL.assoc _ _ _))

include CC CL in
theorem cancel_right {a b c : O} {i : C.Hom a b} {j : C.Hom b a}
    (h : E.Rel (C.comp j i) C.ident) (f : C.Hom a c) :
    E.Rel (C.comp (C.comp f j) i) f :=
  E.trans (assoc_pull_right CC CL f h) (CL.comp_id _)

include CC CL in
theorem comp_inverse {a b c : O} {f : C.Hom a b} {fi : C.Hom b a}
    {g : C.Hom b c} {gi : C.Hom c b}
    (hf : E.Rel (C.comp fi f) C.ident) (hg : E.Rel (C.comp gi g) C.ident) :
    E.Rel (C.comp (C.comp fi gi) (C.comp g f)) C.ident :=
  E.trans (CL.cancel_middle CC hg _ _) hf

include CL in
theorem assoc_right3 {a0 a1 a2 a3 : O} (f1 : C.Hom a0 a1) (f2 : C.Hom a1 a2) (f3 : C.Hom a2 a3) : E.Rel (C.comp (C.comp f3 f2) f1) (C.comp f3 (C.comp f2 f1)) := by
  repeat grw [CL.assoc]

include CL in
theorem assoc_left3 {a0 a1 a2 a3 : O} (f1 : C.Hom a0 a1) (f2 : C.Hom a1 a2) (f3 : C.Hom a2 a3) : E.Rel (C.comp f3 (C.comp f2 f1)) (C.comp (C.comp f3 f2) f1) :=
  E.symm (assoc_right3 CL f1 f2 f3)

include CC CL in
theorem assoc_right4 {a0 a1 a2 a3 a4 : O} (f1 : C.Hom a0 a1) (f2 : C.Hom a1 a2) (f3 : C.Hom a2 a3) (f4 : C.Hom a3 a4) : E.Rel (C.comp (C.comp f4 (C.comp f3 f2)) f1) (C.comp f4 (C.comp f3 (C.comp f2 f1))) := by
  repeat grw [CL.assoc]

include CC CL in
theorem assoc_left4 {a0 a1 a2 a3 a4 : O} (f1 : C.Hom a0 a1) (f2 : C.Hom a1 a2) (f3 : C.Hom a2 a3) (f4 : C.Hom a3 a4) : E.Rel (C.comp f4 (C.comp f3 (C.comp f2 f1))) (C.comp (C.comp f4 (C.comp f3 f2)) f1) :=
  E.symm (assoc_right4 CC CL f1 f2 f3 f4)

include CC CL in
theorem assoc_right5 {a0 a1 a2 a3 a4 a5 : O} (f1 : C.Hom a0 a1) (f2 : C.Hom a1 a2) (f3 : C.Hom a2 a3) (f4 : C.Hom a3 a4) (f5 : C.Hom a4 a5) : E.Rel (C.comp (C.comp f5 (C.comp f4 (C.comp f3 f2))) f1) (C.comp f5 (C.comp f4 (C.comp f3 (C.comp f2 f1)))) := by
  repeat grw [CL.assoc]

include CC CL in
theorem assoc_left5 {a0 a1 a2 a3 a4 a5 : O} (f1 : C.Hom a0 a1) (f2 : C.Hom a1 a2) (f3 : C.Hom a2 a3) (f4 : C.Hom a3 a4) (f5 : C.Hom a4 a5) : E.Rel (C.comp f5 (C.comp f4 (C.comp f3 (C.comp f2 f1)))) (C.comp (C.comp f5 (C.comp f4 (C.comp f3 f2))) f1) :=
  E.symm (assoc_right5 CC CL f1 f2 f3 f4 f5)

include CC CL in
theorem assoc_right6 {a0 a1 a2 a3 a4 a5 a6 : O} (f1 : C.Hom a0 a1) (f2 : C.Hom a1 a2) (f3 : C.Hom a2 a3) (f4 : C.Hom a3 a4) (f5 : C.Hom a4 a5) (f6 : C.Hom a5 a6) : E.Rel (C.comp (C.comp f6 (C.comp f5 (C.comp f4 (C.comp f3 f2)))) f1) (C.comp f6 (C.comp f5 (C.comp f4 (C.comp f3 (C.comp f2 f1))))) := by
  repeat grw [CL.assoc]

include CC CL in
theorem assoc_left6 {a0 a1 a2 a3 a4 a5 a6 : O} (f1 : C.Hom a0 a1) (f2 : C.Hom a1 a2) (f3 : C.Hom a2 a3) (f4 : C.Hom a3 a4) (f5 : C.Hom a4 a5) (f6 : C.Hom a5 a6) : E.Rel (C.comp f6 (C.comp f5 (C.comp f4 (C.comp f3 (C.comp f2 f1))))) (C.comp (C.comp f6 (C.comp f5 (C.comp f4 (C.comp f3 f2)))) f1) :=
  E.symm (assoc_right6 CC CL f1 f2 f3 f4 f5 f6)

include CC CL in
theorem assoc_right7 {a0 a1 a2 a3 a4 a5 a6 a7 : O} (f1 : C.Hom a0 a1) (f2 : C.Hom a1 a2) (f3 : C.Hom a2 a3) (f4 : C.Hom a3 a4) (f5 : C.Hom a4 a5) (f6 : C.Hom a5 a6) (f7 : C.Hom a6 a7) : E.Rel (C.comp (C.comp f7 (C.comp f6 (C.comp f5 (C.comp f4 (C.comp f3 f2))))) f1) (C.comp f7 (C.comp f6 (C.comp f5 (C.comp f4 (C.comp f3 (C.comp f2 f1)))))) := by
  repeat grw [CL.assoc]

include CC CL in
theorem assoc_left7 {a0 a1 a2 a3 a4 a5 a6 a7 : O} (f1 : C.Hom a0 a1) (f2 : C.Hom a1 a2) (f3 : C.Hom a2 a3) (f4 : C.Hom a3 a4) (f5 : C.Hom a4 a5) (f6 : C.Hom a5 a6) (f7 : C.Hom a6 a7) : E.Rel (C.comp f7 (C.comp f6 (C.comp f5 (C.comp f4 (C.comp f3 (C.comp f2 f1)))))) (C.comp (C.comp f7 (C.comp f6 (C.comp f5 (C.comp f4 (C.comp f3 f2))))) f1) :=
  E.symm (assoc_right7 CC CL f1 f2 f3 f4 f5 f6 f7)

include CC in
theorem congr_right2 {a0 a1 a2 a3 : O} {f g : C.Hom a0 a1} (f2 : C.Hom a1 a2) (f3 : C.Hom a2 a3) (h : E.Rel f g) :
    E.Rel (C.comp f3 (C.comp f2 f)) (C.comp f3 (C.comp f2 g)) :=
  CC.comp (E.refl _) (CC.comp (E.refl _) (h))

include CC in
theorem congr_right3 {a0 a1 a2 a3 a4 : O} {f g : C.Hom a0 a1} (f2 : C.Hom a1 a2) (f3 : C.Hom a2 a3) (f4 : C.Hom a3 a4) (h : E.Rel f g) :
    E.Rel (C.comp f4 (C.comp f3 (C.comp f2 f))) (C.comp f4 (C.comp f3 (C.comp f2 g))) :=
  CC.comp (E.refl _) (CC.comp (E.refl _) (CC.comp (E.refl _) (h)))

include CC in
theorem congr_right4 {a0 a1 a2 a3 a4 a5 : O} {f g : C.Hom a0 a1} (f2 : C.Hom a1 a2) (f3 : C.Hom a2 a3) (f4 : C.Hom a3 a4) (f5 : C.Hom a4 a5) (h : E.Rel f g) :
    E.Rel (C.comp f5 (C.comp f4 (C.comp f3 (C.comp f2 f)))) (C.comp f5 (C.comp f4 (C.comp f3 (C.comp f2 g)))) :=
  CC.comp (E.refl _) (CC.comp (E.refl _) (CC.comp (E.refl _) (CC.comp (E.refl _) (h))))

include CC in
theorem congr_right5 {a0 a1 a2 a3 a4 a5 a6 : O} {f g : C.Hom a0 a1} (f2 : C.Hom a1 a2) (f3 : C.Hom a2 a3) (f4 : C.Hom a3 a4) (f5 : C.Hom a4 a5) (f6 : C.Hom a5 a6) (h : E.Rel f g) :
    E.Rel (C.comp f6 (C.comp f5 (C.comp f4 (C.comp f3 (C.comp f2 f))))) (C.comp f6 (C.comp f5 (C.comp f4 (C.comp f3 (C.comp f2 g))))) :=
  CC.comp (E.refl _) (CC.comp (E.refl _) (CC.comp (E.refl _) (CC.comp (E.refl _) (CC.comp (E.refl _) (h)))))

include CC in
theorem congr_right6 {a0 a1 a2 a3 a4 a5 a6 a7 : O} {f g : C.Hom a0 a1} (f2 : C.Hom a1 a2) (f3 : C.Hom a2 a3) (f4 : C.Hom a3 a4) (f5 : C.Hom a4 a5) (f6 : C.Hom a5 a6) (f7 : C.Hom a6 a7) (h : E.Rel f g) :
    E.Rel (C.comp f7 (C.comp f6 (C.comp f5 (C.comp f4 (C.comp f3 (C.comp f2 f)))))) (C.comp f7 (C.comp f6 (C.comp f5 (C.comp f4 (C.comp f3 (C.comp f2 g)))))) :=
  CC.comp (E.refl _) (CC.comp (E.refl _) (CC.comp (E.refl _) (CC.comp (E.refl _) (CC.comp (E.refl _) (CC.comp (E.refl _) (h))))))
end SquareKit.RawReasoning
