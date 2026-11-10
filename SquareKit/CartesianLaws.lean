import SquareKit.CartesianOperations
import Mathlib.Tactic.GRewrite

/-! Cartesian equations hold modulo the caller's semantic equivalence. -/
namespace SquareKit.Cartesian
universe u v
variable {O : Type u} {C : CategoryOps.{u,v} O} {E : HomEquiv C} {P : ProductOps C}
variable (CC : CategoryCongr C E) (CL : CategoryLaws C E)
variable (PC : ProductCongr E P) (PL : ProductLaws E P)
local instance {a b : O} : IsPreorder (C.Hom a b) E.Rel where
  refl := E.refl
  trans _ _ _ := E.trans
attribute [local gcongr] CategoryCongr.comp ProductCongr.pair
attribute [local refl] HomEquiv.refl
attribute [local symm] HomEquiv.symm

include CL PC PL in
theorem pair_projections {a b : O} : E.Rel (P.pair (P.fst (a := a) (b := b)) P.snd) C.ident :=
  E.trans (PC.pair (E.symm (CL.comp_id _)) (E.symm (CL.comp_id _))) (PL.pair_eta _)

include PL in
theorem fst_tensor {a b c d : O} (f : C.Hom a c) (g : C.Hom b d) :
    E.Rel (C.comp P.fst (tensor P f g)) (C.comp f P.fst) := by
  simp only [tensor]
  repeat first

    | grw [PL.fst_pair]

include PL in
theorem snd_tensor {a b c d : O} (f : C.Hom a c) (g : C.Hom b d) :
    E.Rel (C.comp P.snd (tensor P f g)) (C.comp g P.snd) := by
  simp only [tensor]
  repeat first

    | grw [PL.snd_pair]

include PL in
theorem fst_first {a b c : O} (f : C.Hom a c) :
    E.Rel (C.comp P.fst (first P (b := b) f)) (C.comp f P.fst) := by
  simp only [tensor, first]
  repeat first

    | grw [PL.fst_pair]

include CL PL in
theorem snd_first {a b c : O} (f : C.Hom a c) :
    E.Rel (C.comp P.snd (first P (b := b) f)) (P.snd) := by
  simp only [tensor, first]
  repeat first

    | grw [PL.snd_pair]
    | grw [CL.id_comp]

include CL PL in
theorem fst_second {a b d : O} (g : C.Hom b d) :
    E.Rel (C.comp P.fst (second P (a := a) g)) (P.fst) := by
  simp only [tensor, second]
  repeat first

    | grw [PL.fst_pair]

    | grw [CL.id_comp]

include PL in
theorem snd_second {a b d : O} (g : C.Hom b d) :
    E.Rel (C.comp P.snd (second P (a := a) g)) (C.comp g P.snd) := by
  simp only [tensor, second]
  repeat first

    | grw [PL.snd_pair]

include CL PC PL in
theorem tensor_ident (a b : O) :
    E.Rel (tensor P (C.ident (a := a)) (C.ident (a := b))) (C.ident) := by
  simp only [tensor]
  repeat first

    | grw [CL.id_comp]

    | grw [pair_projections CL PC PL]

include CC CL PC PL in
theorem tensor_pair {a b c d x : O} (f : C.Hom a c) (g : C.Hom b d) (h : C.Hom x a) (k : C.Hom x b) :
    E.Rel (C.comp (tensor P f g) (P.pair h k)) (P.pair (C.comp f h) (C.comp g k)) := by
  simp only [tensor]
  repeat first
    | grw [PL.pair_comp CC CL PC]
    | grw [CL.assoc]
    | grw [PL.fst_pair]
    | grw [PL.snd_pair]

include CC CL PC PL in
theorem first_pair {a b c x : O} (f : C.Hom a c) (h : C.Hom x a) (k : C.Hom x b) :
    E.Rel (C.comp (first P f) (P.pair h k)) (P.pair (C.comp f h) k) := by
  simp only [tensor, first]
  repeat first
    | grw [PL.pair_comp CC CL PC]
    | grw [CL.assoc]
    | grw [PL.fst_pair]
    | grw [PL.snd_pair]
    | grw [CL.id_comp]

include CC CL PC PL in
theorem second_pair {a b d x : O} (g : C.Hom b d) (h : C.Hom x a) (k : C.Hom x b) :
    E.Rel (C.comp (second P g) (P.pair h k)) (P.pair h (C.comp g k)) := by
  simp only [tensor, second]
  repeat first
    | grw [PL.pair_comp CC CL PC]
    | grw [CL.assoc]
    | grw [PL.fst_pair]
    | grw [PL.snd_pair]
    | grw [CL.id_comp]

include CC CL PC PL in
theorem tensor_comp {a b c d e f : O} (h : C.Hom c e) (k : C.Hom d f) (f : C.Hom a c) (g : C.Hom b d) :
    E.Rel (C.comp (tensor P h k) (tensor P f g)) (tensor P (C.comp h f) (C.comp k g)) := by
  simp only [tensor]
  repeat first
    | grw [PL.pair_comp CC CL PC]
    | grw [CL.assoc]
    | grw [PL.fst_pair]
    | grw [PL.snd_pair]

include CC CL PC PL in
theorem first_tensor {a b c d e : O} (h : C.Hom c e) (f : C.Hom a c) (g : C.Hom b d) :
    E.Rel (C.comp (first P h) (tensor P f g)) (tensor P (C.comp h f) g) := by
  simp only [tensor, first]
  repeat first
    | grw [PL.pair_comp CC CL PC]
    | grw [CL.assoc]
    | grw [PL.fst_pair]
    | grw [PL.snd_pair]
    | grw [CL.id_comp]

include CC CL PC PL in
theorem tensor_first {a b c d e : O} (h : C.Hom c d) (k : C.Hom b e) (f : C.Hom a c) :
    E.Rel (C.comp (tensor P h k) (first P f)) (tensor P (C.comp h f) k) := by
  simp only [tensor, first]
  repeat first
    | grw [PL.pair_comp CC CL PC]
    | grw [CL.assoc]
    | grw [PL.fst_pair]
    | grw [PL.snd_pair]
    | grw [CL.id_comp]

include CC CL PC PL in
theorem tensor_second {a b c d e : O} (h : C.Hom a d) (k : C.Hom c e) (g : C.Hom b c) :
    E.Rel (C.comp (tensor P h k) (second P g)) (tensor P h (C.comp k g)) := by
  simp only [tensor, second]
  repeat first
    | grw [PL.pair_comp CC CL PC]
    | grw [CL.assoc]
    | grw [PL.fst_pair]
    | grw [PL.snd_pair]
    | grw [CL.id_comp]

include CC CL PC PL in
theorem second_tensor {a b c d e : O} (k : C.Hom d e) (f : C.Hom a c) (g : C.Hom b d) :
    E.Rel (C.comp (second P k) (tensor P f g)) (tensor P f (C.comp k g)) := by
  simp only [tensor, second]
  repeat first
    | grw [PL.pair_comp CC CL PC]
    | grw [CL.assoc]
    | grw [PL.fst_pair]
    | grw [PL.snd_pair]
    | grw [CL.id_comp]

include CC CL PC PL in
theorem first_comp {a b c d : O} (h : C.Hom c d) (f : C.Hom a c) :
    E.Rel (C.comp (first P (b := b) h) (first P f)) (first P (C.comp h f)) := by
  simp only [tensor, first]
  repeat first
    | grw [PL.pair_comp CC CL PC]
    | grw [CL.assoc]
    | grw [PL.fst_pair]
    | grw [PL.snd_pair]
    | grw [CL.id_comp]

include CC CL PC PL in
theorem second_comp {a b c d : O} (k : C.Hom c d) (g : C.Hom b c) :
    E.Rel (C.comp (second P (a := a) k) (second P g)) (second P (C.comp k g)) := by
  simp only [tensor, second]
  repeat first
    | grw [PL.pair_comp CC CL PC]
    | grw [CL.assoc]
    | grw [PL.fst_pair]
    | grw [PL.snd_pair]
    | grw [CL.id_comp]

include CC CL PC PL in
theorem first_second {a b c d : O} (f : C.Hom a c) (g : C.Hom b d) :
    E.Rel (C.comp (first P f) (second P g)) (tensor P f g) := by
  simp only [tensor, first, second]
  repeat first
    | grw [PL.pair_comp CC CL PC]
    | grw [CL.assoc]
    | grw [PL.fst_pair]
    | grw [PL.snd_pair]
    | grw [CL.id_comp]

include CC CL PC PL in
theorem second_first {a b c d : O} (f : C.Hom a c) (g : C.Hom b d) :
    E.Rel (C.comp (second P g) (first P f)) (tensor P f g) := by
  simp only [tensor, first, second]
  repeat first
    | grw [PL.pair_comp CC CL PC]
    | grw [CL.assoc]
    | grw [PL.fst_pair]
    | grw [PL.snd_pair]
    | grw [CL.id_comp]

include PL in
theorem fst_swap (a b : O) :
    E.Rel (C.comp P.fst (swap P (a := a) (b := b))) (P.snd) := by
  simp only [swap]
  repeat first

    | grw [PL.fst_pair]

include PL in
theorem snd_swap (a b : O) :
    E.Rel (C.comp P.snd (swap P (a := a) (b := b))) (P.fst) := by
  simp only [swap]
  repeat first

    | grw [PL.snd_pair]

include CC CL PC PL in
theorem swap_pair {a b x : O} (f : C.Hom x a) (g : C.Hom x b) :
    E.Rel (C.comp (swap P) (P.pair f g)) (P.pair g f) := by
  simp only [swap]
  repeat first
    | grw [PL.pair_comp CC CL PC]

    | grw [PL.fst_pair]
    | grw [PL.snd_pair]

include CC CL PC PL in
theorem swap_swap (a b : O) :
    E.Rel (C.comp (swap P (a := b) (b := a)) (swap P)) (C.ident) := by
  simp only [swap]
  repeat first
    | grw [PL.pair_comp CC CL PC]

    | grw [PL.fst_pair]
    | grw [PL.snd_pair]

    | grw [pair_projections CL PC PL]

include CC CL PC PL in
theorem assocLeft_assocRight (a b c : O) :
    E.Rel (C.comp (assocLeft P (a := a) (b := b) (c := c)) (assocRight P)) (C.ident) := by
  simp only [tensor, first, second, assocLeft, assocRight]
  repeat first
    | grw [PL.pair_comp CC CL PC]
    | grw [CL.assoc]
    | grw [PL.fst_pair]
    | grw [PL.snd_pair]
    | grw [CL.id_comp]

    | grw [PL.pair_eta]
    | grw [pair_projections CL PC PL]

include CC CL PC PL in
theorem assocRight_assocLeft (a b c : O) :
    E.Rel (C.comp (assocRight P (a := a) (b := b) (c := c)) (assocLeft P)) (C.ident) := by
  simp only [tensor, first, second, assocLeft, assocRight]
  repeat first
    | grw [PL.pair_comp CC CL PC]
    | grw [CL.assoc]
    | grw [PL.fst_pair]
    | grw [PL.snd_pair]
    | grw [CL.id_comp]

    | grw [PL.pair_eta]
    | grw [pair_projections CL PC PL]

include CC CL PC PL in
theorem assocRight_pair {a b c x : O} (f : C.Hom x a) (g : C.Hom x b) (h : C.Hom x c) :
    E.Rel (C.comp (assocRight P) (P.pair (P.pair f g) h)) (P.pair f (P.pair g h)) := by
  simp only [tensor, first, assocRight]
  repeat first
    | grw [PL.pair_comp CC CL PC]
    | grw [CL.assoc]
    | grw [PL.fst_pair]
    | grw [PL.snd_pair]
    | grw [CL.id_comp]

include CC CL PC PL in
theorem assocLeft_pair {a b c x : O} (f : C.Hom x a) (g : C.Hom x b) (h : C.Hom x c) :
    E.Rel (C.comp (assocLeft P) (P.pair f (P.pair g h))) (P.pair (P.pair f g) h) := by
  simp only [tensor, second, assocLeft]
  repeat first
    | grw [PL.pair_comp CC CL PC]
    | grw [CL.assoc]
    | grw [PL.fst_pair]
    | grw [PL.snd_pair]
    | grw [CL.id_comp]

include CC CL PC PL in
theorem tensor_assocRight {a b c d e f : O} (h : C.Hom a d) (k : C.Hom b e) (l : C.Hom c f) :
    E.Rel (C.comp (tensor P h (tensor P k l)) (assocRight P)) (C.comp (assocRight P) (tensor P (tensor P h k) l)) := by
  simp only [tensor, first, assocRight]
  repeat first
    | grw [PL.pair_comp CC CL PC]
    | grw [CL.assoc]
    | grw [PL.fst_pair]
    | grw [PL.snd_pair]
    | grw [CL.id_comp]

include CC CL PC PL in
theorem tensor_assocLeft {a b c d e f : O} (h : C.Hom a d) (k : C.Hom b e) (l : C.Hom c f) :
    E.Rel (C.comp (tensor P (tensor P h k) l) (assocLeft P)) (C.comp (assocLeft P) (tensor P h (tensor P k l))) := by
  simp only [tensor, second, assocLeft]
  repeat first
    | grw [PL.pair_comp CC CL PC]
    | grw [CL.assoc]
    | grw [PL.fst_pair]
    | grw [PL.snd_pair]
    | grw [CL.id_comp]

include CC CL PC PL in
theorem first_first_assocLeft {a b c d : O} (f : C.Hom a d) :
    E.Rel (C.comp (first P (b := c) (first P (b := b) f)) (assocLeft P)) (C.comp (assocLeft P) (first P f)) := by
  simp only [tensor, first, second, assocLeft]
  repeat first
    | grw [PL.pair_comp CC CL PC]
    | grw [CL.assoc]
    | grw [PL.fst_pair]
    | grw [PL.snd_pair]
    | grw [CL.id_comp]

include CC CL PC PL in
theorem first_first {a b c d : O} (f : C.Hom a d) :
    E.Rel (first P (b := c) (first P (b := b) f)) (inAssocRight' P (first P f)) := by
  simp only [inAssocRight', tensor, first, second, assocLeft, assocRight]
  repeat first
    | grw [PL.pair_comp CC CL PC]
    | grw [CL.assoc]
    | grw [PL.fst_pair]
    | grw [PL.snd_pair]
    | grw [CL.id_comp]

include CC CL PC PL in
theorem fstTensor_transpose (a b c d : O) :
    E.Rel (C.comp (tensor P P.fst P.fst) (transpose P (a := a) (b := b) (c := c) (d := d))) (P.fst) := by
  simp only [tensor, transpose]
  repeat first
    | grw [PL.pair_comp CC CL PC]
    | grw [CL.assoc]
    | grw [PL.fst_pair]
    | grw [PL.snd_pair]

    | grw [PL.pair_eta]

include CC CL PC PL in
theorem sndTensor_transpose (a b c d : O) :
    E.Rel (C.comp (tensor P P.snd P.snd) (transpose P (a := a) (b := b) (c := c) (d := d))) (P.snd) := by
  simp only [tensor, transpose]
  repeat first
    | grw [PL.pair_comp CC CL PC]
    | grw [CL.assoc]
    | grw [PL.fst_pair]
    | grw [PL.snd_pair]

    | grw [PL.pair_eta]

include CC CL PC PL in
theorem transpose_pairs {a b c d x : O} (f : C.Hom x a) (g : C.Hom x b) (h : C.Hom x c) (k : C.Hom x d) :
    E.Rel (C.comp (transpose P) (P.pair (P.pair f g) (P.pair h k))) (P.pair (P.pair f h) (P.pair g k)) := by
  simp only [transpose]
  repeat first
    | grw [PL.pair_comp CC CL PC]
    | grw [CL.assoc]
    | grw [PL.fst_pair]
    | grw [PL.snd_pair]

include CC CL PC PL in
theorem transpose_pairTensor {a b c d x y : O} (f : C.Hom x a) (g : C.Hom x b) (h : C.Hom y c) (k : C.Hom y d) :
    E.Rel (C.comp (transpose P) (tensor P (P.pair f g) (P.pair h k))) (P.pair (tensor P f h) (tensor P g k)) := by
  simp only [tensor, transpose]
  repeat first
    | grw [PL.pair_comp CC CL PC]
    | grw [CL.assoc]
    | grw [PL.fst_pair]
    | grw [PL.snd_pair]

include CC CL PC PL in
theorem transpose_transpose (a b c d : O) :
    E.Rel (C.comp (transpose P) (transpose P (a := a) (b := b) (c := c) (d := d))) (C.ident) := by
  simp only [transpose]
  repeat first
    | grw [PL.pair_comp CC CL PC]
    | grw [CL.assoc]
    | grw [PL.fst_pair]
    | grw [PL.snd_pair]

    | grw [PL.pair_eta]
    | grw [pair_projections CL PC PL]

include CC PC in
theorem tensor_congr {a b c d : O} {f f' : C.Hom a c} {g g' : C.Hom b d}
    (hf : E.Rel f f') (hg : E.Rel g g') : E.Rel (tensor P f g) (tensor P f' g') :=
  PC.pair (CC.comp hf (E.refl _)) (CC.comp hg (E.refl _))

include PL in
theorem unitLeft_insertLeft (T : TerminalOps C) (a : O) :
    E.Rel (C.comp (unitLeft P T) (insertLeft P T (a := a))) C.ident := PL.snd_pair _ _
include PL in
theorem unitRight_insertRight (T : TerminalOps C) (a : O) :
    E.Rel (C.comp (unitRight P T) (insertRight P T (a := a))) C.ident := PL.fst_pair _ _

include CC CL PC PL in
theorem insertLeft_unitLeft (T : TerminalOps C) (TL : TerminalLaws E T) (a : O) :
    E.Rel (C.comp (insertLeft P T) (unitLeft P T (a := a))) C.ident := by
  change E.Rel (C.comp (P.pair T.terminal C.ident) P.snd) C.ident
  exact E.trans (PL.pair_comp CC CL PC _ _ _)
    (E.trans (PC.pair (E.trans (TL.unique _) (E.symm (TL.unique _))) (CL.id_comp _))
      (pair_projections CL PC PL))

include CC CL PC PL in
theorem insertRight_unitRight (T : TerminalOps C) (TL : TerminalLaws E T) (a : O) :
    E.Rel (C.comp (insertRight P T) (unitRight P T (a := a))) C.ident := by
  change E.Rel (C.comp (P.pair C.ident T.terminal) P.fst) C.ident
  exact E.trans (PL.pair_comp CC CL PC _ _ _)
    (E.trans (PC.pair (CL.id_comp _) (E.trans (TL.unique _) (E.symm (TL.unique _))))
      (pair_projections CL PC PL))

include CC CL PC PL in
theorem terminal_tensor (T : TerminalOps C) (TL : TerminalLaws E T) (a b : O) :
    E.Rel (tensor P (T.terminal (a := a)) (T.terminal (a := b)))
      (C.comp (insertRight P T) T.terminal) := by
  change E.Rel (P.pair _ _) (C.comp (P.pair C.ident T.terminal) T.terminal)
  exact E.trans (PC.pair (TL.unique _) (TL.unique _))
    (E.symm (E.trans (PL.pair_comp CC CL PC _ _ _)
      (PC.pair (CL.id_comp _) (TL.unique _))))
include CC PL in
theorem pair_iff_forward {a b c : O} {f : C.Hom a b} {g : C.Hom a c}
    {k : C.Hom a (P.prod b c)} (h : E.Rel k (P.pair f g)) :
    E.Rel (C.comp P.fst k) f ∧ E.Rel (C.comp P.snd k) g :=
  ⟨E.trans (CC.comp (E.refl _) h) (PL.fst_pair _ _),
   E.trans (CC.comp (E.refl _) h) (PL.snd_pair _ _)⟩

include PC PL in
theorem pair_iff_backward {a b c : O} {f : C.Hom a b} {g : C.Hom a c}
    {k : C.Hom a (P.prod b c)}
    (h : E.Rel (C.comp P.fst k) f ∧ E.Rel (C.comp P.snd k) g) : E.Rel k (P.pair f g) :=
  E.trans (E.symm (PL.pair_eta _)) (PC.pair h.1 h.2)

include CC PC PL in
theorem pair_iff {a b c : O} {f : C.Hom a b} {g : C.Hom a c}
    {k : C.Hom a (P.prod b c)} :
    E.Rel k (P.pair f g) ↔ E.Rel (C.comp P.fst k) f ∧ E.Rel (C.comp P.snd k) g :=
  ⟨pair_iff_forward CC PL,pair_iff_backward PC PL⟩

include PC in
theorem pair_congr_left {a b c : O} {f f' : C.Hom a b} (g : C.Hom a c)
    (h : E.Rel f f') : E.Rel (P.pair f g) (P.pair f' g) := PC.pair h (E.refl _)
include PC in
theorem pair_congr_right {a b c : O} (f : C.Hom a b) {g g' : C.Hom a c}
    (h : E.Rel g g') : E.Rel (P.pair f g) (P.pair f g') := PC.pair (E.refl _) h
include CC PC in
theorem tensor_congr_left {a b c d : O} {f f' : C.Hom a c} (g : C.Hom b d)
    (h : E.Rel f f') : E.Rel (tensor P f g) (tensor P f' g) := tensor_congr CC PC h (E.refl _)
include CC PC in
theorem tensor_congr_right {a b c d : O} (f : C.Hom a c) {g g' : C.Hom b d}
    (h : E.Rel g g') : E.Rel (tensor P f g) (tensor P f g') := tensor_congr CC PC (E.refl _) h
include CC CL PC PL in
theorem transpose_tensorPairs {a b c d x y : O}
    (f : C.Hom x a) (g : C.Hom y b) (h : C.Hom x c) (k : C.Hom y d) :
    E.Rel (C.comp (transpose P) (P.pair (tensor P f g) (tensor P h k)))
      (tensor P (P.pair f h) (P.pair g k)) := by
  simp only [tensor]
  grw [transpose_pairs CC CL PC PL]
  exact PC.pair (E.symm (PL.pair_comp CC CL PC _ _ _))
    (E.symm (PL.pair_comp CC CL PC _ _ _))
end SquareKit.Cartesian
