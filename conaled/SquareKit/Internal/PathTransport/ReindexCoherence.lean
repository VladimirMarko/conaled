import SquareKit.Internal.PathTransport.ConcatenationBeta

namespace SquareKit.Internal.PathTransport.Typed
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true

namespace Model
variable (M : Model)
theorem j_heq {Γ Γ' : M.Context} (hΓ : Γ = Γ')
    {A : M.Family Γ} {A' : M.Family Γ'} (hA : HEq A A')
    {x : M.Section Γ A} {x' : M.Section Γ' A'} (hx : HEq x x')
    {n} {T : StructuralModel.Telescope M.toStructuralModel (M.toStructuralModel.pathContext A x) n}
    {T' : StructuralModel.Telescope M.toStructuralModel (M.toStructuralModel.pathContext A' x') n}
    (hT : HEq T T')
    {D : M.Family (StructuralModel.Telescope.total M.toStructuralModel T)}
    {D' : M.Family (StructuralModel.Telescope.total M.toStructuralModel T')} (hD : HEq D D')
    {d : M.Section _ (M.subTy D (M.toStructuralModel.rootTail A x T))}
    {d' : M.Section _ (M.subTy D' (M.toStructuralModel.rootTail A' x' T'))} (hd : HEq d d') :
    HEq (M.j A x T D d) (M.j A' x' T' D' d') := by
  cases hΓ
  cases eq_of_heq hA
  cases eq_of_heq hx
  cases eq_of_heq hT
  cases eq_of_heq hD
  cases eq_of_heq hd
  rfl
end Model

namespace StructuralModel
variable (M : StructuralModel)

def pathProjection {Γ} (A : M.Family Γ) (x : M.Section Γ A) :=
  M.compSub (M.weaken Γ A) (M.weaken _ (M.pathFamily A x))

def moving {Γ} (A : M.Family Γ) (x : M.Section Γ A) :
    M.Section (M.pathContext A x) (M.subTy A (M.pathProjection A x)) :=
  cast (congrArg (M.Section _) (M.subTy_comp A (M.weaken Γ A) (M.weaken _ (M.pathFamily A x))))
    (M.subTm (M.genericVariable Γ A) (M.weaken _ (M.pathFamily A x)))

theorem pathProjection_sub {Γ Δ} (A : M.Family Γ) (x : M.Section Γ A) (s : M.Substitution Δ Γ) :
    M.compSub (M.pathProjection A x) (M.pathSub A x s) =
      M.compSub s (M.pathProjection (M.subTy A s) (M.subTm x s)) := by
  exact (M.comp_assoc _ _ _).trans
    ((congrArg (M.compSub _) (M.weaken_pathSub A x s)).trans
      ((M.comp_assoc _ _ _).symm.trans
        ((congrArg (fun r => M.compSub r _) (M.weaken_lift A s)).trans (M.comp_assoc _ _ _))))

theorem moving_sub {Γ Δ} (A : M.Family Γ) (x : M.Section Γ A) (s : M.Substitution Δ Γ) :
    HEq (M.subTm (M.moving A x) (M.pathSub A x s))
      (M.moving (M.subTy A s) (M.subTm x s)) := by
  apply (M.subTm_congr (M.subTy_comp A _ _).symm (cast_heq _ _) _).trans
  apply (M.subTm_comp _ _ _).trans
  have h := M.weaken_pathSub A x s
  have he : HEq (M.subTm (M.genericVariable Γ A) (M.compSub (M.weaken _ (M.pathFamily A x)) (M.pathSub A x s)))
      (M.subTm (M.genericVariable Γ A) (M.compSub (M.lift A s) (M.weaken _ (M.pathFamily (M.subTy A s) (M.subTm x s))))) := by rw [h]
  apply he.trans
  apply (M.subTm_comp _ _ _).symm.trans
  apply (M.subTm_congr (M.weaken_lift_type A s) (M.variable_lift A s) _).trans
  exact (cast_heq _ _).symm
theorem baseMoving_type {Γ} (A : M.Family Γ) (x : M.Section Γ A) (e : A = M.base Γ) :
    M.subTy A (M.pathProjection A x) = M.base (M.pathContext A x) :=
  (congrArg (fun a => M.subTy a (M.pathProjection A x)) e).trans (M.base_sub _)

def baseMoving {Γ} (A : M.Family Γ) (x : M.Section Γ A) (e : A = M.base Γ) :
    M.Section (M.pathContext A x) (M.base (M.pathContext A x)) :=
  cast (congrArg (M.Section _) (M.baseMoving_type A x e)) (M.moving A x)

theorem baseMoving_heq {Γ Γ' : M.Context} (hΓ : Γ = Γ')
    {A : M.Family Γ} {A' : M.Family Γ'} (hA : HEq A A')
    {x : M.Section Γ A} {x' : M.Section Γ' A'} (hx : HEq x x')
    (e : A = M.base Γ) (e' : A' = M.base Γ') : HEq (M.baseMoving A x e) (M.baseMoving A' x' e') := by
  cases hΓ
  cases eq_of_heq hA
  cases eq_of_heq hx
  rfl

theorem baseMoving_sub {Γ Δ} (x : M.Section Γ (M.base Γ)) (s : M.Substitution Δ Γ) :
    HEq (M.subTm (M.baseMoving (M.base Γ) x rfl) (M.pathSub (M.base Γ) x s))
      (M.baseMoving (M.subTy (M.base Γ) s) (M.subTm x s) (M.base_sub s)) :=
  (M.subTm_congr (M.baseMoving_type _ _ rfl).symm (cast_heq _ _) _).trans
    ((M.moving_sub _ _ _).trans (cast_heq _ _).symm)

theorem fiber_heq {Γ Γ' : M.Context} (hΓ : Γ = Γ')
    {x : M.Section Γ (M.base Γ)} {x' : M.Section Γ' (M.base Γ')} (hx : HEq x x') :
    HEq (M.fiber x) (M.fiber x') := by
  cases hΓ
  cases eq_of_heq hx
  rfl

theorem movingMotive_sub {Γ Δ} (x : M.Section Γ (M.base Γ)) (s : M.Substitution Δ Γ) :
    M.subTy (M.fiber (M.baseMoving (M.base Γ) x rfl)) (M.pathSub (M.base Γ) x s) =
      M.fiber (M.baseMoving (M.subTy (M.base Γ) s) (M.subTm x s) (M.base_sub s)) :=
  (M.fiber_sub _ _).trans (congrArg M.fiber
    (eq_of_heq ((cast_heq _ _).trans (M.baseMoving_sub x s))))

theorem moving_root {Γ} (A : M.Family Γ) (x : M.Section Γ A) :
    HEq (M.subTm (M.moving A x) (M.rootSub A x)) x := by
  apply (M.subTm_congr (M.subTy_comp A _ _).symm (cast_heq _ _) _).trans
  apply (M.subTm_comp _ _ _).trans
  have h : HEq (M.subTm (M.genericVariable Γ A)
      (M.compSub (M.weaken _ (M.pathFamily A x)) (M.rootSub A x)))
      (M.subTm (M.genericVariable Γ A) (M.sectionSub A x)) := by rw [M.weaken_root]
  exact h.trans (M.variable_section A x)

theorem baseMoving_root {Γ} (A : M.Family Γ) (x : M.Section Γ A) (e : A = M.base Γ) :
    HEq (M.subTm (M.baseMoving A x e) (M.rootSub A x))
      (cast (congrArg (M.Section Γ) e) x) :=
  (M.subTm_congr (M.baseMoving_type A x e).symm (cast_heq _ _) _).trans
    ((M.moving_root A x).trans (cast_heq _ _).symm)

theorem movingMotive_root {Γ} (A : M.Family Γ) (x : M.Section Γ A) (e : A = M.base Γ) :
    M.subTy (M.fiber (M.baseMoving A x e)) (M.rootSub A x) =
      M.fiber (cast (congrArg (M.Section Γ) e) x) :=
  (M.fiber_sub _ _).trans (congrArg M.fiber
    (eq_of_heq ((cast_heq _ _).trans (M.baseMoving_root A x e))))

theorem endpoint_sub {Γ Δ} (A : M.Family Γ) (x y : M.Section Γ A)
    (p : M.Section Γ (M.identity A x y)) (s : M.Substitution Δ Γ) :
    M.compSub (M.pathSub A x s)
      (M.endpointSub (M.subTy A s) (M.subTm x s) (M.subTm y s)
        (cast (congrArg (M.Section Δ) (M.identity_sub A x y s)) (M.subTm p s))) =
      M.compSub (M.endpointSub A x y p) s := by
  apply M.pair_ext (M.pathFamily A x)
  · exact (M.comp_assoc _ _ _).symm.trans
      ((congrArg (fun r => M.compSub r _) (M.weaken_pathSub A x s)).trans
        ((M.comp_assoc _ _ _).trans
          ((congrArg (M.compSub _) (M.weaken_pair _ _ _)).trans
            ((M.section_lift A y s).trans
              ((congrArg (fun r => M.compSub r s) (M.weaken_pair _ _ _).symm).trans
                (M.comp_assoc _ _ _))))))
  · apply (M.subTm_comp _ _ _).symm.trans
    apply (M.subTm_congr (M.variable_pathSub_type A x s) (M.variable_pathSub A x s) _).trans
    apply (M.variable_pair _ _ _).trans
    apply (cast_heq _ _).trans
    apply (cast_heq _ _).trans
    apply HEq.trans _ (M.subTm_comp _ _ _)
    symm
    apply (M.subTm_congr ((M.subTy_comp _ _ _).trans
      ((congrArg (M.subTy _) (M.weaken_pair _ _ _)).trans (M.pathFamily_at A x y)))
      ((M.variable_pair _ _ _).trans (cast_heq _ _)) s)

end StructuralModel

namespace Model
variable (M : Model)
def transportGeneric {Γ} (A : M.Family Γ) (x : M.Section Γ A) (e : A = M.base Γ)
    (b : M.Section Γ (M.fiber (cast (congrArg (M.Section Γ) e) x))) :
    M.Section (M.toStructuralModel.pathContext A x) (M.fiber (M.toStructuralModel.baseMoving A x e)) :=
  M.j A x .nil (M.fiber (M.toStructuralModel.baseMoving A x e))
    (cast (congrArg (M.Section Γ) (M.toStructuralModel.movingMotive_root A x e).symm) b)

theorem transportGeneric_congr {Γ} {A A' : M.Family Γ} (hA : A = A')
    {x : M.Section Γ A} {x' : M.Section Γ A'} (hx : HEq x x')
    (e : A = M.base Γ) (e' : A' = M.base Γ)
    {b : M.Section Γ (M.fiber (cast (congrArg (M.Section Γ) e) x))}
    {b' : M.Section Γ (M.fiber (cast (congrArg (M.Section Γ) e') x'))} (hb : HEq b b') :
    HEq (M.transportGeneric A x e b) (M.transportGeneric A' x' e' b') := by
  cases hA
  cases eq_of_heq hx
  cases eq_of_heq hb
  rfl
theorem transportGeneric_sub {Γ Δ} (x : M.Section Γ (M.base Γ))
    (b : M.Section Γ (M.fiber x)) (s : M.Substitution Δ Γ) :
    HEq (M.subTm (M.transportGeneric (M.base Γ) x rfl b) (M.toStructuralModel.pathSub (M.base Γ) x s))
      (M.transportGeneric (M.subTy (M.base Γ) s) (M.subTm x s) (M.base_sub s)
        (cast (congrArg (M.Section Δ) (M.fiber_sub x s)) (M.subTm b s))) := by
  apply (M.j_sub (M.base Γ) x .nil _ _ s).trans
  apply M.j_heq rfl HEq.rfl HEq.rfl HEq.rfl
    (heq_of_eq (M.toStructuralModel.movingMotive_sub x s))
  apply (cast_heq _ _).trans
  have hbranch : M.toStructuralModel.branchMap (M.base Γ) x .nil s = s :=
    congrArg Subtype.val (StructuralModel.Telescope.square.eq_1 M.toStructuralModel
      (M.toStructuralModel.rootSub (M.base Γ) x)
      (M.toStructuralModel.rootSub (M.subTy (M.base Γ) s) (M.subTm x s))
      (M.toStructuralModel.pathSub (M.base Γ) x s) s (M.toStructuralModel.pathSub_root _ _ _))
  apply (Authoring.subTm_substitution_heq M _ hbranch).trans
  apply (M.toStructuralModel.subTm_congr (M.toStructuralModel.movingMotive_root (M.base Γ) x rfl)
    (cast_heq _ _) s).trans
  exact (cast_heq _ _).symm.trans (cast_heq _ _).symm

def transportApply {Γ} (A : M.Family Γ) (x y : M.Section Γ A)
    (p : M.Section Γ (M.identity A x y)) (e : A = M.base Γ)
    (b : M.Section Γ (M.fiber (cast (congrArg (M.Section Γ) e) x))) :=
  M.subTm (M.transportGeneric A x e b) (M.toStructuralModel.endpointSub A x y p)

theorem transportApply_congr {Γ} {A A' : M.Family Γ} (hA : A = A')
    {x y : M.Section Γ A} {x' y' : M.Section Γ A'} (hx : HEq x x') (hy : HEq y y')
    {p : M.Section Γ (M.identity A x y)} {p' : M.Section Γ (M.identity A' x' y')} (hp : HEq p p')
    (e : A = M.base Γ) (e' : A' = M.base Γ)
    {b : M.Section Γ (M.fiber (cast (congrArg (M.Section Γ) e) x))}
    {b' : M.Section Γ (M.fiber (cast (congrArg (M.Section Γ) e') x'))} (hb : HEq b b') :
    HEq (M.transportApply A x y p e b) (M.transportApply A' x' y' p' e' b') := by
  cases hA
  cases eq_of_heq hx
  cases eq_of_heq hy
  cases eq_of_heq hp
  cases eq_of_heq hb
  rfl

theorem transportApply_sub {Γ Δ} (x y : M.Section Γ (M.base Γ))
    (p : M.Section Γ (M.identity (M.base Γ) x y)) (b : M.Section Γ (M.fiber x))
    (s : M.Substitution Δ Γ) :
    HEq (M.subTm (M.transportApply (M.base Γ) x y p rfl b) s)
      (M.transportApply (M.subTy (M.base Γ) s) (M.subTm x s) (M.subTm y s)
        (cast (congrArg (M.Section Δ) (M.identity_sub (M.base Γ) x y s)) (M.subTm p s))
        (M.base_sub s) (cast (congrArg (M.Section Δ) (M.fiber_sub x s)) (M.subTm b s))) := by
  apply (M.subTm_comp _ _ _).trans
  apply (Authoring.subTm_substitution_heq M _ (M.toStructuralModel.endpoint_sub _ _ _ _ _).symm).trans
  apply (M.subTm_comp _ _ _).symm.trans
  exact M.toStructuralModel.subTm_congr (M.toStructuralModel.movingMotive_sub x s)
    (M.transportGeneric_sub x b s) _

end Model

end SquareKit.Internal.PathTransport.Typed
