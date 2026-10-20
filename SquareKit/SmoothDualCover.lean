import SquareKit.SmoothOpenTopology
import Mathlib.RingTheory.Nilpotent.Basic
import SquareKit.SmoothGeometricDual

noncomputable section
namespace SquareKit.SmoothOpenSite
open CategoryTheory Opposite SmoothAlgebra SmoothPresentationSite SmoothGeometricKL
attribute [local instance] DualExtension.smoothStructure

/-- Restriction to zero on the represented dual extension. -/
def dualZero (A : Code) : dual A ⟶ A := dualLift A A (𝟙 A) ⟨0, by simp⟩

theorem inl_dualZero (A : Code) : inl A ≫ dualZero A = 𝟙 A := dualLift_inl _ _ _ _

theorem dualZero_actual (A : Code) (z : Carrier (dual A)) :
    smoothMap (dualZero A) z = (dualToActual A z).fst := by
  change (dualToActual A z).fst + (dualToActual A z).snd * (0 : Carrier A) = _
  rw [mul_zero, add_zero]

theorem dualZero_natural {A B : Code} (f : A ⟶ B) :
    dualMap f ≫ dualZero B = dualZero A ≫ f := by
  apply Hom.ext
  intro z
  change smoothMap (dualZero B) (smoothMap (dualMap f) z) = smoothMap f (smoothMap (dualZero A) z)
  rw [dualZero_actual, dualMap_actual, dualZero_actual]
  rfl

theorem real_dual_eps (A : Code) (h : Hom (Carrier (dual A)) ℝ) :
    h (eps A).val = 0 := by
  have hs : h (eps A).val * h (eps A).val = 0 := by
    rw [← h.map_mul, (eps A).property]
    exact map_zero h.toAlgHom
  exact (mul_self_eq_zero.mp hs)

theorem real_dual_factor (A : Code) (h : Hom (Carrier (dual A)) ℝ) :
    h = Hom.comp (Hom.comp h (smoothMap (inl A))) (dualZero A) := by
  apply Presentation.unique A.equations
  · rw [← Hom.comp_assoc]
    change Hom.comp h (smoothMap (inl A)) = Hom.comp (Hom.comp h (smoothMap (inl A))) (inl A ≫ dualZero A)
    rw [inl_dualZero]
    rfl
  · change h (eps A).val = h (smoothMap (inl A) (smoothMap (dualZero A) (eps A).val))
    rw [real_dual_eps]
    have he : smoothMap (dualZero A) (eps A).val = 0 := dualLift_eps _ _ _ _
    rw [he]
    change 0 = h.toAlgHom ((smoothMap (inl A)).toAlgHom 0)
    rw [map_zero, map_zero]

/-- The real points agree; this does not identify the full algebras. -/
def dualRealPointEquiv (A : Code) :
    Hom (Carrier (dual A)) ℝ ≃ Hom (Carrier A) ℝ where
  toFun h := Hom.comp h (smoothMap (inl A))
  invFun h := Hom.comp h (smoothMap (dualZero A))
  left_inv h := (real_dual_factor A h).symm
  right_inv h := by
    change Hom.comp (Hom.comp h (dualZero A)) (inl A) = h
    rw [← Hom.comp_assoc]
    change Hom.comp h (inl A ≫ dualZero A) = h
    rw [inl_dualZero]
    rfl

/-- Every arbitrary principal cover of the dual stage has exactly the
zero-restricted covering condition on the base, including empty families. -/
theorem dual_covers_iff (A : Code) {ι : Type*} (s : ι → Carrier (dual A)) :
    OpenCover.Covers s ↔ OpenCover.Covers (fun i => smoothMap (dualZero A) (s i)) := by
  constructor
  · intro hs h
    exact hs (Hom.comp h (smoothMap (dualZero A)))
  · intro hs h
    obtain ⟨i, hi⟩ := hs (Hom.comp h (smoothMap (inl A)))
    refine ⟨i, ?_⟩
    have he := congrArg (fun k : Hom (Carrier (dual A)) ℝ => k (s i)) (real_dual_factor A h)
    exact fun hn => hi (he.symm.trans hn)

theorem dual_nilpotent_difference (A : Code) (s : Carrier (dual A)) :
    IsNilpotent (s - smoothMap (inl A) (smoothMap (dualZero A) s)) := by
  refine ⟨2, ?_⟩
  have inj : Function.Injective (dualToActual A) := by
    intro x y he
    have hx := congrArg (fun h : Hom (Carrier (dual A)) (Carrier (dual A)) => h x)
      (dual_comparison_inverse_rev A)
    have hy := congrArg (fun h : Hom (Carrier (dual A)) (Carrier (dual A)) => h y)
      (dual_comparison_inverse_rev A)
    exact hx.symm.trans ((congrArg (dualFromActual A) he).trans hy)
  apply inj
  rw [pow_two]
  change dualToActual A (_ * _) = dualToActual A 0
  rw [Hom.map_mul]
  have hz : dualToActual A 0 = 0 := map_zero (dualToActual A).toAlgHom
  have hs : dualToActual A (s - smoothMap (inl A) (smoothMap (dualZero A) s)) =
      dualToActual A s - dualToActual A (smoothMap (inl A) (smoothMap (dualZero A) s)) :=
    map_sub (dualToActual A).toAlgHom s _
  rw [hz, hs]
  have hi (a : Carrier A) : dualToActual A (smoothMap (inl A) a) = TrivSqZeroExt.inl a :=
    congrArg (fun h : Hom (Carrier A) (DualNumber (Carrier A)) => h a)
      (Presentation.toDual_inclusion A.equations)
  rw [hi, dualZero_actual]
  apply TrivSqZeroExt.ext
  · simp only [TrivSqZeroExt.fst_mul, TrivSqZeroExt.fst_sub,
      TrivSqZeroExt.fst_inl, sub_self, mul_zero, TrivSqZeroExt.fst_zero]
  · simp only [TrivSqZeroExt.snd_mul, TrivSqZeroExt.fst_sub,
      TrivSqZeroExt.fst_inl, sub_self, MulOpposite.op_zero, zero_smul, add_zero, TrivSqZeroExt.snd_zero]

/-- Inverting an element of a dual stage only depends on its zero restriction,
even after an arbitrary smooth map to an infinitesimal target. -/
theorem dual_isUnit_iff {A B : Code} (f : dual A ⟶ B) (s : Carrier (dual A)) :
    IsUnit (smoothMap f s) ↔
      IsUnit (smoothMap f (smoothMap (inl A) (smoothMap (dualZero A) s))) := by
  let x := smoothMap f s
  let y := smoothMap f (smoothMap (inl A) (smoothMap (dualZero A) s))
  have hn : IsNilpotent (x - y) := by
    have h := (dual_nilpotent_difference A s).map (smoothMap f).toAlgHom
    rwa [map_sub] at h
  constructor
  · intro hx
    have h := hn.neg.isUnit_add_left_of_commute hx (Commute.all _ _)
    have he : x + -(x - y) = y := by ring
    rwa [he] at h
  · intro hy
    have h := hn.isUnit_add_left_of_commute hy (Commute.all _ _)
    have he : y + (x - y) = x := by ring
    rwa [he] at h

/-- A stage arrow belongs to a generated principal sieve precisely when
it inverts one of the listed elements. -/
theorem principalSieve_iff_isUnit {A B : Code} {ι : Type*}
    (s : ι → Carrier A) (f : A ⟶ B) :
    principalSieve A s f.op ↔ ∃ i, IsUnit (smoothMap f (s i)) := by
  constructor
  · rintro ⟨W, u, v, ⟨i⟩, he⟩
    refine ⟨i, ?_⟩
    have h := (PresentedLocalization.atBase_isUnit A.equations (s i)).map
      (smoothMap u.unop).toAlgHom
    have hf : localizationBase A (s i) ≫ u.unop = f := congrArg Quiver.Hom.unop he
    change IsUnit (smoothMap (localizationBase A (s i) ≫ u.unop) (s i)) at h
    rwa [hf] at h
  · rintro ⟨i, hi⟩
    let k : localization A (s i) ⟶ B :=
      (PresentedLocalization.atHomEquiv A.equations (s i)).symm ⟨smoothMap f, hi⟩
    have hk : localizationBase A (s i) ≫ k = f :=
      congrArg Subtype.val ((PresentedLocalization.atHomEquiv A.equations (s i)).apply_symm_apply
        ⟨smoothMap f, hi⟩)
    exact ⟨_, k.op, _, ⟨i⟩, congrArg Quiver.Hom.op hk⟩

/-- Arbitrary principal covering sieves of Dual(A) are pullbacks of their
zero restrictions. Equality tests all stage arrows, including nilpotents. -/
theorem dual_principalSieve (A : Code) {ι : Type*} (s : ι → Carrier (dual A)) :
    principalSieve (dual A) s =
      (principalSieve A (fun i => smoothMap (dualZero A) (s i))).pullback (inl A).op := by
  rw [principalSieve_pullback]
  apply Sieve.ext
  intro B f
  change principalSieve (dual A) s f.unop.op ↔
    principalSieve (dual A) (fun i => smoothMap (inl A) (smoothMap (dualZero A) (s i))) f.unop.op
  rw [principalSieve_iff_isUnit, principalSieve_iff_isUnit]
  exact exists_congr (fun i => dual_isUnit_iff f.unop (s i))

theorem dualMap_id (A : Code) : dualMap (𝟙 A) = 𝟙 (dual A) := by
  apply dual_ext
  · rw [dualMap_inl, Category.id_comp, Category.comp_id]
  · exact dualLift_eps _ _ _ _

theorem dualMap_comp {A B C : Code} (f : A ⟶ B) (g : B ⟶ C) :
    dualMap (f ≫ g) = dualMap f ≫ dualMap g := by
  apply dual_ext
  · rw [dualMap_inl, ← Category.assoc, dualMap_inl]
    simpa only [Category.assoc] using
      congrArg (fun k : B ⟶ dual C => f ≫ k) (dualMap_inl g).symm
  · change smoothMap (dualMap (f ≫ g)) (eps A).val =
      smoothMap (dualMap g) (smoothMap (dualMap f) (eps A).val)
    rw [dualLift_eps, dualLift_eps, dualLift_eps]

abbrev dualFunctor : Code ⥤ Code where
  obj := dual
  map := dualMap
  map_id := dualMap_id
  map_comp := dualMap_comp

/-- Test a sieve using full dualized parameter stages. Unlike real-point
restriction this retains the infinitesimal coordinate in each test arrow. -/
def dualParameterSieve (A : Code) {X : Site} (u : op (dual A) ⟶ X) (R : Sieve X) :
    Sieve (op A) where
  arrows B f := R ((dualMap f.unop).op ≫ u)
  downward_closed := by
    intro B C f hf g
    have h := R.downward_closed hf (dualMap g.unop).op
    change R ((dualMap (g ≫ f).unop).op ≫ u)
    rw [unop_comp, dualMap_comp, op_comp, Category.assoc]
    exact h

/-- Every cover can be lifted to a cover of ordinary parameter stages with
full dual stages above it. This is proved for the generated topology. -/
theorem dualParameterSieve_cover {X : Site} (R : Sieve X) (hR : R ∈ topology X) :
    ∀ (A : Code) (u : op (dual A) ⟶ X), dualParameterSieve A u R ∈ topology (op A) := by
  induction hR with
  | of X R hR =>
    obtain ⟨ι, s, hs, rfl⟩ := hR
    intro A u
    let t : ι → Carrier A := fun i => smoothMap (dualZero A) (smoothMap u.unop (s i))
    have ht : OpenCover.Covers t :=
      (dual_covers_iff A _).mp (OpenCover.map_covers (smoothMap u.unop) s hs)
    apply topology.superset_covering _ (principal_covering A t ht)
    intro B f hf
    obtain ⟨i, hi⟩ := (principalSieve_iff_isUnit t f.unop).mp hf
    change principalSieve X.unop s ((dualMap f.unop).op ≫ u)
    apply (principalSieve_iff_isUnit s (u.unop ≫ dualMap f.unop)).mpr
    refine ⟨i, ?_⟩
    change IsUnit (smoothMap (dualMap f.unop) (smoothMap u.unop (s i)))
    apply (dual_isUnit_iff (dualMap f.unop) _).mpr
    have hc := congrArg (fun k : A ⟶ dual B.unop => smoothMap k (t i)) (dualMap_inl f.unop)
    change smoothMap (dualMap f.unop) (smoothMap (inl A) (t i)) =
      smoothMap (inl B.unop) (smoothMap f.unop (t i)) at hc
    rw [hc]
    exact hi.map (smoothMap (inl B.unop)).toAlgHom
  | top X =>
    intro A u
    exact topology.top_mem _
  | transitive X R S hR hS ihR ihS =>
    intro A u
    apply topology.transitive (ihR A u)
    intro B f hf
    have h := ihS hf B.unop (𝟙 (op (dual B.unop)))
    convert h using 1
    apply Sieve.ext
    intro C g
    change S ((dualMap (g ≫ f).unop).op ≫ u) ↔
      S (((dualMap g.unop).op ≫ 𝟙 _) ≫ ((dualMap f.unop).op ≫ u))
    rw [Category.comp_id, unop_comp, dualMap_comp, op_comp, Category.assoc]

/-- Evaluate the universal dual parameter at the nilpotent carried by an
arbitrary stage arrow. This keeps that nilpotent instead of setting it to zero. -/
def parameterEvaluation {A B : Code} (h : dual A ⟶ B) : dual B ⟶ B :=
  dualLift B B (𝟙 B) ⟨smoothMap h (eps A).val, by
    rw [← (smoothMap h).map_mul, (eps A).property]
    exact map_zero (smoothMap h).toAlgHom⟩

theorem parameterEvaluation_inl {A B : Code} (h : dual A ⟶ B) :
    inl B ≫ parameterEvaluation h = 𝟙 B := dualLift_inl _ _ _ _

theorem parameter_factorization {A B : Code} (h : dual A ⟶ B) :
    dualMap (inl A ≫ h) ≫ parameterEvaluation h = h := by
  apply dual_ext
  · rw [← Category.assoc, dualMap_inl, Category.assoc]
    change (inl A ≫ h) ≫ (inl B ≫ dualLift B B (𝟙 B) _) = _
    rw [dualLift_inl, Category.comp_id]
  · change smoothMap (parameterEvaluation h)
      (smoothMap (dualMap (inl A ≫ h)) (eps A).val) = _
    rw [dualLift_eps]
    exact dualLift_eps _ _ _ _

theorem parameterEvaluation_natural {A B C : Code} (h : dual A ⟶ B) (k : B ⟶ C) :
    dualMap k ≫ parameterEvaluation (h ≫ k) = parameterEvaluation h ≫ k := by
  apply dual_ext
  · rw [← Category.assoc, dualMap_inl, Category.assoc]
    change k ≫ (inl C ≫ dualLift C C (𝟙 C) _) =
      (inl B ≫ dualLift B B (𝟙 B) _) ≫ k
    rw [dualLift_inl, dualLift_inl, Category.comp_id, Category.id_comp]
  · change smoothMap (parameterEvaluation (h ≫ k))
      (smoothMap (dualMap k) (eps B).val) =
      smoothMap k (smoothMap (parameterEvaluation h) (eps B).val)
    rw [dualLift_eps]
    change smoothMap (dualLift C C (𝟙 C) _) (eps C).val =
      smoothMap k (smoothMap (dualLift B B (𝟙 B) _) (eps B).val)
    rw [dualLift_eps, dualLift_eps]
    rfl

/-- The lifted parameter cover refines the original sieve after projection.
This uses full stage-arrow factorization, including nonzero nilpotents. -/
theorem dualParameterSieve_projection (A : Code) {X : Site}
    (u : op (dual A) ⟶ X) (R : Sieve X) :
    (dualParameterSieve A u R).pullback (inl A).op ≤ R.pullback u := by
  intro B f hf
  have h := R.downward_closed hf (parameterEvaluation f.unop).op
  change R ((parameterEvaluation f.unop).op ≫
    ((dualMap (inl A ≫ f.unop)).op ≫ u)) at h
  rw [← Category.assoc, ← op_comp, parameter_factorization] at h
  exact h

end SquareKit.SmoothOpenSite
