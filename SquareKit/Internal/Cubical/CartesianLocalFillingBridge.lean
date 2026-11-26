import SquareKit.Internal.Cubical.CartesianLocalFilling

/-! Generalized-point evaluation for reconstructing filling from represented tests. -/
set_option autoImplicit false
set_option warningAsError true
namespace SquareKit.Cubical.Cartesian
open CategoryTheory
universe u

theorem Term.val_heq {Γ : Context.{u}} {A : Family Γ} (t : Term A)
    {x y : Γ.Elements} (h : x = y) : HEq (t.val x) (t.val y) := by
  cases h
  rfl

def intervalBase {Δ : Context.{u}} (x : (total (interval Δ)).Elements) : Δ.Elements :=
  (projection (interval Δ)).mapElements.obj x

def intervalGeneric {Δ : Context.{u}} (x : (total (interval Δ)).Elements) :
    (total (interval (representable.{u} x.obj.unop))).Elements :=
  (total (interval (representable x.obj.unop))).elementsMk x.obj ⟨⟨𝟙 _⟩,x.val.2⟩

def intervalEvaluation {Δ : Context.{u}} (x : (total (interval Δ)).Elements) :
    (intervalSub (represented (intervalBase x))).mapElements.obj (intervalGeneric x) ⟶ x :=
  Functor.Elements.homMk (𝟙 x.obj) (by
    change (total (interval Δ)).map (𝟙 x.obj)
      ⟨Δ.map (𝟙 x.obj) x.val.1,x.val.2⟩ = x.val
    exact (ConcreteCategory.congr_hom ((total (interval Δ)).map_id x.obj) _).trans
      (congrArg (fun v : Δ.obj x.obj => (⟨v,x.val.2⟩ : (total (interval Δ)).obj x.obj))
        (ConcreteCategory.congr_hom (Δ.map_id x.obj) x.val.1)))


def LocalFilling.value {Γ Δ : Context.{u}} {A : Family Γ} (F : LocalFilling A)
    (p : total (interval Δ) ⟶ Γ) (φ : Subcontext Δ) (r : Term (interval Δ)) (b : OpenBox (Cartesian.reindex A p) φ r)
    (x : (total (interval Δ)).Elements) : (Cartesian.reindex A p).obj x :=
  (Cartesian.reindex A p).map (intervalEvaluation x)
    ((F.fill (intervalSub (represented (intervalBase x)) ≫ p)
      (φ.reindex (represented (intervalBase x)))
      (Term.reindex r (represented (intervalBase x)))
      (b.reindex (represented (intervalBase x)))).val (intervalGeneric x))

/-- Restricting a native uniform filler and evaluating at the generic point
recovers its selected value, not merely an endpoint. -/
theorem Filling.toLocal_value {Γ Δ : Context.{u}} {A : Family Γ} (F : Filling A)
    (hF : F.Lawful) (p : total (interval Δ) ⟶ Γ) (φ : Subcontext Δ)
    (r : Term (interval Δ)) (b : OpenBox (Cartesian.reindex A p) φ r) (x : (total (interval Δ)).Elements) :
    F.toLocal.value p φ r b x = (F.fill p φ r b).val x := by
  unfold LocalFilling.value
  change (Cartesian.reindex A p).map (intervalEvaluation x)
    ((F.fill (intervalSub (represented (intervalBase x)) ≫ p)
      (φ.reindex (represented (intervalBase x)))
      (Term.reindex r (represented (intervalBase x)))
      (b.reindex (represented (intervalBase x)))).val (intervalGeneric x)) = _
  rw [hF.uniform]
  exact (F.fill p φ r b).property (intervalEvaluation x)

def intervalChartHom {Δ : Context.{u}} {x y : (total (interval Δ)).Elements} (f : x ⟶ y) :
    intervalGeneric x ⟶
      (intervalSub (representableMap f.hom.unop)).mapElements.obj
        (intervalGeneric y) :=
  Functor.Elements.homMk f.hom (by
    have hr := @congrArg ((total (interval Δ)).obj y.obj) (ULift.{u} (Cube.Hom y.obj.unop ⟨1⟩))
      _ _ (fun z => z.2) f.map_val
    change (⟨⟨f.hom.unop ≫ 𝟙 _⟩,⟨f.hom.unop ≫ x.val.2.down⟩⟩ :
      (total (interval (representable x.obj.unop))).obj y.obj) = ⟨⟨𝟙 _ ≫ f.hom.unop⟩,y.val.2⟩
    have he : (⟨f.hom.unop ≫ x.val.2.down⟩ : ULift (y.obj.unop ⟶ ⟨1⟩)) = y.val.2 := hr
    apply Sigma.ext
    · exact congrArg ULift.up ((Category.comp_id f.hom.unop).trans (Category.id_comp f.hom.unop).symm)
    · exact heq_of_eq he)

theorem intervalEvaluation_source {Δ : Context.{u}} (x : (total (interval Δ)).Elements) :
    (intervalSub (represented (intervalBase x))).mapElements.obj (intervalGeneric x) = x :=
  Functor.Elements.ext _ _ rfl (intervalEvaluation x).map_val

theorem family_map_heq {Γ : Context.{u}} (A : Family Γ) {x y z : Γ.Elements}
    (f : x ⟶ y) (g : x ⟶ z) (e : y = z) (h : HEq f.hom g.hom) (v : A.obj x) :
    HEq (A.map f v) (A.map g v) :=
  RepresentableClassification.family_map_heq A f g e h v

theorem family_map_identity_heq {Γ : Context.{u}} (A : Family Γ) {x y : Γ.Elements}
    (f : x ⟶ y) (e : x = y) (h : HEq f.hom (𝟙 x.obj)) (v : A.obj x) :
    HEq (A.map f v) v :=
  RepresentableClassification.family_map_identity_heq A f e h v

private theorem local_fill_at_heq {Γ Δ : Context.{u}} {A : Family Γ} (F : LocalFilling A)
    (p : total (interval Δ) ⟶ Γ) (φ : Subcontext Δ) (r : Term (interval Δ)) (b : OpenBox (Cartesian.reindex A p) φ r)
    {I : Cube} {σ τ : representable I ⟶ Δ} (e : σ = τ)
    (x : (total (interval (representable I))).Elements) :
    HEq ((F.fill (intervalSub σ ≫ p) (φ.reindex σ) (Term.reindex r σ) (b.reindex σ)).val x)
      ((F.fill (intervalSub τ ≫ p) (φ.reindex τ) (Term.reindex r τ) (b.reindex τ)).val x) := by
  cases e
  rfl

theorem LocalFilling.value_natural {Γ Δ : Context.{u}} {A : Family Γ} (F : LocalFilling A)
    (hF : F.Lawful) (p : total (interval Δ) ⟶ Γ) (φ : Subcontext Δ)
    (r : Term (interval Δ)) (b : OpenBox (Cartesian.reindex A p) φ r)
    {x y : (total (interval Δ)).Elements} (f : x ⟶ y) :
    (Cartesian.reindex A p).map f (F.value p φ r b x) = F.value p φ r b y := by
  let sx := represented (intervalBase x)
  let sy := represented (intervalBase y)
  let k := representableMap f.hom.unop
  let tx := F.fill (intervalSub sx ≫ p) (φ.reindex sx) (Term.reindex r sx) (b.reindex sx)
  have baseRel : k ≫ sx = sy := represented_restrict ((projection (interval Δ)).mapElements.map f)
  have liftedRel : intervalSub k ≫ intervalSub sx =
      intervalSub sy := by
    change intervalSub (k ≫ sx) = intervalSub sy
    exact @congrArg (representable.{u} y.obj.unop ⟶ Δ)
      (total (interval (representable.{u} y.obj.unop)) ⟶ total (interval Δ))
      _ _ (fun σ => intervalSub σ) baseRel
  have targetRel : (intervalSub sx).mapElements.obj
      ((intervalSub k).mapElements.obj (intervalGeneric y)) = y :=
    (congrArg (fun σ => σ.mapElements.obj (intervalGeneric y)) liftedRel).trans (intervalEvaluation_source y)
  have unif := hF.uniform (intervalSub sx ≫ p) (φ.reindex sx) (Term.reindex r sx) (b.reindex sx) f.hom.unop
  have vrel := local_fill_at_heq F p φ r b baseRel (intervalGeneric y)
  have hv : HEq (tx.val ((intervalSub k).mapElements.obj (intervalGeneric y)))
      ((F.fill (intervalSub sy ≫ p) (φ.reindex sy) (Term.reindex r sy) (b.reindex sy)).val (intervalGeneric y)) := by
    exact (heq_of_eq (congrArg (fun t => t.val (intervalGeneric y)) unif).symm).trans vrel
  apply eq_of_heq
  have m := (Cartesian.reindex A p).map_comp (intervalEvaluation x) f
  have hm := family_map_heq (Cartesian.reindex A p) (intervalEvaluation x ≫ f)
    ((intervalSub sx).mapElements.map (intervalChartHom f)) targetRel.symm
    (heq_of_eq (Category.id_comp f.hom)) (tx.val (intervalGeneric x))
  have hn := tx.property (intervalChartHom f)
  have hy := family_map_identity_heq (Cartesian.reindex A p) (intervalEvaluation y)
    (intervalEvaluation_source y) HEq.rfl
    ((F.fill (intervalSub sy ≫ p) (φ.reindex sy) (Term.reindex r sy) (b.reindex sy)).val (intervalGeneric y))
  exact (heq_of_eq (ConcreteCategory.congr_hom m (tx.val (intervalGeneric x))).symm).trans
    (hm.trans ((heq_of_eq hn).trans (hv.trans hy.symm)))

def LocalFilling.toFilling {Γ : Context.{u}} {A : Family Γ} (F : LocalFilling A)
    (hF : F.Lawful) : Filling A where
  fill p φ r b := ⟨F.value p φ r b, fun f => F.value_natural hF p φ r b f⟩

theorem LocalFilling.value_substitution {Γ Δ Θ : Context.{u}} {A : Family Γ}
    (F : LocalFilling A) (p : total (interval Δ) ⟶ Γ) (φ : Subcontext Δ)
    (r : Term (interval Δ)) (b : OpenBox (Cartesian.reindex A p) φ r) (σ : Θ ⟶ Δ)
    (x : (total (interval Θ)).Elements) :
    F.value (intervalSub σ ≫ p) (φ.reindex σ) (Term.reindex r σ) (b.reindex σ) x =
      F.value p φ r b ((intervalSub σ).mapElements.obj x) := by
  let y := (intervalSub σ).mapElements.obj x
  have e : represented (intervalBase x) ≫ σ = represented (intervalBase y) :=
    (represented_naturality σ (intervalBase x)).symm
  have hv := local_fill_at_heq F p φ r b e (intervalGeneric x)
  have hx := family_map_identity_heq (Cartesian.reindex A (intervalSub σ ≫ p))
    (intervalEvaluation x) (intervalEvaluation_source x) HEq.rfl
    ((F.fill (intervalSub (represented (intervalBase x)) ≫ intervalSub σ ≫ p)
      ((φ.reindex σ).reindex (represented (intervalBase x)))
      (Term.reindex (Term.reindex r σ) (represented (intervalBase x)))
      ((b.reindex σ).reindex (represented (intervalBase x)))).val (intervalGeneric x))
  have hy := family_map_identity_heq (Cartesian.reindex A p)
    (intervalEvaluation y) (intervalEvaluation_source y) HEq.rfl
    ((F.fill (intervalSub (represented (intervalBase y)) ≫ p)
      (φ.reindex (represented (intervalBase y)))
      (Term.reindex r (represented (intervalBase y)))
      (b.reindex (represented (intervalBase y)))).val (intervalGeneric y))
  exact eq_of_heq (hx.trans (hv.trans hy.symm))

theorem Filling.toLocal_toFilling {Γ : Context.{u}} {A : Family Γ} (F : Filling A)
    (hF : F.Lawful) : F.toLocal.toFilling (Filling.toLocal_lawful hF) = F := by
  cases F with
  | mk fill =>
    change Filling.mk _ = Filling.mk fill
    apply congrArg Filling.mk
    funext Δ p φ r b
    apply Term.ext
    intro x
    exact Filling.toLocal_value ⟨fill⟩ hF p φ r b x

theorem LocalFilling.toFilling_fills {Γ Δ : Context.{u}} {A : Family Γ}
    (F : LocalFilling A) (hF : F.Lawful) (p : total (interval Δ) ⟶ Γ)
    (φ : Subcontext Δ) (r : Term (interval Δ)) (b : OpenBox (Cartesian.reindex A p) φ r) :
    b.Fills ((F.toFilling hF).fill p φ r b) := by
  constructor
  · apply Term.ext
    intro x
    let y := (graph r).mapElements.obj x
    let σ := represented x
    have hc := congrArg (fun t => t.val (representableGeneric x.obj.unop))
      (hF.fills (intervalSub σ ≫ p) (φ.reindex σ) (Term.reindex r σ) (b.reindex σ)).1
    have hy := family_map_identity_heq (Cartesian.reindex A p)
      (intervalEvaluation y) (intervalEvaluation_source y) HEq.rfl
      ((F.fill (intervalSub σ ≫ p) (φ.reindex σ) (Term.reindex r σ)
        (b.reindex σ)).val (intervalGeneric y))
    have e : σ.mapElements.obj (representableGeneric x.obj.unop) = x := by
      exact Functor.Elements.ext (σ.mapElements.obj (representableGeneric x.obj.unop)) x rfl
        ((ConcreteCategory.congr_hom (Δ.map_id x.obj) _).trans (represented_id x))
    have hr : r.val (σ.mapElements.obj (representableGeneric x.obj.unop)) = r.val x :=
      eq_of_heq (Term.val_heq r e)
    have ec : (graph (Term.reindex r σ)).mapElements.obj (representableGeneric x.obj.unop) =
        intervalGeneric y := by
      have ev : ((graph (Term.reindex r σ)).mapElements.obj
          (representableGeneric x.obj.unop)).val = (intervalGeneric y).val := by
        apply Sigma.ext
        · rfl
        · exact heq_of_eq hr
      exact Functor.Elements.ext _ _ rfl
        ((ConcreteCategory.congr_hom ((total (interval (representable x.obj.unop))).map_id x.obj) _).trans ev)
    have hv := Term.val_heq (F.fill (intervalSub σ ≫ p) (φ.reindex σ)
      (Term.reindex r σ) (b.reindex σ)) ec
    exact eq_of_heq (hy.trans (hv.symm.trans ((heq_of_eq hc).trans (Term.val_heq b.base e))))
  · intro x hx
    let σ := represented (intervalBase x)
    have ht : (φ.reindex (projection (interval Δ))).Holds
        ((intervalSub σ).mapElements.obj (intervalGeneric x)) :=
      (congrArg (φ.reindex (projection (interval Δ))).Holds (intervalEvaluation_source x)).mpr hx
    have hl := (hF.fills (intervalSub σ ≫ p) (φ.reindex σ) (Term.reindex r σ) (b.reindex σ)).2
      (intervalGeneric x) ht
    change (Cartesian.reindex A p).map (intervalEvaluation x) _ = _
    rw [hl]
    exact b.tube.natural (intervalEvaluation x) ht

theorem LocalFilling.toFilling_lawful {Γ : Context.{u}} {A : Family Γ}
    (F : LocalFilling A) (hF : F.Lawful) : (F.toFilling hF).Lawful where
  fills := F.toFilling_fills hF
  uniform p φ r b σ := by
    apply Term.ext
    intro x
    exact F.value_substitution p φ r b σ x

theorem LocalFilling.toFilling_toLocal {Γ : Context.{u}} {A : Family Γ}
    (F : LocalFilling A) (hF : F.Lawful) : (F.toFilling hF).toLocal = F := by
  cases F with
  | mk fill =>
    change LocalFilling.mk _ = LocalFilling.mk fill
    apply congrArg LocalFilling.mk
    funext I p φ r b
    apply Term.ext
    intro x
    change LocalFilling.value ⟨fill⟩ p φ r b x = (fill p φ r b).val x
    unfold LocalFilling.value
    have hu := hF.uniform p φ r b x.val.1.down
    change (Cartesian.reindex A p).map (intervalEvaluation x)
      ((fill (intervalSub (representableMap x.val.1.down) ≫ p)
        (φ.reindex (representableMap x.val.1.down))
        (Term.reindex r (representableMap x.val.1.down))
        (b.reindex (representableMap x.val.1.down))).val (intervalGeneric x)) = _
    exact (congrArg (fun t => (Cartesian.reindex A p).map (intervalEvaluation x)
      (t.val (intervalGeneric x))) hu).trans ((fill p φ r b).property (intervalEvaluation x))


end SquareKit.Cubical.Cartesian
