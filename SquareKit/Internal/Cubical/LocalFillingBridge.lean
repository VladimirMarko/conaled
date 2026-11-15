import SquareKit.Internal.Cubical.LocalFilling
import SquareKit.Internal.Cubical.PartialRestriction
import SquareKit.Internal.Cubical.FreshExtensionSubstitution

/-! Generalized-point evaluation for reconstructing filling from represented tests. -/
set_option autoImplicit false
set_option warningAsError true
namespace SquareKit.Cubical.Presheaf
open CategoryTheory
universe u

def intervalBase {Δ : Context.{u}} (x : (total (interval Δ)).Elements) : Δ.Elements :=
  (projection (interval Δ)).mapElements.obj x

def intervalGeneric {Δ : Context.{u}} (x : (total (interval Δ)).Elements) :
    (total (interval (representable.{u} x.obj.unop))).Elements :=
  (total (interval (representable x.obj.unop))).elementsMk x.obj ⟨⟨𝟙 _⟩,x.val.2⟩

def intervalEvaluation {Δ : Context.{u}} (x : (total (interval Δ)).Elements) :
    (liftSub (interval Δ) (represented (intervalBase x))).mapElements.obj (intervalGeneric x) ⟶ x :=
  Functor.Elements.homMk (𝟙 x.obj) (by
    change (total (interval Δ)).map (𝟙 x.obj)
      ⟨Δ.map (𝟙 x.obj) x.val.1,x.val.2⟩ = x.val
    exact (ConcreteCategory.congr_hom ((total (interval Δ)).map_id x.obj) _).trans
      (congrArg (fun v : Δ.obj x.obj => (⟨v,x.val.2⟩ : (total (interval Δ)).obj x.obj))
        (ConcreteCategory.congr_hom (Δ.map_id x.obj) x.val.1)))


def LocalFilling.value {Γ Δ : Context.{u}} {A : Family Γ} (F : LocalFilling A)
    (p : total (interval Δ) ⟶ Γ) (φ : Cofibration Δ) (b : OpenBox (Presheaf.reindex A p) φ)
    (x : (total (interval Δ)).Elements) : (Presheaf.reindex A p).obj x :=
  (Presheaf.reindex A p).map (intervalEvaluation x)
    ((F.fill (liftSub (interval Δ) (represented (intervalBase x)) ≫ p)
      (φ.reindex (represented (intervalBase x)))
      (b.reindex (represented (intervalBase x)))).val (intervalGeneric x))

/-- Restricting a native uniform filler and evaluating at the generic point
recovers its selected value, not merely an endpoint. -/
theorem Filling.toLocal_value {Γ Δ : Context.{u}} {A : Family Γ} (F : Filling A)
    (hF : F.Lawful) (p : total (interval Δ) ⟶ Γ) (φ : Cofibration Δ)
    (b : OpenBox (Presheaf.reindex A p) φ) (x : (total (interval Δ)).Elements) :
    F.toLocal.value p φ b x = (F.fill p φ b).val x := by
  unfold LocalFilling.value
  change (Presheaf.reindex A p).map (intervalEvaluation x)
    ((F.fill (liftSub (interval Δ) (represented (intervalBase x)) ≫ p)
      (φ.reindex (represented (intervalBase x)))
      (b.reindex (represented (intervalBase x)))).val (intervalGeneric x)) = _
  rw [hF.uniform]
  exact (F.fill p φ b).property (intervalEvaluation x)

def intervalChartHom {Δ : Context.{u}} {x y : (total (interval Δ)).Elements} (f : x ⟶ y) :
    intervalGeneric x ⟶
      (liftSub (interval (representable x.obj.unop)) (representableMap f.hom.unop)).mapElements.obj
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
    (liftSub (interval Δ) (represented (intervalBase x))).mapElements.obj (intervalGeneric x) = x :=
  Functor.Elements.ext _ _ rfl (intervalEvaluation x).map_val

theorem family_map_heq {Γ : Context.{u}} (A : Family Γ) {x y z : Γ.Elements}
    (f : x ⟶ y) (g : x ⟶ z) (e : y = z) (h : HEq f.hom g.hom) (v : A.obj x) :
    HEq (A.map f v) (A.map g v) := by
  cases e
  have hfg : f = g := Functor.Elements.hom_ext (eq_of_heq h)
  cases hfg
  rfl

theorem family_map_identity_heq {Γ : Context.{u}} (A : Family Γ) {x y : Γ.Elements}
    (f : x ⟶ y) (e : x = y) (h : HEq f.hom (𝟙 x.obj)) (v : A.obj x) :
    HEq (A.map f v) v := by
  cases e
  have hfid : f = 𝟙 x := Functor.Elements.hom_ext (eq_of_heq h)
  cases hfid
  exact heq_of_eq (ConcreteCategory.congr_hom (A.map_id x) v)

private theorem local_fill_at_heq {Γ Δ : Context.{u}} {A : Family Γ} (F : LocalFilling A)
    (p : total (interval Δ) ⟶ Γ) (φ : Cofibration Δ) (b : OpenBox (Presheaf.reindex A p) φ)
    {I : Cube} {σ τ : representable I ⟶ Δ} (e : σ = τ)
    (x : (total (interval (representable I))).Elements) :
    HEq ((F.fill (liftSub (interval Δ) σ ≫ p) (φ.reindex σ) (b.reindex σ)).val x)
      ((F.fill (liftSub (interval Δ) τ ≫ p) (φ.reindex τ) (b.reindex τ)).val x) := by
  cases e
  rfl

theorem LocalFilling.value_natural {Γ Δ : Context.{u}} {A : Family Γ} (F : LocalFilling A)
    (hF : F.Lawful) (p : total (interval Δ) ⟶ Γ) (φ : Cofibration Δ)
    (b : OpenBox (Presheaf.reindex A p) φ)
    {x y : (total (interval Δ)).Elements} (f : x ⟶ y) :
    (Presheaf.reindex A p).map f (F.value p φ b x) = F.value p φ b y := by
  let sx := represented (intervalBase x)
  let sy := represented (intervalBase y)
  let k := representableMap f.hom.unop
  let tx := F.fill (liftSub (interval Δ) sx ≫ p) (φ.reindex sx) (b.reindex sx)
  have baseRel : k ≫ sx = sy := represented_restrict ((projection (interval Δ)).mapElements.map f)
  have liftedRel : liftSub (interval (representable x.obj.unop)) k ≫ liftSub (interval Δ) sx =
      liftSub (interval Δ) sy := by
    change liftSub (interval Δ) (k ≫ sx) = liftSub (interval Δ) sy
    exact @congrArg (representable.{u} y.obj.unop ⟶ Δ)
      (total (interval (representable.{u} y.obj.unop)) ⟶ total (interval Δ))
      _ _ (fun σ => liftSub (interval Δ) σ) baseRel
  have targetRel : (liftSub (interval Δ) sx).mapElements.obj
      ((liftSub (interval (representable x.obj.unop)) k).mapElements.obj (intervalGeneric y)) = y :=
    (congrArg (fun σ => σ.mapElements.obj (intervalGeneric y)) liftedRel).trans (intervalEvaluation_source y)
  have unif := hF.uniform (liftSub (interval Δ) sx ≫ p) (φ.reindex sx) (b.reindex sx) f.hom.unop
  have vrel := local_fill_at_heq F p φ b baseRel (intervalGeneric y)
  have hv : HEq (tx.val ((liftSub (interval (representable x.obj.unop)) k).mapElements.obj (intervalGeneric y)))
      ((F.fill (liftSub (interval Δ) sy ≫ p) (φ.reindex sy) (b.reindex sy)).val (intervalGeneric y)) := by
    exact (heq_of_eq (congrArg (fun t => t.val (intervalGeneric y)) unif).symm).trans vrel
  apply eq_of_heq
  have m := (Presheaf.reindex A p).map_comp (intervalEvaluation x) f
  have hm := family_map_heq (Presheaf.reindex A p) (intervalEvaluation x ≫ f)
    ((liftSub (interval Δ) sx).mapElements.map (intervalChartHom f)) targetRel.symm
    (heq_of_eq (Category.id_comp f.hom)) (tx.val (intervalGeneric x))
  have hn := tx.property (intervalChartHom f)
  have hy := family_map_identity_heq (Presheaf.reindex A p) (intervalEvaluation y)
    (intervalEvaluation_source y) HEq.rfl
    ((F.fill (liftSub (interval Δ) sy ≫ p) (φ.reindex sy) (b.reindex sy)).val (intervalGeneric y))
  exact (heq_of_eq (ConcreteCategory.congr_hom m (tx.val (intervalGeneric x))).symm).trans
    (hm.trans ((heq_of_eq hn).trans (hv.trans hy.symm)))

def LocalFilling.toFilling {Γ : Context.{u}} {A : Family Γ} (F : LocalFilling A)
    (hF : F.Lawful) : Filling A where
  fill p φ b := ⟨F.value p φ b, fun f => F.value_natural hF p φ b f⟩

theorem LocalFilling.value_substitution {Γ Δ Θ : Context.{u}} {A : Family Γ}
    (F : LocalFilling A) (p : total (interval Δ) ⟶ Γ) (φ : Cofibration Δ)
    (b : OpenBox (Presheaf.reindex A p) φ) (σ : Θ ⟶ Δ)
    (x : (total (interval Θ)).Elements) :
    F.value (liftSub (interval Δ) σ ≫ p) (φ.reindex σ) (b.reindex σ) x =
      F.value p φ b ((liftSub (interval Δ) σ).mapElements.obj x) := by
  let y := (liftSub (interval Δ) σ).mapElements.obj x
  have e : represented (intervalBase x) ≫ σ = represented (intervalBase y) :=
    (represented_naturality σ (intervalBase x)).symm
  have hv := local_fill_at_heq F p φ b e (intervalGeneric x)
  have hx := family_map_identity_heq (Presheaf.reindex A (liftSub (interval Δ) σ ≫ p))
    (intervalEvaluation x) (intervalEvaluation_source x) HEq.rfl
    ((F.fill (liftSub (interval Θ) (represented (intervalBase x)) ≫ liftSub (interval Δ) σ ≫ p)
      ((φ.reindex σ).reindex (represented (intervalBase x)))
      ((b.reindex σ).reindex (represented (intervalBase x)))).val (intervalGeneric x))
  have hy := family_map_identity_heq (Presheaf.reindex A p)
    (intervalEvaluation y) (intervalEvaluation_source y) HEq.rfl
    ((F.fill (liftSub (interval Δ) (represented (intervalBase y)) ≫ p)
      (φ.reindex (represented (intervalBase y)))
      (b.reindex (represented (intervalBase y)))).val (intervalGeneric y))
  exact eq_of_heq (hx.trans (hv.trans hy.symm))

theorem Filling.toLocal_toFilling {Γ : Context.{u}} {A : Family Γ} (F : Filling A)
    (hF : F.Lawful) : F.toLocal.toFilling (Filling.toLocal_lawful hF) = F := by
  cases F with
  | mk fill =>
    change Filling.mk _ = Filling.mk fill
    apply congrArg Filling.mk
    funext Δ p φ b
    apply Term.ext
    intro x
    exact Filling.toLocal_value ⟨fill⟩ hF p φ b x

theorem LocalFilling.toFilling_fills {Γ Δ : Context.{u}} {A : Family Γ}
    (F : LocalFilling A) (hF : F.Lawful) (p : total (interval Δ) ⟶ Γ)
    (φ : Cofibration Δ) (b : OpenBox (Presheaf.reindex A p) φ) :
    b.Fills ((F.toFilling hF).fill p φ b) := by
  constructor
  · apply Term.ext
    intro x
    let y := (endpointSub Δ false).mapElements.obj x
    let σ := represented x
    have hc := congrArg (fun t => t.val (representableGeneric x.obj.unop))
      (hF.fills (liftSub (interval Δ) σ ≫ p) (φ.reindex σ) (b.reindex σ)).1
    have hy := family_map_identity_heq (Presheaf.reindex A p)
      (intervalEvaluation y) (intervalEvaluation_source y) HEq.rfl
      ((F.fill (liftSub (interval Δ) σ ≫ p) (φ.reindex σ)
        (b.reindex σ)).val (intervalGeneric y))
    have e : σ.mapElements.obj (representableGeneric x.obj.unop) = x := by
      exact Functor.Elements.ext (σ.mapElements.obj (representableGeneric x.obj.unop)) x rfl
        ((ConcreteCategory.congr_hom (Δ.map_id x.obj) _).trans (represented_id x))
    exact eq_of_heq (hy.trans ((heq_of_eq hc).trans (b.base.val_heq e)))
  · intro x hx
    let σ := represented (intervalBase x)
    have ht : (φ.reindex (projection (interval Δ))).full
        ((liftSub (interval Δ) σ).mapElements.obj (intervalGeneric x)) :=
      (congrArg (φ.reindex (projection (interval Δ))).full (intervalEvaluation_source x)).mpr hx
    have hl := (hF.fills (liftSub (interval Δ) σ ≫ p) (φ.reindex σ) (b.reindex σ)).2
      (intervalGeneric x) ht
    change (Presheaf.reindex A p).map (intervalEvaluation x) _ = _
    rw [hl]
    exact b.tube.property (intervalEvaluation x) ht

theorem LocalFilling.toFilling_lawful {Γ : Context.{u}} {A : Family Γ}
    (F : LocalFilling A) (hF : F.Lawful) : (F.toFilling hF).Lawful where
  fills := F.toFilling_fills hF
  uniform p φ b σ := by
    apply Term.ext
    intro x
    exact F.value_substitution p φ b σ x

theorem LocalFilling.toFilling_toLocal {Γ : Context.{u}} {A : Family Γ}
    (F : LocalFilling A) (hF : F.Lawful) : (F.toFilling hF).toLocal = F := by
  cases F with
  | mk fill =>
    change LocalFilling.mk _ = LocalFilling.mk fill
    apply congrArg LocalFilling.mk
    funext I p φ b
    apply Term.ext
    intro x
    change LocalFilling.value ⟨fill⟩ p φ b x = (fill p φ b).val x
    unfold LocalFilling.value
    have hu := hF.uniform p φ b x.val.1.down
    change (Presheaf.reindex A p).map (intervalEvaluation x)
      ((fill (liftSub (interval (representable I)) (representableMap x.val.1.down) ≫ p)
        (φ.reindex (representableMap x.val.1.down))
        (b.reindex (representableMap x.val.1.down))).val (intervalGeneric x)) = _
    exact (congrArg (fun t => (Presheaf.reindex A p).map (intervalEvaluation x)
      (t.val (intervalGeneric x))) hu).trans ((fill p φ b).property (intervalEvaluation x))


/-- Representable-local endpoint composition supplied by the selected filler. -/
def LocalFilling.comp {Γ : Context.{u}} {A : Family Γ} (F : LocalFilling A)
    {I : Cube} (p : total (interval (representable.{u} I)) ⟶ Γ)
    (φ : Cofibration (representable.{u} I)) (b : OpenBox (Presheaf.reindex A p) φ) :
    Term (Presheaf.reindex A (endpointSub (representable I) true ≫ p)) :=
  (F.fill p φ b).reindex (endpointSub (representable I) true)

theorem LocalFilling.comp_boundary {Γ : Context.{u}} {A : Family Γ}
    (F : LocalFilling A) (hF : F.Lawful) {I : Cube}
    (p : total (interval (representable.{u} I)) ⟶ Γ)
    (φ : Cofibration (representable.{u} I)) (b : OpenBox (Presheaf.reindex A p) φ)
    (x : (representable.{u} I).Elements) (hx : φ.full x) :
    (F.comp p φ b).val x = b.tube.val ((endpointSub _ true).mapElements.obj x) hx :=
  (hF.fills p φ b).2 ((endpointSub _ true).mapElements.obj x) hx

theorem LocalFilling.comp_reindex {Γ : Context.{u}} {A : Family Γ}
    (F : LocalFilling A) (hF : F.Lawful) {I J : Cube}
    (p : total (interval (representable.{u} I)) ⟶ Γ)
    (φ : Cofibration (representable.{u} I)) (b : OpenBox (Presheaf.reindex A p) φ) (f : J ⟶ I) :
    F.comp (liftSub (interval (representable I)) (representableMap f) ≫ p)
      (φ.reindex (representableMap f)) (b.reindex (representableMap f)) =
      (F.comp p φ b).reindex (representableMap f) :=
  congrArg (fun t => t.reindex (endpointSub (representable J) true)) (hF.uniform p φ b f)

theorem LocalFilling.comp_native {Γ : Context.{u}} {A : Family Γ}
    (F : LocalFilling A) (hF : F.Lawful) {I : Cube}
    (p : total (interval (representable.{u} I)) ⟶ Γ)
    (φ : Cofibration (representable.{u} I)) (b : OpenBox (Presheaf.reindex A p) φ) :
    (F.toFilling hF).comp p φ b = F.comp p φ b :=
  congrArg (fun G : LocalFilling A => G.comp p φ b) (F.toFilling_toLocal hF)

end SquareKit.Cubical.Presheaf
