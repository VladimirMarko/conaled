import SquareKit.Internal.Cubical.NativeUnivalenceUa
import SquareKit.Internal.Cubical.UnivalenceEliminationSubstitution

set_option autoImplicit false
set_option warningAsError true
namespace SquareKit.Cubical.Presheaf.SmallUniverse.NativeUnivalence
open CategoryTheory
universe u
variable {Ξ : Context.{u+1}} (a b : Ξ ⟶ smallFamilyCodes.{u})
  (f : liftedDecode a ⟶ liftedDecode b) (E : HomotopyEquivalence f)

noncomputable def chartUnglue {Γ : Context.{u}} (σ : raisedContext Γ ⟶ Ξ) :
    Presheaf.decode (chartCode a b f E σ) ⟶
      reindex (Presheaf.decode (σ ≫ b)) (projection (interval Γ)) :=
  Univalence.unglueLine (σ ≫ a) (σ ≫ b) (lowerChartMap a b σ f)
    (lowerChartEquivalence a b σ f E)

private theorem sourceCast_heq {Γ : Context.{u}} {A A' B : Family Γ}
    (h : A = A') (g : A' ⟶ B) : HEq (eqToHom h ≫ g) g := by
  cases h
  rfl

private theorem unglueChosen_congr {Γ : Context.{u}}
    (a b : raisedContext Γ ⟶ smallFamilyCodes.{u}) (f : Presheaf.decode a ⟶ Presheaf.decode b)
    (E E' : HomotopyEquivalence f) (h : E = E') :
    HEq (Univalence.unglueLine a b f E) (Univalence.unglueLine a b f E') := by
  cases h
  rfl

theorem chartUnglue_reindex {Γ Δ : Context.{u}} (σ : raisedContext Γ ⟶ Ξ) (τ : Δ ⟶ Γ) :
    HEq (Functor.whiskerLeft (liftSub (interval Γ) τ).mapElements (chartUnglue a b f E σ))
      (chartUnglue a b f E (raisedSub τ ≫ σ)) := by
  have h := Univalence.unglueLine_reindex (σ ≫ a) (σ ≫ b)
    (lowerChartMap a b σ f) (lowerChartEquivalence a b σ f E) τ
  exact (heq_of_eq h).trans ((sourceCast_heq _ _).trans
    (unglueChosen_congr (raisedSub τ ≫ σ ≫ a) (raisedSub τ ≫ σ ≫ b)
      (lowerChartMap a b (raisedSub τ ≫ σ) f) _ _
      (lowerChartEquivalence_reindex a b σ f E τ).symm))


def smallPoint (x : (total (interval Ξ)).Elements) :
    (total (interval (representable.{u} x.obj.unop))).Elements :=
  (total (interval (representable.{u} x.obj.unop))).elementsMk x.obj (chartPoint x).down

def chartBasePoint (x : (total (interval Ξ)).Elements) : Ξ.Elements :=
  (chart (intervalBase x)).mapElements.obj
    ((raisedElements (representable.{u} x.obj.unop)).obj
      ((projection (interval (representable.{u} x.obj.unop))).mapElements.obj (smallPoint x)))

theorem chartBasePoint_eq (x : (total (interval Ξ)).Elements) :
    chartBasePoint x = intervalBase x := by
  change Ξ.elementsMk x.obj _ = Ξ.elementsMk x.obj _
  exact congrArg (Ξ.elementsMk x.obj) (chart_generic (intervalBase x))

noncomputable def unglueValue (x : (total (interval Ξ)).Elements)
    (z : (liftedDecode (code (uaLine a b f E))).obj x) :
    (liftedDecode b).obj (intervalBase x) :=
  cast (congrArg (liftedDecode b).obj (chartBasePoint_eq x))
    ⟨(chartUnglue a b f E (chart (intervalBase x))).app (smallPoint x) z.down⟩

private theorem map_input_heq {Γ : Context.{u}} (A : Family Γ)
    {x x' y y' : Γ.Elements} (hx : x = x') (hy : y = y')
    (g : x ⟶ y) (g' : x' ⟶ y') (hg : HEq g.hom g'.hom)
    (z : A.obj x) (z' : A.obj x') (hz : HEq z z') :
    HEq (A.map g z) (A.map g' z') := by
  cases hx
  cases hy
  have h : g = g' := Functor.Elements.Hom.ext (eq_of_heq hg)
  cases h
  cases hz
  rfl

private theorem nat_app_heq {Γ : Context.{u}} {A A' B B' : Family Γ}
    (hA : A = A') (hB : B = B') (g : A ⟶ B) (g' : A' ⟶ B')
    (hg : HEq g g') (x : Γ.Elements) (z : A.obj x) (z' : A'.obj x)
    (hz : HEq z z') : HEq (g.app x z) (g'.app x z') := by
  cases hA
  cases hB
  cases hg
  cases hz
  rfl

def smallSub {x y : (total (interval Ξ)).Elements} (g : x ⟶ y) :=
  liftSub (interval (representable.{u} x.obj.unop)) (representableMap.{u} g.hom.unop)

def smallArrow {x y : (total (interval Ξ)).Elements} (g : x ⟶ y) :
    smallPoint x ⟶ (smallSub g).mapElements.obj (smallPoint y) :=
  Functor.Elements.homMk g.hom (congrArg ULift.down (chartPoint_natural g))

private theorem input_restrict_heq {x y : (total (interval Ξ)).Elements} (g : x ⟶ y)
    (z : (liftedDecode (code (uaLine a b f E))).obj x) :
    HEq ((Presheaf.decode (chartCode a b f E (chart (intervalBase x)))).map (smallArrow g) z.down)
      (((liftedDecode (code (uaLine a b f E))).map g z).down) :=
  (cast_heq _ _).trans (cast_heq _ _).symm


private theorem chartUnglue_congr {Γ : Context.{u}} (σ τ : raisedContext Γ ⟶ Ξ)
    (h : σ = τ) : HEq (chartUnglue a b f E σ) (chartUnglue a b f E τ) := by
  cases h
  rfl

private theorem output_restrict_heq {x y : (total (interval Ξ)).Elements} (g : x ⟶ y)
    (z : (liftedDecode (code (uaLine a b f E))).obj x) :
    HEq ((reindex (Presheaf.decode (chart (intervalBase x) ≫ b))
      (projection (interval (representable.{u} x.obj.unop)))).map (smallArrow g)
        ((chartUnglue a b f E (chart (intervalBase x))).app (smallPoint x) z.down))
      ((chartUnglue a b f E (chart (intervalBase y))).app (smallPoint y)
        (((liftedDecode (code (uaLine a b f E))).map g z).down)) := by
  let σ := chart (intervalBase x)
  let τ := representableMap.{u} g.hom.unop
  have hs : raisedSub τ ≫ σ = chart (intervalBase y) :=
    chart_restrict ((projection (interval Ξ)).mapElements.map g)
  have hA := congrArg Presheaf.decode
    ((chartCode_reindex a b f E σ τ).trans (congrArg (chartCode a b f E) hs))
  have hB := congrArg (fun t : raisedContext (representable.{u} y.obj.unop) ⟶ Ξ =>
    reindex (Presheaf.decode (t ≫ b)) (projection (interval (representable.{u} y.obj.unop)))) hs
  have hG := (chartUnglue_reindex a b f E σ τ).trans
    (chartUnglue_congr a b f E _ _ hs)
  have hn := ConcreteCategory.congr_hom
    ((chartUnglue a b f E σ).naturality (smallArrow g)) z.down
  exact (heq_of_eq hn.symm).trans
    (nat_app_heq hA hB _ _ hG (smallPoint y) _ _ (input_restrict_heq a b f E g z))

def chartBaseArrow {x y : (total (interval Ξ)).Elements} (g : x ⟶ y) :=
  (chart (intervalBase x)).mapElements.map
    ((raisedElements (representable.{u} x.obj.unop)).map
      ((projection (interval (representable.{u} x.obj.unop))).mapElements.map (smallArrow g)))

theorem chartBaseArrow_target {x y : (total (interval Ξ)).Elements} (g : x ⟶ y) :
    (chart (intervalBase x)).mapElements.obj
      ((raisedElements (representable.{u} x.obj.unop)).obj
        ((projection (interval (representable.{u} x.obj.unop))).mapElements.obj
          ((smallSub g).mapElements.obj (smallPoint y)))) = intervalBase y := by
  change Ξ.elementsMk y.obj _ = Ξ.elementsMk y.obj _
  apply congrArg (Ξ.elementsMk y.obj)
  exact (chartBaseArrow g).map_val.symm.trans
    ((congrArg (Ξ.map g.hom) (chart_generic (intervalBase x))).trans
      ((projection (interval Ξ)).mapElements.map g).map_val)

private theorem ulift_heq {A B : Type u} {z : A} {w : B} (h : HEq z w) :
    HEq (ULift.up.{u+1} z) (ULift.up.{u+1} w) := by
  cases h
  rfl

theorem unglueValue_natural {x y : (total (interval Ξ)).Elements} (g : x ⟶ y)
    (z : (liftedDecode (code (uaLine a b f E))).obj x) :
    (liftedDecode b).map ((projection (interval Ξ)).mapElements.map g)
      (unglueValue a b f E x z) =
    unglueValue a b f E y ((liftedDecode (code (uaLine a b f E))).map g z) := by
  apply eq_of_heq
  have hm := map_input_heq (liftedDecode b) (chartBasePoint_eq x)
    (chartBaseArrow_target g) (chartBaseArrow g)
    ((projection (interval Ξ)).mapElements.map g) HEq.rfl
    (show (liftedDecode b).obj (chartBasePoint x) from
      ⟨(chartUnglue a b f E (chart (intervalBase x))).app (smallPoint x) z.down⟩)
    (unglueValue a b f E x z) (cast_heq _ _).symm
  exact hm.symm.trans ((ulift_heq (output_restrict_heq a b f E g z)).trans
    (cast_heq _ _).symm)

noncomputable def unglue : liftedDecode (code (uaLine a b f E)) ⟶
    reindex (liftedDecode b) (projection (interval Ξ)) where
  app x := TypeCat.ofHom (unglueValue a b f E x)
  naturality x y g := by
    apply ConcreteCategory.hom_ext
    intro z
    exact (unglueValue_natural a b f E g z).symm


private theorem point_app_heq {Γ : Context.{u}} {A B : Family Γ} (g : A ⟶ B)
    {x y : Γ.Elements} (h : x = y) (z : A.obj x) (w : A.obj y) (hz : HEq z w) :
    HEq (g.app x z) (g.app y w) := by
  cases h
  cases hz
  rfl

theorem unglue_zero :
    Functor.whiskerLeft (endpointSub Ξ false).mapElements (unglue a b f E) =
      eqToHom (decode_zero (ua a b f E)) ≫ f := by
  apply NatTrans.ext
  funext x
  apply ConcreteCategory.hom_ext
  intro z
  apply eq_of_heq
  let sx := (representable.{u} x.obj.unop).elementsMk x.obj ⟨𝟙 x.obj.unop⟩
  let σ := chart x
  let h₀ := congrArg Presheaf.decode
    (Univalence.uaCode_zero (σ ≫ a) (σ ≫ b)
      (lowerChartMap a b σ f) (lowerChartEquivalence a b σ f E))
  let w := (eqToHom h₀).app sx z.down
  have h := congrArg (fun k => k.app sx z.down)
    (Univalence.unglueLine_zero (σ ≫ a) (σ ≫ b)
      (lowerChartMap a b σ f) (lowerChartEquivalence a b σ f E))
  have hw : HEq (ULift.up.{u+1} w) ((eqToHom (decode_zero (ua a b f E))).app x z) :=
    (ulift_heq (family_eqToIso_hom_heq h₀ sx z.down)).trans
      (family_eqToIso_hom_heq (decode_zero (ua a b f E)) x z).symm
  exact (cast_heq _ _).trans ((heq_of_eq (congrArg ULift.up h)).trans
    (point_app_heq f (chartBasePoint_eq ((endpointSub Ξ false).mapElements.obj x)) _ _ hw))

theorem unglue_one :
    Functor.whiskerLeft (endpointSub Ξ true).mapElements (unglue a b f E) =
      eqToHom (decode_one (ua a b f E)) := by
  apply NatTrans.ext
  funext x
  apply ConcreteCategory.hom_ext
  intro z
  apply eq_of_heq
  let sx := (representable.{u} x.obj.unop).elementsMk x.obj ⟨𝟙 x.obj.unop⟩
  let σ := chart x
  let h₁ := congrArg Presheaf.decode
    (Univalence.uaCode_one (σ ≫ a) (σ ≫ b)
      (lowerChartMap a b σ f) (lowerChartEquivalence a b σ f E))
  have h := congrArg (fun k => k.app sx z.down)
    (Univalence.unglueLine_one (σ ≫ a) (σ ≫ b)
      (lowerChartMap a b σ f) (lowerChartEquivalence a b σ f E))
  exact (cast_heq _ _).trans ((heq_of_eq (congrArg ULift.up h)).trans
    ((ulift_heq (family_eqToIso_hom_heq h₁ sx z.down)).trans
      (family_eqToIso_hom_heq (decode_one (ua a b f E)) x z).symm))

/-- Comparison uses the actual universal decoding filler, retaining its chosen transport. -/
noncomputable def uaComparison (x : Term (liftedDecode a)) :
    Term (homogeneousPath (liftedDecode b) (Term.map f x)
      (Term.map (pathToMap (ua a b f E)) x)) :=
  IntervalTransport.mapLineComparisonTo
    (NativeDecode.filling (codeOfPath (ua a b f E)))
    (NativeDecode.filling_lawful (codeOfPath (ua a b f E)))
    (decode_zero (ua a b f E)) (decode_one (ua a b f E))
    (unglue a b f E) f (unglue_zero a b f E) (unglue_one a b f E) x


end SquareKit.Cubical.Presheaf.SmallUniverse.NativeUnivalence
