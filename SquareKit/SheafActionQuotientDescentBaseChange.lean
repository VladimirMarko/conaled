import SquareKit.SheafActionQuotientDescentCategory

/-! Pull back actual local quotient cocycles along a parameter map. -/
noncomputable section
set_option backward.isDefEq.respectTransparency false
namespace SquareKit.SheafActionQuotient.Descent
open CategoryTheory
universe u v
variable {C : Type u} [Category.{v} C] {J : GrothendieckTopology C}
variable {G : Sheaf J GrpCat.{max u v}} {M X Y Z : Sheaf J (Type (max u v))}
variable {a : Action G M} {A : SplitSheaf.Ty X}

/-- Reindex the local object and its actual cocycle. No descended object is
used to define the pulled-back data. -/
def Datum.baseChange (d : Datum (a := a) A) (f : Y ⟶ X) :
    Datum (a := a) (SplitSheaf.tySub A f) where
  localObject := reindex d.localObject (SplitSheaf.lift A f)
  torsorDatum := {
    transport x := d.torsorDatum.transport (f.hom.mapElements.obj x)
    identity x := d.torsorDatum.identity (f.hom.mapElements.obj x)
    cocycle x := d.torsorDatum.cocycle (f.hom.mapElements.obj x)
    natural k := d.torsorDatum.natural (f.hom.mapElements.map k)
    equivariant x := d.torsorDatum.equivariant (f.hom.mapElements.obj x) }
  value_compatible x := d.value_compatible (f.hom.mapElements.obj x)

/-- Compatible local maps restrict together with their cocycles. -/
def Map.baseChange {d e : Datum (a := a) A} (h : Map d e) (f : Y ⟶ X) :
    Map (d.baseChange f) (e.baseChange f) where
  torsorMap := {
    hom := Functor.whiskerLeft (SplitSheaf.lift A f).hom.mapElements h.torsorMap.hom
    equivariant x := h.torsorMap.equivariant ((SplitSheaf.lift A f).hom.mapElements.obj x)
    transport x := h.torsorMap.transport (f.hom.mapElements.obj x) }
  preserves x := h.preserves ((SplitSheaf.lift A f).hom.mapElements.obj x)

/-- Base change acts on the entire cocycle category, not just its objects. -/
def baseChange (f : Y ⟶ X) : Datum (a := a) A ⥤ Datum (a := a) (SplitSheaf.tySub A f) where
  obj d := d.baseChange f
  map h := h.baseChange f
  map_id _ := Map.ext_hom _ _ rfl
  map_comp _ _ := Map.ext_hom _ _ rfl

/-- The selected local arrow is precisely the restricted original arrow. -/
theorem Map.baseChange_localArrow {d e : Datum (a := a) A} (h : Map d e) (f : Y ⟶ X) :
    (h.baseChange f).localArrow = h.localArrow.reindex (SplitSheaf.lift A f) := by
  apply Arrow.ext
  apply SheafTorsor.Arrow.ext
  rfl

@[simp] theorem Datum.baseChange_id (d : Datum (a := a) A) : d.baseChange (𝟙 X) = d := rfl

@[simp] theorem Datum.baseChange_comp (d : Datum (a := a) A) (f : Y ⟶ X) (g : Z ⟶ Y) :
    (d.baseChange f).baseChange g = d.baseChange (g ≫ f) := rfl

@[simp] theorem baseChange_id : baseChange (a := a) (A := A) (𝟙 X) = 𝟭 (Datum A) := rfl

@[simp] theorem baseChange_comp (f : Y ⟶ X) (g : Z ⟶ Y) :
    baseChange (a := a) (A := A) f ⋙ baseChange g = baseChange (g ≫ f) := rfl

/-- A split cover remains locally surjective after arbitrary parameter change. -/
instance baseChangeCover_locallySurjective (f : Y ⟶ X)
    [Presheaf.IsLocallySurjective J (SplitSheaf.p A).hom] :
    Presheaf.IsLocallySurjective J (SplitSheaf.p (SplitSheaf.tySub A f)).hom where
  imageSieve_mem {U} y := by
    apply J.superset_covering _
      (Presheaf.imageSieve_mem J (SplitSheaf.p A).hom (f.hom.app (Opposite.op U) y))
    intro V k hk
    obtain ⟨⟨x,b⟩, hx⟩ := hk
    change x = X.obj.map k.op (f.hom.app (Opposite.op U) y) at hx
    subst x
    have hn := NatTrans.naturality_apply f.hom k.op y
    change f.hom.app (Opposite.op V) (Y.obj.map k.op y) =
      X.obj.map k.op (f.hom.app (Opposite.op U) y) at hn
    rw [← hn] at b
    exact ⟨⟨Y.obj.map k.op y,b⟩, rfl⟩

variable [Presheaf.IsLocallySurjective J (SplitSheaf.p A).hom]

/-- The original local recovery arrow, restricted to the pullback cover, is
compatible with its cocycle. It does not select a torsor trivialization. -/
def Datum.baseChangeRecoveryMap (d : Datum (a := a) A) (f : Y ⟶ X) :
    Map (canonicalDatum (SplitSheaf.tySub A f) (reindex d.object f)) (d.baseChange f) where
  torsorMap := {
    toEquivariantMap := SheafTorsor.equivariantArrowEquiv.symm
      (d.comparison.reindex (SplitSheaf.lift A f)).torsorArrow
    transport x b c p :=
      (SheafTorsor.Descent.evaluation_transport d.torsorDatum
        (f.hom.mapElements.obj x) b c p).symm }
  preserves := (d.comparison.reindex (SplitSheaf.lift A f)).preserves

/-- Comparison between restricting the constructed descent and descending
its directly pulled-back local data. -/
def Datum.baseChangeComparison (d : Datum (a := a) A) (f : Y ⟶ X) :
    Arrow (reindex d.object f) (d.baseChange f).object :=
  (canonicalEmbedding (SplitSheaf.tySub A f) (reindex d.object f)).comp
    (d.baseChangeRecoveryMap f).arrow

/-- The comparison recovers precisely the restricted original local arrow. -/
theorem Datum.baseChangeComparison_recover (d : Datum (a := a) A) (f : Y ⟶ X) :
    ((d.baseChangeComparison f).reindex (SplitSheaf.p (SplitSheaf.tySub A f))).comp
      (d.baseChange f).comparison = d.comparison.reindex (SplitSheaf.lift A f) := by
  apply Arrow.ext
  apply SheafTorsor.Arrow.ext
  ext x p
  have he := (d.baseChangeRecoveryMap f).torsorMap.evaluation
    (Y.obj.elementsMk x.obj x.val.1) x.val.2
    ((SheafTorsor.Descent.canonicalEmbedding (SplitSheaf.tySub A f)
      (reindex d.object f).torsor).hom.app (Y.obj.elementsMk x.obj x.val.1) p)
  have hc := congrArg (fun h => h.iso.hom.app x p)
    (SheafTorsor.Descent.canonicalEmbedding_evaluation
      (SplitSheaf.tySub A f) (reindex d.object f).torsor)
  exact he.trans (congrArg
    ((d.baseChangeRecoveryMap f).torsorMap.hom.app x) hc)

/-- Equality of quotient arrows can be checked on the cover. -/
theorem restriction_injective {P Q : Object a X} {h k : P ⟶ Q}
    (he : h.reindex (SplitSheaf.p A) = k.reindex (SplitSheaf.p A)) : h = k := by
  apply Arrow.ext
  apply SheafTorsor.Arrow.ext
  ext x p
  apply SheafTorsor.Descent.fiber_ext Q.torsor.family x
    (Presheaf.imageSieve (SplitSheaf.p A).hom x.val)
    (Presheaf.imageSieve_mem J (SplitSheaf.p A).hom x.val)
  intro V r hr
  obtain ⟨⟨y,b⟩, hy⟩ := hr
  change y = X.obj.map r.op x.val at hy
  subst y
  let z := X.obj.elementsMk (Opposite.op V) (X.obj.map r.op x.val)
  let t := P.torsor.family.family.map (ElementFamilies.along X.obj r.op x.val) p
  have hv := congrArg (fun c => c.torsorArrow.iso.hom.app
    (SheafTorsor.Descent.point A z b) t) he
  erw [← NatTrans.naturality_apply h.torsorArrow.iso.hom
      (ElementFamilies.along X.obj r.op x.val) p,
    ← NatTrans.naturality_apply k.torsorArrow.iso.hom
      (ElementFamilies.along X.obj r.op x.val) p]
  exact hv

/-- Recovery characterizes the comparison uniquely as an actual quotient arrow. -/
theorem Datum.baseChangeComparison_unique (d : Datum (a := a) A) (f : Y ⟶ X)
    (k : Arrow (reindex d.object f) (d.baseChange f).object)
    (hk : (k.reindex (SplitSheaf.p (SplitSheaf.tySub A f))).comp
      (d.baseChange f).comparison = d.comparison.reindex (SplitSheaf.lift A f)) :
    k = d.baseChangeComparison f := by
  apply restriction_injective (A := SplitSheaf.tySub A f)
  apply (cancel_mono (C := Object a (SplitSheaf.Ext (SplitSheaf.tySub A f))) ((d.baseChange f).comparison :
    reindex (d.baseChange f).object (SplitSheaf.p (SplitSheaf.tySub A f)) ⟶
      (d.baseChange f).localObject)).1
  exact hk.trans (d.baseChangeComparison_recover f).symm

/-- Descending and restricting commute on every compatible local map. -/
theorem Map.baseChangeComparison_naturality {d e : Datum (a := a) A}
    (h : Map d e) (f : Y ⟶ X) :
    (h.arrow.reindex f).comp (e.baseChangeComparison f) =
      (d.baseChangeComparison f).comp (h.baseChange f).arrow := by
  apply restriction_injective (A := SplitSheaf.tySub A f)
  apply (cancel_mono (C := Object a (SplitSheaf.Ext (SplitSheaf.tySub A f))) ((e.baseChange f).comparison :
    reindex (e.baseChange f).object (SplitSheaf.p (SplitSheaf.tySub A f)) ⟶
      (e.baseChange f).localObject)).1
  change ((h.arrow.reindex f).reindex (SplitSheaf.p (SplitSheaf.tySub A f))).comp
    (((e.baseChangeComparison f).reindex (SplitSheaf.p (SplitSheaf.tySub A f))).comp
      (e.baseChange f).comparison) =
    ((d.baseChangeComparison f).reindex (SplitSheaf.p (SplitSheaf.tySub A f))).comp
      (((h.baseChange f).arrow.reindex (SplitSheaf.p (SplitSheaf.tySub A f))).comp
        (e.baseChange f).comparison)
  rw [e.baseChangeComparison_recover f, Map.comparison_naturality]
  change ((h.arrow.reindex f).reindex (SplitSheaf.p (SplitSheaf.tySub A f))).comp
    (e.comparison.reindex (SplitSheaf.lift A f)) =
    (((d.baseChangeComparison f).reindex (SplitSheaf.p (SplitSheaf.tySub A f))).comp
      (d.baseChange f).comparison).comp (h.baseChange f).localArrow
  rw [d.baseChangeComparison_recover f, Map.baseChange_localArrow]
  exact congrArg (fun k => k.reindex (SplitSheaf.lift A f))
    (Map.comparison_naturality a A h)

/-- The base-change square is a natural isomorphism of complete quotient
functors, with the selected recovery comparison as its components. -/
def baseChangeComparison (f : Y ⟶ X) :
    descentFunctor a A ⋙ restriction f ≅
      baseChange f ⋙ descentFunctor a (SplitSheaf.tySub A f) :=
  NatIso.ofComponents (fun d => (d.baseChangeComparison f).toIso)
    (fun h => Map.baseChangeComparison_naturality h f)

/-- The selected comparison for identity restriction is the identity arrow. -/
theorem Datum.baseChangeComparison_id (d : Datum (a := a) A) :
    d.baseChangeComparison (𝟙 X) = Arrow.ident d.object :=
  (d.baseChangeComparison_unique (𝟙 X) (Arrow.ident d.object) rfl).symm

/-- Successive base changes retain the same selected comparison as their
composite, rather than unrelated objectwise comparison choices. -/
theorem Datum.baseChangeComparison_comp (d : Datum (a := a) A)
    (f : Y ⟶ X) (g : Z ⟶ Y) :
    ((d.baseChangeComparison f).reindex g).comp ((d.baseChange f).baseChangeComparison g) =
      d.baseChangeComparison (g ≫ f) := by
  apply d.baseChangeComparison_unique (g ≫ f)
  change (((d.baseChangeComparison f).reindex g).reindex
      (SplitSheaf.p (SplitSheaf.tySub (SplitSheaf.tySub A f) g))).comp
      ((((d.baseChange f).baseChangeComparison g).reindex
        (SplitSheaf.p (SplitSheaf.tySub (SplitSheaf.tySub A f) g))).comp
          ((d.baseChange f).baseChange g).comparison) = _
  rw [(d.baseChange f).baseChangeComparison_recover g]
  exact congrArg (fun h => h.reindex (SplitSheaf.lift (SplitSheaf.tySub A f) g))
    (d.baseChangeComparison_recover f)

end SquareKit.SheafActionQuotient.Descent
