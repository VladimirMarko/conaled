import SquareKit.SheafActionQuotientStackDescent
import SquareKit.SheafContextTopology

/-! The sheaf action quotient as a Mathlib stack on locally surjective contexts. -/
noncomputable section
set_option autoImplicit false
set_option warningAsError true
namespace SquareKit.SheafActionQuotient.Stack
open CategoryTheory Opposite
open SheafCover
universe u v
variable {C : Type u} [Category.{v} C] {J : GrothendieckTopology C}
variable {G : Sheaf J GrpCat.{max u v}} {M : Sheaf J (Type (max u v))}
variable (a : Action G M)
variable {X : Sheaf J (Type (max u v))}

/-- Every locally surjective sheaf map gives effective quotient descent. -/
theorem isStackFor_cover {Y : Sheaf J (Type (max u v))} (f : Y ⟶ X)
    [Presheaf.IsLocallySurjective J f.hom] :
    (pseudofunctor a).IsStackFor (Presieve.ofArrows _ (fun _ : Unit => f)) := by
  apply ((pseudofunctor a).isStackFor_iff_of_sieve_eq (display_sieve f)).mp
  rw [Pseudofunctor.isStackFor_ofArrows_iff]
  infer_instance

instance isPrestack : (pseudofunctor a).IsPrestack (topology (J := J)) where
  isSheaf {S} M N := by
    apply Presheaf.IsSheaf.of_le (over_topology_le S)
    rw [isSheaf_iff_isSheaf_of_type, Presieve.isSheaf_coverage]
    rintro X R ⟨Y, f, rfl, hf⟩
    rw [Presieve.isSheafFor_iff_generate]
    apply Pseudofunctor.IsPrestackFor.isSheafFor'
    rw [Sieve.overEquiv_generate, ← Sieve.arrows_generate_map_eq_functorPushforward,
      Sieve.generate_sieve]
    simp only [Presieve.map_singleton]
    rw [← Presieve.ofArrows_pUnit.{0}]
    apply (Pseudofunctor.IsPrestackFor_generate_iff _ _).mpr
    exact (isStackFor_cover (a := a) f.left).isPrestackFor

instance isStack : (pseudofunctor a).IsStack (topology (J := J)) := by
  apply Pseudofunctor.IsStack.of_isStackFor
  rintro X R ⟨Y, f, hf, hR⟩
  apply Pseudofunctor.IsStackFor.of_le (pseudofunctor a) (isStackFor_cover (a := a) f) (J := topology (J := J))
  · exact ⟨Y, f, hf, Sieve.ofArrows_mk _ _ ()⟩
  · intro Z g hg
    cases hg
    exact hR

variable {a} {A : SplitSheaf.Ty X}
variable [Presheaf.IsLocallySurjective J (SplitSheaf.p A).hom]

/-- The chosen object retains the constructive target map and group action. -/
theorem glue_value (D : Data a A) (x : X.obj.Elements)
    (p : (glue D).torsor.family.family.obj x) :
    (glue D).value x p = (datum D).value x p := rfl

theorem glue_action (D : Data a A) (x : X.obj.Elements) (g : G.obj.obj x.obj)
    (p : (glue D).torsor.family.family.obj x) :
    (glue D).torsor.act x g p = (datum D).descendedTorsor.act x g p := rfl

/-- Recovery commutes with the group action on the actual local fibers. -/
theorem localComparison_action (D : Data a A) (x : (SplitSheaf.extension A).obj.Elements)
    (g : G.obj.obj x.obj)
    (p : (reindex (glue D) (SplitSheaf.p A)).torsor.family.family.obj x) :
    ((localComparison D).hom.hom ()).torsorArrow.iso.hom.app x
      ((reindex (glue D) (SplitSheaf.p A)).torsor.act x g p) =
    (D.obj ()).torsor.act x g (((localComparison D).hom.hom ()).torsorArrow.iso.hom.app x p) :=
  ((localComparison D).hom.hom ()).torsorArrow.equivariant x g p

/-- Recovery also retains the full equivariant target value. -/
theorem localComparison_target (D : Data a A) (x : (SplitSheaf.extension A).obj.Elements)
    (p : (reindex (glue D) (SplitSheaf.p A)).torsor.family.family.obj x) :
    (D.obj ()).value x (((localComparison D).hom.hom ()).torsorArrow.iso.hom.app x p) =
      (reindex (glue D) (SplitSheaf.p A)).value x p :=
  ((localComparison D).hom.hom ()).preserves x p

/-- The actual local recovery map is over the cover context. -/
theorem localComparison_projection (D : Data a A) :
    (SheafTorsor.equivariantArrowEquiv.symm (datum D).comparison.torsorArrow).totalMap ≫
      SplitSheaf.p (D.obj ()).torsor.family =
        SplitSheaf.p (SheafTorsor.reindex (glue D).torsor (SplitSheaf.p A)).family :=
  rfl

/-- Restricting the selected effective object agrees with direct base change of
its local cocycle, using the existing constructive comparison. -/
def baseChangeComparison (D : Data a A) {Y : Sheaf J (Type (max u v))} (f : Y ⟶ X) :
    Arrow (reindex (glue D) f) ((datum D).baseChange f).object :=
  (datum D).baseChangeComparison f

theorem baseChangeComparison_recover (D : Data a A)
    {Y : Sheaf J (Type (max u v))} (f : Y ⟶ X) :
    ((baseChangeComparison D f).reindex (SplitSheaf.p (SplitSheaf.tySub A f))).comp
      ((datum D).baseChange f).comparison =
        ((localComparison D).hom.hom ()).reindex (SplitSheaf.lift A f) := by
  rw [localComparison_hom]
  exact (datum D).baseChangeComparison_recover f

theorem baseChangeComparison_natural {D E : Data a A} (h : D ⟶ E)
    {Y : Sheaf J (Type (max u v))} (f : Y ⟶ X) :
    ((glueFunctor.map h).reindex f).comp (baseChangeComparison E f) =
      (baseChangeComparison D f).comp ((datumMap h).baseChange f).arrow :=
  (datumMap h).baseChangeComparison_naturality f

theorem baseChangeComparison_id (D : Data a A) :
    baseChangeComparison D (𝟙 X) = Arrow.ident (glue D) :=
  (datum D).baseChangeComparison_id

theorem baseChangeComparison_comp (D : Data a A)
    {Y Z : Sheaf J (Type (max u v))} (f : Y ⟶ X) (g : Z ⟶ Y) :
    ((baseChangeComparison D f).reindex g).comp
      (((datum D).baseChange f).baseChangeComparison g) = baseChangeComparison D (g ≫ f) :=
  (datum D).baseChangeComparison_comp f g

end SquareKit.SheafActionQuotient.Stack
