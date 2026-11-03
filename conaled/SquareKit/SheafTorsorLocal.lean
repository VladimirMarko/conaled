import SquareKit.SheafTorsor

/-! Torsor axioms descend along locally surjective sheaf maps. -/
noncomputable section
namespace SquareKit.SheafTorsor
open CategoryTheory Opposite
universe u v w
variable {C : Type u} [Category.{v} C] {J : GrothendieckTopology C}
variable {G : Sheaf J GrpCat.{w}} {X Y : Sheaf J (Type w)}

namespace Action

/-- An ordinary display with a natural action over its base determines the
split-family action on its actual section fibers. -/
def ofDisplay {B : Sheaf J (Type w)} (d : B ⟶ X)
    (act : ∀ U : Cᵒᵖ, G.obj.obj U → B.obj.obj U → B.obj.obj U)
    (over : ∀ U g b, d.hom.app U (act U g b) = d.hom.app U b)
    (one : ∀ U b, act U 1 b = b)
    (mul : ∀ U g h b, act U (g * h) b = act U g (act U h b))
    (natural : ∀ {U V : Cᵒᵖ} (k : U ⟶ V) g b,
      B.obj.map k (act U g b) = act V (G.obj.map k g) (B.obj.map k b)) :
    Action G X where
  family := SplitSheaf.ofDisplay d
  act x g p := ⟨act x.obj g p.val, (over x.obj g p.val).trans p.property⟩
  one_act x p := Subtype.ext (one x.obj p.val)
  mul_act x g h p := Subtype.ext (mul x.obj g h p.val)
  natural k g p := Subtype.ext (natural k.hom g p.val)

variable (Q : Action G X)

def totalAct (U : Cᵒᵖ) (g : G.obj.obj U) (p : (SplitSheaf.Ext Q.family).obj.obj U) :
    (SplitSheaf.Ext Q.family).obj.obj U :=
  ⟨p.1, Q.act (X.obj.elementsMk U p.1) g p.2⟩

theorem totalAct_natural {U V : Cᵒᵖ} (k : U ⟶ V) (g : G.obj.obj U)
    (p : (SplitSheaf.Ext Q.family).obj.obj U) :
    (SplitSheaf.Ext Q.family).obj.map k (Q.totalAct U g p) =
      Q.totalAct V (G.obj.map k g) ((SplitSheaf.Ext Q.family).obj.map k p) := by
  exact congrArg (Sigma.mk _) (Q.natural (ElementFamilies.along X.obj k p.1) g p.2)

theorem principal_at_lift (f : Y ⟶ X)
    (hp : ∀ (y : Y.obj.Elements) (p q : (Q.reindex f).family.family.obj y),
      ∃! g : G.obj.obj y.obj, (Q.reindex f).act y g p = q)
    (U : Cᵒᵖ) (p q : (SplitSheaf.Ext Q.family).obj.obj U) (hb : p.1 = q.1)
    (y : Y.obj.obj U) (hy : f.hom.app U y = p.1) :
    ∃! g : G.obj.obj U, Q.totalAct U g p = q := by
  rcases p with ⟨x,p⟩
  rcases q with ⟨z,q⟩
  dsimp at hb hy
  subst z
  subst x
  obtain ⟨g,hg,hu⟩ := hp (Y.obj.elementsMk U y) p q
  refine ⟨g, congrArg (Sigma.mk _) hg, ?_⟩
  intro h hh
  exact hu h (eq_of_heq (Sigma.mk.inj_iff.mp hh).2)

theorem total_principal_of_sieve (U : C) (p q : (SplitSheaf.Ext Q.family).obj.obj (op U))
    (S : Sieve U) (hS : S ∈ J U)
    (hp : ∀ (V : C) (k : V ⟶ U), S k →
      ∃! g : G.obj.obj (op V),
        Q.totalAct (op V) g ((SplitSheaf.Ext Q.family).obj.map k.op p) =
          (SplitSheaf.Ext Q.family).obj.map k.op q) :
    ∃! g : G.obj.obj (op U), Q.totalAct (op U) g p = q := by
  let F := SplitSheaf.Ext Q.family
  let c : Presieve.FamilyOfElements (groupSheaf G).obj S.arrows :=
    fun V k hk => (hp V k hk).choose
  have hc (V : C) (k : V ⟶ U) (hk : S k) :
      Q.totalAct (op V) (c k hk) (F.obj.map k.op p) = F.obj.map k.op q :=
    (hp V k hk).choose_spec.1
  have hcompat : c.Compatible := by
    apply (Presieve.compatible_iff_sieveCompatible c).mpr
    intro V W k l hk
    symm
    apply (hp W (l ≫ k) (S.downward_closed hk l)).choose_spec.2
    change Q.totalAct (op W) (G.obj.map l.op (c k hk))
      (F.obj.map (l ≫ k).op p) = F.obj.map (l ≫ k).op q
    change Q.totalAct (op W) (G.obj.map l.op (c k hk))
      (F.obj.map (k.op ≫ l.op) p) = F.obj.map (k.op ≫ l.op) q
    erw [Functor.map_comp, types_comp_apply, types_comp_apply]
    erw [← Q.totalAct_natural]
    exact congrArg (fun z => F.obj.map l.op z) (hc V k hk)
  obtain ⟨g, hg, hu⟩ := ((isSheaf_iff_isSheaf_of_type _ _).mp (groupSheaf G).property)
    S hS c hcompat
  refine ⟨g, ?_, ?_⟩
  · apply (((isSheaf_iff_isSheaf_of_type _ _).mp F.property) S hS).isSeparatedFor.ext
    intro V k hk
    erw [Q.totalAct_natural]
    change Q.totalAct (op V) ((groupSheaf G).obj.map k.op g) (F.obj.map k.op p) = _
    rw [hg k hk]
    exact hc V k hk
  · intro h hh
    apply hu h
    intro V k hk
    apply (hp V k hk).choose_spec.2
    change Q.totalAct (op V) (G.obj.map k.op h)
      ((SplitSheaf.Ext Q.family).obj.map k.op p) = _
    rw [← Q.totalAct_natural, hh]

theorem principal_of_reindex (f : Y ⟶ X)
    [Presheaf.IsLocallySurjective J f.hom]
    (hp : ∀ (y : Y.obj.Elements) (p q : (Q.reindex f).family.family.obj y),
      ∃! g : G.obj.obj y.obj, (Q.reindex f).act y g p = q)
    (x : X.obj.Elements) (p q : Q.family.family.obj x) :
    ∃! g : G.obj.obj x.obj, Q.act x g p = q := by
  obtain ⟨g, hg, hu⟩ := Q.total_principal_of_sieve x.obj.unop ⟨x.val,p⟩ ⟨x.val,q⟩
    (Presheaf.imageSieve f.hom x.val) (Presheaf.imageSieve_mem J f.hom x.val)
    (by
      intro V k hk
      obtain ⟨y, hy⟩ := hk
      exact Q.principal_at_lift f hp _ _ _ rfl y hy)
  refine ⟨g, eq_of_heq (Sigma.mk.inj_iff.mp hg).2, ?_⟩
  intro h hh
  exact hu h (congrArg (Sigma.mk x.val) hh)

theorem locallySurjective_of_reindex (f : Y ⟶ X)
    [Presheaf.IsLocallySurjective J f.hom]
    [Presheaf.IsLocallySurjective J (SplitSheaf.p (Q.reindex f).family).hom] :
    Presheaf.IsLocallySurjective J (SplitSheaf.p Q.family).hom where
  imageSieve_mem {U} x := by
    apply J.transitive (Presheaf.imageSieve_mem J f.hom x)
    intro V k hk
    obtain ⟨y, hy⟩ := hk
    apply J.superset_covering _ (Presheaf.imageSieve_mem J
      (SplitSheaf.p (Q.reindex f).family).hom y)
    intro W l hl
    obtain ⟨⟨z,p⟩, hz⟩ := hl
    refine ⟨⟨f.hom.app (op W) z,p⟩, ?_⟩
    change f.hom.app (op W) z = X.obj.map (l ≫ k).op x
    change z = Y.obj.map l.op y at hz
    rw [hz, NatTrans.naturality_apply, hy]
    exact (Functor.map_comp_apply X.obj k.op l.op x).symm

/-- Construct the torsor after checking its axioms on a covering base map.
The action and family are retained exactly. -/
def torsorOfReindex (f : Y ⟶ X)
    [Presheaf.IsLocallySurjective J f.hom]
    (hp : ∀ (y : Y.obj.Elements) (p q : (Q.reindex f).family.family.obj y),
      ∃! g : G.obj.obj y.obj, (Q.reindex f).act y g p = q)
    [Presheaf.IsLocallySurjective J (SplitSheaf.p (Q.reindex f).family).hom] :
    Torsor G X where
  toAction := Q
  principal := Q.principal_of_reindex f hp
  locallySurjective := Q.locallySurjective_of_reindex f

end Action
end SquareKit.SheafTorsor
