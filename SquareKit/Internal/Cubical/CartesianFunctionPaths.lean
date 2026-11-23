import SquareKit.Internal.Cubical.CartesianDependentFamilies

/-! Paths in dependent functions are native dependent functions of paths. -/
set_option autoImplicit false
set_option warningAsError true
namespace SquareKit.Cubical.Cartesian.FunctionPaths
open CategoryTheory
universe u
variable {Γ : Context.{u}} {A : Family Γ} {B : Family (total A)}
variable (f g : Term (pi A B))

abbrev whole : Family Γ := homogeneousPath (pi A B) f g
abbrev pointwise : Family Γ := pi A (homogeneousPath B (app f) (app g))

private theorem evaluation_natural {x : Γ.Elements} (p : PiElement A B x)
    {y z : (total A).Elements} (k : x ⟶ (projection A).mapElements.obj y) (h : y ⟶ z) :
    B.map h (p.val k y.val.2) =
      p.val (k ≫ (projection A).mapElements.map h) z.val.2 := by
  rcases y with @⟨I, y⟩
  rcases z with @⟨J, z⟩
  rcases h with ⟨h, hh⟩
  change I ⟶ J at h
  change totalMap A h y = z at hh
  subst z
  rcases y with ⟨γ, a⟩
  let l : Γ.elementsMk I γ ⟶ Γ.elementsMk J (Γ.map h γ) :=
    Functor.Elements.homMk h rfl
  exact p.naturality k l a

set_option backward.isDefEq.respectTransparency false in
/-- Evaluate a whole function path at every generalized dependent argument. -/
def toPointwise {x : Γ.Elements} (p : (whole f g).obj x) : (pointwise f g).obj x where
  val {y} k a := ⟨{
    val := fun {z} h r =>
      (p.val.val (k ≫ (projection A).mapElements.map h) r).val (𝟙 _) z.val.2
    naturality := by
      intro z w h l r
      let m := (projection A).mapElements.map h
      let n := (projection A).mapElements.map l
      have he := evaluation_natural (p.val.val (k ≫ m) r) (𝟙 _) l
      have hp := congrArg (fun q : PiElement A B ((projection A).mapElements.obj w) =>
        q.val (𝟙 _) w.val.2) (p.val.naturality (k ≫ m) n r)
      change (p.val.val (k ≫ m) r).val (n ≫ 𝟙 _) w.val.2 =
        (p.val.val ((k ≫ m) ≫ n) ((interval Γ).map n r)).val (𝟙 _) w.val.2 at hp
      have he' : B.map l ((p.val.val (k ≫ m) r).val (𝟙 _) z.val.2) =
          (p.val.val (k ≫ m) r).val n w.val.2 := by
        simpa only [Category.id_comp] using he
      have hp' : (p.val.val (k ≫ m) r).val n w.val.2 =
          (p.val.val ((k ≫ m) ≫ n) ((interval Γ).map n r)).val (𝟙 _) w.val.2 := by
        simpa only [Category.comp_id] using hp
      have hm : k ≫ (projection A).mapElements.map (h ≫ l) = (k ≫ m) ≫ n :=
        (congrArg (fun t => k ≫ t) ((projection A).mapElements.map_comp h l)).trans
          (Category.assoc k m n).symm
      exact he'.trans (hp'.trans (congrArg (fun t =>
        (show B.obj w from (p.val.val t ((interval Γ).map n r)).val (𝟙 _) w.val.2)) hm.symm)) },
    fun {z} h =>
      ⟨congrArg (fun q : PiElement A B ((projection A).mapElements.obj z) =>
          q.val (𝟙 _) z.val.2) (p.property (k ≫ (projection A).mapElements.map h)).1,
        congrArg (fun q : PiElement A B ((projection A).mapElements.obj z) =>
          q.val (𝟙 _) z.val.2) (p.property (k ≫ (projection A).mapElements.map h)).2⟩⟩
  naturality k l a := by
    apply Subtype.ext
    apply PiElement.ext
    intro z h r
    change (p.val.val (k ≫ (l ≫ (projection A).mapElements.map h)) r).val (𝟙 _) z.val.2 =
      (p.val.val ((k ≫ l) ≫ (projection A).mapElements.map h) r).val (𝟙 _) z.val.2
    rw [Category.assoc]

set_option backward.isDefEq.respectTransparency false in
/-- Abstract a dependent family of paths without forgetting its restriction indices. -/
def assemble {x : Γ.Elements} (q : (pointwise f g).obj x) : (whole f g).obj x :=
  ⟨{ val := fun {y} k r => {
       val := fun {z} l a => (q.val (k ≫ l) a).val.val (𝟙 _) ((interval Γ).map l r)
       naturality := by
         intro z w l m a
         have hp := (q.val (k ≫ l) a).val.naturality (𝟙 _)
           (extendHom A m a) ((interval Γ).map l r)
         have hq := congrArg (fun p : (homogeneousPath B (app f) (app g)).obj
             (extendObj A w (A.map m a)) =>
           p.val.val (𝟙 _) ((interval Γ).map m ((interval Γ).map l r)))
           (q.naturality (k ≫ l) m a)
         change B.map (extendHom A m a)
             ((q.val (k ≫ l) a).val.val (𝟙 _) ((interval Γ).map l r)) =
           (q.val (k ≫ l) a).val.val (𝟙 _ ≫ extendHom A m a)
             ((interval Γ).map m ((interval Γ).map l r)) at hp
         change (q.val (k ≫ l) a).val.val (extendHom A m a ≫ 𝟙 _)
             ((interval Γ).map m ((interval Γ).map l r)) =
           (q.val ((k ≫ l) ≫ m) (A.map m a)).val.val (𝟙 _)
             ((interval Γ).map m ((interval Γ).map l r)) at hq
         have hp' : B.map (extendHom A m a)
             ((q.val (k ≫ l) a).val.val (𝟙 _) ((interval Γ).map l r)) =
           (q.val (k ≫ l) a).val.val (extendHom A m a)
             ((interval Γ).map m ((interval Γ).map l r)) := by
           simpa only [Category.id_comp] using hp
         have hq' : (q.val (k ≫ l) a).val.val (extendHom A m a)
             ((interval Γ).map m ((interval Γ).map l r)) =
           (q.val (k ≫ l ≫ m) (A.map m a)).val.val (𝟙 _)
             ((interval Γ).map m ((interval Γ).map l r)) := by
           simpa only [Category.comp_id, Category.assoc] using hq
         exact hp'.trans (hq'.trans (congrArg (fun t : (interval Γ).obj w =>
           (show B.obj (extendObj A w (A.map m a)) from
             (q.val (k ≫ l ≫ m) (A.map m a)).val.val (𝟙 _) t))
           (congrArg (fun t => t r) ((interval Γ).map_comp l m)).symm)) }
     naturality := by
       intro y z k l r
       apply PiElement.ext
       intro w m a
       change (q.val (k ≫ (l ≫ m)) a).val.val (𝟙 _) ((interval Γ).map (l ≫ m) r) =
         (q.val ((k ≫ l) ≫ m) a).val.val (𝟙 _) ((interval Γ).map m ((interval Γ).map l r))
       rw [Category.assoc, Functor.map_comp]
       rfl }, by
    intro y k
    constructor
    · apply PiElement.ext
      intro z l a
      have hr := (endpoint Γ false).property l
      have hp := (q.val (k ≫ l) a).property (𝟙 _)
      have hf := congrArg (fun t : Term (pi A B) => (t.val y).val l a) (lam_app f)
      exact (congrArg (fun r : (interval Γ).obj z =>
        (show B.obj (extendObj A z a) from (q.val (k ≫ l) a).val.val (𝟙 _) r)) hr).trans (hp.1.trans hf)
    · apply PiElement.ext
      intro z l a
      have hr := (endpoint Γ true).property l
      have hp := (q.val (k ≫ l) a).property (𝟙 _)
      have hg := congrArg (fun t : Term (pi A B) => (t.val y).val l a) (lam_app g)
      exact (congrArg (fun r : (interval Γ).obj z =>
        (show B.obj (extendObj A z a) from (q.val (k ≫ l) a).val.val (𝟙 _) r)) hr).trans (hp.2.trans hg)⟩

set_option backward.isDefEq.respectTransparency false in
theorem assemble_toPointwise {x : Γ.Elements} (p : (whole f g).obj x) :
    assemble f g (toPointwise f g p) = p := by
  apply Subtype.ext
  apply PiElement.ext
  intro y k r
  apply PiElement.ext
  intro z l a
  have h := congrArg (fun q : PiElement A B z => q.val (𝟙 _) a) (p.val.naturality k l r)
  change (p.val.val k r).val (l ≫ 𝟙 _) a =
    (p.val.val (k ≫ l) ((interval Γ).map l r)).val (𝟙 _) a at h
  change (p.val.val ((k ≫ l) ≫ 𝟙 z) ((interval Γ).map l r)).val (𝟙 z) a =
    (p.val.val k r).val l a
  simp only [Category.comp_id] at h ⊢
  exact h.symm

set_option backward.isDefEq.respectTransparency false in
theorem toPointwise_assemble {x : Γ.Elements} (q : (pointwise f g).obj x) :
    toPointwise f g (assemble f g q) = q := by
  apply PiElement.ext
  intro y k a
  apply Subtype.ext
  apply PiElement.ext
  intro z h r
  have hn := evaluation_natural q (y := extendObj A y a) k h
  have he := congrArg (fun p : (homogeneousPath B (app f) (app g)).obj z =>
    p.val.val (𝟙 _) r) hn
  change (q.val k a).val.val (h ≫ 𝟙 z) r =
    (q.val (k ≫ (projection A).mapElements.map h) z.val.2).val.val (𝟙 z) r at he
  change (q.val ((k ≫ (projection A).mapElements.map h) ≫ 𝟙 _) z.val.2).val.val (𝟙 z)
    ((interval Γ).map (𝟙 ((projection A).mapElements.obj z)) r) = (q.val k a).val.val h r
  simp only [Category.comp_id] at he ⊢
  have hr : (interval Γ).map (𝟙 ((projection A).mapElements.obj z)) r = r :=
    congrArg (fun t => t r) ((interval Γ).map_id ((projection A).mapElements.obj z))
  exact (congrArg (fun t : (interval Γ).obj ((projection A).mapElements.obj z) =>
    (show B.obj z from (q.val (k ≫ (projection A).mapElements.map h) z.val.2).val.val (𝟙 z) t))
    hr).trans he.symm

set_option backward.isDefEq.respectTransparency false in
/-- The complete native path family is isomorphic to the dependent family of pointwise paths. -/
def decomposition : whole f g ≅ pointwise f g :=
  NatIso.ofComponents (fun x => (show (whole f g).obj x ≃ (pointwise f g).obj x from {
    toFun := toPointwise f g
    invFun := assemble f g
    left_inv := assemble_toPointwise f g
    right_inv := toPointwise_assemble f g }).toIso) (by
      intro x y h
      apply ConcreteCategory.hom_ext
      intro p
      apply PiElement.ext
      intro z k a
      apply Subtype.ext
      apply PiElement.ext
      intro w l r
      change (p.val.val (h ≫ (k ≫ (projection A).mapElements.map l)) r).val (𝟙 _) w.val.2 =
        (p.val.val ((h ≫ k) ≫ (projection A).mapElements.map l) r).val (𝟙 _) w.val.2
      rw [Category.assoc])


/-- Forward comparison evaluates at the later dependent argument, at its supplied interval value. -/
@[simp] theorem decomposition_hom_apply {x y : Γ.Elements}
    (p : (whole f g).obj x) (k : x ⟶ y) (a : A.obj y)
    {z : (total A).Elements} (h : extendObj A y a ⟶ z)
    (r : (interval (total A)).obj z) :
    (((decomposition f g).hom.app x p).val k a).val.val h r =
      (p.val.val (k ≫ (projection A).mapElements.map h) r).val (𝟙 _) z.val.2 := rfl

/-- Inverse comparison restricts the interval argument along the function's restriction index. -/
@[simp] theorem decomposition_inv_apply {x y z : Γ.Elements}
    (q : (pointwise f g).obj x) (k : x ⟶ y) (r : (interval Γ).obj y)
    (l : y ⟶ z) (a : A.obj z) :
    (((decomposition f g).inv.app x q).val.val k r).val l a =
      (q.val (k ≫ l) a).val.val (𝟙 _) ((interval Γ).map l r) := rfl

end SquareKit.Cubical.Cartesian.FunctionPaths
