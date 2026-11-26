import SquareKit.Internal.Cubical.CartesianNerve
import SquareKit.Internal.Cubical.CartesianDependentFamilies
import Mathlib.Algebra.Group.Basic

/-! The nerve of a one-object groupoid, as a small Cartesian family.
Its arrows retain group elements rather than only vertex objects. -/
set_option autoImplicit false
set_option warningAsError true
namespace SquareKit.Cubical.Cartesian
open CategoryTheory
universe u v

structure GroupSystem (G : Type u) [Group G] (V : Type v) where
  arrow : V → V → G
  identity : ∀ v, arrow v v = 1
  composition : ∀ v w z, arrow v w * arrow w z = arrow v z

namespace GroupSystem
variable {G : Type u} [Group G] {V W Z : Type v}

@[ext] theorem ext {T U : GroupSystem G V} (h : T.arrow = U.arrow) : T = U := by
  cases T; cases U; cases h; rfl

def reindex (T : GroupSystem G V) (f : W → V) : GroupSystem G W where
  arrow v w := T.arrow (f v) (f w)
  identity v := T.identity (f v)
  composition v w z := T.composition (f v) (f w) (f z)

@[simp] theorem reindex_id (T : GroupSystem G V) : T.reindex id = T := rfl
@[simp] theorem reindex_comp (T : GroupSystem G V) (f : W → V) (g : Z → W) :
    (T.reindex f).reindex g = T.reindex (f ∘ g) := rfl

def conjugate (T : GroupSystem G V) (e : V → G) : GroupSystem G V where
  arrow v w := (e v)⁻¹ * T.arrow v w * e w
  identity v := by simp [T.identity]
  composition v w z := by simp only [mul_assoc, mul_inv_cancel_left]; rw [← mul_assoc (T.arrow v w), T.composition]

@[simp] theorem conjugate_one (T : GroupSystem G V) : T.conjugate (fun _ => 1) = T := by
  ext v w; simp [conjugate]

theorem inverse_arrow (T : GroupSystem G V) (v w : V) : (T.arrow v w)⁻¹ = T.arrow w v := by
  apply inv_eq_of_mul_eq_one_right
  exact (T.composition v w v).trans (T.identity v)

theorem conjugate_from_system (T : GroupSystem G V) (f : V → V) :
    (T.reindex f).conjugate (fun v => T.arrow (f v) v) = T := by
  ext v w
  change (T.arrow (f v) v)⁻¹ * T.arrow (f v) (f w) * T.arrow (f w) w = _
  rw [inverse_arrow, T.composition, T.composition]

/-- A potential specifies every arrow, including the chosen path between vertices. -/
def ofPotential (a : V → G) : GroupSystem G V where
  arrow v w := (a v)⁻¹ * a w
  identity v := inv_mul_cancel (a v)
  composition v w z := by simp [mul_assoc]

end GroupSystem

namespace GroupNerve
variable (G : Type u) [Group G]

def family (Γ : Context.{u}) : Family Γ where
  obj x := GroupSystem G (Vertex x.obj.unop.dimension)
  map f := TypeCat.ofHom (fun T => T.reindex (Cube.vertices f.hom.unop))
  map_id _ := rfl
  map_comp f g := by
    apply ConcreteCategory.hom_ext
    intro T
    exact congrArg T.reindex (funext (Cube.vertices_comp g.hom.unop f.hom.unop))

variable {G}
namespace Fill
variable {Γ : Context.{u}} {φ : Subcontext Γ} {r : Term (interval Γ)}
  (fallback : G) (b : OpenBox (family G (total (interval Γ))) φ r)

abbrev line (x : Γ.Elements) (v : Vertex x.obj.unop.dimension) (hv : φ.Holds (vertexPoint x v)) :=
  (b.tube.val (freshExtension (vertexPoint x v)) (φ.natural (freshBaseHom _) hv)).reindex
    (fun z : Bool => (fun _ : Fin 1 => z))

def closedLine (γ : Γ.obj (.op ⟨0⟩)) (h : φ.Holds (Γ.elementsMk (.op ⟨0⟩) γ)) :
    GroupSystem G Bool :=
  (b.tube.val (freshExtension (Γ.elementsMk (.op ⟨0⟩) γ))
    (φ.natural (freshBaseHom _) h)).reindex (fun z : Bool => (fun _ : Fin 1 => z))

theorem line_natural {x y : Γ.Elements} (f : x ⟶ y)
    (v : Vertex y.obj.unop.dimension) (hy : φ.Holds (vertexPoint y v))
    (hx : φ.Holds (vertexPoint x (Cube.vertices f.hom.unop v))) :
    line b y v hy = line b x (Cube.vertices f.hom.unop v) hx := by
  have he := map_vertex_natural f v
  change closedLine b _ hy = closedLine b _ hx
  have hh : (⟨Γ.map (Quiver.Hom.op (Cube.vertex v)) y.val, hy⟩ :
      {γ : Γ.obj (.op ⟨0⟩) // φ.Holds (Γ.elementsMk (.op ⟨0⟩) γ)}) =
      ⟨Γ.map (Quiver.Hom.op (Cube.vertex (Cube.vertices f.hom.unop v))) x.val, hx⟩ := Subtype.ext he
  exact congrArg (fun z : {γ : Γ.obj (.op ⟨0⟩) // φ.Holds (Γ.elementsMk (.op ⟨0⟩) γ)} =>
    closedLine b z.val z.property) hh

noncomputable def vertical (x : Γ.Elements) (vz : Vertex x.obj.unop.dimension × Bool) : G := by
  classical
  exact if hv : φ.Holds (vertexPoint x vz.1) then
    (line b x vz.1 hv).arrow (((r.val x).down 0).eval vz.1) vz.2 else if ((r.val x).down 0).eval vz.1 = vz.2 then 1 else fallback

noncomputable def system (x : Γ.Elements) : GroupSystem G (Vertex x.obj.unop.dimension × Bool) :=
  ((b.base.val x).reindex Prod.fst).conjugate (vertical fallback b x)

theorem vertical_source (x : Γ.Elements) (v : Vertex x.obj.unop.dimension) :
    vertical fallback b x (v, ((r.val x).down 0).eval v) = 1 := by
  classical
  unfold vertical
  split
  · exact GroupSystem.identity _ _
  · simp

theorem system_source (x : Γ.Elements) :
    (system fallback b x).reindex (fun v => (v, ((r.val x).down 0).eval v)) = b.base.val x := by
  ext v w
  change (vertical fallback b x (v, _))⁻¹ * (b.base.val x).arrow v w * vertical fallback b x (w, _) = _
  simp [vertical_source]

theorem dimension_natural {x y : Γ.Elements} (f : x ⟶ y) (v : Vertex y.obj.unop.dimension) :
    ((r.val y).down 0).eval v = ((r.val x).down 0).eval (Cube.vertices f.hom.unop v) := by
  have h := congrArg (fun z => (z.down 0).eval v) (r.property f)
  exact h.symm.trans (Dim.eval_subst f.hom.unop ((r.val x).down 0) v)

theorem vertical_natural {x y : Γ.Elements} (f : x ⟶ y)
    (vz : Vertex y.obj.unop.dimension × Bool) :
    vertical fallback b y vz = vertical fallback b x (Cube.vertices f.hom.unop vz.1, vz.2) := by
  classical
  have hp := vertexPoint_natural f vz.1
  unfold vertical
  by_cases hy : φ.Holds (vertexPoint y vz.1)
  · have hx : φ.Holds (vertexPoint x (Cube.vertices f.hom.unop vz.1)) := hp ▸ hy
    rw [dite_eq_left hy, dite_eq_left hx, line_natural b f vz.1 hy hx, dimension_natural f vz.1]
  · have hx : ¬φ.Holds (vertexPoint x (Cube.vertices f.hom.unop vz.1)) := fun h => hy (hp.symm ▸ h)
    rw [dite_eq_right hy, dite_eq_right hx, dimension_natural f vz.1]

theorem system_natural {x y : Γ.Elements} (f : x ⟶ y) :
    system fallback b y = (system fallback b x).reindex (fun vz : Vertex y.obj.unop.dimension × Bool =>
      (Cube.vertices f.hom.unop vz.1, vz.2)) := by
  ext v w
  change (vertical fallback b y v)⁻¹ * (b.base.val y).arrow v.1 w.1 * vertical fallback b y w = _
  rw [vertical_natural fallback b f v, vertical_natural fallback b f w, ← b.base.property f]
  rfl

noncomputable def value (x : (total (interval Γ)).Elements) :
    GroupSystem G (Vertex x.obj.unop.dimension) :=
  (system fallback b ((projection (interval Γ)).mapElements.obj x)).reindex
    (fun v => (v, (x.val.2.down 0).eval v))

theorem value_source (x : Γ.Elements) :
    value fallback b ((graph r).mapElements.obj x) = b.base.val x := system_source fallback b x

theorem value_natural {x y : (total (interval Γ)).Elements} (f : x ⟶ y) :
    (value fallback b x).reindex (Cube.vertices f.hom.unop) = value fallback b y := by
  let g := (projection (interval Γ)).mapElements.map f
  have hs := system_natural fallback b g
  have hi : Cube.comp f.hom.unop x.val.2.down = y.val.2.down := by
    have h := (Sigma.mk.inj f.map_val).2
    exact congrArg ULift.down (eq_of_heq h)
  unfold value
  rw [hs]
  apply congrArg (GroupSystem.reindex (system fallback b ((projection (interval Γ)).mapElements.obj x)))
  funext v
  apply Prod.ext
  · rfl
  have he := congrArg (fun z => (z 0).eval v) hi
  exact (Dim.eval_subst f.hom.unop (x.val.2.down 0) v).symm.trans he

noncomputable def fillSection : Term (family G (total (interval Γ))) where
  val := value fallback b
  property := value_natural fallback b

def vertexPair {n : Nat} (vz : Vertex n × Bool) : Vertex (n+1) := Fin.cases vz.2 vz.1

def genericSystem (x : Γ.Elements) (hx : φ.Holds x) :
    GroupSystem G (Vertex x.obj.unop.dimension × Bool) :=
  (b.tube.val (freshExtension x) (φ.natural (freshBaseHom x) hx)).reindex vertexPair

theorem genericSystem_source (x : Γ.Elements) (hx : φ.Holds x) :
    (genericSystem b x hx).reindex (fun v => (v, ((r.val x).down 0).eval v)) = b.base.val x := by
  have ht := b.tube.natural (intervalArgument (𝟙 x) (r.val x))
    (φ.natural (freshBaseHom x) hx)
  have he : Cube.vertices (intervalArgument (𝟙 x) (r.val x)).hom.unop =
      fun v => vertexPair (v, ((r.val x).down 0).eval v) := by
    funext v i
    refine Fin.cases ?_ (fun j => ?_) i
    · rfl
    · rfl
  change (b.tube.val (freshExtension x) _).reindex _ = _ at ht
  rw [he] at ht
  exact ht.trans (b.boundary x hx)

theorem genericSystem_line (x : Γ.Elements) (hx : φ.Holds x)
    (v : Vertex x.obj.unop.dimension) :
    (genericSystem b x hx).reindex (fun z => (v,z)) =
      line b x v (φ.natural (vertexHom x v) hx) := by
  let a := vertexPoint x v
  let k := intervalArgument (vertexHom x v ≫ freshBaseHom a) ⟨Cube.fresh a.obj.unop⟩
  have ht := b.tube.natural k (φ.natural (freshBaseHom x) hx)
  have he : (fun z : Bool => Cube.vertices k.hom.unop (fun _ => z)) =
      fun z => vertexPair (v,z) := by
    funext z i
    refine Fin.cases ?_ (fun j => ?_) i
    · rfl
    · rfl
  have h := congrArg (fun T : GroupSystem G (Vertex 1) =>
    T.reindex (fun z : Bool => (fun _ : Fin 1 => z))) ht
  change (b.tube.val (freshExtension x) _).reindex _ = _ at h
  exact (congrArg (GroupSystem.reindex (b.tube.val (freshExtension x)
    (φ.natural (freshBaseHom x) hx))) he).symm.trans h

theorem vertical_tube (x : Γ.Elements) (hx : φ.Holds x)
    (vz : Vertex x.obj.unop.dimension × Bool) :
    vertical fallback b x vz = (genericSystem b x hx).arrow
      (vz.1, ((r.val x).down 0).eval vz.1) vz := by
  classical
  unfold vertical
  rw [dite_eq_left (φ.natural (vertexHom x vz.1) hx)]
  exact (congrArg (fun T => T.arrow (((r.val x).down 0).eval vz.1) vz.2)
    (genericSystem_line b x hx vz.1)).symm

theorem system_tube (x : Γ.Elements) (hx : φ.Holds x) :
    system fallback b x = genericSystem b x hx := by
  have h := (genericSystem b x hx).conjugate_from_system
    (fun vz => (vz.1, ((r.val x).down 0).eval vz.1))
  rw [← h]
  ext v w
  change (vertical fallback b x v)⁻¹ * (b.base.val x).arrow v.1 w.1 * vertical fallback b x w = _
  rw [vertical_tube fallback b x hx v, vertical_tube fallback b x hx w, ← genericSystem_source b x hx]
  rfl

theorem value_tube (x : (total (interval Γ)).Elements)
    (hx : φ.Holds ((projection (interval Γ)).mapElements.obj x)) :
    value fallback b x = b.tube.val x hx := by
  let a := (projection (interval Γ)).mapElements.obj x
  have ht := b.tube.natural (intervalArgument (𝟙 a) x.val.2)
    (φ.natural (freshBaseHom a) hx)
  have he : Cube.vertices (intervalArgument (𝟙 a) x.val.2).hom.unop =
      fun v => vertexPair (v, (x.val.2.down 0).eval v) := by
    funext v i
    refine Fin.cases ?_ (fun j => ?_) i
    · rfl
    · rfl
  unfold value
  rw [system_tube fallback b a hx]
  exact (congrArg (GroupSystem.reindex (b.tube.val (freshExtension a)
    (φ.natural (freshBaseHom a) hx))) he).symm.trans ht

theorem fillSection_fills : b.Fills (fillSection fallback b) := by
  constructor
  · apply Term.ext
    exact value_source fallback b
  · exact value_tube fallback b

theorem vertexPoint_reindex {Δ : Context.{u}} (σ : Δ ⟶ Γ)
    (x : Δ.Elements) (v : Vertex x.obj.unop.dimension) :
    σ.mapElements.obj (vertexPoint x v) = vertexPoint (σ.mapElements.obj x) v := by
  apply congrArg (Γ.elementsMk (.op ⟨0⟩))
  exact σ.naturality_apply (Quiver.Hom.op (Cube.vertex v)) x.val

theorem freshExtension_reindex {Δ : Context.{u}} (σ : Δ ⟶ Γ) (x : Δ.Elements) :
    (intervalSub σ).mapElements.obj (freshExtension x) = freshExtension (σ.mapElements.obj x) := by
  apply congrArg ((total (interval Γ)).elementsMk (.op (Cube.extend x.obj.unop)))
  apply Sigma.ext
  · exact σ.naturality_apply (dropOpp x.obj) x.val
  · rfl

private theorem tube_val_heq {x y : (total (interval Γ)).Elements} (h : x = y)
    (hx : φ.Holds ((projection (interval Γ)).mapElements.obj x))
    (hy : φ.Holds ((projection (interval Γ)).mapElements.obj y)) :
    HEq (b.tube.val x hx) (b.tube.val y hy) := by
  subst y
  rfl

theorem line_reindex {Δ : Context.{u}} (σ : Δ ⟶ Γ) (x : Δ.Elements)
    (v : Vertex x.obj.unop.dimension)
    (hx : (φ.reindex σ).Holds (vertexPoint x v))
    (hy : φ.Holds (vertexPoint (σ.mapElements.obj x) v)) :
    line (b.reindex σ) x v hx = line b (σ.mapElements.obj x) v hy := by
  have hp := vertexPoint_reindex σ x v
  have hf := (freshExtension_reindex σ (vertexPoint x v)).trans
    (congrArg freshExtension hp)
  unfold line
  change (b.tube.val _ _).reindex _ = (b.tube.val _ _).reindex _
  have he : HEq (b.tube.val ((intervalSub σ).mapElements.obj (freshExtension (vertexPoint x v)))
      ((φ.reindex σ).natural (freshBaseHom (vertexPoint x v)) hx))
      (b.tube.val (freshExtension (vertexPoint (σ.mapElements.obj x) v))
        (φ.natural (freshBaseHom _) hy)) := tube_val_heq b hf _ _
  exact congrArg (fun T : GroupSystem G (Vertex 1) => T.reindex (fun z : Bool => fun _ => z))
    (eq_of_heq he)

theorem vertical_reindex {Δ : Context.{u}} (σ : Δ ⟶ Γ) (x : Δ.Elements)
    (vz : Vertex x.obj.unop.dimension × Bool) :
    vertical fallback (b.reindex σ) x vz = vertical fallback b (σ.mapElements.obj x) vz := by
  classical
  have hp := vertexPoint_reindex σ x vz.1
  unfold vertical
  by_cases hx : (φ.reindex σ).Holds (vertexPoint x vz.1)
  · have hy : φ.Holds (vertexPoint (σ.mapElements.obj x) vz.1) := hp ▸ hx
    rw [dite_eq_left hx, dite_eq_left hy, line_reindex b σ x vz.1 hx hy]
    rfl
  · have hy : ¬φ.Holds (vertexPoint (σ.mapElements.obj x) vz.1) := fun h => hx (show φ.Holds (σ.mapElements.obj (vertexPoint x vz.1)) from hp.symm ▸ h)
    rw [dite_eq_right hx, dite_eq_right hy]
    rfl

theorem system_reindex {Δ : Context.{u}} (σ : Δ ⟶ Γ) (x : Δ.Elements) :
    system fallback (b.reindex σ) x = system fallback b (σ.mapElements.obj x) := by
  ext v w
  change (vertical fallback (b.reindex σ) x v)⁻¹ * _ * vertical fallback (b.reindex σ) x w = _
  rw [vertical_reindex fallback b σ x v, vertical_reindex fallback b σ x w]
  rfl

theorem fillSection_reindex {Δ : Context.{u}} (σ : Δ ⟶ Γ) :
    fillSection fallback (b.reindex σ) = Term.reindex (fillSection fallback b) (intervalSub σ) := by
  apply Term.ext
  intro x
  exact congrArg (fun T => T.reindex (fun v => (v, (x.val.2.down 0).eval v)))
    (system_reindex fallback b σ ((projection (interval Δ)).mapElements.obj x))

end Fill

noncomputable def chosenFilling (fallback : G) (Γ : Context.{u}) : Filling (family G Γ) where
  fill _ _ _ b := Fill.fillSection fallback b

theorem chosenFilling_lawful (fallback : G) (Γ : Context.{u}) : (chosenFilling fallback Γ).Lawful where
  fills _ _ _ b := Fill.fillSection_fills fallback b
  uniform _ _ _ b σ := Fill.fillSection_reindex fallback b σ

noncomputable def filling (Γ : Context.{u}) : Filling (family G Γ) := chosenFilling 1 Γ

theorem filling_lawful (Γ : Context.{u}) : (filling (G := G) Γ).Lawful := chosenFilling_lawful 1 Γ

/-- A based edge of the one-object groupoid retains its group element. -/
def loop (g : G) : GroupSystem G Bool :=
  GroupSystem.ofPotential (fun b => if b then g else 1)

@[simp] theorem loop_arrow (g : G) : (loop g).arrow false true = g := by
  simp [loop, GroupSystem.ofPotential]

/-- A square with constant vertical edges cannot identify distinct based edges. -/
theorem square_rigidity (T : GroupSystem G (Bool × Bool))
    (left : T.arrow (false,false) (false,true) = 1)
    (right : T.arrow (true,false) (true,true) = 1) :
    T.arrow (false,false) (true,false) = T.arrow (false,true) (true,true) := by
  have h₁ := T.composition (false,false) (true,false) (true,true)
  have h₂ := T.composition (false,false) (false,true) (true,true)
  rw [right, mul_one] at h₁
  rw [left, one_mul] at h₂
  exact h₁.trans h₂.symm

/-- A common endpoint-change path can be cancelled without treating it as
reflexivity. Both vertical edges, including their nontrivial group value, remain. -/
theorem common_boundary_cancel (T U : GroupSystem G (Bool × Bool))
    (left : T.arrow (false,false) (false,true) = U.arrow (false,false) (false,true))
    (right : T.arrow (true,false) (true,true) = U.arrow (true,false) (true,true))
    (bottom : T.arrow (false,false) (true,false) = U.arrow (false,false) (true,false)) :
    T.arrow (false,true) (true,true) = U.arrow (false,true) (true,true) := by
  apply mul_left_cancel (a := U.arrow (false,false) (false,true))
  calc
    _ = T.arrow (false,false) (false,true) * T.arrow (false,true) (true,true) := by rw [left]
    _ = T.arrow (false,false) (true,false) * T.arrow (true,false) (true,true) :=
      (T.composition _ _ _).trans (T.composition _ _ _).symm
    _ = U.arrow (false,false) (true,false) * U.arrow (true,false) (true,true) := by rw [bottom, right]
    _ = _ := (U.composition _ _ _).trans (U.composition _ _ _).symm

end GroupNerve

namespace GroupSystem
variable {G : Type u} [CommGroup G] {V : Type v}

theorem conjugate_constant (T : GroupSystem G V) (g : G) :
    T.conjugate (fun _ => g) = T := by
  ext v w
  change g⁻¹ * T.arrow v w * g = T.arrow v w
  rw [mul_comm (g⁻¹), mul_assoc, inv_mul_cancel, mul_one]

theorem conjugate_inverse (T : GroupSystem G V) (e : V → G) :
    (T.conjugate e).conjugate (fun v => (e v)⁻¹) = T := by
  ext v w
  simp [conjugate, mul_assoc]
end GroupSystem

namespace GroupNerve
variable {G : Type u} [CommGroup G]

/-- The central natural automorphism, at every cube and every interval argument. -/
def centralHomotopy (Γ : Context.{u}) (g : G) :
    family G (total (interval Γ)) ⟶ family G (total (interval Γ)) where
  app x := TypeCat.ofHom (fun T => T.conjugate
    (fun v => if (x.val.2.down 0).eval v then g else 1))
  naturality x y f := by
    apply ConcreteCategory.hom_ext
    intro T
    have hi : Cube.comp f.hom.unop x.val.2.down = y.val.2.down := by
      have h := (Sigma.mk.inj f.map_val).2
      exact congrArg ULift.down (eq_of_heq h)
    have hd (v : Vertex y.obj.unop.dimension) :
        (x.val.2.down 0).eval (Cube.vertices f.hom.unop v) = (y.val.2.down 0).eval v :=
      (Dim.eval_subst f.hom.unop (x.val.2.down 0) v).symm.trans
        (congrArg (fun z => (z 0).eval v) hi)
    apply GroupSystem.ext
    funext v w
    change (if (y.val.2.down 0).eval v then g else 1)⁻¹ * _ *
      (if (y.val.2.down 0).eval w then g else 1) = _
    rw [← hd v, ← hd w]
    rfl

theorem centralHomotopy_endpoint (Γ : Context.{u}) (g : G)
    (x : Γ.Elements) (b : Bool) (T : GroupSystem G (Vertex x.obj.unop.dimension)) :
    (centralHomotopy Γ g).app (extendObj (interval Γ) x ⟨Cube.endpoint x.obj.unop b⟩) T = T := by
  change T.conjugate (fun _ => if b then g else 1) = T
  exact T.conjugate_constant _

/-- The central loop is a loop of actual family isomorphisms. -/
def centralIso (Γ : Context.{u}) (g : G) :
    family G (total (interval Γ)) ≅ family G (total (interval Γ)) where
  hom := centralHomotopy Γ g
  inv := centralHomotopy Γ g⁻¹
  hom_inv_id := by
    ext x T
    change (T.conjugate _).conjugate _ = T
    simpa only [apply_ite, inv_one] using
      T.conjugate_inverse (fun v => if (x.val.2.down 0).eval v then g else 1)
  inv_hom_id := by
    ext x T
    change (T.conjugate _).conjugate _ = T
    simpa only [apply_ite, inv_one, inv_inv] using
      T.conjugate_inverse (fun v => if (x.val.2.down 0).eval v then g⁻¹ else 1)

theorem centralIso_endpoint (Γ : Context.{u}) (g : G) (b : Bool) :
    Functor.isoWhiskerLeft (endpointSub Γ b).mapElements (centralIso Γ g) =
      Iso.refl (family G Γ) := by
  apply Iso.ext
  ext x T
  exact centralHomotopy_endpoint Γ g x b T

theorem centralIso_reindex {Γ Δ : Context.{u}} (σ : Δ ⟶ Γ) (g : G) :
    Functor.isoWhiskerLeft (intervalSub σ).mapElements (centralIso Γ g) =
      centralIso Δ g := by
  apply Iso.ext
  rfl

/-- Evaluating the central homotopy at a fixed vertex gives the chosen group loop. -/
theorem centralHomotopy_vertex (Γ : Context.{u}) (g : G)
    (x : Γ.Elements)
    (T : GroupSystem G (Vertex x.obj.unop.dimension)) :
    ((centralHomotopy Γ g).app (freshExtension x)
      (T.reindex (Cube.vertices (Cube.drop x.obj.unop)))).reindex
        (fun b => Fin.cases b (fun _ => false)) = loop g := by
  apply GroupSystem.ext
  funext b c
  change (if b then g else 1)⁻¹ * T.arrow (fun _ => false) (fun _ => false) *
    (if c then g else 1) = _
  rw [T.identity, mul_one]
  rfl

end GroupNerve
end SquareKit.Cubical.Cartesian
