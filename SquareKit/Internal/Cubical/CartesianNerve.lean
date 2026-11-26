import SquareKit.Internal.Cubical.CartesianFilling

/-! Finite local systems on Boolean vertices and their small tuple decoders. -/
set_option autoImplicit false
set_option warningAsError true
namespace SquareKit.Cubical.Cartesian
open CategoryTheory
universe u v

abbrev Vertex (n : ℕ) := Fin n → Bool

def Dim.eval {n : ℕ} : Dim n → Vertex n → Bool
  | .endpoint b, _ => b
  | .var i, v => v i

@[simp] theorem Dim.eval_subst {n m : ℕ} (f : Fin n → Dim m) (r : Dim n) (v : Vertex m) :
    (r.subst f).eval v = r.eval (fun i => (f i).eval v) := by cases r <;> rfl

def Cube.vertices {I J : Cube} (f : I ⟶ J) (v : Vertex I.dimension) : Vertex J.dimension :=
  fun i => (f i).eval v

@[simp] theorem Cube.vertices_id (I : Cube) (v : Vertex I.dimension) :
    Cube.vertices (𝟙 I) v = v := rfl
@[simp] theorem Cube.vertices_comp {I J K : Cube} (f : I ⟶ J) (g : J ⟶ K)
    (v : Vertex I.dimension) : Cube.vertices (f ≫ g) v = Cube.vertices g (Cube.vertices f v) := by
  funext i
  exact Dim.eval_subst f (g i) v

/-- The object universe is one level larger than every decoded carrier. -/
structure FiniteCode where
  Carrier : Type u
  finite : Finite Carrier

attribute [instance] FiniteCode.finite

/-- A functor from the indiscrete groupoid of vertices to finite sets and bijections. -/
structure VertexSystem (V : Type v) where
  obj : V → FiniteCode.{u}
  arrow : ∀ v w, (obj v).Carrier ≃ (obj w).Carrier
  identity : ∀ v, arrow v v = Equiv.refl _
  composition : ∀ v w z, (arrow v w).trans (arrow w z) = arrow v z

namespace VertexSystem
variable {V W Z : Type v}

def reindex (T : VertexSystem.{u} V) (f : W → V) : VertexSystem.{u} W where
  obj w := T.obj (f w)
  arrow v w := T.arrow (f v) (f w)
  identity w := T.identity (f w)
  composition v w z := T.composition (f v) (f w) (f z)

@[simp] theorem reindex_id (T : VertexSystem.{u} V) : T.reindex id = T := rfl
@[simp] theorem reindex_comp (T : VertexSystem.{u} V) (f : W → V) (g : Z → W) :
    (T.reindex f).reindex g = T.reindex (f ∘ g) := rfl

/-- The decoder has small fibers even though the code type is large. -/
def Tuple (T : VertexSystem.{u} V) :=
  { x : ∀ v, (T.obj v).Carrier // ∀ v w, T.arrow v w (x v) = x w }

@[ext] theorem Tuple.ext {T : VertexSystem.{u} V} {x y : T.Tuple}
    (h : ∀ v, x.val v = y.val v) : x = y := Subtype.ext (funext h)

theorem Tuple.hext {T U : VertexSystem.{u} V} (hT : T = U) {a : T.Tuple} {b : U.Tuple}
    (h : ∀ v, HEq (a.val v) (b.val v)) : HEq a b := by
  subst U
  exact heq_of_eq (Tuple.ext (fun v => eq_of_heq (h v)))

theorem Tuple.val_heq {T U : VertexSystem.{u} V} (hT : T = U) {a : T.Tuple} {b : U.Tuple}
    (h : HEq a b) (v : V) : HEq (a.val v) (b.val v) := by
  subst U
  cases h
  rfl

def Tuple.reindex {T : VertexSystem.{u} V} (x : T.Tuple) (f : W → V) : (T.reindex f).Tuple :=
  ⟨fun w => x.val (f w), fun v w => x.property (f v) (f w)⟩

@[simp] theorem Tuple.reindex_comp {T : VertexSystem.{u} V} (x : T.Tuple)
    (f : W → V) (g : Z → W) : (x.reindex f).reindex g = x.reindex (f ∘ g) := rfl

def tupleEquiv (T : VertexSystem.{u} V) (v : V) : T.Tuple ≃ (T.obj v).Carrier where
  toFun x := x.val v
  invFun a := ⟨fun w => T.arrow v w a, fun w z => by
    exact congrArg (fun e : (T.obj v).Carrier ≃ (T.obj z).Carrier => e a)
      (T.composition v w z)⟩
  left_inv x := by
    apply Tuple.ext
    intro w
    exact x.property v w
  right_inv a := by simp [T.identity]

theorem arrow_symm (T : VertexSystem.{u} V) (v w : V) :
    (T.arrow v w).symm = T.arrow w v := by
  apply Equiv.ext
  intro a
  apply (T.arrow v w).injective
  rw [Equiv.apply_symm_apply]
  have h := congrArg (fun e => e a) (T.composition w v w)
  exact (h.trans (congrArg (fun e => e a) (T.identity w))).symm

theorem arrow_comp_apply (T : VertexSystem.{u} V) (v w z : V) (a : (T.obj v).Carrier) :
    T.arrow w z (T.arrow v w a) = T.arrow v z a :=
  congrArg (fun e => e a) (T.composition v w z)

/-- Any chosen vertex of the local system presents every represented tuple. -/
def tupleGlobalEquiv (T : VertexSystem.{u} V) (f : W → V) (w₀ : W) (v₀ : V) :
    (T.reindex f).Tuple ≃ (T.obj v₀).Carrier :=
  (tupleEquiv (T.reindex f) w₀).trans (T.arrow (f w₀) v₀)

theorem tupleGlobalEquiv_apply (T : VertexSystem.{u} V) (f : W → V) (w₀ w : W)
    (v₀ : V) (x : (T.reindex f).Tuple) :
    tupleGlobalEquiv T f w₀ v₀ x = T.arrow (f w) v₀ (x.val w) := by
  have hc := congrArg (fun e => e (x.val w₀)) (T.composition (f w₀) (f w) v₀)
  change T.arrow (f w₀) v₀ (x.val w₀) = _
  exact hc.symm.trans (congrArg (T.arrow (f w) v₀) (x.property w₀ w))

theorem tupleGlobalEquiv_symm_apply (T : VertexSystem.{u} V) (f : W → V)
    (w₀ w : W) (v₀ : V) (a : (T.obj v₀).Carrier) :
    ((tupleGlobalEquiv T f w₀ v₀).symm a).val w = T.arrow v₀ (f w) a := by
  change T.arrow (f w₀) (f w) ((T.arrow (f w₀) v₀).symm a) = _
  rw [arrow_symm]
  exact T.arrow_comp_apply v₀ (f w₀) (f w) a

theorem tupleGlobalEquiv_reindex (T : VertexSystem.{u} V) (f : W → V) (g : Z → W)
    (w₀ : W) (z₀ : Z) (v₀ : V) (x : (T.reindex f).Tuple) :
    tupleGlobalEquiv T (f ∘ g) z₀ v₀ (x.reindex g) = tupleGlobalEquiv T f w₀ v₀ x :=
  (tupleGlobalEquiv_apply T f w₀ (g z₀) v₀ x).symm

/-- Fill a tuple along arbitrary vertexwise sources, using the actual code arrows. -/
def fillTuple {V : Type v} (T : VertexSystem.{u} (V × Bool)) (r : V → Bool)
    (base : (T.reindex (fun v => (v, r v))).Tuple) : T.Tuple where
  val vz := T.arrow (vz.1, r vz.1) vz (base.val vz.1)
  property vz wz := by
    have h₁ := congrArg (fun e => e (base.val vz.1)) (T.composition (vz.1, r vz.1) vz wz)
    have h₂ := congrArg (fun e => e (base.val vz.1))
      (T.composition (vz.1, r vz.1) (wz.1, r wz.1) wz)
    change T.arrow vz wz (T.arrow (vz.1, r vz.1) vz (base.val vz.1)) = _
    exact h₁.trans (h₂.symm.trans
      (congrArg (T.arrow (wz.1, r wz.1) wz) (base.property vz.1 wz.1)))

theorem fillTuple_source {V : Type v} (T : VertexSystem.{u} (V × Bool)) (r : V → Bool)
    (base : (T.reindex (fun v => (v, r v))).Tuple) :
    (fillTuple T r base).reindex (fun v => (v, r v)) = base := by
  apply Tuple.ext
  intro v
  exact congrArg (fun e => e (base.val v)) (T.identity (v, r v))

/-- Any tube tuple agreeing on the source graph agrees with the computed filler. -/
theorem fillTuple_tube {V W : Type v} (T : VertexSystem.{u} (V × Bool))
    (r : V → Bool) (base : (T.reindex (fun v => (v, r v))).Tuple)
    (f : W → V) (tube : (T.reindex (fun wz : W × Bool => (f wz.1, wz.2))).Tuple)
    (h : ∀ w, tube.val (w, r (f w)) = base.val (f w)) :
    (fillTuple T r base).reindex (fun wz : W × Bool => (f wz.1, wz.2)) = tube := by
  apply Tuple.ext
  intro wz
  change T.arrow (f wz.1, r (f wz.1)) (f wz.1, wz.2) (base.val (f wz.1)) = tube.val wz
  rw [← h wz.1]
  exact tube.property (wz.1, r (f wz.1)) wz

theorem fillTuple_natural {V W : Type v} (T : VertexSystem.{u} (V × Bool))
    (r : V → Bool) (base : (T.reindex (fun v => (v, r v))).Tuple) (f : W → V) :
    fillTuple (T.reindex (fun wz : W × Bool => (f wz.1, wz.2))) (r ∘ f) (base.reindex f) =
      (fillTuple T r base).reindex (fun wz : W × Bool => (f wz.1, wz.2)) := rfl

/-- Rebuild all arrows by conjugating the base system with chosen vertical bijections. -/
def conjugate (B : VertexSystem.{u} V) (A : V → FiniteCode.{u})
    (e : ∀ v, (B.obj v).Carrier ≃ (A v).Carrier) : VertexSystem.{u} V where
  obj := A
  arrow v w := (e v).symm.trans ((B.arrow v w).trans (e w))
  identity v := by ext a; simp [B.identity]
  composition v w z := by
    ext a
    change e z (B.arrow w z ((e w).symm (e w (B.arrow v w ((e v).symm a))))) = _
    rw [Equiv.symm_apply_apply]
    exact congrArg (e z) (B.arrow_comp_apply v w z ((e v).symm a))

@[ext] theorem ext {B C : VertexSystem.{u} V} (ho : B.obj = C.obj)
    (ha : HEq B.arrow C.arrow) : B = C := by
  cases B
  cases C
  cases ho
  cases ha
  rfl

/-- Conjugation recovers a system when its chosen vertical arrows are its own arrows. -/
theorem conjugate_from_system (T : VertexSystem.{u} V) (f : V → V) :
    (T.reindex f).conjugate T.obj (fun v => T.arrow (f v) v) = T := by
  refine VertexSystem.ext (B := (T.reindex f).conjugate T.obj (fun v => T.arrow (f v) v)) (C := T) rfl ?_
  apply heq_of_eq
  funext v w
  apply Equiv.ext
  intro a
  change T.arrow (f w) w (T.arrow (f v) (f w) ((T.arrow (f v) v).symm a)) = _
  rw [T.arrow_symm]
  exact (congrArg (T.arrow (f w) w) (T.arrow_comp_apply v (f v) (f w) a)).trans
    (T.arrow_comp_apply v (f w) w a)


theorem conjugate_eq (B : VertexSystem.{u} V) (A : V → FiniteCode.{u})
    (e : ∀ v, (B.obj v).Carrier ≃ (A v).Carrier) (ho : A = B.obj)
    (he : ∀ v, HEq (e v) (Equiv.refl (B.obj v).Carrier)) : B.conjugate A e = B := by
  subst A
  have hh : e = fun v => Equiv.refl (B.obj v).Carrier := funext (fun v => eq_of_heq (he v))
  subst e
  rfl


theorem conjugate_congr {B C : VertexSystem.{u} V} (hB : B = C)
    {A D : V → FiniteCode.{u}} (hA : A = D)
    {e : ∀ v, (B.obj v).Carrier ≃ (A v).Carrier}
    {g : ∀ v, (C.obj v).Carrier ≃ (D v).Carrier}
    (he : ∀ v, HEq (e v) (g v)) : B.conjugate A e = C.conjugate D g := by
  subst C
  subst D
  have hh : e = g := funext (fun v => eq_of_heq (he v))
  subst g
  rfl

end VertexSystem

/-- Finite vertex-box data, with the entire source functor as its boundary. -/
structure VertexBox (V : Type v) (φ : V → Prop) (r : V → Bool) where
  base : VertexSystem.{u} V
  tube : VertexSystem.{u} ({v // φ v} × Bool)
  boundary : tube.reindex (fun v : {v // φ v} => (v, r v.val)) = base.reindex Subtype.val

namespace VertexBox
variable {V : Type v} {φ : V → Prop} {r : V → Bool}

noncomputable def object (b : VertexBox.{u} V φ r) (vz : V × Bool) : FiniteCode.{u} := by
  classical
  exact if hv : φ vz.1 then b.tube.obj (⟨vz.1, hv⟩, vz.2) else b.base.obj vz.1

theorem source_object (b : VertexBox.{u} V φ r) (v : V) :
    b.object (v, r v) = b.base.obj v := by
  classical
  unfold object
  split
  · rename_i hv
    exact congrFun (congrArg VertexSystem.obj b.boundary) ⟨v, hv⟩
  · rfl

noncomputable def vertical (b : VertexBox.{u} V φ r) (vz : V × Bool) :
    (b.base.obj vz.1).Carrier ≃ (b.object vz).Carrier := by
  classical
  unfold object
  split
  · rename_i hv
    have ho : b.tube.obj (⟨vz.1, hv⟩, r vz.1) = b.base.obj vz.1 :=
      congrFun (congrArg VertexSystem.obj b.boundary) ⟨vz.1, hv⟩
    exact (Equiv.cast (congrArg FiniteCode.Carrier ho.symm)).trans
      (b.tube.arrow (⟨vz.1, hv⟩, r vz.1) (⟨vz.1, hv⟩, vz.2))
  · exact Equiv.refl _

private theorem cast_heq (A B : Type u) (h : A = B) :
    HEq (Equiv.cast h) (Equiv.refl A) := by subst B; rfl

theorem vertical_source (b : VertexBox.{u} V φ r) (v : V) :
    HEq (b.vertical (v, r v)) (Equiv.refl (b.base.obj v).Carrier) := by
  classical
  unfold vertical
  split
  · rename_i hv
    rw [b.tube.identity]
    exact (_root_.cast_heq _ _).trans (cast_heq _ _ _)
  · exact _root_.cast_heq _ _

noncomputable def fill (b : VertexBox.{u} V φ r) : VertexSystem.{u} (V × Bool) :=
  (b.base.reindex Prod.fst).conjugate b.object b.vertical

theorem fill_source (b : VertexBox.{u} V φ r) :
    b.fill.reindex (fun v => (v, r v)) = b.base :=
  b.base.conjugate_eq (fun v => b.object (v, r v)) (fun v => b.vertical (v, r v))
    (funext b.source_object) b.vertical_source

private theorem cast_trans_heq {A B C : Type u} (h : A = B) (e : B ≃ C) :
    HEq ((Equiv.cast h).trans e) e := by subst B; rfl

theorem tube_object (b : VertexBox.{u} V φ r) (vz : {v // φ v} × Bool) :
    b.object (vz.1.val, vz.2) = b.tube.obj vz := by
  classical
  exact dite_eq_left vz.1.property

theorem vertical_tube (b : VertexBox.{u} V φ r) (vz : {v // φ v} × Bool) :
    HEq (b.vertical (vz.1.val, vz.2)) (b.tube.arrow (vz.1, r vz.1.val) vz) := by
  classical
  unfold vertical
  split
  · exact (_root_.cast_heq _ _).trans (cast_trans_heq _ _)
  · rename_i hn
    exact (hn vz.1.property).elim

theorem fill_tube (b : VertexBox.{u} V φ r) :
    b.fill.reindex (fun vz : {v // φ v} × Bool => (vz.1.val, vz.2)) = b.tube := by
  have hb : b.base.reindex (fun vz : {v // φ v} × Bool => vz.1.val) =
      b.tube.reindex (fun vz : {v // φ v} × Bool => (vz.1, r vz.1.val)) :=
    congrArg (fun T => T.reindex (fun vz : {v // φ v} × Bool => vz.1)) b.boundary.symm
  exact (VertexSystem.conjugate_congr hb (funext b.tube_object) b.vertical_tube).trans
    (b.tube.conjugate_from_system (fun vz => (vz.1, r vz.1.val)))

def reindex {W : Type v} (b : VertexBox.{u} V φ r) (f : W → V) :
    VertexBox.{u} W (φ ∘ f) (r ∘ f) where
  base := b.base.reindex f
  tube := b.tube.reindex (fun wz => (⟨f wz.1.val, wz.1.property⟩, wz.2))
  boundary := congrArg (fun T => T.reindex (fun w : {w // (φ ∘ f) w} =>
    (⟨f w.val, w.property⟩ : {v // φ v}))) b.boundary

theorem fill_reindex {W : Type v} (b : VertexBox.{u} V φ r) (f : W → V) :
    (b.reindex f).fill = b.fill.reindex (fun wz : W × Bool => (f wz.1, wz.2)) := rfl

end VertexBox

def finiteNerve : Context.{u+1} where
  obj I := VertexSystem.{u} (Vertex I.unop.dimension)
  map f := TypeCat.ofHom (fun T => T.reindex (Cube.vertices f.unop))
  map_id I := rfl
  map_comp f g := by
    apply ConcreteCategory.hom_ext
    intro T
    change T.reindex (Cube.vertices (f ≫ g).unop) = _
    have h : Cube.vertices (f ≫ g).unop = Cube.vertices f.unop ∘ Cube.vertices g.unop := by
      funext v
      exact Cube.vertices_comp g.unop f.unop v
    rw [h]
    rfl

/-- The nerve regarded as a family over any context in its code universe. -/
def nerveFamily (Γ : Context.{u+1}) : Family Γ where
  obj x := VertexSystem.{u} (Vertex x.obj.unop.dimension)
  map f := TypeCat.ofHom (fun T => T.reindex (Cube.vertices f.hom.unop))
  map_id _ := rfl
  map_comp f g := by
    apply ConcreteCategory.hom_ext
    intro T
    have h : Cube.vertices (f ≫ g).hom.unop =
        Cube.vertices f.hom.unop ∘ Cube.vertices g.hom.unop :=
      funext (Cube.vertices_comp g.hom.unop f.hom.unop)
    exact congrArg T.reindex h

def Cube.vertex {I : Cube} (v : Vertex I.dimension) : (⟨0⟩ : Cube) ⟶ I :=
  fun i => .endpoint (v i)

@[simp] theorem Dim.subst_endpoints {n : ℕ} (d : Dim n) (v : Vertex n) :
    d.subst (fun i => (Dim.endpoint (v i) : Dim 0)) = .endpoint (d.eval v) := by
  cases d <;> rfl

@[simp] theorem Cube.vertex_comp {I J : Cube} (v : Vertex I.dimension) (f : I ⟶ J) :
    Cube.vertex v ≫ f = Cube.vertex (Cube.vertices f v) := by
  funext i
  exact Dim.subst_endpoints (f i) v

def vertexPoint {Γ : Context.{u}} (x : Γ.Elements) (v : Vertex x.obj.unop.dimension) : Γ.Elements :=
  Γ.elementsMk (.op ⟨0⟩) (Γ.map (Quiver.Hom.op (Cube.vertex v)) x.val)

def vertexHom {Γ : Context.{u}} (x : Γ.Elements) (v : Vertex x.obj.unop.dimension) :
    x ⟶ vertexPoint x v := Functor.Elements.homMk (Quiver.Hom.op (Cube.vertex v)) rfl

def emptyVertex : Vertex 0 := Fin.elim0

theorem vertexPoint_natural {Γ : Context.{u}} {x y : Γ.Elements} (f : x ⟶ y)
    (v : Vertex y.obj.unop.dimension) : vertexPoint y v = vertexPoint x (Cube.vertices f.hom.unop v) := by
  apply congrArg (Γ.elementsMk (.op ⟨0⟩))
  change Γ.map (Quiver.Hom.op (Cube.vertex v)) y.val =
    Γ.map (Quiver.Hom.op (Cube.vertex (Cube.vertices f.hom.unop v))) x.val
  rw [← f.map_val]
  have hc : f.hom ≫ Quiver.Hom.op (Cube.vertex v) =
      Quiver.Hom.op (Cube.vertex (Cube.vertices f.hom.unop v)) :=
    congrArg Quiver.Hom.op (Cube.vertex_comp v f.hom.unop)
  rw [← types_comp_apply, ← Γ.map_comp, hc]

theorem map_vertex_natural {Γ : Context.{u}} {x y : Γ.Elements} (f : x ⟶ y)
    (v : Vertex y.obj.unop.dimension) :
    Γ.map (Quiver.Hom.op (Cube.vertex v)) y.val =
      Γ.map (Quiver.Hom.op (Cube.vertex (Cube.vertices f.hom.unop v))) x.val := by
  rw [← f.map_val]
  have hc : f.hom ≫ Quiver.Hom.op (Cube.vertex v) =
      Quiver.Hom.op (Cube.vertex (Cube.vertices f.hom.unop v)) :=
    congrArg Quiver.Hom.op (Cube.vertex_comp v f.hom.unop)
  rw [← types_comp_apply, ← Γ.map_comp, hc]

namespace NerveFilling
variable {Γ : Context.{u+1}} {φ : Subcontext Γ} {r : Term (interval Γ)}
  (b : OpenBox (nerveFamily (total (interval Γ))) φ r)

abbrev line (x : Γ.Elements) (v : Vertex x.obj.unop.dimension) (hv : φ.Holds (vertexPoint x v)) :=
  (b.tube.val (freshExtension (vertexPoint x v)) (φ.natural (freshBaseHom _) hv)).reindex
    (fun z : Bool => (fun _ : Fin 1 => z))

theorem source_dimension (x : Γ.Elements) (v : Vertex x.obj.unop.dimension) :
    (r.val (vertexPoint x v)).down 0 = .endpoint (((r.val x).down 0).eval v) := by
  have h := congrArg (fun z => z.down 0) (r.property (vertexHom x v))
  exact h.symm.trans (Dim.subst_endpoints ((r.val x).down 0) v)

theorem line_source (x : Γ.Elements) (v : Vertex x.obj.unop.dimension)
    (hv : φ.Holds (vertexPoint x v)) :
    (line b x v hv).obj (((r.val x).down 0).eval v) = (b.base.val x).obj v := by
  let a := vertexPoint x v
  let k := intervalArgument (𝟙 a) (r.val a)
  have ht := b.tube.natural k (φ.natural (freshBaseHom a) hv)
  have ho := congrArg (fun T => T.obj emptyVertex) ht
  have hb := congrArg (fun T => T.obj emptyVertex) (b.boundary a hv)
  have hn := congrArg (fun T => T.obj emptyVertex) (b.base.property (vertexHom x v))
  have he : Cube.vertices k.hom.unop emptyVertex = fun _ : Fin 1 => ((r.val x).down 0).eval v := by
    funext i
    rw [Fin.eq_zero i]
    change Dim.eval ((r.val a).down 0) emptyVertex = _
    rw [source_dimension]
    rfl
  change (b.tube.val (freshExtension a) _).obj (Cube.vertices k.hom.unop emptyVertex) = _ at ho
  rw [he] at ho
  exact ho.trans (hb.trans hn.symm)

def closedLine (γ : Γ.obj (.op ⟨0⟩)) (h : φ.Holds (Γ.elementsMk (.op ⟨0⟩) γ)) :
    VertexSystem.{u} Bool :=
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

noncomputable def object (x : Γ.Elements) (vz : Vertex x.obj.unop.dimension × Bool) : FiniteCode.{u} := by
  classical
  exact if hv : φ.Holds (vertexPoint x vz.1) then (line b x vz.1 hv).obj vz.2
    else (b.base.val x).obj vz.1

noncomputable def vertical (x : Γ.Elements) (vz : Vertex x.obj.unop.dimension × Bool) :
    ((b.base.val x).obj vz.1).Carrier ≃ (object b x vz).Carrier := by
  classical
  unfold object
  split
  · rename_i hv
    exact (Equiv.cast (congrArg FiniteCode.Carrier (line_source b x vz.1 hv).symm)).trans
      ((line b x vz.1 hv).arrow (((r.val x).down 0).eval vz.1) vz.2)
  · exact Equiv.refl _

noncomputable def system (x : Γ.Elements) : VertexSystem.{u} (Vertex x.obj.unop.dimension × Bool) :=
  ((b.base.val x).reindex Prod.fst).conjugate (object b x) (vertical b x)

private theorem equiv_cast_heq {A B : Type u} (h : A = B) :
    HEq (Equiv.cast h) (Equiv.refl A) := by subst B; rfl

theorem object_source (x : Γ.Elements) (v : Vertex x.obj.unop.dimension) :
    object b x (v, ((r.val x).down 0).eval v) = (b.base.val x).obj v := by
  classical
  unfold object
  split
  · exact line_source b x v _
  · rfl

theorem vertical_source (x : Γ.Elements) (v : Vertex x.obj.unop.dimension) :
    HEq (vertical b x (v, ((r.val x).down 0).eval v))
      (Equiv.refl ((b.base.val x).obj v).Carrier) := by
  classical
  unfold vertical
  split
  · rw [VertexSystem.identity]
    exact (_root_.cast_heq _ _).trans (equiv_cast_heq _)
  · exact _root_.cast_heq _ _

theorem system_source (x : Γ.Elements) :
    (system b x).reindex (fun v => (v, ((r.val x).down 0).eval v)) = b.base.val x :=
  (b.base.val x).conjugate_eq _ _ (funext (object_source b x)) (vertical_source b x)

theorem dimension_natural {x y : Γ.Elements} (f : x ⟶ y) (v : Vertex y.obj.unop.dimension) :
    ((r.val y).down 0).eval v = ((r.val x).down 0).eval (Cube.vertices f.hom.unop v) := by
  have h := congrArg (fun z => (z.down 0).eval v) (r.property f)
  exact h.symm.trans (Dim.eval_subst f.hom.unop ((r.val x).down 0) v)

theorem object_natural {x y : Γ.Elements} (f : x ⟶ y)
    (vz : Vertex y.obj.unop.dimension × Bool) :
    object b y vz = object b x (Cube.vertices f.hom.unop vz.1, vz.2) := by
  classical
  have hp := vertexPoint_natural f vz.1
  unfold object
  by_cases hy : φ.Holds (vertexPoint y vz.1)
  · have hx : φ.Holds (vertexPoint x (Cube.vertices f.hom.unop vz.1)) := hp ▸ hy
    simp only [dite_eq_left hy, dite_eq_left hx]
    exact congrArg (fun T => T.obj vz.2) (line_natural b f vz.1 hy hx)
  · have hx : ¬φ.Holds (vertexPoint x (Cube.vertices f.hom.unop vz.1)) := fun h => hy (hp.symm ▸ h)
    simp only [dite_eq_right hy, dite_eq_right hx]
    exact (congrArg (fun T => T.obj vz.1) (b.base.property f)).symm

private theorem equiv_cast_trans_heq {A B C : Type u} (h : A = B) (e : B ≃ C) :
    HEq ((Equiv.cast h).trans e) e := by subst B; rfl

theorem vertical_line (x : Γ.Elements) (vz : Vertex x.obj.unop.dimension × Bool)
    (h : φ.Holds (vertexPoint x vz.1)) :
    HEq (vertical b x vz) ((line b x vz.1 h).arrow (((r.val x).down 0).eval vz.1) vz.2) := by
  classical
  unfold vertical
  split
  · exact (_root_.cast_heq _ _).trans (equiv_cast_trans_heq _ _)
  · rename_i hn
    exact (hn h).elim

private theorem arrow_heq {W : Type} {T U : VertexSystem.{u} W} (h : T = U)
    {v w v' w' : W} (hv : v = v') (hw : w = w') : HEq (T.arrow v w) (U.arrow v' w') := by
  subst U
  subst v'
  subst w'
  rfl

private theorem equiv_refl_heq {A B : Type u} (h : A = B) :
    HEq (Equiv.refl A) (Equiv.refl B) := by subst B; rfl

theorem vertical_natural {x y : Γ.Elements} (f : x ⟶ y)
    (vz : Vertex y.obj.unop.dimension × Bool) :
    HEq (vertical b y vz) (vertical b x (Cube.vertices f.hom.unop vz.1, vz.2)) := by
  classical
  have hp := vertexPoint_natural f vz.1
  by_cases hy : φ.Holds (vertexPoint y vz.1)
  · have hx : φ.Holds (vertexPoint x (Cube.vertices f.hom.unop vz.1)) := hp ▸ hy
    exact (vertical_line b y vz hy).trans
      ((arrow_heq (line_natural b f vz.1 hy hx) (dimension_natural f vz.1) rfl).trans
        (vertical_line b x (Cube.vertices f.hom.unop vz.1, vz.2) hx).symm)
  · have hx : ¬φ.Holds (vertexPoint x (Cube.vertices f.hom.unop vz.1)) := fun h => hy (hp.symm ▸ h)
    have left : HEq (vertical b y vz) (Equiv.refl ((b.base.val y).obj vz.1).Carrier) := by
      unfold vertical
      split
      · contradiction
      · exact _root_.cast_heq _ _
    have right : HEq (vertical b x (Cube.vertices f.hom.unop vz.1, vz.2))
        (Equiv.refl ((b.base.val x).obj (Cube.vertices f.hom.unop vz.1)).Carrier) := by
      unfold vertical
      split
      · contradiction
      · exact _root_.cast_heq _ _
    exact left.trans ((equiv_refl_heq (congrArg (fun T => (T.obj vz.1).Carrier)
      (b.base.property f).symm)).trans right.symm)

theorem system_natural {x y : Γ.Elements} (f : x ⟶ y) :
    system b y = (system b x).reindex (fun vz : Vertex y.obj.unop.dimension × Bool =>
      (Cube.vertices f.hom.unop vz.1, vz.2)) :=
  VertexSystem.conjugate_congr (congrArg (fun T : VertexSystem.{u} (Vertex y.obj.unop.dimension) =>
      T.reindex (Prod.fst : Vertex y.obj.unop.dimension × Bool → Vertex y.obj.unop.dimension))
        (b.base.property f).symm)
    (funext (object_natural b f)) (vertical_natural b f)

noncomputable def value (x : (total (interval Γ)).Elements) :
    VertexSystem.{u} (Vertex x.obj.unop.dimension) :=
  (system b ((projection (interval Γ)).mapElements.obj x)).reindex
    (fun v => (v, (x.val.2.down 0).eval v))

theorem value_source (x : Γ.Elements) :
    value b ((graph r).mapElements.obj x) = b.base.val x := system_source b x

theorem value_natural {x y : (total (interval Γ)).Elements} (f : x ⟶ y) :
    (value b x).reindex (Cube.vertices f.hom.unop) = value b y := by
  let g := (projection (interval Γ)).mapElements.map f
  have hs := system_natural b g
  have hi : Cube.comp f.hom.unop x.val.2.down = y.val.2.down := by
    have h := (Sigma.mk.inj f.map_val).2
    exact congrArg ULift.down (eq_of_heq h)
  unfold value
  rw [hs]
  apply congrArg (VertexSystem.reindex (system b ((projection (interval Γ)).mapElements.obj x)))
  funext v
  apply Prod.ext
  · rfl
  have he := congrArg (fun z => (z 0).eval v) hi
  exact (Dim.eval_subst f.hom.unop (x.val.2.down 0) v).symm.trans he

noncomputable def fillSection : Term (nerveFamily (total (interval Γ))) where
  val := value b
  property := value_natural b

def vertexPair {n : Nat} (vz : Vertex n × Bool) : Vertex (n+1) := Fin.cases vz.2 vz.1

def genericSystem (x : Γ.Elements) (hx : φ.Holds x) :
    VertexSystem.{u} (Vertex x.obj.unop.dimension × Bool) :=
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
  have h := congrArg (fun T : VertexSystem.{u} (Vertex 1) =>
    T.reindex (fun z : Bool => (fun _ : Fin 1 => z))) ht
  change (b.tube.val (freshExtension x) _).reindex _ = _ at h
  exact (congrArg (VertexSystem.reindex (b.tube.val (freshExtension x)
    (φ.natural (freshBaseHom x) hx))) he).symm.trans h

theorem object_tube (x : Γ.Elements) (hx : φ.Holds x)
    (vz : Vertex x.obj.unop.dimension × Bool) :
    object b x vz = (genericSystem b x hx).obj vz := by
  classical
  unfold object
  rw [dite_eq_left (φ.natural (vertexHom x vz.1) hx)]
  exact (congrArg (fun T => T.obj vz.2) (genericSystem_line b x hx vz.1)).symm

theorem vertical_tube (x : Γ.Elements) (hx : φ.Holds x)
    (vz : Vertex x.obj.unop.dimension × Bool) :
    HEq (vertical b x vz) ((genericSystem b x hx).arrow
      (vz.1, ((r.val x).down 0).eval vz.1) vz) :=
  (vertical_line b x vz (φ.natural (vertexHom x vz.1) hx)).trans
    (arrow_heq (genericSystem_line b x hx vz.1).symm rfl rfl)

theorem system_tube (x : Γ.Elements) (hx : φ.Holds x) :
    system b x = genericSystem b x hx := by
  have hb := congrArg (fun T : VertexSystem.{u} (Vertex x.obj.unop.dimension) =>
    T.reindex (Prod.fst : Vertex x.obj.unop.dimension × Bool → Vertex x.obj.unop.dimension))
      (genericSystem_source b x hx).symm
  exact (VertexSystem.conjugate_congr hb (funext (object_tube b x hx))
    (vertical_tube b x hx)).trans
      ((genericSystem b x hx).conjugate_from_system
        (fun vz => (vz.1, ((r.val x).down 0).eval vz.1)))

theorem value_tube (x : (total (interval Γ)).Elements)
    (hx : φ.Holds ((projection (interval Γ)).mapElements.obj x)) :
    value b x = b.tube.val x hx := by
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
  rw [system_tube b a hx]
  exact (congrArg (VertexSystem.reindex (b.tube.val (freshExtension a)
    (φ.natural (freshBaseHom a) hx))) he).symm.trans ht

theorem fillSection_fills : b.Fills (fillSection b) := by
  constructor
  · apply Term.ext
    exact value_source b
  · exact value_tube b

theorem vertexPoint_reindex {Δ : Context.{u+1}} (σ : Δ ⟶ Γ)
    (x : Δ.Elements) (v : Vertex x.obj.unop.dimension) :
    σ.mapElements.obj (vertexPoint x v) = vertexPoint (σ.mapElements.obj x) v := by
  apply congrArg (Γ.elementsMk (.op ⟨0⟩))
  exact σ.naturality_apply (Quiver.Hom.op (Cube.vertex v)) x.val

theorem freshExtension_reindex {Δ : Context.{u+1}} (σ : Δ ⟶ Γ) (x : Δ.Elements) :
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

theorem line_reindex {Δ : Context.{u+1}} (σ : Δ ⟶ Γ) (x : Δ.Elements)
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
  exact congrArg (fun T : VertexSystem.{u} (Vertex 1) => T.reindex (fun z : Bool => fun _ => z))
    (eq_of_heq he)

theorem object_reindex {Δ : Context.{u+1}} (σ : Δ ⟶ Γ) (x : Δ.Elements)
    (vz : Vertex x.obj.unop.dimension × Bool) :
    object (b.reindex σ) x vz = object b (σ.mapElements.obj x) vz := by
  classical
  have hp := vertexPoint_reindex σ x vz.1
  unfold object
  by_cases hx : (φ.reindex σ).Holds (vertexPoint x vz.1)
  · have hy : φ.Holds (vertexPoint (σ.mapElements.obj x) vz.1) := hp ▸ hx
    rw [dite_eq_left hx, dite_eq_left hy]
    exact congrArg (fun T => T.obj vz.2) (line_reindex b σ x vz.1 hx hy)
  · have hy : ¬φ.Holds (vertexPoint (σ.mapElements.obj x) vz.1) := fun h => hx (show φ.Holds (σ.mapElements.obj (vertexPoint x vz.1)) from hp.symm ▸ h)
    rw [dite_eq_right hx, dite_eq_right hy]
    rfl

theorem vertical_reindex {Δ : Context.{u+1}} (σ : Δ ⟶ Γ) (x : Δ.Elements)
    (vz : Vertex x.obj.unop.dimension × Bool) :
    HEq (vertical (b.reindex σ) x vz) (vertical b (σ.mapElements.obj x) vz) := by
  classical
  have hp := vertexPoint_reindex σ x vz.1
  by_cases hx : (φ.reindex σ).Holds (vertexPoint x vz.1)
  · have hy : φ.Holds (vertexPoint (σ.mapElements.obj x) vz.1) := hp ▸ hx
    exact (vertical_line (b.reindex σ) x vz hx).trans
      ((arrow_heq (line_reindex b σ x vz.1 hx hy) rfl rfl).trans
        (vertical_line b (σ.mapElements.obj x) vz hy).symm)
  · have hy : ¬φ.Holds (vertexPoint (σ.mapElements.obj x) vz.1) := fun h => hx (show φ.Holds (σ.mapElements.obj (vertexPoint x vz.1)) from hp.symm ▸ h)
    have left : HEq (vertical (b.reindex σ) x vz)
        (Equiv.refl ((b.base.val (σ.mapElements.obj x)).obj vz.1).Carrier) := by
      unfold vertical
      split
      · contradiction
      · exact _root_.cast_heq _ _
    have right : HEq (vertical b (σ.mapElements.obj x) vz)
        (Equiv.refl ((b.base.val (σ.mapElements.obj x)).obj vz.1).Carrier) := by
      unfold vertical
      split
      · contradiction
      · exact _root_.cast_heq _ _
    exact left.trans right.symm

theorem system_reindex {Δ : Context.{u+1}} (σ : Δ ⟶ Γ) (x : Δ.Elements) :
    system (b.reindex σ) x = system b (σ.mapElements.obj x) :=
  VertexSystem.conjugate_congr rfl (funext (object_reindex b σ x)) (vertical_reindex b σ x)

theorem fillSection_reindex {Δ : Context.{u+1}} (σ : Δ ⟶ Γ) :
    fillSection (b.reindex σ) = Term.reindex (fillSection b) (intervalSub σ) := by
  apply Term.ext
  intro x
  exact congrArg (fun T => T.reindex (fun v => (v, (x.val.2.down 0).eval v)))
    (system_reindex b σ ((projection (interval Δ)).mapElements.obj x))

end NerveFilling

noncomputable def nerveFilling (Γ : Context.{u+1}) : Filling (nerveFamily Γ) where
  fill _ _ _ b := NerveFilling.fillSection b

theorem nerveFilling_lawful (Γ : Context.{u+1}) : (nerveFilling Γ).Lawful where
  fills _ _ _ b := NerveFilling.fillSection_fills b
  uniform _ _ _ b σ := NerveFilling.fillSection_reindex b σ

namespace VertexSystem

def reindexEquiv {V W : Type} (T : VertexSystem.{u} V) (f : W → V) (w : W) :
    T.Tuple ≃ (T.reindex f).Tuple :=
  (T.tupleEquiv (f w)).trans (T.reindex f |>.tupleEquiv w).symm

theorem reindexEquiv_apply {V W : Type} (T : VertexSystem.{u} V) (f : W → V)
    (w : W) (a : T.Tuple) : reindexEquiv T f w a = a.reindex f := by
  apply Tuple.ext
  intro z
  exact a.property (f w) (f z)

theorem cast_tuple_val_heq {V : Type} {T U : VertexSystem.{u} V} (h : T = U)
    (a : T.Tuple) (v : V) :
    HEq ((cast (congrArg Tuple h) a).val v) (a.val v) := by
  subst U
  rfl

end VertexSystem

namespace TupleDecoder

noncomputable def mapEquiv {x y : finiteNerve.{u}.Elements} (f : x ⟶ y) :
    x.val.Tuple ≃ y.val.Tuple :=
  (VertexSystem.reindexEquiv x.val (Cube.vertices f.hom.unop) (fun _ => false)).trans
    (Equiv.cast (congrArg VertexSystem.Tuple f.map_val))

theorem mapEquiv_coordinate {x y : finiteNerve.{u}.Elements} (f : x ⟶ y)
    (a : x.val.Tuple) (v : Vertex y.obj.unop.dimension) :
    HEq ((mapEquiv f a).val v) (a.val (Cube.vertices f.hom.unop v)) := by
  unfold mapEquiv
  change HEq ((cast (congrArg VertexSystem.Tuple f.map_val)
    (VertexSystem.reindexEquiv x.val (Cube.vertices f.hom.unop) (fun _ => false) a)).val v) _
  exact (VertexSystem.cast_tuple_val_heq f.map_val _ v).trans
    (heq_of_eq (congrArg (fun z => z.val v)
      (VertexSystem.reindexEquiv_apply x.val (Cube.vertices f.hom.unop) (fun _ => false) a)))

private theorem tuple_val_heq_of_index_eq {V : Type} {T : VertexSystem.{u} V} (a : T.Tuple)
    {v w : V} (h : v = w) : HEq (a.val v) (a.val w) := by
  subst w
  rfl

noncomputable def family : Family finiteNerve.{u} where
  obj x := ULift.{u+1} x.val.Tuple
  map f := TypeCat.ofHom (fun a => ⟨mapEquiv f a.down⟩)
  map_id x := by
    apply ConcreteCategory.hom_ext
    intro a
    apply ULift.ext
    apply VertexSystem.Tuple.ext
    intro v
    exact eq_of_heq (mapEquiv_coordinate (𝟙 x) a.down v)
  map_comp f g := by
    apply ConcreteCategory.hom_ext
    intro a
    apply ULift.ext
    apply VertexSystem.Tuple.ext
    intro v
    exact eq_of_heq ((mapEquiv_coordinate (f ≫ g) a.down v).trans
      ((tuple_val_heq_of_index_eq a.down (Cube.vertices_comp g.hom.unop f.hom.unop v)).trans
        ((mapEquiv_coordinate f a.down (Cube.vertices g.hom.unop v)).symm.trans
          (mapEquiv_coordinate g (mapEquiv f a.down) v).symm)))

theorem bijective : BijectiveRestrictions family.{u} := by
  intro x y f
  change Function.Bijective (fun a : ULift.{u+1} x.val.Tuple =>
    (⟨mapEquiv f a.down⟩ : ULift.{u+1} y.val.Tuple))
  exact ((Equiv.ulift).trans ((mapEquiv f).trans Equiv.ulift.symm)).bijective

noncomputable def filling : Filling family.{u} := bijectiveFilling bijective

theorem filling_lawful : filling.{u}.Lawful := bijectiveFilling_lawful bijective

/-- Every selected decoder filler is the unique compatible section with its source. -/
theorem fill_eq {Γ : Context.{u+1}} (p : total (interval Γ) ⟶ finiteNerve.{u})
    (φ : Subcontext Γ) (r : Term (interval Γ)) (b : OpenBox (reindex family p) φ r)
    (t : Term (reindex family p)) (h : Term.reindex t (graph r) = b.base) :
    filling.fill p φ r b = t :=
  sections_equal_source (fun f => bijective (p.mapElements.map f)) r _ _
    ((filling_lawful.fills p φ r b).1.trans h.symm)

/-- A target cube chart; its domain has all Cartesian substitutions. -/
def chart {n : ℕ} (T : VertexSystem.{u} (Vertex n)) :
    representable.{u+1} ⟨n⟩ ⟶ finiteNerve.{u} where
  app _ := TypeCat.ofHom (fun f => T.reindex (Cube.vertices f.down))
  naturality _ _ f := by
    apply ConcreteCategory.hom_ext
    intro x
    exact congrArg (VertexSystem.reindex T) (funext (Cube.vertices_comp f.unop x.down))

noncomputable def chartSection {n : ℕ} (T : VertexSystem.{u} (Vertex n)) (a : T.Tuple) :
    Term (reindex family (chart T)) where
  val x := ⟨a.reindex (Cube.vertices x.val.down)⟩
  property {x y} f := by
    apply ULift.ext
    apply VertexSystem.Tuple.ext
    intro v
    have h : f.hom.unop ≫ x.val.down = y.val.down := congrArg ULift.down f.map_val
    exact eq_of_heq ((mapEquiv_coordinate ((chart T).mapElements.map f) _ v).trans
      (by
        change HEq (a.val (Cube.vertices x.val.down (Cube.vertices f.hom.unop v)))
          (a.val (Cube.vertices y.val.down v))
        rw [← Cube.vertices_comp, h]))

/-- The actual all-box filler recovers the complete target tuple section. -/
theorem fill_chart {Γ : Context.{u+1}} {n : ℕ} (T : VertexSystem.{u} (Vertex n))
    (p : total (interval Γ) ⟶ representable.{u+1} ⟨n⟩)
    (φ : Subcontext Γ) (r : Term (interval Γ))
    (b : OpenBox (reindex family (p ≫ chart T)) φ r) (a : T.Tuple)
    (h : Term.reindex (chartSection T a) (graph r ≫ p) = b.base) :
    filling.fill (p ≫ chart T) φ r b = Term.reindex (chartSection T a) p :=
  fill_eq _ φ r b _ h

end TupleDecoder

end SquareKit.Cubical.Cartesian
