import SquareKit.CartesianMap
import SquareKit.FirstOrderCategory
import SquareKit.FunctionCategory

/-! First-order syntax is interpreted at the boundary of the object-polymorphic
interfaces. An image model retains `F.obj (obj a)` as its carrier, using explicit
product comparisons rather than identifying it with a product definitionally. -/
namespace SquareKit.FirstOrderNaturality
open FirstOrderCompiler
universe u v w z u₃ v₃

structure Model {O : Type u} (C : CategoryOps.{u,v} O) (Prim : Ty → Ty → Type) (obj : Ty → O) where
  terminal : {a : Ty} → C.Hom (obj a) (obj .unit)
  fst : {a b : Ty} → C.Hom (obj (.prod a b)) (obj a)
  snd : {a b : Ty} → C.Hom (obj (.prod a b)) (obj b)
  pair : {a b c : Ty} → C.Hom (obj a) (obj b) → C.Hom (obj a) (obj c) → C.Hom (obj a) (obj (.prod b c))
  primitive : {a b : Ty} → Prim a b → C.Hom (obj a) (obj b)

variable {O : Type u} {C : CategoryOps.{u,v} O} {Prim : Ty → Ty → Type}

def objects (T : TerminalOps C) (P : ProductOps C) (base : O) : Ty → O
  | .base => base
  | .unit => T.unit
  | .prod a b => P.prod (objects T P base a) (objects T P base b)

def cartesian (T : TerminalOps C) (P : ProductOps C) (base : O)
    (primitive : {a b : Ty} → Prim a b → C.Hom (objects T P base a) (objects T P base b)) : Model C Prim (objects T P base) where
  terminal := T.terminal
  fst := P.fst
  snd := P.snd
  pair := P.pair
  primitive := primitive

def ofTarget (K : Target Prim) : Model (FirstOrderCategory.ops K) Prim id where
  terminal := K.terminal
  fst := K.fst
  snd := K.snd
  pair := K.pair
  primitive := K.primitive

variable {A : Ty → O}

def compileVar (M : Model C Prim A) : Var Γ a → C.Hom (A (context Γ)) (A a)
  | .here => M.snd
  | .there v => C.comp (compileVar M v) M.fst

def compile (M : Model C Prim A) : Term Prim Γ a → C.Hom (A (context Γ)) (A a)
  | .var v => compileVar M v
  | .unit => M.terminal
  | .pair t u => M.pair (compile M t) (compile M u)
  | .fst t => C.comp M.fst (compile M t)
  | .snd t => C.comp M.snd (compile M t)
  | .letE t u => C.comp (compile M u) (M.pair C.ident (compile M t))
  | .prim p t => C.comp (M.primitive p) (compile M t)

variable {Q : Type w} {D : CategoryOps.{w,z} Q}

/-- Local preservation between models, including the primitive obligation. -/
structure Preserves (F : RawMap C D) (H : HomEquiv D)
    (M : Model C Prim A) (N : Model D Prim (F.obj ∘ A)) : Prop where
  terminal : ∀ {a}, H.Rel (F.map (M.terminal (a := a))) N.terminal
  fst : ∀ {a b}, H.Rel (F.map (M.fst (a := a) (b := b))) N.fst
  snd : ∀ {a b}, H.Rel (F.map (M.snd (a := a) (b := b))) N.snd
  pair : ∀ {a b c} (f : C.Hom (A a) (A b)) (g : C.Hom (A a) (A c)),
    H.Rel (F.map (M.pair f g)) (N.pair (F.map f) (F.map g))
  primitive : ∀ {a b} (p : Prim a b), H.Rel (F.map (M.primitive p)) (N.primitive p)

structure ModelCongr (H : HomEquiv C) (M : Model C Prim A) : Prop where
  pair : ∀ {a b c} {f f' : C.Hom (A a) (A b)} {g g' : C.Hom (A a) (A c)},
    H.Rel f f' → H.Rel g g' → H.Rel (M.pair f g) (M.pair f' g')

variable {F : RawMap C D} {E : HomEquiv C} {H : HomEquiv D}
variable {M : Model C Prim A} {N : Model D Prim (F.obj ∘ A)}

theorem variable_naturality (L : MapLaws F E H) (K : CategoryCongr D H)
    (S : Preserves F H M N) (v : Var Γ a) :
    H.Rel (F.map (compileVar M v)) (compileVar N v) := by
  induction v with
  | here => exact S.snd
  | there v ih => exact H.trans (L.comp _ _) (K.comp ih S.fst)

/-- All terms and contexts; no source laws or function interpretation are needed. -/
theorem naturality (L : MapLaws F E H) (K : CategoryCongr D H)
    (P : ModelCongr H N) (S : Preserves F H M N) (t : Term Prim Γ a) :
    H.Rel (F.map (compile M t)) (compile N t) := by
  induction t with
  | var v => exact variable_naturality L K S v
  | unit => exact S.terminal
  | pair t u it iu => exact H.trans (S.pair _ _) (P.pair it iu)
  | fst t it => exact H.trans (L.comp _ _) (K.comp S.fst it)
  | snd t it => exact H.trans (L.comp _ _) (K.comp S.snd it)
  | letE t u it iu =>
    exact H.trans (L.comp _ _) (K.comp iu (H.trans (S.pair _ _) (P.pair L.ident it)))
  | prim p t it => exact H.trans (L.comp _ _) (K.comp (S.primitive p) it)

/-- The image model inserts the supplied non-strict comparisons at products. -/
def image (F : RawMap C D) (T : TerminalOps C) (P : ProductOps C)
    (U : TerminalOps D) (V : ProductOps D) (base : O)
    (i : TerminalMap F T U) (j : ProductMap F P V)
    (primitive : {a b : Ty} → Prim a b → D.Hom (F.obj (objects T P base a)) (F.obj (objects T P base b))) :
    Model D Prim (F.obj ∘ objects T P base) where
  terminal := D.comp i.inv U.terminal
  fst := D.comp V.fst (j _ _).hom
  snd := D.comp V.snd (j _ _).hom
  pair f g := D.comp (j _ _).inv (V.pair f g)
  primitive := primitive

variable {T : TerminalOps C} {P : ProductOps C} {U : TerminalOps D} {V : ProductOps D}

theorem image_congr (K : CategoryCongr D H) (VC : ProductCongr H V)
    (i : TerminalMap F T U) (j : ProductMap F P V) (base : O) (primitive : {a b : Ty} → Prim a b → D.Hom (F.obj (objects T P base a)) (F.obj (objects T P base b))) :
    ModelCongr H (image F T P U V base i j primitive) where
  pair hf hg := K.comp (H.refl _) (VC.pair hf hg)

theorem image_preserves (i : TerminalMap F T U) (j : ProductMap F P V)
    (TI : TerminalMapLaws H i) (PJ : ProductMapLaws H j) (base : O)
    (primitive : {a b : Ty} → Prim a b → C.Hom (objects T P base a) (objects T P base b))
    (primitive' : {a b : Ty} → Prim a b → D.Hom (F.obj (objects T P base a)) (F.obj (objects T P base b)))
    (hprim : ∀ {a b} (p : Prim a b), H.Rel (F.map (primitive p)) (primitive' p)) :
    Preserves F H (cartesian T P base primitive) (image F T P U V base i j primitive') where
  terminal := TI.terminal
  fst := PJ.fst
  snd := PJ.snd
  pair := PJ.pair
  primitive := hprim

/-- Naturality with explicit product and terminal comparison coherence.
Inverse equations are needed to call the comparisons isomorphisms, but the
preservation equation itself needs only the displayed operation coherence. -/
theorem cartesian_naturality (L : MapLaws F E H) (K : CategoryCongr D H)
    (VC : ProductCongr H V) (i : TerminalMap F T U) (j : ProductMap F P V)
    (TI : TerminalMapLaws H i) (PJ : ProductMapLaws H j) (base : O)
    (primitive : {a b : Ty} → Prim a b → C.Hom (objects T P base a) (objects T P base b))
    (primitive' : {a b : Ty} → Prim a b → D.Hom (F.obj (objects T P base a)) (F.obj (objects T P base b)))
    (hprim : ∀ {a b} (p : Prim a b), H.Rel (F.map (primitive p)) (primitive' p))
    (t : Term Prim Γ a) :
    H.Rel (F.map (compile (cartesian T P base primitive) t))
      (compile (image F T P U V base i j primitive') t) :=
  naturality L K (image_congr K VC i j base primitive')
    (image_preserves i j TI PJ base primitive primitive' hprim) t

/-- Composition needs no further syntax induction. -/
theorem preserves_comp {R : Type u₃} {B : CategoryOps.{u₃,v₃} R}
    {G : RawMap D B} {J : HomEquiv B}
    {W : Model B Prim (G.obj ∘ (F.obj ∘ A))}
    (LG : MapLaws G H J) (S : Preserves F H M N) (S' : Preserves G J N W) :
    Preserves (F.comp G) J M W where
  terminal := J.trans (LG.congr S.terminal) S'.terminal
  fst := J.trans (LG.congr S.fst) S'.fst
  snd := J.trans (LG.congr S.snd) S'.snd
  pair f g := J.trans (LG.congr (S.pair f g)) (S'.pair _ _)
  primitive p := J.trans (LG.congr (S.primitive p)) (S'.primitive p)

/-- Compatibility is structural, and leaves the original dependency-free API intact. -/
theorem compileVar_ofTarget (K : Target Prim) (v : Var Γ a) :
    compileVar (ofTarget K) v = FirstOrderCompiler.compileVar K v := by
  induction v with
  | here => rfl
  | there v ih => exact congrArg (fun f => K.comp f K.fst) ih

theorem compile_ofTarget (K : Target Prim) (t : Term Prim Γ a) :
    compile (ofTarget K) t = FirstOrderCompiler.compile K t := by
  induction t with
  | var v => exact compileVar_ofTarget K v
  | unit => rfl
  | pair t u it iu => exact congrArg₂ K.pair it iu
  | fst t it => exact congrArg (K.comp K.fst) it
  | snd t it => exact congrArg (K.comp K.snd) it
  | letE t u it iu => exact congrArg₂ K.comp iu (congrArg (K.pair K.ident) it)
  | prim p t it => exact congrArg (K.comp (K.primitive p)) it

def semantics (B : Type) (meaning : {a b : Ty} → Prim a b → Val B a → Val B b) :
    Model FunctionCategory.ops Prim (Val B) where
  terminal _ := ()
  fst := Prod.fst
  snd := Prod.snd
  pair f g x := (f x, g x)
  primitive := meaning

theorem semantics_variable (B : Type) (meaning : {a b : Ty} → Prim a b → Val B a → Val B b)
    (v : Var Γ a) (ρ : Val B (context Γ)) :
    compileVar (semantics B meaning) v ρ = lookup v ρ := by
  induction v with
  | here => rfl
  | there v ih => exact ih ρ.1

theorem semantics_compile (B : Type) (meaning : {a b : Ty} → Prim a b → Val B a → Val B b)
    (t : Term Prim Γ a) (ρ : Val B (context Γ)) :
    compile (semantics B meaning) t ρ = eval meaning t ρ := by
  induction t with
  | var v => exact semantics_variable B meaning v ρ
  | unit => rfl
  | pair t u it iu => exact Prod.ext (it ρ) (iu ρ)
  | fst t it => exact congrArg Prod.fst (it ρ)
  | snd t it => exact congrArg Prod.snd (it ρ)
  | letE t u it iu =>
    change compile (semantics B meaning) u (ρ, compile (semantics B meaning) t ρ) = _
    rw [it ρ, iu]
    rfl
  | prim p t it => exact congrArg (meaning p) (it ρ)

def soundMap (K : Target Prim) (S : Sound B K meaning) :
    RawMap (FirstOrderCategory.ops K) FunctionCategory.ops where
  obj := Val B
  map := S.denote

theorem soundMap_laws (K : Target Prim) (S : Sound B K meaning) :
    MapLaws (soundMap K S) ((soundMap K S).induced (equality _)) (equality _) where
  congr h := h
  ident := funext S.ident
  comp g f := funext (S.comp g f)

theorem sound_preserves (K : Target Prim) (S : Sound B K meaning) :
    Preserves (soundMap K S) (equality _) (ofTarget K) (semantics B meaning) where
  terminal := funext S.terminal
  fst := funext S.fst
  snd := funext S.snd
  pair f g := funext (S.pair f g)
  primitive p := funext (S.primitive p)

/-- The old Sound contract supplies precisely a shared map plus local preservation. -/
theorem compile_sound (K : Target Prim) (S : Sound B K meaning)
    (t : Term Prim Γ a) (ρ : Val B (context Γ)) :
    S.denote (FirstOrderCompiler.compile K t) ρ = eval meaning t ρ := by
  have h := naturality (soundMap_laws K S) (equalityCongr _)
    (show ModelCongr (equality _) (semantics B meaning) from
      ⟨by intros; subst_vars; rfl⟩) (sound_preserves K S) t
  have hp := congrFun h ρ
  change S.denote (compile (ofTarget K) t) ρ = compile (semantics B meaning) t ρ at hp
  rw [compile_ofTarget, semantics_compile] at hp
  exact hp

/-- Legacy targets also admit non-strict images into arbitrary object models. -/
def targetImage (K : Target Prim) (F : RawMap (FirstOrderCategory.ops K) D)
    (U : TerminalOps D) (V : ProductOps D)
    (i : TerminalMap F (FirstOrderCategory.terminal K) U)
    (j : ProductMap F (FirstOrderCategory.products K) V)
    (primitive : {a b : Ty} → Prim a b → D.Hom (F.obj a) (F.obj b)) :
    Model D Prim F.obj where
  terminal := D.comp i.inv U.terminal
  fst := D.comp V.fst (j _ _).hom
  snd := D.comp V.snd (j _ _).hom
  pair f g := D.comp (j _ _).inv (V.pair f g)
  primitive := primitive

theorem targetImage_congr (K : Target Prim) (F : RawMap (FirstOrderCategory.ops K) D)
    (U : TerminalOps D) (V : ProductOps D)
    (i : TerminalMap F (FirstOrderCategory.terminal K) U)
    (j : ProductMap F (FirstOrderCategory.products K) V)
    (primitive : {a b : Ty} → Prim a b → D.Hom (F.obj a) (F.obj b))
    (DC : CategoryCongr D H) (VC : ProductCongr H V) :
    ModelCongr H (targetImage K F U V i j primitive) where
  pair hf hg := DC.comp (H.refl _) (VC.pair hf hg)

theorem targetImage_preserves (K : Target Prim) (F : RawMap (FirstOrderCategory.ops K) D)
    (U : TerminalOps D) (V : ProductOps D)
    (i : TerminalMap F (FirstOrderCategory.terminal K) U)
    (j : ProductMap F (FirstOrderCategory.products K) V)
    (TI : TerminalMapLaws H i) (PJ : ProductMapLaws H j)
    (primitive : {a b : Ty} → Prim a b → D.Hom (F.obj a) (F.obj b))
    (hprim : ∀ {a b} (p : Prim a b), H.Rel (F.map (K.primitive p)) (primitive p)) :
    Preserves F H (ofTarget K) (targetImage K F U V i j primitive) where
  terminal := TI.terminal
  fst := PJ.fst
  snd := PJ.snd
  pair := PJ.pair
  primitive := hprim

/-- Recover the value-level soundness contract from a map and its product
preservation. Comparisons need only act as identity on values; their packages
need not be definitionally identities. Terminal compatibility follows from
uniqueness of the value of `Unit`. Primitive meanings remain a local obligation. -/
def soundOfProducts (K : Target Prim) (B : Type)
    {E : HomEquiv (FirstOrderCategory.ops K)}
    {meaning : {a b : Ty} → Prim a b → Val B a → Val B b}
    (denote : {a b : Ty} → K.Hom a b → Val B a → Val B b)
    (L : MapLaws (⟨Val B, denote⟩ : RawMap (FirstOrderCategory.ops K) FunctionCategory.ops)
      E (equality _))
    (j : ProductMap (⟨Val B, denote⟩ : RawMap (FirstOrderCategory.ops K) FunctionCategory.ops)
      (FirstOrderCategory.products K) FunctionCategory.products)
    (PJ : ProductMapLaws (equality _) j)
    (hom : ∀ a b (x : Val B (.prod a b)), (j a b).hom x = x)
    (inv : ∀ a b (x : Val B a × Val B b), (j a b).inv x = x)
    (primitive : ∀ {a b} (p : Prim a b) x, denote (K.primitive p) x = meaning p x) :
    Sound B K meaning where
  denote := denote
  ident x := congrFun L.ident x
  comp g f x := congrFun (L.comp g f) x
  terminal x := Subsingleton.elim _ _
  fst {a b} x := by
    have h := congrFun (PJ.fst (a := a) (b := b)) x
    change denote K.fst x = ((j a b).hom x).1 at h
    rw [hom] at h
    exact h
  snd {a b} x := by
    have h := congrFun (PJ.snd (a := a) (b := b)) x
    change denote K.snd x = ((j a b).hom x).2 at h
    rw [hom] at h
    exact h
  pair f g x := (congrFun (PJ.pair f g) x).trans (inv _ _ _)
  primitive := primitive

end SquareKit.FirstOrderNaturality
