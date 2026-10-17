import SquareKit.OptionalMap
import SquareKit.STLCCategory
import SquareKit.FunctionCategory

/-! Full-source syntax is interpreted at the boundary of the object-polymorphic
interfaces. The interpretation retains arbitrary object models and proves preservation under local operation obligations. -/
namespace SquareKit.STLCNaturality
open CategoricalCompiler
universe u v w z u₃ v₃

structure Model {O : Type u} (C : CategoryOps.{u,v} O) (Prim : Ty → Ty → Type) (obj : Ty → O) where
  terminal : {a : Ty} → C.Hom (obj a) (obj .unit)
  fst : {a b : Ty} → C.Hom (obj (.prod a b)) (obj a)
  snd : {a b : Ty} → C.Hom (obj (.prod a b)) (obj b)
  pair : {a b c : Ty} → C.Hom (obj a) (obj b) → C.Hom (obj a) (obj c) → C.Hom (obj a) (obj (.prod b c))
  inl : {a b : Ty} → C.Hom (obj a) (obj (.sum a b))
  inr : {a b : Ty} → C.Hom (obj b) (obj (.sum a b))
  copair : {a b c : Ty} → C.Hom (obj a) (obj c) → C.Hom (obj b) (obj c) → C.Hom (obj (.sum a b)) (obj c)
  dist : {a b c : Ty} → C.Hom (obj (.prod a (.sum b c))) (obj (.sum (.prod a b) (.prod a c)))
  curry : {x a b : Ty} → C.Hom (obj (.prod x a)) (obj b) → C.Hom (obj x) (obj (.arr a b))
  apply : {a b : Ty} → C.Hom (obj (.prod (.arr a b) a)) (obj b)
  primitive : {a b : Ty} → Prim a b → C.Hom (obj a) (obj b)

variable {O : Type u} {C : CategoryOps.{u,v} O} {Prim : Ty → Ty → Type}

def ofTarget (K : Target Prim) : Model (STLCCategory.ops K) Prim id where
  terminal := K.terminal
  fst := K.fst
  snd := K.snd
  pair := K.pair
  inl := K.inl
  inr := K.inr
  copair := K.copair
  dist := K.dist
  curry := K.curry
  apply := K.apply
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
  | .lam t => M.curry (compile M t)
  | .app t u => C.comp M.apply (M.pair (compile M t) (compile M u))
  | .inl t => C.comp M.inl (compile M t)
  | .inr t => C.comp M.inr (compile M t)
  | .caseE s l r => C.comp (M.copair (compile M l) (compile M r))
      (C.comp M.dist (M.pair C.ident (compile M s)))
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
  inl : ∀ {a b}, H.Rel (F.map (M.inl (a := a) (b := b))) N.inl
  inr : ∀ {a b}, H.Rel (F.map (M.inr (a := a) (b := b))) N.inr
  copair : ∀ {a b c} (f : C.Hom (A a) (A c)) (g : C.Hom (A b) (A c)),
    H.Rel (F.map (M.copair f g)) (N.copair (F.map f) (F.map g))
  dist : ∀ {a b c}, H.Rel (F.map (M.dist (a := a) (b := b) (c := c))) N.dist
  curry : ∀ {x a b} (f : C.Hom (A (.prod x a)) (A b)), H.Rel (F.map (M.curry f)) (N.curry (F.map f))
  apply : ∀ {a b}, H.Rel (F.map (M.apply (a := a) (b := b))) N.apply
  primitive : ∀ {a b} (p : Prim a b), H.Rel (F.map (M.primitive p)) (N.primitive p)

structure ModelCongr (H : HomEquiv C) (M : Model C Prim A) : Prop where
  pair : ∀ {a b c} {f f' : C.Hom (A a) (A b)} {g g' : C.Hom (A a) (A c)},
    H.Rel f f' → H.Rel g g' → H.Rel (M.pair f g) (M.pair f' g')
  copair : ∀ {a b c} {f f' : C.Hom (A a) (A c)} {g g' : C.Hom (A b) (A c)},
    H.Rel f f' → H.Rel g g' → H.Rel (M.copair f g) (M.copair f' g')
  curry : ∀ {x a b} {f g : C.Hom (A (.prod x a)) (A b)}, H.Rel f g → H.Rel (M.curry f) (M.curry g)

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
  | lam t it => exact H.trans (S.curry _) (P.curry it)
  | app t u it iu => exact H.trans (L.comp _ _) (K.comp S.apply (H.trans (S.pair _ _) (P.pair it iu)))
  | inl t it => exact H.trans (L.comp _ _) (K.comp S.inl it)
  | inr t it => exact H.trans (L.comp _ _) (K.comp S.inr it)
  | caseE s l r is il ir =>
    exact H.trans (L.comp _ _) (K.comp (H.trans (S.copair _ _) (P.copair il ir))
      (H.trans (L.comp _ _) (K.comp S.dist (H.trans (S.pair _ _) (P.pair L.ident is)))))
  | prim p t it => exact H.trans (L.comp _ _) (K.comp (S.primitive p) it)

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
  inl := J.trans (LG.congr S.inl) S'.inl
  inr := J.trans (LG.congr S.inr) S'.inr
  copair f g := J.trans (LG.congr (S.copair f g)) (S'.copair _ _)
  dist := J.trans (LG.congr S.dist) S'.dist
  curry f := J.trans (LG.congr (S.curry f)) (S'.curry _)
  apply := J.trans (LG.congr S.apply) S'.apply
  primitive p := J.trans (LG.congr (S.primitive p)) (S'.primitive p)

/-- A composed interpretation reuses the two local preservation packages. -/
theorem naturality_comp {R : Type u₃} {B : CategoryOps.{u₃,v₃} R}
    {G : RawMap D B} {J : HomEquiv B}
    {W : Model B Prim (G.obj ∘ (F.obj ∘ A))}
    (LF : MapLaws F E H) (LG : MapLaws G H J)
    (K : CategoryCongr B J) (P : ModelCongr J W)
    (S : Preserves F H M N) (S' : Preserves G J N W) (t : Term Prim Γ a) :
    J.Rel (G.map (F.map (compile M t))) (compile W t) :=
  naturality (RawMap.comp_laws LF LG) K P (preserves_comp LG S S') t

/-- Compatibility is structural, and leaves the original dependency-free API intact. -/
theorem compileVar_ofTarget (K : Target Prim) (v : Var Γ a) :
    compileVar (ofTarget K) v = CategoricalCompiler.compileVar K v := by
  induction v with
  | here => rfl
  | there v ih => exact congrArg (fun f => K.comp f K.fst) ih

theorem compile_ofTarget (K : Target Prim) (t : Term Prim Γ a) :
    compile (ofTarget K) t = CategoricalCompiler.compile K t := by
  induction t with
  | var v => exact compileVar_ofTarget K v
  | unit => rfl
  | pair t u it iu => exact congrArg₂ K.pair it iu
  | fst t it => exact congrArg (K.comp K.fst) it
  | snd t it => exact congrArg (K.comp K.snd) it
  | letE t u it iu => exact congrArg₂ K.comp iu (congrArg (K.pair K.ident) it)
  | lam t it => exact congrArg K.curry it
  | app t u it iu => exact congrArg (K.comp K.apply) (congrArg₂ K.pair it iu)
  | inl t it => exact congrArg (K.comp K.inl) it
  | inr t it => exact congrArg (K.comp K.inr) it
  | caseE s l r is il ir =>
    exact congrArg₂ K.comp (congrArg₂ K.copair il ir)
      (congrArg (K.comp K.dist) (congrArg (K.pair K.ident) is))
  | prim p t it => exact congrArg (K.comp (K.primitive p)) it

def semantics (B : Type) (meaning : {a b : Ty} → Prim a b → Val B a → Val B b) :
    Model FunctionCategory.ops Prim (Val B) where
  terminal _ := ()
  fst := Prod.fst
  snd := Prod.snd
  pair f g x := (f x, g x)
  inl := Sum.inl
  inr := Sum.inr
  copair := Sum.elim
  dist := distribute
  curry f x a := f (x, a)
  apply p := p.1 p.2
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
  | lam t it => exact funext (fun x => it (ρ, x))
  | app t u it iu => exact congrArg₂ (fun f x => f x) (it ρ) (iu ρ)
  | inl t it => exact congrArg Sum.inl (it ρ)
  | inr t it => exact congrArg Sum.inr (it ρ)
  | caseE s l r is il ir =>
    change Sum.elim (compile (semantics B meaning) l) (compile (semantics B meaning) r)
      (distribute (ρ, compile (semantics B meaning) s ρ)) = _
    rw [is ρ]
    cases h : eval meaning s ρ with
    | inl x => simpa [eval, h, distribute, Sum.elim] using il (ρ, x)
    | inr x => simpa [eval, h, distribute, Sum.elim] using ir (ρ, x)
  | prim p t it => exact congrArg (meaning p) (it ρ)

def soundMap (K : Target Prim) (S : Sound B K meaning) :
    RawMap (STLCCategory.ops K) FunctionCategory.ops where
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
  inl := funext S.inl
  inr := funext S.inr
  copair f g := funext (S.copair f g)
  dist := funext S.dist
  curry f := funext (fun x => funext (S.curry f x))
  apply := funext S.apply
  primitive p := funext (S.primitive p)

/-- The old Sound contract supplies precisely a shared map plus local preservation. -/
theorem compile_sound (K : Target Prim) (S : Sound B K meaning)
    (t : Term Prim Γ a) (ρ : Val B (context Γ)) :
    S.denote (CategoricalCompiler.compile K t) ρ = eval meaning t ρ := by
  have h := naturality (soundMap_laws K S) (equalityCongr _)
    (show ModelCongr (equality _) (semantics B meaning) from
      ⟨by intros; subst_vars; rfl, by intros; subst_vars; rfl, by intros; subst_vars; rfl⟩) (sound_preserves K S) t
  have hp := congrFun h ρ
  change S.denote (compile (ofTarget K) t) ρ = compile (semantics B meaning) t ρ at hp
  rw [compile_ofTarget, semantics_compile] at hp
  exact hp

end SquareKit.STLCNaturality
