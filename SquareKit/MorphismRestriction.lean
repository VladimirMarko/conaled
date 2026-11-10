import SquareKit.CartesianMap

namespace SquareKit.MorphismRestriction
universe u v w
variable {O : Type u} (C : CategoryOps.{u,v} O)

/-- Admissibility retains a selected witness even when semantics ignores it. -/
structure Hom (M : {a b : O} → C.Hom a b → Type w) (a b : O) where
  arrow : C.Hom a b
  sat : M arrow

structure CategoryClosure (M : {a b : O} → C.Hom a b → Type w) where
  ident : ∀ {a}, M (C.ident (a := a))
  comp : ∀ {a b c} {g : C.Hom b c} {f : C.Hom a b}, M g → M f → M (C.comp g f)

variable {C} {M : {a b : O} → C.Hom a b → Type w}

def ops (K : CategoryClosure C M) : CategoryOps O where
  Hom := Hom C M
  ident := ⟨C.ident, K.ident⟩
  comp g f := ⟨C.comp g.arrow f.arrow, K.comp g.sat f.sat⟩

def forget (K : CategoryClosure C M) : RawMap (ops K) C :=
  ⟨id, fun f => f.arrow⟩

def equiv (K : CategoryClosure C M) (E : HomEquiv C) : HomEquiv (ops K) :=
  (forget K).induced E

theorem forget_laws (K : CategoryClosure C M) (E : HomEquiv C) :
    MapLaws (forget K) (equiv K E) E :=
  RawMap.inducedLaws (forget K) E (E.refl _) (fun _ _ => E.refl _)

theorem congr (K : CategoryClosure C M) {E : HomEquiv C} (CC : CategoryCongr C E) :
    CategoryCongr (ops K) (equiv K E) :=
  RawMap.transportCongr (forget_laws K E) ((forget K).induced_reflects E) CC

theorem laws (K : CategoryClosure C M) {E : HomEquiv C}
    (CC : CategoryCongr C E) (CL : CategoryLaws C E) : CategoryLaws (ops K) (equiv K E) :=
  RawMap.transportLaws (forget_laws K E) ((forget K).induced_reflects E) CC CL

structure TerminalClosure (T : TerminalOps C) where
  terminal : ∀ {a}, M (T.terminal (a := a))

structure ProductClosure (P : ProductOps C) where
  fst : ∀ {a b}, M (P.fst (a := a) (b := b))
  snd : ∀ {a b}, M (P.snd (a := a) (b := b))
  pair : ∀ {a b c} {f : C.Hom a b} {g : C.Hom a c}, M f → M g → M (P.pair f g)

def terminal (K : CategoryClosure C M) (T : TerminalOps C) (KT : TerminalClosure (M := M) T) :
    TerminalOps (ops K) := ⟨T.unit, ⟨T.terminal, KT.terminal⟩⟩

def products (K : CategoryClosure C M) (P : ProductOps C) (KP : ProductClosure (M := M) P) :
    ProductOps (ops K) where
  prod := P.prod
  fst := ⟨P.fst, KP.fst⟩
  snd := ⟨P.snd, KP.snd⟩
  pair f g := ⟨P.pair f.arrow g.arrow, KP.pair f.sat g.sat⟩

theorem terminalLaws (K : CategoryClosure C M) (T : TerminalOps C)
    (KT : TerminalClosure (M := M) T) {E : HomEquiv C} (L : TerminalLaws E T) :
    TerminalLaws (equiv K E) (terminal K T KT) := ⟨fun f => L.unique f.arrow⟩

theorem productCongr (K : CategoryClosure C M) (P : ProductOps C)
    (KP : ProductClosure (M := M) P) {E : HomEquiv C} (L : ProductCongr E P) :
    ProductCongr (equiv K E) (products K P KP) := ⟨fun h k => L.pair h k⟩

theorem productLaws (K : CategoryClosure C M) (P : ProductOps C)
    (KP : ProductClosure (M := M) P) {E : HomEquiv C} (L : ProductLaws E P) :
    ProductLaws (equiv K E) (products K P KP) :=
  ⟨fun f g => L.fst_pair f.arrow g.arrow,
    fun f g => L.snd_pair f.arrow g.arrow, fun f => L.pair_eta f.arrow⟩

def terminalComparison (K : CategoryClosure C M) (T : TerminalOps C)
    (KT : TerminalClosure (M := M) T) : TerminalMap (forget K) (terminal K T KT) T := Comparison.id C T.unit

def productComparison (K : CategoryClosure C M) (P : ProductOps C)
    (KP : ProductClosure (M := M) P) : ProductMap (forget K) (products K P KP) P :=
  fun a b => Comparison.id C (P.prod a b)

theorem forget_terminal (K : CategoryClosure C M) (T : TerminalOps C)
    (KT : TerminalClosure (M := M) T) {E : HomEquiv C} (L : CategoryLaws C E) :
    TerminalMapLaws E (terminalComparison K T KT) := ⟨E.symm (L.id_comp _)⟩

theorem forget_products (K : CategoryClosure C M) (P : ProductOps C)
    (KP : ProductClosure (M := M) P) {E : HomEquiv C} (L : CategoryLaws C E) :
    ProductMapLaws E (productComparison K P KP) :=
  ⟨E.symm (L.comp_id _),E.symm (L.comp_id _),fun _ _ => E.symm (L.id_comp _)⟩

theorem terminalComparison_inverse (K : CategoryClosure C M) (T : TerminalOps C)
    (KT : TerminalClosure (M := M) T) {E : HomEquiv C} (L : CategoryLaws C E) :
    ComparisonLaws E (terminalComparison K T KT) := Comparison.id_laws L _
theorem productComparison_inverse (K : CategoryClosure C M) (P : ProductOps C)
    (KP : ProductClosure (M := M) P) {E : HomEquiv C} (L : CategoryLaws C E) (a b : O) :
    ComparisonLaws E (productComparison K P KP a b) := Comparison.id_laws L _
end SquareKit.MorphismRestriction
