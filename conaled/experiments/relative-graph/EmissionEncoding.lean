import ArtifactAudit
import SquareKit.Internal.GraphEmissionContract
import ConLeche.Denotes

/-! Structural encoding of the actual pure producer's type and proof body.
Metavariables are rejected. Binder order and helper applications are preserved.
The inverse supplies a kernel-checked identification with native syntax. -/
namespace EmissionEncoding
open SquareKit.Internal
namespace N
 def encode : Lean.Name → ConLeche.Name
  | .anonymous => .anonymous
  | .str p s => .str (encode p) s
  | .num p n => .num (encode p) n
 def decode : ConLeche.Name → Lean.Name
  | .anonymous => .anonymous
  | .str p s => .str (decode p) s
  | .num p n => .num (decode p) n
 @[simp] theorem roundtrip (n : Lean.Name) : decode (encode n) = n := by
  induction n <;> simp_all [encode, decode]
end N
namespace U
 def encode : Lean.Level → Option ConLeche.Level
  | .zero => some .zero
  | .succ u => return .succ (← encode u)
  | .max u v => return .max (← encode u) (← encode v)
  | .imax u v => return .imax (← encode u) (← encode v)
  | .param n => some (.param (N.encode n))
  | .mvar _ => none
 def decode : ConLeche.Level → Lean.Level
  | .zero => .zero
  | .succ u => .succ (decode u)
  | .max u v => .max (decode u) (decode v)
  | .imax u v => .imax (decode u) (decode v)
  | .param n => .param (N.decode n)
 theorem roundtrip (u : Lean.Level) (v : ConLeche.Level) (h : encode u = some v) :
    decode v = u := by
  induction u generalizing v with
  | zero => cases h; rfl
  | param n => cases h; simp [decode]
  | mvar n => cases h
  | succ u ih =>
    simp only [encode, bind, pure, Option.bind_eq_some_iff, Option.some.injEq] at h
    obtain ⟨w, hw, rfl⟩ := h
    simp [decode, ih _ hw]
  | max u v ihu ihv | imax u v ihu ihv =>
    simp only [encode, bind, pure, Option.bind_eq_some_iff, Option.some.injEq] at h
    obtain ⟨a, ha, b, hb, rfl⟩ := h
    simp [decode, ihu _ ha, ihv _ hb]
end U

def levels : List Lean.Level → Option (List ConLeche.Level)
  | [] => some []
  | u :: us => return (← U.encode u) :: (← levels us)

theorem levels_roundtrip (us : List Lean.Level) (vs : List ConLeche.Level)
    (h : levels us = some vs) : vs.map U.decode = us := by
  induction us generalizing vs with
  | nil => cases h; rfl
  | cons u us ih =>
    simp only [levels, bind, pure, Option.bind_eq_some_iff, Option.some.injEq] at h
    obtain ⟨v, hv, vs, hvs, rfl⟩ := h
    simp [U.roundtrip _ _ hv, ih _ hvs]

def encode : CoreSyntax.Expr → Option ConLeche.Expr
  | .bvar i => some (.bvar i)
  | .sort u => return .sort (← U.encode u)
  | .const n us => return .const (N.encode n) (← levels us)
  | .app f a => return .app (← encode f) (← encode a)
  | .lam a b => return .lam (← encode a) (← encode b)
  | .all a b => return .forallE (← encode a) (← encode b)

/-- Decode only the binder fragment admitted by the producer. -/
def decode : ConLeche.Expr → Option CoreSyntax.Expr
  | .bvar i => some (.bvar i)
  | .sort u => some (.sort (U.decode u))
  | .const n us => some (.const (N.decode n) (us.map U.decode))
  | .app f a => return .app (← decode f) (← decode a)
  | .lam a b => return .lam (← decode a) (← decode b)
  | .forallE a b => return .all (← decode a) (← decode b)
  | _ => none

theorem roundtrip (e : CoreSyntax.Expr) (r : ConLeche.Expr) (h : encode e = some r) :
    decode r = some e := by
  induction e generalizing r with
  | bvar i => cases h; rfl
  | sort u =>
    simp only [encode, bind, pure, Option.bind_eq_some_iff, Option.some.injEq] at h
    obtain ⟨v, hv, rfl⟩ := h
    simp [decode, U.roundtrip _ _ hv]
  | const n us =>
    simp only [encode, bind, pure, Option.bind_eq_some_iff, Option.some.injEq] at h
    obtain ⟨vs, hv, rfl⟩ := h
    simp [decode, levels_roundtrip _ _ hv]
  | app f a ihf iha | lam f a ihf iha | all f a ihf iha =>
    simp only [encode, bind, pure, Option.bind_eq_some_iff, Option.some.injEq] at h
    obtain ⟨f', hf, a', ha, rfl⟩ := h
    simp [decode, ihf _ hf, iha _ ha]

theorem rename_encodable (e : CoreSyntax.Expr) (r : Nat → Nat)
    (h : ∃ e', encode e = some e') : ∃ e', encode (e.rename r) = some e' := by
  obtain ⟨e', he⟩ := h
  induction e generalizing e' r with
  | bvar i => exact ⟨_, rfl⟩
  | sort u => exact ⟨e', he⟩
  | const n us => exact ⟨e', he⟩
  | app a b iha ihb =>
    simp only [encode, bind, pure, Option.bind_eq_some_iff, Option.some.injEq] at he
    obtain ⟨a', ha, b', hb, rfl⟩ := he
    obtain ⟨ar, har⟩ := iha r _ ha
    obtain ⟨br, hbr⟩ := ihb r _ hb
    exact ⟨.app ar br, by simp [CoreSyntax.Expr.rename, encode, har, hbr]⟩
  | lam a b iha ihb =>
    simp only [encode, bind, pure, Option.bind_eq_some_iff, Option.some.injEq] at he
    obtain ⟨a', ha, b', hb, rfl⟩ := he
    obtain ⟨ar, har⟩ := iha r _ ha
    obtain ⟨br, hbr⟩ := ihb (CoreSyntax.liftRen r) _ hb
    exact ⟨.lam ar br, by simp [CoreSyntax.Expr.rename, encode, har, hbr]⟩
  | all a b iha ihb =>
    simp only [encode, bind, pure, Option.bind_eq_some_iff, Option.some.injEq] at he
    obtain ⟨a', ha, b', hb, rfl⟩ := he
    obtain ⟨ar, har⟩ := iha r _ ha
    obtain ⟨br, hbr⟩ := ihb (CoreSyntax.liftRen r) _ hb
    exact ⟨.forallE ar br, by simp [CoreSyntax.Expr.rename, encode, har, hbr]⟩

/-- Successful encoding identifies both actual native expressions, including
all de Bruijn indices. It does not identify the older handwritten graph family. -/
theorem emitted_identity (d : GraphTarget.Declaration) (ty body : ConLeche.Expr)
    (ht : encode (GraphEmissionPure.emitCore d).1 = some ty)
    (hb : encode (GraphEmissionPure.emitCore d).2 = some body) :
    (decode ty).map CoreSyntax.Expr.toLean = some (GraphEmissionPure.emit d).1 ∧
    (decode body).map CoreSyntax.Expr.toLean = some (GraphEmissionPure.emit d).2 := by
  rw [roundtrip _ _ ht, roundtrip _ _ hb]
  exact ⟨rfl, rfl⟩

end EmissionEncoding
#audit_graph_module
