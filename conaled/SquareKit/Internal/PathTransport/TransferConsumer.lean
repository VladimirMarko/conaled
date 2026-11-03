import SquareKit.Internal.PathTransport.Transfer
import SquareKit.Internal.PathTransport.TransferSoundness
noncomputable section
namespace SquareKit.Internal.PathTransport.GroupoidModel.TransferConsumer
open CategoryTheory Typed Typed.Authoring
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
universe u
variable (C : Type u) [Groupoid.{u} C] (B : C ⥤ Type u)
local notation "M" => Instance.fullModel C B
variable {Γ : RawCtx} {γ : CtxCode.{u+1}}

theorem action_relabel {G : Type u} [Category.{u} G]
    {x₀ y₀ z₀ x y z : Section (constant (Γ := G) C)}
    (hx : x₀ = x) (hy : y₀ = y) (hz : z₀ = z)
    (p₀ : ULift.{u+1} (Section (identityFamily (constant C) x₀ y₀)))
    (q₀ : ULift.{u+1} (Section (identityFamily (constant C) y₀ z₀)))
    (b₀ : ULift.{u+1} (Section (primitiveFiber B x₀)))
    (p : ULift.{u+1} (Section (identityFamily (constant C) x y)))
    (q : ULift.{u+1} (Section (identityFamily (constant C) y z)))
    (b : ULift.{u+1} (Section (primitiveFiber B x)))
    (hp : HEq p₀ p) (hq : HEq q₀ q) (hb : HEq b₀ b) (g : G)
    (e : B.map ((p₀.down.obj g).as ≫ (q₀.down.obj g).as) (b₀.down.obj g).as =
      B.map (q₀.down.obj g).as (B.map (p₀.down.obj g).as (b₀.down.obj g).as)) :
    B.map ((p.down.obj g).as ≫ (q.down.obj g).as) (b.down.obj g).as =
      B.map (q.down.obj g).as (B.map (p.down.obj g).as (b.down.obj g).as) := by
  cases hx; cases hy; cases hz
  cases eq_of_heq hp; cases eq_of_heq hq; cases eq_of_heq hb
  exact e

variable (hΓ : CtxDeriv Γ γ) (x y z : BasePoint Γ γ)
  (p : Path x y) (q : Path y z) (b : FiberElement x)

def resultCode := subTyCode
  (identityCode (fiberCode (TransferFrame.last hΓ x).code)
    (TransferFrame.left hΓ x).code (TransferFrame.right hΓ x).code)
  (substitutionCode (TransferApplication.endpoint hΓ x y z p q b))

/-- The target equation is extracted from the generated proof's interpretation. -/
theorem consume {t : Expr} {ξ : TmCode γ (resultCode hΓ x y z p q b)}
    (proof : TmDeriv Γ γ
      (.identity (.fiber z.raw) (transport hΓ (concat hΓ p q) b).raw
        (transport hΓ q (transport hΓ p b)).raw)
      (resultCode hΓ x y z p q b) t ξ)
    (g : ↥(show Grpd.{u,u} from γ M)) :
    B.map (((p.code M).down.obj g).as ≫ ((q.code M).down.obj g).as) ((b.code M).down.obj g).as =
      B.map ((q.code M).down.obj g).as (B.map ((p.code M).down.obj g).as ((b.code M).down.obj g).as) := by
  let s := substitutionCode (TransferApplication.endpoint hΓ x y z p q b)
  let v := (s M).down.obj g
  have e : (((TransferFrame.left hΓ x).code M).down.obj v).as =
      (((TransferFrame.right hΓ x).code M).down.obj v).as :=
    Discrete.eq_of_hom (((interpretTm M proof).down.obj g).as)
  change (((transport (TransferFrame.context hΓ x) _ _).code M).down.obj v).as =
    (((transport (TransferFrame.context hΓ x) _ _).code M).down.obj v).as at e
  rw [SourceSemantics.transport_obj, SourceSemantics.transport_obj,
    SourceSemantics.transport_obj, ConcatSemantics.concat_obj] at e
  have hx : ((TransferFrame.fixed hΓ x).code M).down.reindex (s M).down = (x.code M).down := by
    have h := congrArg (fun a => a M) (TransferApplication.fixed_at hΓ x y z p q b)
    rw [ConcatSemantics.baseReindex_eval] at h
    exact congrArg ULift.down h
  have hy : ((TransferFrame.moving hΓ x).code M).down.reindex (s M).down = (y.code M).down := by
    have h := congrArg (fun a => a M) (TransferApplication.moving_at hΓ x y z p q b)
    rw [ConcatSemantics.baseReindex_eval] at h
    exact congrArg ULift.down h
  have hz : ((TransferFrame.last hΓ x).code M).down.reindex (s M).down = (z.code M).down := by
    have h := congrArg (fun a => a M) (TransferApplication.last_at hΓ x y z p q b)
    rw [ConcatSemantics.baseReindex_eval] at h
    exact congrArg ULift.down h
  exact action_relabel C B hx hy hz
    ((M).subTm ((TransferFrame.first hΓ x).code M) (s M))
    ((M).subTm ((TransferFrame.second hΓ x).code M) (s M))
    ((M).subTm ((TransferFrame.element hΓ x).code M) (s M))
    (p.code M) (q.code M) (b.code M)
    (TransferApplication.first_at hΓ x y z p q b M)
    (TransferApplication.second_at hΓ x y z p q b M)
    (TransferApplication.element_at hΓ x y z p q b M) g e

include hΓ in
/-- The ordinary equation obtained from the transferred source proof. -/
theorem interpreted_trConcat (g : ↥(show Grpd.{u,u} from γ M)) :
    B.map (((p.code M).down.obj g).as ≫ ((q.code M).down.obj g).as) ((b.code M).down.obj g).as =
      B.map ((q.code M).down.obj g).as (B.map ((p.code M).down.obj g).as ((b.code M).down.obj g).as) :=
  consume C B hΓ x y z p q b (trConcat hΓ p q b) g

end SquareKit.Internal.PathTransport.GroupoidModel.TransferConsumer
