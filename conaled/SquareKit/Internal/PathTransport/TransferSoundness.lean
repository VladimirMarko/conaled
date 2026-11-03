import SquareKit.Internal.PathTransport.ConcatSemantics
import SquareKit.Internal.PathTransport.TransferBranch

noncomputable section
namespace SquareKit.Internal.PathTransport.GroupoidModel.TransferSoundness
open CategoryTheory Typed Typed.Authoring
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
universe u
variable (C : Type u) [Groupoid.{u} C] (B : C ⥤ Type u)
local notation "M" => Instance.fullModel C B
variable {Γ : RawCtx} {γ : CtxCode.{u+1}}

/-- An interpreted source identity element retains the underlying base arrow. -/
def basePathEquiv (x y : BasePoint Γ γ) (g : ↥(show Grpd.{u,u} from γ M)) :
    ↥((identityCode (baseCode γ) x.code y.code M).obj g) ≃
      ((x.code M).down.obj g ⟶ (y.code M).down.obj g) where
  toFun := Discrete.as
  invFun := Discrete.mk
  left_inv := by intro p; cases p; rfl
  right_inv := by intro p; rfl

theorem basePathEquiv_refl (hΓ : CtxDeriv Γ γ) (x : BasePoint Γ γ)
    (g : ↥(show Grpd.{u,u} from γ M)) :
    basePathEquiv C B x x g (((Path.reflexivity hΓ x).code M).down.obj g) = 𝟙 _ := rfl

theorem basePathEquiv_concat (hΓ : CtxDeriv Γ γ) {x y z : BasePoint Γ γ}
    (p : Path x y) (q : Path y z) (g : ↥(show Grpd.{u,u} from γ M)) :
    basePathEquiv C B x z g (((concat hΓ p q).code M).down.obj g) =
      basePathEquiv C B x y g ((p.code M).down.obj g) ≫
      basePathEquiv C B y z g ((q.code M).down.obj g) :=
  ConcatSemantics.concat_obj C B hΓ x p q g

/-- Consume any generated source identity derivation through the all-rule
interpreter; no target equation is supplied as a premise. -/
theorem fiberIdentity {z : BasePoint Γ γ} (l r : FiberElement z)
    {t : Expr} {ξ : TmCode γ (identityCode (fiberCode z.code) l.code r.code)}
    (proof : TmDeriv Γ γ (.identity (.fiber z.raw) l.raw r.raw)
      (identityCode (fiberCode z.code) l.code r.code) t ξ)
    (g : ↥(show Grpd.{u,u} from γ M)) :
    ((l.code M).down.obj g).as = ((r.code M).down.obj g).as :=
  Discrete.eq_of_hom (((interpretTm M proof).down.obj g).as)

end SquareKit.Internal.PathTransport.GroupoidModel.TransferSoundness
