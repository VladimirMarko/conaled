import Lean

/-! Exact pinned native declarations required by graph emission. Generated from
Lean 4.35.0; structural comparison is supplemental installation validation. -/
namespace SquareKit.Internal.GraphPrimitiveEnvironment
open Lean

def declarations : List ConstantInfo := [
Lean.ConstantInfo.inductInfo
  { toConstantVal := { name := `Eq,
                       levelParams := [`u_1],
                       type := Lean.Expr.forallE
                                 `α
                                 (Lean.Expr.sort (Lean.Level.param `u_1))
                                 (Lean.Expr.forallE
                                   (Lean.Name.mkNum `a.«_@»._internal._hyg 0)
                                   (Lean.Expr.bvar 0)
                                   (Lean.Expr.forallE
                                     (Lean.Name.mkNum `a.«_@»._internal._hyg 0)
                                     (Lean.Expr.bvar 1)
                                     (Lean.Expr.sort (Lean.Level.zero))
                                     (Lean.BinderInfo.default))
                                   (Lean.BinderInfo.default))
                                 (Lean.BinderInfo.implicit) },
    numParams := 2,
    numIndices := 1,
    all := [`Eq],
    ctors := [`Eq.refl],
    numNested := 0,
    isRec := false,
    isUnsafe := false,
    isReflexive := false },
Lean.ConstantInfo.ctorInfo
  { toConstantVal := { name := `Eq.refl,
                       levelParams := [`u_1],
                       type := Lean.Expr.forallE
                                 `α
                                 (Lean.Expr.sort (Lean.Level.param `u_1))
                                 (Lean.Expr.forallE
                                   `a
                                   (Lean.Expr.bvar 0)
                                   (Lean.Expr.app
                                     (Lean.Expr.app
                                       (Lean.Expr.app (Lean.Expr.const `Eq [Lean.Level.param `u_1]) (Lean.Expr.bvar 1))
                                       (Lean.Expr.bvar 0))
                                     (Lean.Expr.bvar 0))
                                   (Lean.BinderInfo.default))
                                 (Lean.BinderInfo.implicit) },
    induct := `Eq,
    cidx := 0,
    numParams := 2,
    numFields := 0,
    isUnsafe := false },
Lean.ConstantInfo.recInfo
  { toConstantVal := { name := `Eq.rec,
                       levelParams := [`u, `u_1],
                       type := Lean.Expr.forallE
                                 `α
                                 (Lean.Expr.sort (Lean.Level.param `u_1))
                                 (Lean.Expr.forallE
                                   (Lean.Name.mkNum `a.«_@»._internal._hyg 0)
                                   (Lean.Expr.bvar 0)
                                   (Lean.Expr.forallE
                                     `motive
                                     (Lean.Expr.forallE
                                       (Lean.Name.mkNum `a.«_@»._internal._hyg 0)
                                       (Lean.Expr.bvar 1)
                                       (Lean.Expr.forallE
                                         `t
                                         (Lean.Expr.app
                                           (Lean.Expr.app
                                             (Lean.Expr.app
                                               (Lean.Expr.const `Eq [Lean.Level.param `u_1])
                                               (Lean.Expr.bvar 2))
                                             (Lean.Expr.bvar 1))
                                           (Lean.Expr.bvar 0))
                                         (Lean.Expr.sort (Lean.Level.param `u))
                                         (Lean.BinderInfo.default))
                                       (Lean.BinderInfo.default))
                                     (Lean.Expr.forallE
                                       `refl
                                       (Lean.Expr.app
                                         (Lean.Expr.app (Lean.Expr.bvar 0) (Lean.Expr.bvar 1))
                                         (Lean.Expr.app
                                           (Lean.Expr.app
                                             (Lean.Expr.const `Eq.refl [Lean.Level.param `u_1])
                                             (Lean.Expr.bvar 2))
                                           (Lean.Expr.bvar 1)))
                                       (Lean.Expr.forallE
                                         (Lean.Name.mkNum `a.«_@»._internal._hyg 0)
                                         (Lean.Expr.bvar 3)
                                         (Lean.Expr.forallE
                                           `t
                                           (Lean.Expr.app
                                             (Lean.Expr.app
                                               (Lean.Expr.app
                                                 (Lean.Expr.const `Eq [Lean.Level.param `u_1])
                                                 (Lean.Expr.bvar 4))
                                               (Lean.Expr.bvar 3))
                                             (Lean.Expr.bvar 0))
                                           (Lean.Expr.app
                                             (Lean.Expr.app (Lean.Expr.bvar 3) (Lean.Expr.bvar 1))
                                             (Lean.Expr.bvar 0))
                                           (Lean.BinderInfo.default))
                                         (Lean.BinderInfo.implicit))
                                       (Lean.BinderInfo.default))
                                     (Lean.BinderInfo.implicit))
                                   (Lean.BinderInfo.implicit))
                                 (Lean.BinderInfo.implicit) },
    all := [`Eq],
    numParams := 2,
    numIndices := 1,
    numMotives := 1,
    numMinors := 1,
    rules := [{ ctor := `Eq.refl,
                nfields := 0,
                rhs := Lean.Expr.lam
                         `α
                         (Lean.Expr.sort (Lean.Level.param `u_1))
                         (Lean.Expr.lam
                           (Lean.Name.mkNum `a.«_@»._internal._hyg 0)
                           (Lean.Expr.bvar 0)
                           (Lean.Expr.lam
                             `motive
                             (Lean.Expr.forallE
                               (Lean.Name.mkNum `a.«_@»._internal._hyg 0)
                               (Lean.Expr.bvar 1)
                               (Lean.Expr.forallE
                                 `t
                                 (Lean.Expr.app
                                   (Lean.Expr.app
                                     (Lean.Expr.app (Lean.Expr.const `Eq [Lean.Level.param `u_1]) (Lean.Expr.bvar 2))
                                     (Lean.Expr.bvar 1))
                                   (Lean.Expr.bvar 0))
                                 (Lean.Expr.sort (Lean.Level.param `u))
                                 (Lean.BinderInfo.default))
                               (Lean.BinderInfo.default))
                             (Lean.Expr.lam
                               `refl
                               (Lean.Expr.app
                                 (Lean.Expr.app (Lean.Expr.bvar 0) (Lean.Expr.bvar 1))
                                 (Lean.Expr.app
                                   (Lean.Expr.app (Lean.Expr.const `Eq.refl [Lean.Level.param `u_1]) (Lean.Expr.bvar 2))
                                   (Lean.Expr.bvar 1)))
                               (Lean.Expr.bvar 0)
                               (Lean.BinderInfo.default))
                             (Lean.BinderInfo.default))
                           (Lean.BinderInfo.default))
                         (Lean.BinderInfo.implicit) }],
    k := true,
    isUnsafe := false },
Lean.ConstantInfo.inductInfo
  { toConstantVal := { name := `And,
                       levelParams := [],
                       type := Lean.Expr.forallE
                                 `a
                                 (Lean.Expr.sort (Lean.Level.zero))
                                 (Lean.Expr.forallE
                                   `b
                                   (Lean.Expr.sort (Lean.Level.zero))
                                   (Lean.Expr.sort (Lean.Level.zero))
                                   (Lean.BinderInfo.default))
                                 (Lean.BinderInfo.default) },
    numParams := 2,
    numIndices := 0,
    all := [`And],
    ctors := [`And.intro],
    numNested := 0,
    isRec := false,
    isUnsafe := false,
    isReflexive := false },
Lean.ConstantInfo.ctorInfo
  { toConstantVal := { name := `And.intro,
                       levelParams := [],
                       type := Lean.Expr.forallE
                                 `a
                                 (Lean.Expr.sort (Lean.Level.zero))
                                 (Lean.Expr.forallE
                                   `b
                                   (Lean.Expr.sort (Lean.Level.zero))
                                   (Lean.Expr.forallE
                                     `left
                                     (Lean.Expr.bvar 1)
                                     (Lean.Expr.forallE
                                       `right
                                       (Lean.Expr.bvar 1)
                                       (Lean.Expr.app
                                         (Lean.Expr.app (Lean.Expr.const `And []) (Lean.Expr.bvar 3))
                                         (Lean.Expr.bvar 2))
                                       (Lean.BinderInfo.default))
                                     (Lean.BinderInfo.default))
                                   (Lean.BinderInfo.implicit))
                                 (Lean.BinderInfo.implicit) },
    induct := `And,
    cidx := 0,
    numParams := 2,
    numFields := 2,
    isUnsafe := false },
Lean.ConstantInfo.inductInfo
  { toConstantVal := { name := `Exists,
                       levelParams := [`u],
                       type := Lean.Expr.forallE
                                 `α
                                 (Lean.Expr.sort (Lean.Level.param `u))
                                 (Lean.Expr.forallE
                                   `p
                                   (Lean.Expr.forallE
                                     (Lean.Name.mkNum `a.«_@»._internal._hyg 0)
                                     (Lean.Expr.bvar 0)
                                     (Lean.Expr.sort (Lean.Level.zero))
                                     (Lean.BinderInfo.default))
                                   (Lean.Expr.sort (Lean.Level.zero))
                                   (Lean.BinderInfo.default))
                                 (Lean.BinderInfo.implicit) },
    numParams := 2,
    numIndices := 0,
    all := [`Exists],
    ctors := [`Exists.intro],
    numNested := 0,
    isRec := false,
    isUnsafe := false,
    isReflexive := false },
Lean.ConstantInfo.ctorInfo
  { toConstantVal := { name := `Exists.intro,
                       levelParams := [`u],
                       type := Lean.Expr.forallE
                                 `α
                                 (Lean.Expr.sort (Lean.Level.param `u))
                                 (Lean.Expr.forallE
                                   `p
                                   (Lean.Expr.forallE
                                     (Lean.Name.mkNum `a.«_@»._internal._hyg 0)
                                     (Lean.Expr.bvar 0)
                                     (Lean.Expr.sort (Lean.Level.zero))
                                     (Lean.BinderInfo.default))
                                   (Lean.Expr.forallE
                                     `w
                                     (Lean.Expr.bvar 1)
                                     (Lean.Expr.forallE
                                       `h
                                       (Lean.Expr.app (Lean.Expr.bvar 1) (Lean.Expr.bvar 0))
                                       (Lean.Expr.app
                                         (Lean.Expr.app
                                           (Lean.Expr.const `Exists [Lean.Level.param `u])
                                           (Lean.Expr.bvar 3))
                                         (Lean.Expr.bvar 2))
                                       (Lean.BinderInfo.default))
                                     (Lean.BinderInfo.default))
                                   (Lean.BinderInfo.implicit))
                                 (Lean.BinderInfo.implicit) },
    induct := `Exists,
    cidx := 0,
    numParams := 2,
    numFields := 2,
    isUnsafe := false },
Lean.ConstantInfo.recInfo
  { toConstantVal := { name := `Exists.rec,
                       levelParams := [`u],
                       type := Lean.Expr.forallE
                                 `α
                                 (Lean.Expr.sort (Lean.Level.param `u))
                                 (Lean.Expr.forallE
                                   `p
                                   (Lean.Expr.forallE
                                     (Lean.Name.mkNum `a.«_@»._internal._hyg 0)
                                     (Lean.Expr.bvar 0)
                                     (Lean.Expr.sort (Lean.Level.zero))
                                     (Lean.BinderInfo.default))
                                   (Lean.Expr.forallE
                                     `motive
                                     (Lean.Expr.forallE
                                       `t
                                       (Lean.Expr.app
                                         (Lean.Expr.app
                                           (Lean.Expr.const `Exists [Lean.Level.param `u])
                                           (Lean.Expr.bvar 1))
                                         (Lean.Expr.bvar 0))
                                       (Lean.Expr.sort (Lean.Level.zero))
                                       (Lean.BinderInfo.default))
                                     (Lean.Expr.forallE
                                       `intro
                                       (Lean.Expr.forallE
                                         `w
                                         (Lean.Expr.bvar 2)
                                         (Lean.Expr.forallE
                                           `h
                                           (Lean.Expr.app (Lean.Expr.bvar 2) (Lean.Expr.bvar 0))
                                           (Lean.Expr.app
                                             (Lean.Expr.bvar 2)
                                             (Lean.Expr.app
                                               (Lean.Expr.app
                                                 (Lean.Expr.app
                                                   (Lean.Expr.app
                                                     (Lean.Expr.const `Exists.intro [Lean.Level.param `u])
                                                     (Lean.Expr.bvar 4))
                                                   (Lean.Expr.bvar 3))
                                                 (Lean.Expr.bvar 1))
                                               (Lean.Expr.bvar 0)))
                                           (Lean.BinderInfo.default))
                                         (Lean.BinderInfo.default))
                                       (Lean.Expr.forallE
                                         `t
                                         (Lean.Expr.app
                                           (Lean.Expr.app
                                             (Lean.Expr.const `Exists [Lean.Level.param `u])
                                             (Lean.Expr.bvar 3))
                                           (Lean.Expr.bvar 2))
                                         (Lean.Expr.app (Lean.Expr.bvar 2) (Lean.Expr.bvar 0))
                                         (Lean.BinderInfo.default))
                                       (Lean.BinderInfo.default))
                                     (Lean.BinderInfo.implicit))
                                   (Lean.BinderInfo.implicit))
                                 (Lean.BinderInfo.implicit) },
    all := [`Exists],
    numParams := 2,
    numIndices := 0,
    numMotives := 1,
    numMinors := 1,
    rules := [{ ctor := `Exists.intro,
                nfields := 2,
                rhs := Lean.Expr.lam
                         `α
                         (Lean.Expr.sort (Lean.Level.param `u))
                         (Lean.Expr.lam
                           `p
                           (Lean.Expr.forallE
                             (Lean.Name.mkNum `a.«_@»._internal._hyg 0)
                             (Lean.Expr.bvar 0)
                             (Lean.Expr.sort (Lean.Level.zero))
                             (Lean.BinderInfo.default))
                           (Lean.Expr.lam
                             `motive
                             (Lean.Expr.forallE
                               `t
                               (Lean.Expr.app
                                 (Lean.Expr.app (Lean.Expr.const `Exists [Lean.Level.param `u]) (Lean.Expr.bvar 1))
                                 (Lean.Expr.bvar 0))
                               (Lean.Expr.sort (Lean.Level.zero))
                               (Lean.BinderInfo.default))
                             (Lean.Expr.lam
                               `intro
                               (Lean.Expr.forallE
                                 `w
                                 (Lean.Expr.bvar 2)
                                 (Lean.Expr.forallE
                                   `h
                                   (Lean.Expr.app (Lean.Expr.bvar 2) (Lean.Expr.bvar 0))
                                   (Lean.Expr.app
                                     (Lean.Expr.bvar 2)
                                     (Lean.Expr.app
                                       (Lean.Expr.app
                                         (Lean.Expr.app
                                           (Lean.Expr.app
                                             (Lean.Expr.const `Exists.intro [Lean.Level.param `u])
                                             (Lean.Expr.bvar 4))
                                           (Lean.Expr.bvar 3))
                                         (Lean.Expr.bvar 1))
                                       (Lean.Expr.bvar 0)))
                                   (Lean.BinderInfo.default))
                                 (Lean.BinderInfo.default))
                               (Lean.Expr.lam
                                 `w
                                 (Lean.Expr.bvar 3)
                                 (Lean.Expr.lam
                                   `h
                                   (Lean.Expr.app (Lean.Expr.bvar 3) (Lean.Expr.bvar 0))
                                   (Lean.Expr.app
                                     (Lean.Expr.app (Lean.Expr.bvar 2) (Lean.Expr.bvar 1))
                                     (Lean.Expr.bvar 0))
                                   (Lean.BinderInfo.default))
                                 (Lean.BinderInfo.default))
                               (Lean.BinderInfo.default))
                             (Lean.BinderInfo.default))
                           (Lean.BinderInfo.default))
                         (Lean.BinderInfo.implicit) }],
    k := false,
    isUnsafe := false },
Lean.ConstantInfo.thmInfo
  { toConstantVal := { name := `Eq.symm,
                       levelParams := [`u],
                       type := Lean.Expr.forallE
                                 `α
                                 (Lean.Expr.sort (Lean.Level.param `u))
                                 (Lean.Expr.forallE
                                   `a
                                   (Lean.Expr.bvar 0)
                                   (Lean.Expr.forallE
                                     `b
                                     (Lean.Expr.bvar 1)
                                     (Lean.Expr.forallE
                                       `h
                                       (Lean.Expr.app
                                         (Lean.Expr.app
                                           (Lean.Expr.app
                                             (Lean.Expr.const `Eq [Lean.Level.param `u])
                                             (Lean.Expr.bvar 2))
                                           (Lean.Expr.bvar 1))
                                         (Lean.Expr.bvar 0))
                                       (Lean.Expr.app
                                         (Lean.Expr.app
                                           (Lean.Expr.app
                                             (Lean.Expr.const `Eq [Lean.Level.param `u])
                                             (Lean.Expr.bvar 3))
                                           (Lean.Expr.bvar 1))
                                         (Lean.Expr.bvar 2))
                                       (Lean.BinderInfo.default))
                                     (Lean.BinderInfo.implicit))
                                   (Lean.BinderInfo.implicit))
                                 (Lean.BinderInfo.implicit) },
    value := Lean.Expr.lam
               `α
               (Lean.Expr.sort (Lean.Level.param `u))
               (Lean.Expr.lam
                 `a
                 (Lean.Expr.bvar 0)
                 (Lean.Expr.lam
                   `b
                   (Lean.Expr.bvar 1)
                   (Lean.Expr.lam
                     `h
                     (Lean.Expr.app
                       (Lean.Expr.app
                         (Lean.Expr.app (Lean.Expr.const `Eq [Lean.Level.param `u]) (Lean.Expr.bvar 2))
                         (Lean.Expr.bvar 1))
                       (Lean.Expr.bvar 0))
                     (Lean.Expr.app
                       (Lean.Expr.app
                         (Lean.Expr.app
                           (Lean.Expr.app
                             (Lean.Expr.app
                               (Lean.Expr.app
                                 (Lean.Expr.const `Eq.rec [Lean.Level.zero, Lean.Level.param `u])
                                 (Lean.Expr.bvar 3))
                               (Lean.Expr.bvar 2))
                             (Lean.Expr.lam
                               (Lean.Name.mkNum (Lean.Name.mkStr (Lean.Name.mkStr (Lean.Name.mkNum `x.«_@».Init.Prelude 2345006592) "_hygCtx") "_hyg") 14)
                               (Lean.Expr.bvar 3)
                               (Lean.Expr.lam
                                 (Lean.Name.mkNum (Lean.Name.mkStr (Lean.Name.mkStr (Lean.Name.mkNum `h.«_@».Init.Prelude 2345006592) "_hygCtx") "_hyg") 15)
                                 (Lean.Expr.app
                                   (Lean.Expr.app
                                     (Lean.Expr.app (Lean.Expr.const `Eq [Lean.Level.param `u]) (Lean.Expr.bvar 4))
                                     (Lean.Expr.bvar 3))
                                   (Lean.Expr.bvar 0))
                                 (Lean.Expr.app
                                   (Lean.Expr.app
                                     (Lean.Expr.app (Lean.Expr.const `Eq [Lean.Level.param `u]) (Lean.Expr.bvar 5))
                                     (Lean.Expr.bvar 1))
                                   (Lean.Expr.bvar 4))
                                 (Lean.BinderInfo.default))
                               (Lean.BinderInfo.default)))
                           (Lean.Expr.app
                             (Lean.Expr.app (Lean.Expr.const `rfl [Lean.Level.param `u]) (Lean.Expr.bvar 3))
                             (Lean.Expr.bvar 2)))
                         (Lean.Expr.bvar 1))
                       (Lean.Expr.bvar 0))
                     (Lean.BinderInfo.default))
                   (Lean.BinderInfo.implicit))
                 (Lean.BinderInfo.implicit))
               (Lean.BinderInfo.implicit),
    all := [`Eq.symm] },
Lean.ConstantInfo.thmInfo
  { toConstantVal := { name := `Eq.trans,
                       levelParams := [`u],
                       type := Lean.Expr.forallE
                                 `α
                                 (Lean.Expr.sort (Lean.Level.param `u))
                                 (Lean.Expr.forallE
                                   `a
                                   (Lean.Expr.bvar 0)
                                   (Lean.Expr.forallE
                                     `b
                                     (Lean.Expr.bvar 1)
                                     (Lean.Expr.forallE
                                       `c
                                       (Lean.Expr.bvar 2)
                                       (Lean.Expr.forallE
                                         `h₁
                                         (Lean.Expr.app
                                           (Lean.Expr.app
                                             (Lean.Expr.app
                                               (Lean.Expr.const `Eq [Lean.Level.param `u])
                                               (Lean.Expr.bvar 3))
                                             (Lean.Expr.bvar 2))
                                           (Lean.Expr.bvar 1))
                                         (Lean.Expr.forallE
                                           `h₂
                                           (Lean.Expr.app
                                             (Lean.Expr.app
                                               (Lean.Expr.app
                                                 (Lean.Expr.const `Eq [Lean.Level.param `u])
                                                 (Lean.Expr.bvar 4))
                                               (Lean.Expr.bvar 2))
                                             (Lean.Expr.bvar 1))
                                           (Lean.Expr.app
                                             (Lean.Expr.app
                                               (Lean.Expr.app
                                                 (Lean.Expr.const `Eq [Lean.Level.param `u])
                                                 (Lean.Expr.bvar 5))
                                               (Lean.Expr.bvar 4))
                                             (Lean.Expr.bvar 2))
                                           (Lean.BinderInfo.default))
                                         (Lean.BinderInfo.default))
                                       (Lean.BinderInfo.implicit))
                                     (Lean.BinderInfo.implicit))
                                   (Lean.BinderInfo.implicit))
                                 (Lean.BinderInfo.implicit) },
    value := Lean.Expr.lam
               `α
               (Lean.Expr.sort (Lean.Level.param `u))
               (Lean.Expr.lam
                 `a
                 (Lean.Expr.bvar 0)
                 (Lean.Expr.lam
                   `b
                   (Lean.Expr.bvar 1)
                   (Lean.Expr.lam
                     `c
                     (Lean.Expr.bvar 2)
                     (Lean.Expr.lam
                       `h₁
                       (Lean.Expr.app
                         (Lean.Expr.app
                           (Lean.Expr.app (Lean.Expr.const `Eq [Lean.Level.param `u]) (Lean.Expr.bvar 3))
                           (Lean.Expr.bvar 2))
                         (Lean.Expr.bvar 1))
                       (Lean.Expr.lam
                         `h₂
                         (Lean.Expr.app
                           (Lean.Expr.app
                             (Lean.Expr.app (Lean.Expr.const `Eq [Lean.Level.param `u]) (Lean.Expr.bvar 4))
                             (Lean.Expr.bvar 2))
                           (Lean.Expr.bvar 1))
                         (Lean.Expr.app
                           (Lean.Expr.app
                             (Lean.Expr.app
                               (Lean.Expr.app
                                 (Lean.Expr.app
                                   (Lean.Expr.app
                                     (Lean.Expr.const `Eq.rec [Lean.Level.zero, Lean.Level.param `u])
                                     (Lean.Expr.bvar 5))
                                   (Lean.Expr.bvar 3))
                                 (Lean.Expr.lam
                                   (Lean.Name.mkNum (Lean.Name.mkStr (Lean.Name.mkStr (Lean.Name.mkNum `x.«_@».Init.Prelude 4164849530) "_hygCtx") "_hyg") 18)
                                   (Lean.Expr.bvar 5)
                                   (Lean.Expr.lam
                                     (Lean.Name.mkNum (Lean.Name.mkStr (Lean.Name.mkStr (Lean.Name.mkNum `h.«_@».Init.Prelude 4164849530) "_hygCtx") "_hyg") 19)
                                     (Lean.Expr.app
                                       (Lean.Expr.app
                                         (Lean.Expr.app (Lean.Expr.const `Eq [Lean.Level.param `u]) (Lean.Expr.bvar 6))
                                         (Lean.Expr.bvar 4))
                                       (Lean.Expr.bvar 0))
                                     (Lean.Expr.app
                                       (Lean.Expr.app
                                         (Lean.Expr.app (Lean.Expr.const `Eq [Lean.Level.param `u]) (Lean.Expr.bvar 7))
                                         (Lean.Expr.bvar 6))
                                       (Lean.Expr.bvar 1))
                                     (Lean.BinderInfo.default))
                                   (Lean.BinderInfo.default)))
                               (Lean.Expr.bvar 1))
                             (Lean.Expr.bvar 2))
                           (Lean.Expr.bvar 0))
                         (Lean.BinderInfo.default))
                       (Lean.BinderInfo.default))
                     (Lean.BinderInfo.implicit))
                   (Lean.BinderInfo.implicit))
                 (Lean.BinderInfo.implicit))
               (Lean.BinderInfo.implicit),
    all := [`Eq.trans] },
Lean.ConstantInfo.thmInfo
  { toConstantVal := { name := `congrArg,
                       levelParams := [`u, `v],
                       type := Lean.Expr.forallE
                                 `α
                                 (Lean.Expr.sort (Lean.Level.param `u))
                                 (Lean.Expr.forallE
                                   `β
                                   (Lean.Expr.sort (Lean.Level.param `v))
                                   (Lean.Expr.forallE
                                     `a₁
                                     (Lean.Expr.bvar 1)
                                     (Lean.Expr.forallE
                                       `a₂
                                       (Lean.Expr.bvar 2)
                                       (Lean.Expr.forallE
                                         `f
                                         (Lean.Expr.forallE
                                           (Lean.Name.mkNum `a.«_@»._internal._hyg 0)
                                           (Lean.Expr.bvar 3)
                                           (Lean.Expr.bvar 3)
                                           (Lean.BinderInfo.default))
                                         (Lean.Expr.forallE
                                           `h
                                           (Lean.Expr.app
                                             (Lean.Expr.app
                                               (Lean.Expr.app
                                                 (Lean.Expr.const `Eq [Lean.Level.param `u])
                                                 (Lean.Expr.bvar 4))
                                               (Lean.Expr.bvar 2))
                                             (Lean.Expr.bvar 1))
                                           (Lean.Expr.app
                                             (Lean.Expr.app
                                               (Lean.Expr.app
                                                 (Lean.Expr.const `Eq [Lean.Level.param `v])
                                                 (Lean.Expr.bvar 4))
                                               (Lean.Expr.app (Lean.Expr.bvar 1) (Lean.Expr.bvar 3)))
                                             (Lean.Expr.app (Lean.Expr.bvar 1) (Lean.Expr.bvar 2)))
                                           (Lean.BinderInfo.default))
                                         (Lean.BinderInfo.default))
                                       (Lean.BinderInfo.implicit))
                                     (Lean.BinderInfo.implicit))
                                   (Lean.BinderInfo.implicit))
                                 (Lean.BinderInfo.implicit) },
    value := Lean.Expr.lam
               `α
               (Lean.Expr.sort (Lean.Level.param `u))
               (Lean.Expr.lam
                 `β
                 (Lean.Expr.sort (Lean.Level.param `v))
                 (Lean.Expr.lam
                   `a₁
                   (Lean.Expr.bvar 1)
                   (Lean.Expr.lam
                     `a₂
                     (Lean.Expr.bvar 2)
                     (Lean.Expr.lam
                       `f
                       (Lean.Expr.forallE
                         (Lean.Name.mkNum `a.«_@»._internal._hyg 0)
                         (Lean.Expr.bvar 3)
                         (Lean.Expr.bvar 3)
                         (Lean.BinderInfo.default))
                       (Lean.Expr.lam
                         `h
                         (Lean.Expr.app
                           (Lean.Expr.app
                             (Lean.Expr.app (Lean.Expr.const `Eq [Lean.Level.param `u]) (Lean.Expr.bvar 4))
                             (Lean.Expr.bvar 2))
                           (Lean.Expr.bvar 1))
                         (Lean.Expr.app
                           (Lean.Expr.app
                             (Lean.Expr.app
                               (Lean.Expr.app
                                 (Lean.Expr.app
                                   (Lean.Expr.app
                                     (Lean.Expr.const `Eq.rec [Lean.Level.zero, Lean.Level.param `u])
                                     (Lean.Expr.bvar 5))
                                   (Lean.Expr.bvar 3))
                                 (Lean.Expr.lam
                                   (Lean.Name.mkNum (Lean.Name.mkStr (Lean.Name.mkStr (Lean.Name.mkNum `x.«_@».Init.Prelude 2375064143) "_hygCtx") "_hyg") 24)
                                   (Lean.Expr.bvar 5)
                                   (Lean.Expr.lam
                                     (Lean.Name.mkNum (Lean.Name.mkStr (Lean.Name.mkStr (Lean.Name.mkNum `h.«_@».Init.Prelude 2375064143) "_hygCtx") "_hyg") 25)
                                     (Lean.Expr.app
                                       (Lean.Expr.app
                                         (Lean.Expr.app (Lean.Expr.const `Eq [Lean.Level.param `u]) (Lean.Expr.bvar 6))
                                         (Lean.Expr.bvar 4))
                                       (Lean.Expr.bvar 0))
                                     (Lean.Expr.app
                                       (Lean.Expr.app
                                         (Lean.Expr.app (Lean.Expr.const `Eq [Lean.Level.param `v]) (Lean.Expr.bvar 6))
                                         (Lean.Expr.app (Lean.Expr.bvar 3) (Lean.Expr.bvar 5)))
                                       (Lean.Expr.app (Lean.Expr.bvar 3) (Lean.Expr.bvar 1)))
                                     (Lean.BinderInfo.default))
                                   (Lean.BinderInfo.default)))
                               (Lean.Expr.app
                                 (Lean.Expr.app (Lean.Expr.const `rfl [Lean.Level.param `v]) (Lean.Expr.bvar 4))
                                 (Lean.Expr.app (Lean.Expr.bvar 1) (Lean.Expr.bvar 3))))
                             (Lean.Expr.bvar 2))
                           (Lean.Expr.bvar 0))
                         (Lean.BinderInfo.default))
                       (Lean.BinderInfo.default))
                     (Lean.BinderInfo.implicit))
                   (Lean.BinderInfo.implicit))
                 (Lean.BinderInfo.implicit))
               (Lean.BinderInfo.implicit),
    all := [`congrArg] },
Lean.ConstantInfo.defnInfo
  { toConstantVal := { name := `rfl,
                       levelParams := [`u],
                       type := Lean.Expr.forallE
                                 `α
                                 (Lean.Expr.sort (Lean.Level.param `u))
                                 (Lean.Expr.forallE
                                   `a
                                   (Lean.Expr.bvar 0)
                                   (Lean.Expr.app
                                     (Lean.Expr.app
                                       (Lean.Expr.app (Lean.Expr.const `Eq [Lean.Level.param `u]) (Lean.Expr.bvar 1))
                                       (Lean.Expr.bvar 0))
                                     (Lean.Expr.bvar 0))
                                   (Lean.BinderInfo.implicit))
                                 (Lean.BinderInfo.implicit) },
    value := Lean.Expr.lam
               `α
               (Lean.Expr.sort (Lean.Level.param `u))
               (Lean.Expr.lam
                 `a
                 (Lean.Expr.bvar 0)
                 (Lean.Expr.app
                   (Lean.Expr.app (Lean.Expr.const `Eq.refl [Lean.Level.param `u]) (Lean.Expr.bvar 1))
                   (Lean.Expr.bvar 0))
                 (Lean.BinderInfo.implicit))
               (Lean.BinderInfo.implicit),
    hints := Lean.ReducibilityHints.regular 1,
    safety := Lean.DefinitionSafety.safe,
    all := [`rfl] },
Lean.ConstantInfo.thmInfo
  { toConstantVal := { name := `And.left,
                       levelParams := [],
                       type := Lean.Expr.forallE
                                 `a
                                 (Lean.Expr.sort (Lean.Level.zero))
                                 (Lean.Expr.forallE
                                   `b
                                   (Lean.Expr.sort (Lean.Level.zero))
                                   (Lean.Expr.forallE
                                     `self
                                     (Lean.Expr.app
                                       (Lean.Expr.app (Lean.Expr.const `And []) (Lean.Expr.bvar 1))
                                       (Lean.Expr.bvar 0))
                                     (Lean.Expr.bvar 2)
                                     (Lean.BinderInfo.default))
                                   (Lean.BinderInfo.implicit))
                                 (Lean.BinderInfo.implicit) },
    value := Lean.Expr.lam
               `a
               (Lean.Expr.sort (Lean.Level.zero))
               (Lean.Expr.lam
                 `b
                 (Lean.Expr.sort (Lean.Level.zero))
                 (Lean.Expr.lam
                   `self
                   (Lean.Expr.app (Lean.Expr.app (Lean.Expr.const `And []) (Lean.Expr.bvar 1)) (Lean.Expr.bvar 0))
                   (Lean.Expr.proj `And 0 (Lean.Expr.bvar 0))
                   (Lean.BinderInfo.default))
                 (Lean.BinderInfo.default))
               (Lean.BinderInfo.default),
    all := [`And.left] },
Lean.ConstantInfo.thmInfo
  { toConstantVal := { name := `And.right,
                       levelParams := [],
                       type := Lean.Expr.forallE
                                 `a
                                 (Lean.Expr.sort (Lean.Level.zero))
                                 (Lean.Expr.forallE
                                   `b
                                   (Lean.Expr.sort (Lean.Level.zero))
                                   (Lean.Expr.forallE
                                     `self
                                     (Lean.Expr.app
                                       (Lean.Expr.app (Lean.Expr.const `And []) (Lean.Expr.bvar 1))
                                       (Lean.Expr.bvar 0))
                                     (Lean.Expr.bvar 1)
                                     (Lean.BinderInfo.default))
                                   (Lean.BinderInfo.implicit))
                                 (Lean.BinderInfo.implicit) },
    value := Lean.Expr.lam
               `a
               (Lean.Expr.sort (Lean.Level.zero))
               (Lean.Expr.lam
                 `b
                 (Lean.Expr.sort (Lean.Level.zero))
                 (Lean.Expr.lam
                   `self
                   (Lean.Expr.app (Lean.Expr.app (Lean.Expr.const `And []) (Lean.Expr.bvar 1)) (Lean.Expr.bvar 0))
                   (Lean.Expr.proj `And 1 (Lean.Expr.bvar 0))
                   (Lean.BinderInfo.default))
                 (Lean.BinderInfo.default))
               (Lean.BinderInfo.default),
    all := [`And.right] },
Lean.ConstantInfo.thmInfo
  { toConstantVal := { name := `Exists.elim,
                       levelParams := [`u],
                       type := Lean.Expr.forallE
                                 `α
                                 (Lean.Expr.sort (Lean.Level.param `u))
                                 (Lean.Expr.forallE
                                   `p
                                   (Lean.Expr.forallE
                                     (Lean.Name.mkNum `a.«_@»._internal._hyg 0)
                                     (Lean.Expr.bvar 0)
                                     (Lean.Expr.sort (Lean.Level.zero))
                                     (Lean.BinderInfo.default))
                                   (Lean.Expr.forallE
                                     `b
                                     (Lean.Expr.sort (Lean.Level.zero))
                                     (Lean.Expr.forallE
                                       `h₁
                                       (Lean.Expr.app
                                         (Lean.Expr.app
                                           (Lean.Expr.const `Exists [Lean.Level.param `u])
                                           (Lean.Expr.bvar 2))
                                         (Lean.Expr.lam
                                           `x
                                           (Lean.Expr.bvar 2)
                                           (Lean.Expr.app (Lean.Expr.bvar 2) (Lean.Expr.bvar 0))
                                           (Lean.BinderInfo.default)))
                                       (Lean.Expr.forallE
                                         `h₂
                                         (Lean.Expr.forallE
                                           `a
                                           (Lean.Expr.bvar 3)
                                           (Lean.Expr.forallE
                                             (Lean.Name.mkNum `a.«_@»._internal._hyg 0)
                                             (Lean.Expr.app (Lean.Expr.bvar 3) (Lean.Expr.bvar 0))
                                             (Lean.Expr.bvar 3)
                                             (Lean.BinderInfo.default))
                                           (Lean.BinderInfo.default))
                                         (Lean.Expr.bvar 2)
                                         (Lean.BinderInfo.default))
                                       (Lean.BinderInfo.default))
                                     (Lean.BinderInfo.implicit))
                                   (Lean.BinderInfo.implicit))
                                 (Lean.BinderInfo.implicit) },
    value := Lean.Expr.lam
               `α
               (Lean.Expr.sort (Lean.Level.param `u))
               (Lean.Expr.lam
                 `p
                 (Lean.Expr.forallE
                   (Lean.Name.mkNum `a.«_@»._internal._hyg 0)
                   (Lean.Expr.bvar 0)
                   (Lean.Expr.sort (Lean.Level.zero))
                   (Lean.BinderInfo.default))
                 (Lean.Expr.lam
                   `b
                   (Lean.Expr.sort (Lean.Level.zero))
                   (Lean.Expr.lam
                     `h₁
                     (Lean.Expr.app
                       (Lean.Expr.app (Lean.Expr.const `Exists [Lean.Level.param `u]) (Lean.Expr.bvar 2))
                       (Lean.Expr.lam
                         `x
                         (Lean.Expr.bvar 2)
                         (Lean.Expr.app (Lean.Expr.bvar 2) (Lean.Expr.bvar 0))
                         (Lean.BinderInfo.default)))
                     (Lean.Expr.lam
                       `h₂
                       (Lean.Expr.forallE
                         `a
                         (Lean.Expr.bvar 3)
                         (Lean.Expr.forallE
                           (Lean.Name.mkNum `a.«_@»._internal._hyg 0)
                           (Lean.Expr.app (Lean.Expr.bvar 3) (Lean.Expr.bvar 0))
                           (Lean.Expr.bvar 3)
                           (Lean.BinderInfo.default))
                         (Lean.BinderInfo.default))
                       (Lean.Expr.app
                         (Lean.Expr.app
                           (Lean.Expr.app
                             (Lean.Expr.app
                               (Lean.Expr.app
                                 (Lean.Expr.const
                                   (Lean.Name.mkStr (Lean.Name.mkStr (Lean.Name.mkStr (Lean.Name.mkNum `_private.Init.Core 0) "Exists") "elim") "match_1_1")
                                   [Lean.Level.param `u])
                                 (Lean.Expr.bvar 4))
                               (Lean.Expr.bvar 3))
                             (Lean.Expr.lam
                               (Lean.Name.mkNum (Lean.Name.mkStr (Lean.Name.mkStr (Lean.Name.mkNum `h₁.«_@».Init.Core 2135250729) "_hygCtx") "_hyg") 30)
                               (Lean.Expr.app
                                 (Lean.Expr.app (Lean.Expr.const `Exists [Lean.Level.param `u]) (Lean.Expr.bvar 4))
                                 (Lean.Expr.lam
                                   `x
                                   (Lean.Expr.bvar 4)
                                   (Lean.Expr.app (Lean.Expr.bvar 4) (Lean.Expr.bvar 0))
                                   (Lean.BinderInfo.default)))
                               (Lean.Expr.bvar 3)
                               (Lean.BinderInfo.default)))
                           (Lean.Expr.bvar 1))
                         (Lean.Expr.lam
                           `a
                           (Lean.Expr.bvar 4)
                           (Lean.Expr.lam
                             `h
                             (Lean.Expr.app (Lean.Expr.bvar 4) (Lean.Expr.bvar 0))
                             (Lean.Expr.app (Lean.Expr.app (Lean.Expr.bvar 2) (Lean.Expr.bvar 1)) (Lean.Expr.bvar 0))
                             (Lean.BinderInfo.default))
                           (Lean.BinderInfo.default)))
                       (Lean.BinderInfo.default))
                     (Lean.BinderInfo.default))
                   (Lean.BinderInfo.implicit))
                 (Lean.BinderInfo.implicit))
               (Lean.BinderInfo.implicit),
    all := [`Exists.elim] },
Lean.ConstantInfo.defnInfo
  { toConstantVal := { name := `Exists.casesOn,
                       levelParams := [`u],
                       type := Lean.Expr.forallE
                                 `α
                                 (Lean.Expr.sort (Lean.Level.param `u))
                                 (Lean.Expr.forallE
                                   `p
                                   (Lean.Expr.forallE
                                     (Lean.Name.mkNum `a.«_@»._internal._hyg 0)
                                     (Lean.Expr.bvar 0)
                                     (Lean.Expr.sort (Lean.Level.zero))
                                     (Lean.BinderInfo.default))
                                   (Lean.Expr.forallE
                                     `motive
                                     (Lean.Expr.forallE
                                       `t
                                       (Lean.Expr.app
                                         (Lean.Expr.app
                                           (Lean.Expr.const `Exists [Lean.Level.param `u])
                                           (Lean.Expr.bvar 1))
                                         (Lean.Expr.bvar 0))
                                       (Lean.Expr.sort (Lean.Level.zero))
                                       (Lean.BinderInfo.default))
                                     (Lean.Expr.forallE
                                       `t
                                       (Lean.Expr.app
                                         (Lean.Expr.app
                                           (Lean.Expr.const `Exists [Lean.Level.param `u])
                                           (Lean.Expr.bvar 2))
                                         (Lean.Expr.bvar 1))
                                       (Lean.Expr.forallE
                                         `intro
                                         (Lean.Expr.forallE
                                           `w
                                           (Lean.Expr.bvar 3)
                                           (Lean.Expr.forallE
                                             `h
                                             (Lean.Expr.app (Lean.Expr.bvar 3) (Lean.Expr.bvar 0))
                                             (Lean.Expr.app
                                               (Lean.Expr.bvar 3)
                                               (Lean.Expr.app
                                                 (Lean.Expr.app
                                                   (Lean.Expr.app
                                                     (Lean.Expr.app
                                                       (Lean.Expr.const `Exists.intro [Lean.Level.param `u])
                                                       (Lean.Expr.bvar 5))
                                                     (Lean.Expr.bvar 4))
                                                   (Lean.Expr.bvar 1))
                                                 (Lean.Expr.bvar 0)))
                                             (Lean.BinderInfo.default))
                                           (Lean.BinderInfo.default))
                                         (Lean.Expr.app (Lean.Expr.bvar 2) (Lean.Expr.bvar 1))
                                         (Lean.BinderInfo.default))
                                       (Lean.BinderInfo.default))
                                     (Lean.BinderInfo.implicit))
                                   (Lean.BinderInfo.implicit))
                                 (Lean.BinderInfo.implicit) },
    value := Lean.Expr.lam
               `α
               (Lean.Expr.sort (Lean.Level.param `u))
               (Lean.Expr.lam
                 `p
                 (Lean.Expr.forallE
                   (Lean.Name.mkNum `a.«_@»._internal._hyg 0)
                   (Lean.Expr.bvar 0)
                   (Lean.Expr.sort (Lean.Level.zero))
                   (Lean.BinderInfo.default))
                 (Lean.Expr.lam
                   `motive
                   (Lean.Expr.forallE
                     `t
                     (Lean.Expr.app
                       (Lean.Expr.app (Lean.Expr.const `Exists [Lean.Level.param `u]) (Lean.Expr.bvar 1))
                       (Lean.Expr.bvar 0))
                     (Lean.Expr.sort (Lean.Level.zero))
                     (Lean.BinderInfo.default))
                   (Lean.Expr.lam
                     `t
                     (Lean.Expr.app
                       (Lean.Expr.app (Lean.Expr.const `Exists [Lean.Level.param `u]) (Lean.Expr.bvar 2))
                       (Lean.Expr.bvar 1))
                     (Lean.Expr.lam
                       `intro
                       (Lean.Expr.forallE
                         `w
                         (Lean.Expr.bvar 3)
                         (Lean.Expr.forallE
                           `h
                           (Lean.Expr.app (Lean.Expr.bvar 3) (Lean.Expr.bvar 0))
                           (Lean.Expr.app
                             (Lean.Expr.bvar 3)
                             (Lean.Expr.app
                               (Lean.Expr.app
                                 (Lean.Expr.app
                                   (Lean.Expr.app
                                     (Lean.Expr.const `Exists.intro [Lean.Level.param `u])
                                     (Lean.Expr.bvar 5))
                                   (Lean.Expr.bvar 4))
                                 (Lean.Expr.bvar 1))
                               (Lean.Expr.bvar 0)))
                           (Lean.BinderInfo.default))
                         (Lean.BinderInfo.default))
                       (Lean.Expr.app
                         (Lean.Expr.app
                           (Lean.Expr.app
                             (Lean.Expr.app
                               (Lean.Expr.app (Lean.Expr.const `Exists.rec [Lean.Level.param `u]) (Lean.Expr.bvar 4))
                               (Lean.Expr.bvar 3))
                             (Lean.Expr.bvar 2))
                           (Lean.Expr.lam
                             `w
                             (Lean.Expr.bvar 4)
                             (Lean.Expr.lam
                               `h
                               (Lean.Expr.app (Lean.Expr.bvar 4) (Lean.Expr.bvar 0))
                               (Lean.Expr.app (Lean.Expr.app (Lean.Expr.bvar 2) (Lean.Expr.bvar 1)) (Lean.Expr.bvar 0))
                               (Lean.BinderInfo.default))
                             (Lean.BinderInfo.default)))
                         (Lean.Expr.bvar 1))
                       (Lean.BinderInfo.default))
                     (Lean.BinderInfo.default))
                   (Lean.BinderInfo.implicit))
                 (Lean.BinderInfo.implicit))
               (Lean.BinderInfo.implicit),
    hints := Lean.ReducibilityHints.abbrev,
    safety := Lean.DefinitionSafety.safe,
    all := [`Exists.casesOn] },
Lean.ConstantInfo.defnInfo
  { toConstantVal := { name := Lean.Name.mkStr (Lean.Name.mkStr (Lean.Name.mkStr (Lean.Name.mkNum `_private.Init.Core 0) "Exists") "elim") "match_1_1",
                       levelParams := [`u_1],
                       type := Lean.Expr.forallE
                                 `α
                                 (Lean.Expr.sort (Lean.Level.param `u_1))
                                 (Lean.Expr.forallE
                                   `p
                                   (Lean.Expr.forallE
                                     (Lean.Name.mkNum `a.«_@»._internal._hyg 0)
                                     (Lean.Expr.bvar 0)
                                     (Lean.Expr.sort (Lean.Level.zero))
                                     (Lean.BinderInfo.default))
                                   (Lean.Expr.forallE
                                     `motive
                                     (Lean.Expr.forallE
                                       (Lean.Name.mkNum (Lean.Name.mkStr (Lean.Name.mkStr (Lean.Name.mkNum `h₁.«_@».Init.Core 2135250729) "_hygCtx") "_hyg") 30)
                                       (Lean.Expr.app
                                         (Lean.Expr.app
                                           (Lean.Expr.const `Exists [Lean.Level.param `u_1])
                                           (Lean.Expr.bvar 1))
                                         (Lean.Expr.lam
                                           `x
                                           (Lean.Expr.bvar 1)
                                           (Lean.Expr.app (Lean.Expr.bvar 1) (Lean.Expr.bvar 0))
                                           (Lean.BinderInfo.default)))
                                       (Lean.Expr.sort (Lean.Level.zero))
                                       (Lean.BinderInfo.default))
                                     (Lean.Expr.forallE
                                       (Lean.Name.mkNum (Lean.Name.mkStr (Lean.Name.mkStr (Lean.Name.mkNum `h₁.«_@».Init.Core 2135250729) "_hygCtx") "_hyg") 30)
                                       (Lean.Expr.app
                                         (Lean.Expr.app
                                           (Lean.Expr.const `Exists [Lean.Level.param `u_1])
                                           (Lean.Expr.bvar 2))
                                         (Lean.Expr.lam
                                           `x
                                           (Lean.Expr.bvar 2)
                                           (Lean.Expr.app (Lean.Expr.bvar 2) (Lean.Expr.bvar 0))
                                           (Lean.BinderInfo.default)))
                                       (Lean.Expr.forallE
                                         `h_1
                                         (Lean.Expr.forallE
                                           `a
                                           (Lean.Expr.bvar 3)
                                           (Lean.Expr.forallE
                                             `h
                                             (Lean.Expr.app (Lean.Expr.bvar 3) (Lean.Expr.bvar 0))
                                             (Lean.Expr.app
                                               (Lean.Expr.bvar 3)
                                               (Lean.Expr.app
                                                 (Lean.Expr.app
                                                   (Lean.Expr.app
                                                     (Lean.Expr.app
                                                       (Lean.Expr.const `Exists.intro [Lean.Level.param `u_1])
                                                       (Lean.Expr.bvar 5))
                                                     (Lean.Expr.lam
                                                       `x
                                                       (Lean.Expr.bvar 5)
                                                       (Lean.Expr.app (Lean.Expr.bvar 5) (Lean.Expr.bvar 0))
                                                       (Lean.BinderInfo.default)))
                                                   (Lean.Expr.bvar 1))
                                                 (Lean.Expr.bvar 0)))
                                             (Lean.BinderInfo.default))
                                           (Lean.BinderInfo.default))
                                         (Lean.Expr.app (Lean.Expr.bvar 2) (Lean.Expr.bvar 1))
                                         (Lean.BinderInfo.default))
                                       (Lean.BinderInfo.default))
                                     (Lean.BinderInfo.default))
                                   (Lean.BinderInfo.implicit))
                                 (Lean.BinderInfo.implicit) },
    value := Lean.Expr.lam
               `α
               (Lean.Expr.sort (Lean.Level.param `u_1))
               (Lean.Expr.lam
                 `p
                 (Lean.Expr.forallE
                   (Lean.Name.mkNum `a.«_@»._internal._hyg 0)
                   (Lean.Expr.bvar 0)
                   (Lean.Expr.sort (Lean.Level.zero))
                   (Lean.BinderInfo.default))
                 (Lean.Expr.lam
                   `motive
                   (Lean.Expr.forallE
                     (Lean.Name.mkNum (Lean.Name.mkStr (Lean.Name.mkStr (Lean.Name.mkNum `h₁.«_@».Init.Core 2135250729) "_hygCtx") "_hyg") 30)
                     (Lean.Expr.app
                       (Lean.Expr.app (Lean.Expr.const `Exists [Lean.Level.param `u_1]) (Lean.Expr.bvar 1))
                       (Lean.Expr.lam
                         `x
                         (Lean.Expr.bvar 1)
                         (Lean.Expr.app (Lean.Expr.bvar 1) (Lean.Expr.bvar 0))
                         (Lean.BinderInfo.default)))
                     (Lean.Expr.sort (Lean.Level.zero))
                     (Lean.BinderInfo.default))
                   (Lean.Expr.lam
                     (Lean.Name.mkNum (Lean.Name.mkStr (Lean.Name.mkStr (Lean.Name.mkNum `h₁.«_@».Init.Core 2135250729) "_hygCtx") "_hyg") 30)
                     (Lean.Expr.app
                       (Lean.Expr.app (Lean.Expr.const `Exists [Lean.Level.param `u_1]) (Lean.Expr.bvar 2))
                       (Lean.Expr.lam
                         `x
                         (Lean.Expr.bvar 2)
                         (Lean.Expr.app (Lean.Expr.bvar 2) (Lean.Expr.bvar 0))
                         (Lean.BinderInfo.default)))
                     (Lean.Expr.lam
                       `h_1
                       (Lean.Expr.forallE
                         `a
                         (Lean.Expr.bvar 3)
                         (Lean.Expr.forallE
                           `h
                           (Lean.Expr.app (Lean.Expr.bvar 3) (Lean.Expr.bvar 0))
                           (Lean.Expr.app
                             (Lean.Expr.bvar 3)
                             (Lean.Expr.app
                               (Lean.Expr.app
                                 (Lean.Expr.app
                                   (Lean.Expr.app
                                     (Lean.Expr.const `Exists.intro [Lean.Level.param `u_1])
                                     (Lean.Expr.bvar 5))
                                   (Lean.Expr.lam
                                     `x
                                     (Lean.Expr.bvar 5)
                                     (Lean.Expr.app (Lean.Expr.bvar 5) (Lean.Expr.bvar 0))
                                     (Lean.BinderInfo.default)))
                                 (Lean.Expr.bvar 1))
                               (Lean.Expr.bvar 0)))
                           (Lean.BinderInfo.default))
                         (Lean.BinderInfo.default))
                       (Lean.Expr.app
                         (Lean.Expr.app
                           (Lean.Expr.app
                             (Lean.Expr.app
                               (Lean.Expr.app
                                 (Lean.Expr.const `Exists.casesOn [Lean.Level.param `u_1])
                                 (Lean.Expr.bvar 4))
                               (Lean.Expr.lam
                                 `x
                                 (Lean.Expr.bvar 4)
                                 (Lean.Expr.app (Lean.Expr.bvar 4) (Lean.Expr.bvar 0))
                                 (Lean.BinderInfo.default)))
                             (Lean.Expr.lam
                               `x
                               (Lean.Expr.app
                                 (Lean.Expr.app (Lean.Expr.const `Exists [Lean.Level.param `u_1]) (Lean.Expr.bvar 4))
                                 (Lean.Expr.lam
                                   `x
                                   (Lean.Expr.bvar 4)
                                   (Lean.Expr.app (Lean.Expr.bvar 4) (Lean.Expr.bvar 0))
                                   (Lean.BinderInfo.default)))
                               (Lean.Expr.app (Lean.Expr.bvar 3) (Lean.Expr.bvar 0))
                               (Lean.BinderInfo.default)))
                           (Lean.Expr.bvar 1))
                         (Lean.Expr.lam
                           (Lean.Name.mkNum (Lean.Name.mkStr (Lean.Name.mkStr (Lean.Name.mkNum `w.«_@».Init.Core 2135250729) "_hygCtx") "_hyg") 42)
                           (Lean.Expr.bvar 4)
                           (Lean.Expr.lam
                             (Lean.Name.mkNum (Lean.Name.mkStr (Lean.Name.mkStr (Lean.Name.mkNum `h.«_@».Init.Core 2135250729) "_hygCtx") "_hyg") 43)
                             (Lean.Expr.app (Lean.Expr.bvar 4) (Lean.Expr.bvar 0))
                             (Lean.Expr.app (Lean.Expr.app (Lean.Expr.bvar 2) (Lean.Expr.bvar 1)) (Lean.Expr.bvar 0))
                             (Lean.BinderInfo.default))
                           (Lean.BinderInfo.default)))
                       (Lean.BinderInfo.default))
                     (Lean.BinderInfo.default))
                   (Lean.BinderInfo.default))
                 (Lean.BinderInfo.implicit))
               (Lean.BinderInfo.implicit),
    hints := Lean.ReducibilityHints.abbrev,
    safety := Lean.DefinitionSafety.safe,
    all := [Lean.Name.mkStr (Lean.Name.mkStr (Lean.Name.mkStr (Lean.Name.mkNum `_private.Init.Core 0) "Exists") "elim") "match_1_1"] }
]

end SquareKit.Internal.GraphPrimitiveEnvironment
