import SquareKit.Internal.PathTransport.Transfer

/-! The supported Lean authoring fragment has no Π constructor, injection of
host functions, or equality reflection. These are Lean elaborator diagnostics,
not claims of an Agda parser or a general Agda translation frontend. -/
open SquareKit.Internal.PathTransport

/-- error: Unknown constant `SquareKit.Internal.PathTransport.Expr.pi` -/
#guard_msgs in
#check Expr.pi

/-- error: Unknown constant `SquareKit.Internal.PathTransport.Typed.TmDeriv.hostFunction` -/
#guard_msgs in
#check Typed.TmDeriv.hostFunction

/-- error: Unknown constant `SquareKit.Internal.PathTransport.Typed.TyEqDeriv.reflect` -/
#guard_msgs in
#check Typed.TyEqDeriv.reflect
