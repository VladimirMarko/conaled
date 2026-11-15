import SquareKit.WitnessCartesian

/-! Constructive rewriting for computational witnesses. Each branch builds a
term from the supplied congruence and transitivity operations. -/
namespace SquareKit.WitnessEquivalence
syntax "witness_rewrite_at " term ", " term ", " term ", " term : tactic
macro_rules
| `(tactic| witness_rewrite_at $e, $k, $p, $h) =>
  `(tactic| first
    | apply $h
    | (apply ($k).comp
       · witness_rewrite_at $e, $k, $p, $h
       · exact ($e).refl _)
    | (apply ($k).comp
       · exact ($e).refl _
       · witness_rewrite_at $e, $k, $p, $h)
    | (apply ($p).pair
       · witness_rewrite_at $e, $k, $p, $h
       · exact ($e).refl _)
    | (apply ($p).pair
       · exact ($e).refl _
       · witness_rewrite_at $e, $k, $p, $h))
syntax "witness_rewrite " term ", " term ", " term ", " term : tactic
macro_rules
| `(tactic| witness_rewrite $e, $k, $p, $h) =>
  `(tactic| refine ($e).trans (by witness_rewrite_at $e, $k, $p, $h) ?_)
end SquareKit.WitnessEquivalence
