# Represented local families and coherent arrow diagrams

[Issue #651](https://github.com/VladimirMarko/conaled/issues/651) supplies an
independent local-data interface for the existing coherent decoder. The
implementation is [RepresentedLocalFamily.lean](../../SquareKit/Internal/RepresentedLocalFamily.lean),
with checked uses in [Examples.RepresentedLocalFamily](../../Examples/RepresentedLocalFamily.lean).
Direct arrow-diagram clients remain unchanged.

## Local input and categorical recovery

Let `C : Type v` with `[Category.{w} C]`. A context
`Γ : Context.{u} C` is a functor `Cᵒᵖ ⥤ Type (max u w)`. The target
`V : Type a` has `[Category.{b} V]`, with independent `a` and `b`.
For this context, `representedDiagram Γ` sends a root
`x : Γ.Elements` to the category of elements of the representable at its
underlying object. Its domain is `Γ.Elementsᵒᵖ`; a root arrow `x ⟶ y` induces
restriction from the represented context at `y` to that at `x`.

`LocalData F V` is specified before any reference to `Code`. It consists of
functors `A.app x : F.obj x ⥤ V` and isomorphisms
`F.map f ⋙ A.app y ≅ A.app x`, with unit and composition laws. Morphisms are
arbitrary component natural transformations commuting with these comparisons.
Identity and composition are componentwise. The definitions allow independent
object and morphism universes for `V`, the index category, and the categories
in `F`; they impose no groupoid or smallness hypothesis on `V`.

`toTotal` assembles this data into a functor from Mathlib's
`Pseudofunctor.CoGrothendieck F.toPseudofunctor'`. An arrow square decomposes into
a root arrow and a map inside a represented context. `arrowToTotal` implements
that decomposition, and `toCode` composes it with assembly. Invertibility of the
selected comparisons makes the resulting arrow diagram coherent.

`fromCode` restricts a code to each represented context and obtains its
comparison isomorphisms from the established coherent restriction theorem.
`localRecoveryIso` recovers each local functor, its maps, and its selected
comparisons. `codeRecoveryIso` recovers every arrow square. Both are natural in
all morphisms, giving `equivalence`, then `classification` by composition with
the existing category-valued classifier. The equivalence constructor adjusts
the unit to satisfy the triangle law; `localRecoveryIso` remains available as
the direct componentwise round-trip comparison.

Context substitution is defined directly on local roots. `toCode_reindex` is
an equality of functors; `fromCodeReindex` supplies the inverse comparison
through the recovery isomorphisms. `comparison` packages it as a Mathlib pseudonatural
transformation, and `decoder` composes it with the existing pseudonatural
decoder. `classification_unit` and `classification_counit` give the precise
composites with the old unit and counit. `decodeReindex_id`,
`decodeReindex_comp`, `recovery_reindex`, and `localRecovery_reindex` retain the
substitution laws for decoding and recovery.

## Which coherent presentation is used

At common `Cat` universes these local objects are pseudonatural cocones from
`F.toPseudofunctor'` to the constant pseudofunctor at `V`. The checked
`toStrongTrans`/`ofStrongTrans` and `toModification`/`ofModification` round trips
identify their objects and all compatible maps. These conversions require the
source fibers and target to inhabit the same `Cat.{k,l}`. That requirement is
local to this bridge: the main local-data and classification theorems keep
independent target universes. The Boolean example uses that more general
interface; the `ℕᵒᵖ` example also instantiates the common-universe bridge.

The assembly proof uses the actual contravariant Grothendieck category, its
fiber maps, identities, and composition. It does not assert an equivalence with
an unspecified category of cartesian sections. Such a statement would need a
chosen fibration, a direction for section comparison, and a proof identifying
its cartesian maps. No cartesian-section hypothesis is added to recovery.

The theorem classifies ordinary functors `Γ.Elements ⥤ V`, even when `V` has
noninvertible arrows. It does not classify an arbitrary weak pseudofunctor of
contexts. That problem lacks the concrete represented arrow decomposition and
decoder used here; coherence of a weak context action alone does not supply
these constructions. Remaining stronger coherence work stays under
[#647](https://github.com/VladimirMarko/conaled/issues/647), including its
separate [task #652](https://github.com/VladimirMarko/conaled/issues/652).

## Checked cases and contract boundary

The Boolean case specifies constant local fibers directly. Root restriction
uses the parity swap, so restriction along `2 → 1` and the assembled decoder
both send `false` to `true`. A compatible collapse to `PUnit` is proved
noninvertible; naturality of the classification unit recovers that map. The
`ℕᵒᵖ` case has a decoded arrow with no inverse, checked separately from the
noninvertibility of a map between local families. Successor followed by double
substitution recovers the dependent fiber `Fin 6` at the chosen point and
satisfies the decoder comparison composition law.

Invertible restriction comparisons are part of the requested contract. The
existing `badData_no_recovery` and `badData_not_coherent` examples exhibit why
arbitrary noninvertible restriction maps do not suffice: a root-only order
diagram would need an impossible inverse order arrow to recover its target
view. No new assumption on ordinary family arrows is introduced.

## Client setup and measured elaboration

The local client supplies functors, restriction isomorphisms, and their two
coherence laws. Assembly, coherence of arrow squares, categorical recovery, and
the context decoder are reusable library proofs. A direct client instead
supplies an arrow functor and proves that it inverts the designated squares.
For the parity example, the direct constructor is short because a root-only
functor already describes every square; local input does not reduce that
particular setup.

The retained [local fixture](../../experiments/represented-local-families/local.lean.txt)
and [arrow fixture](../../experiments/represented-local-families/arrow.lean.txt)
each construct that Boolean input afresh and check the same decoded swap.
Both import the same compiled modules. Measurements cover their source
commands, not the one-time compilation of the library comparison theorem.

Reproduce with the pinned development environment and prebuilt imports:

```sh
direnv exec . lake build Examples.RepresentedLocalFamily
direnv exec . python3 - <<'PY'
import importlib.util
import json
from pathlib import Path
spec = importlib.util.spec_from_file_location(
    'bench', 'scripts/benchmark-classification-clients.py')
bench = importlib.util.module_from_spec(spec)
spec.loader.exec_module(bench)
for repeat in range(3):
    names = ('local', 'arrow') if repeat % 2 == 0 else ('arrow', 'local')
    for name in names:
        path = Path(f'experiments/represented-local-families/{name}.lean.txt')
        print(json.dumps({'client': name, 'repeat': repeat} |
                         bench.run(Path.cwd(), path, timeout=30)))
PY
```

This reuses the retained runner's command profiler, with asynchronous elaboration
disabled, a 200,000-heartbeat per-command budget, recursion depth 512, and a
30-second whole-process timeout. Only unindented inclusive command traces are
summed. Raw counts are internal heartbeats (1,000 per budget unit); summing a
whole fixture is not a single-command budget measurement. Wall time includes
import loading and profiling overhead. These small fixtures measure this client
setup and observation; they do not predict all downstream elaboration costs.

The [raw measurements](../../experiments/represented-local-families/results.json)
retain all six results, diagnostics, commands, source and runner hashes, compiler
version, and dependency revisions. They were taken in a coordinated quiet window
after the concurrent #656 audit, against base
`b58619bd3bae3ed518469dc13d6d58c915ff9e89` plus the new implementation whose
individual hashes are recorded there. No source or dependency input changed
during the measurements.

| Fresh client setup | Internal heartbeats, each of three runs | Whole-process seconds, min / median / max |
| --- | ---: | ---: |
| Represented local data | 5,460,599 | 1.015 / 1.055 / 1.114 |
| Direct coherent arrow diagram | 315,806 | 0.933 / 0.974 / 1.059 |

All runs passed at the stated bounds. The direct constructor used less measured
elaboration work in this root-only case. The process times include common import
and profiler costs, and three repetitions do not establish a general wall-time
advantage. Keep direct clients for convenient arrow presentations; use the new
interface when the supplied mathematics is already local functors and coherent
restriction isomorphisms. No replacement of the established decoder or direct
presentation is needed.
