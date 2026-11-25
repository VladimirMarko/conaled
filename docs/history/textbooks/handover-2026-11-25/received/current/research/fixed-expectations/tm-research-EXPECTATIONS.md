# Fixed primitive-transition expectations

These expectations precede the proposed Lean implementation. They are calculated
from the pinned Mathlib TM1to0.trAux definition, which emits one TM0 move/write
per target step and folds loads/branches into that finite transition choice.
Every terminal goto or halt emits an additional write of the current symbol.

| Case | Actual primitive sequence | Count | Endpoint |
|---|---|---:|---|
| TM1 goto | write current symbol | 1 | Same tape/registers; next programme body selected. |
| One outward scan step | move right; write current symbol | 2 | Same go label/registers, head one cell right, no content change. |
| Empty push action | write pushed symbol; move right; write current symbol | 3 | ret label, same registers, new selected symbol retained. |
| Empty pop at bottom | write current symbol | 1 | ret label, action-updated registers, unchanged tape. |
| Empty peek at bottom | move left; move right; write current symbol | 3 | ret label, action-updated registers, unchanged tape. |

For the empty peek, its first primitive configuration has head at the cell left
of the bottom marker. The second returns to the bottom and the third selects
the ret programme. Native TM1 boundary states alone omit the left excursion.

The chosen source for the stack cases has one Unit-indexed Boolean stack,
Unit source labels, Boolean registers, and a halting source programme. The go
continuation is halt. The outward case starts with selected stack [false]; the
three action cases start with an empty selected stack. Push inserts true.
Peek/pop set the register to whether the observed optional symbol is none, so
empty actions change false to true. Complete tape and control endpoints are
retained in the proposed case statements.

These five fragment cases start at explicitly supplied primitive body/go
configurations. The chosen source programme itself is halt-only, so its
default execution does not reach the action go states used to inspect the
translation. They test the generic simulator's actual local bodies; they do
not assert genuine-init reachability for that halt-only programme. The
two-label whole-run case below separately consumes an actual source run, and
the controller consumer uses its genuine-init theorem.

These exact counts describe the constructed native TM0 iteration, not a new
first-arrival minimality theorem. A goto self-loop illustrates why equal start
and end configurations alone do not identify an execution count.

An additional independently specified whole-run case uses Boolean labels:
false jumps to true, and true executes halt. Registers start true and the tape
is arbitrary. The source takes two native TM1 transitions to a live halted
configuration. The primitive translation writes the current symbol for the
goto, then writes it again for halt: exactly two transitions preserve the
entire tape and reach the translated live halt; only transition three returns
outer none. The syntax bound is one at either source label, so the generic
finite-run theorem must also supply a bound of two for this actual source run.

No compiler has checked the new primitive files while whole139 owns compilation.
