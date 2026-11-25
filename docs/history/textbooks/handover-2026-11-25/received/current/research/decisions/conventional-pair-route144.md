# Prospective paid delimiter-input route

Root design note, after the actual ordinary-I/O research and primary-source
reading. This is a route to investigate, not installed source, a checked
transducer, an NP theorem, or a qualification change. The fixed Boolean raw
decider currently under development remains a useful separate milestone.

## The representation obligation

Cook's official checking-relation convention starts the machine on a delimited
pair, while the actual current verifier consumes the strict Boolean frame.
The native TM0 model also separates movement and stationary writes. Both
differences should be connected by actual paid machine constructions before
claiming that chosen conventional definition. Source reference and actual
reading limits are in native-decider-design-decision143.md.

An input length equality or an arbitrary whole-word encoding field cannot
replace either execution. The existing short witness and exact binary language
correspondence must remain independent of the chosen machine.

## A source-machine route for the literal delimiter

Use the fixed three-letter input alphabet `Option Bool`: `some false`,
`some true`, and delimiter `none`. The literal pair is

    input.map some ++ [none] ++ certificate.map some.

Within the actual multiplexed working alphabet, even the delimiter is a
nonblank letter: its designated track contains `some none`, whereas a blank
track contains outer `none`. A Boolean output can use the fixed letter
`MarkedInput.symbol inputIndex (some answer)`.

The existing FrontEndStreamMachine.Statement already permits caller bodies to
use the full indexed alphabet, labels and registers. A concrete finite caller
can therefore implement preprocessing without changing the existing checker:

- Choose one finite caller-store index with alphabet `Option Bool`, a finite
  caller-label family for prefix/certificate/reverse/reject-drain phases, and
  a finite user register capable of holding the actual popped option.
- Define a new FinTM2 package with the same full program and Boolean fuel
  output index, but with the real main label at the caller prelude and the
  real input index at that caller store. Its defaults must use those fields.
- Pop the literal input. Before the unique delimiter, append the two bits
  `false,b` for each bit b to a reverse work stack; at the delimiter append
  `true`; afterwards append each certificate bit once. A repeated delimiter
  or missing delimiter must reject through an actual finite control path.
- Reverse the work stack into the existing framedRaw store. On success, prove
  that the complete configuration equals the old controller's actual
  initializer on `BitPairFraming.frame input certificate`: the same program,
  old main label, initial registers, and every other store empty.
- On malformed input, consume the remaining input and clear the actual work
  stack before entering a known rejecting controller start or a proved clean
  rejecting path. Do not assume that the old controller clears arbitrary
  caller stores; it preserves caller context and that is a real obligation.
- The old genuine-init controller theorem can then supply its exact execution
  from the proved handoff configuration. The new package's literal halt agrees
  because its output index and initial register value are the same.

All phases, callbacks and stores must be chosen before the input. If the
preprocessor temporarily changes the user register, restore the supplied
initial value at handoff; no old default may be substituted silently.

For raw delimiter input length N, the constructed Boolean frame is bounded
by `2*N+1`; for a valid pair its exact length remains `2*I+C+1`. A source
prelude with a proved `c*N+c` bound and real prefix occupancy at most
`2*N+1` would compose with the existing quadratic source controller bound.
The generic stack-to-tape/primitive compiler then gives a polynomial genuine
native run on the three-letter ordinary input. These are proposed bounds,
not yet a frozen list of exact case counts; the actual finite statement
design and independent small traces must precede compiler feedback.

The complete singleton-output result should be derived from the composed
literal halt, then use the actual ordinary reflection/prelude/emitter bridge.
This route pays for encoding inside the machine, instead of assuming a free
conversion from a delimiter to the existing strict frame.

## Native actions to a combined print-and-move model

A separate reusable finite-state adapter can keep a normal copy of each native
control and an intermediate return copy. At a normal state:

- A native move prints the currently read symbol and performs that move once.
- A native write prints the new symbol and moves right, then the return state
  preserves the next symbol and moves left to the next normal state.
- A real native halt observes the fixed Boolean output letter and enters the
  designated accept/reject state with a fixed final transition.

At normal simulation boundaries the entire physical tape is the same, not
merely its output head. The intended live-run bound is at most `2*T`, followed
by one accepting/rejecting transition. Prove each actual step and finite-prefix
composition; do not assert the bound solely from this prose. The intermediate
right excursion is a real visited cell and belongs in the space accounting.

The actual finite carriers and start/blank/input injections must be preserved.
Existence of a finite transition table is distinct from exporting a numerical
executable enumeration. The controller's native transition is already an actual
definition; this adapter must retain that connection.

## Remaining class details

A future generic decider interface should support a fixed finite input alphabet
and a separate fixed Boolean output injection when used for this three-letter
relation. Avoid duplicating the current Boolean-only contract without an
explicit relationship. The certificate definition uses the literal delimiter
protocol and the independently established `BinaryYes` language.

The witness bound is already the exact power `I^2`, including the small
instances. For a conventional time form `N^k+k`, any conversion from an actual
Nat polynomial must be proved at N=0 and N=1 as well as larger inputs. One
possible arithmetic route uses the coefficient sum S and degree d, bounding
evaluation by `S*N^d` for N at least1 and absorbing S into `N^S` for N at least2;
choose k large enough for the two small cases. This is not yet a checked lemma.

An independent nondeterministic-machine equivalence is unnecessary only if
the selected target is explicitly the conventional checking-relation
definition and the applicable adapters above are actually supplied. No public
NP name, completeness claim, exact diameter result or textbook row closure
follows from the present design note.
