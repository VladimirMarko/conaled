# All-outcome continuation decomposition —10019 prerequisite

This adds source-specific composition/decomposition laws over the existing
Core.Machine and Progress.Evaluates, without changing its step function or
existing Continuation APIs. The actual pure-language bridge must still be
implemented separately.

## Independently selected cases and statement boundary

An allocating body creates ref0=5, then attempts to read integer0 as an address.
It faults after10 transitions, retaining the allocation. Appending a source
exception handler cannot catch this machine fault or undo its memory.

In the second case, the body is integer7 and returns normally in2 transitions;
its caller is a read frame. The whole run faults in2 transitions, with a1-step
caller run replacing the body's final delivery: (2-1)+1=2. Therefore a final
whole-run fault must not imply that the isolated body faulted.

The public all-outcome split has exactly these branches: an isolated stuck run
with the same answer/count, or an isolated delivered boundary plus a residual
caller run and the exact existing subtraction-of-one count equation. No
termination/type-safety/nonreentrancy premise is introduced. A forward stuck
composition law supplies the first connected case; the all-outcome split and
finite-run uniqueness recover the normal body in the second.

## Development evidence

Round1 ended exit1 with unchanged source hashes. The only compiler diagnostic
was a missing explicit stuck-boundary argument to the forward induction
hypothesis; the all-outcome split itself produced no errors. Round2 supplies
that argument without changing any statement or client expectation. Focused
client success and whole-candidate acceptance remain required.

Round2 passed with unchanged recorded inputs, including both fault clients.
This verifies only the continuation prerequisite, not pure nonreentrancy or
the still-unwritten raw-to-pure representation/occurrence bridge.
