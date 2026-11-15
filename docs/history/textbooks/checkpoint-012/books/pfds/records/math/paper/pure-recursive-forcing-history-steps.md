# Executed histories and concrete suspension steps

Local10019; root-owned History, Simulation and Forcing modules and their
connected clients, within the existing implementation/review loop.

## Contracts and composition

BodyHistory retains an immutable address meaning and an actual unfinished
pure prefix from that meaning's isolated body start. ActiveHistories indexes
every raw memoize-frame occurrence separately and uses the corresponding
pure stack prefix before that index. It assumes neither distinct active
addresses nor future termination. ConfigRep additionally supplies aligned
raw/pure frame lists, related controls and represented memory; the history
predicate intentionally does not duplicate that structural relation.

World extension preserves the old meaning literally. Local keep/push/pop/
replace laws compose actual pure prefixes for every surviving occurrence.
Normal delivery closes the accumulated prefix into an Evaluates certificate.
Reentering an already active address adds one actual body-entry step to its
old prefix, yielding a strictly positive recurrence at exactly the same
code/effective-environment input. The established recurrence theorem then
excludes all finite pure results, including faults.

Forcing connects this bookkeeping to actual raw transitions. Delay performs
one allocation and installs the corresponding world meaning without executing
its body. Uncached forcing starts a zero-length new history and advances all
older histories, even when the address is already active. A cache hit obtains
the finite body witness from CellRep and expands it in n+1 pure transitions.
Normal memoize return constructs its certificate from the top past history,
then justifies the actual write. It does not require the current cell to remain
a thunk. Exceptional memoize return drops the frame without its own write.

These local laws need no primitive compatibility law because none invokes a
primitive. They do not assert the general raw execution correspondence or
code-domain preservation. Those remain separately owned obligations.

## Connected cases and statement review

The literal history has one actual past transition, followed by the isolated
delivery that produces the cache certificate. This witness is consumed by the
public actual memoization law. The recursive client uses its independently
checked14-transition preentry prefix, then takes the next actual body-entry
step. Both raw and pure before/after configurations are related, and the new
history deliberately retains two pending occurrences of address0. The result
is pure nontermination, not yet a claim about reachability of those complete
raw configurations or impossibility of raw completion.

The forcing clients use the general laws, not just independent reductions.
They retain a cyclic entry with an already pending address, a successful write
before an inner pattern rejects the result, a cache hit expanding a two-step
body certificate in exactly three pure transitions, and an exceptional exit
that leaves the thunk unchanged. Actual delay also allocates a second suspension
whose body is already known not to terminate, without running that body.

Statement review checked the index/take boundary shifts, literal world identity,
normal versus raised/fault observations, lack of current-thunk/first-write/
active-distinctness premises, and distinction between local actual steps and
the still-missing arbitrary finite execution theorem. Map performed a limited
read-only design/statement pass with no mismatch found; it is not either of
the independent acceptance review axes.

## Validation

- History/Simulation and all connected clients: first focused round GREEN,
  exit0,756jobs, unchanged recorded import/configuration inputs.
- Forcing's four force/cache cases and clients: first round GREEN, exit0,
  758jobs, unchanged inputs.
- Added actual delay law and nonterminating-body allocation client: second
  Forcing round GREEN, exit0,758jobs, unchanged inputs. Earlier cases retained.

Exact timestamps, hashes and logs are in session/validation under
suspension-pure-history-r1 and suspension-pure-forcing-r1/r2. No proof budget,
linter, axiom or admission exception was introduced. These focused results
are not complete-candidate build/audit/review acceptance.
