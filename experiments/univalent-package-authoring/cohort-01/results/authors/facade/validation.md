
Copy `task.md`, `TrialTask.lean` and `ExpectedInterface.lean` to an author's
isolated `trial/` directory. The author writes `trial/AuthorSubmission.lean`
with the prescribed namespace and declarations. `ExpectedInterface.lean`
intentionally imports that initially absent submission. Its failure before a
submission exists is not a fixture defect or an integrated build failure.

Run from the root of the author's prepared checkout, retaining each attempted
source and complete log before the next edit:

```sh
flock /tmp/conaled-wave-20261115/build.lock taskset -c 0 nice -n 10 \
  direnv exec /home/vlad/Code/conaled bash -c '
set -euo pipefail
export LEAN_PATH="$(lake env printenv LEAN_PATH):$PWD/trial"
lean -o trial/TrialTask.olean trial/TrialTask.lean
lean -o trial/AuthorSubmission.olean trial/AuthorSubmission.lean
lean trial/ExpectedInterface.lean
'
```

The direct arm imports `TrialTask` and specific accepted baseline modules. The
facade arm may additionally import its facade. Keep default heartbeat limits;
record any requested change as an environment/interface intervention rather
than silently tuning one arm. No admissions, new axioms or unsafe shortcuts
are permitted. Both authors have identical tools, copied warm project outputs
and shared pinned dependency artifacts; record deviations, host load, queue
waits and interruptions. There is no inherited token cap, and wall duration
is not a performance ranking.

The declaration checker tests the public boundary, not all acceptance content.
After submission, the coordinator substitutes only the submission import in the
same frozen private oracle body. It checks full records, universal observations,
both endpoints, section decoding/recovery, path recovery and rejection, then
reviews native API dependencies. Successful trial artifacts receive a separate
integrated validation/audit before final publication. The current two integrated
facade modules and their public calibration are covered by repository acceptance;
the experimental task/checker are covered by focused private replay, not by the
integrated library audit.
