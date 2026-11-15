#!/usr/bin/env bash
set -uo pipefail
attempt=$1
date -u +%FT%TZ > "trial/attempts/$attempt/timing.txt"
flock /tmp/conaled-wave-20261115/build.lock taskset -c 0 nice -n 10 direnv exec /home/vlad/Code/conaled bash -c '
set -euo pipefail
date -u +%FT%TZ
export LEAN_PATH="$(lake env printenv LEAN_PATH):$PWD/trial"
lean -o trial/TrialTask.olean trial/TrialTask.lean
lean -o trial/AuthorSubmission.olean trial/AuthorSubmission.lean
lean trial/ExpectedInterface.lean
' > "trial/attempts/$attempt/compiler.log" 2>&1
status=$?
printf 'exit_status=%s\n' "$status" >> "trial/attempts/$attempt/timing.txt"
date -u +%FT%TZ >> "trial/attempts/$attempt/timing.txt"
cat "trial/attempts/$attempt/compiler.log"
exit "$status"
