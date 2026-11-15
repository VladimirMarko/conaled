#!/usr/bin/env bash
set -euo pipefail
printf 'queued: '; date -u +%FT%TZ
flock /tmp/conaled-wave-20261115/build.lock taskset -c 0 nice -n 10 \
  direnv exec /home/vlad/Code/conaled bash -c '
set -euo pipefail
printf "lock acquired: "; date -u +%FT%TZ
export LEAN_PATH="$(lake env printenv LEAN_PATH):$PWD/trial"
lean -o trial/TrialTask.olean trial/TrialTask.lean
lean -o trial/AuthorSubmission.olean trial/AuthorSubmission.lean
lean trial/ExpectedInterface.lean
printf "finished: "; date -u +%FT%TZ
'
