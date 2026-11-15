#!/usr/bin/env bash
set -u
cd /tmp/conaled-followups-orchestration/author-b
record=experiments/construction-observation-authoring/author-b
attempt=$1
cp Examples/ConstructionObservationAuthorB.lean "$record/$attempt.lean"
(
 date -u +%FT%TZ
 echo 'COMMAND: direnv exec . lake env lean Examples/ConstructionObservationAuthorB.lean'
 direnv exec . lake env lean Examples/ConstructionObservationAuthorB.lean
 status=$?
 echo "EXIT: $status"
 date -u +%FT%TZ
 exit "$status"
) > "$record/$attempt.log" 2>&1
status=$?
cat "$record/$attempt.log"
exit "$status"
