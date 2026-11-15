#!/usr/bin/env bash
set -euo pipefail
cd /tmp/conaled-314-320/317
direnv exec . ./check.sh --candidate HEAD > /tmp/conaled-314-320/reviews/317-candidate-check.log 2>&1
direnv exec . lake env python3 scripts/test-proof-audit.py > /tmp/conaled-314-320/reviews/317-audit-regressions.log 2>&1
direnv exec . ./check.sh --verify-candidate HEAD > /tmp/conaled-314-320/reviews/317-verify-candidate.log 2>&1
cp .lake/verification.json /tmp/conaled-314-320/reviews/317-verification.json
git status --short > /tmp/conaled-314-320/reviews/317-final-status.log
