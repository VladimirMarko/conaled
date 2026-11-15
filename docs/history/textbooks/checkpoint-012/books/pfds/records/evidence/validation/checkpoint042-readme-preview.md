# conaled / PFDS checkpoint 042

This checkpoint preserves unfinished work. Read session/STATUS.md for exact
accepted scope and outstanding gates. It is not a proof-completion certificate.

## Restore after losing the original workspace or chat

1. Extract this archive into any directory.
2. Run `python3 restore.py /absolute/path/to/a/NEW-directory` with Python 3.12+
   and Git available. The script verifies all member hashes before restoring.
3. In the new directory read `session/requirements/REQUEST.md`,
   `session/STATUS.md`, `session/tracker/tickets.json`, and the latest review and
   environment records. They preserve authorization and outstanding work.
4. Read `conaled/AGENTS.md` and `session/environment/RECOVER-ENVIRONMENT.md`.
   The user permits the exact Lean/Lake setup without Nix. Follow that runbook
   to restore the verified toolchain, all pinned dependencies and their cache.
   The source, proof, review and candidate-acceptance requirements still apply.
5. Resume the earliest unaccepted chapter. Retain both independent review
   axes, full source scope and the required candidate build/proof audit.

Git HEAD: `76d77a107deb37c30e0b061c30b03a3f8c6aa12c`; branch: `pfds/local`. Full Git history and local refs are
in `repository.bundle`; staged and working changes are separate binary patches.
Reproducible toolchains/build caches and third-party manuscripts are excluded.
All task records in `session/` are preserved regardless of extension or size,
apart from the explicitly excluded transfer helpers, downloaded tool inputs,
Python caches and the reproducible Nix installer. Git-ignored repository files
are excluded unless listed in `session/checkpoint-includes.json`; keep required
validation evidence in `session/` or list it there explicitly.
Check source URLs in the research records or request the book from the user
when the needed pages are unavailable. No GitHub write is part of recovery.
