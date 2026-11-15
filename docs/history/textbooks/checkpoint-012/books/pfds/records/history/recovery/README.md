# conaled / PFDS checkpoint 057

This checkpoint preserves unfinished work. Read session/STATUS.md for exact
accepted scope and outstanding gates. It is not a proof-completion certificate.

## Restore after losing the original workspace or chat

1. Extract this archive into any directory.
2. Run `python3 restore.py /absolute/path/to/a/NEW-directory` with Python 3.12+
   and Git available. The script verifies all member hashes, obtains the exact
   public upstream baseline from GitHub and restores all task-owned work.
   For offline source recovery, add `--base-repository /path/to/local/conaled`
   using a repository containing the exact baseline below. A restored original
   checkpoint044 also supplies it. No moving upstream branch is substituted.
3. In the new directory read `session/requirements/REQUEST.md`,
   `session/STATUS.md`, `session/tracker/tickets.json`, and the latest review and
   environment records. They preserve authorization and outstanding work.
4. Read `conaled/AGENTS.md` and `session/environment/RECOVER-INTEGRATION.md`.
   The complete supplied unified native-kit archive is included under
   `session/environment/`. Follow the current runbook to restore the exact
   Lean/Lake setup, all pinned dependencies and their cache without Nix.
   The source, proof, review and candidate-acceptance requirements still apply.
5. Resume the earliest unaccepted chapter. Retain both independent review
   axes, full source scope and the required candidate build/proof audit.

Git HEAD: `76d77a107deb37c30e0b061c30b03a3f8c6aa12c`; branch: `pfds/local`. All task Git commits and local refs are
in `repository.bundle`; staged and working changes are separate binary patches.
The declared source prerequisite is `7c1b4a3fd55f9aeeab3fe7850e2d20000836bfcd` from `https://github.com/VladimirMarko/conaled.git`.
The unchanged upstream baseline and unrelated upstream history are not copied
into each recovery archive. Source recovery requires that exact public commit
or a local repository containing it; the checkpoint is not an offline copy of
all third-party inputs. Current formal candidates and their complete review
bases are retained. Historical remote-tracking branches unrelated to this task
are omitted; this is recovery packaging, not a source change.
Reproducible toolchains/build caches and third-party manuscripts are excluded.
All task records in `session/` are preserved regardless of extension or size,
apart from the explicitly excluded transfer helpers, downloaded tool inputs,
Python caches and the reproducible Nix installer. Git-ignored repository files
are excluded unless listed in `session/checkpoint-includes.json`; keep required
validation evidence in `session/` or list it there explicitly.
Check source URLs in the research records or request the book from the user
when the needed pages are unavailable. No GitHub write is part of recovery.
