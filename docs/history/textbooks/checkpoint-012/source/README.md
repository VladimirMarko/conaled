# Exact mathematical source and history

`repository.bundle` is a complete, prerequisite-free Git source store for the
three recovered projects. It contains their Lean, committed mathematical notes,
original review bases, accepted versions and unfinished branches. It is not an
incremental patch requiring a previous checkpoint. The original source histories
were consolidated without changing their commits, trees or blob bytes.

`refs.json` is the sole ref/role registry. Original names are preserved as
metadata and mapped into `refs/checkpoint/<book>/...`, so similarly named refs
from different projects cannot collide. The two shared baseline advertisements
are retained alongside the 5 VFA, 79 FDSA and 45 PFDS original refs.

The `main` and `candidate` roles can differ. In particular, PFDS's latest
mathematical candidate is not its original main HEAD. All FDSA Chapter 4 draft
branches remain present even though the default FDSA role selects its historical
accepted main. `saved-worktrees.json` retains the nine FDSA worktree views.

Recover this store through the root RESUME guide. The recovered directory contains
`repository.git` and detached book candidates under `worktrees/`. To inspect an
original branch, use the exact stored ref in `refs.json` with ordinary `git show`
or `git log` against that bare store. Do not move the frozen imported refs.

Some loose historical records are byte-identical to Git blobs and therefore have
one owner here. Their compact record maps name the exact `git_blob`; after source
recovery, `git --git-dir /recovered/repository.git cat-file blob OBJECT_ID` returns
those bytes. Range aliases and reconstructed chapter inventories are documented
inside each book's frozen records, with no external checkpoint dependency.

The four preexisting archive blobs are in the original baseline tree itself.
Their exact identities are fixed by policy and included once in this Git store.
Removing them would break the complete original Git tree/commit identities.
They do not authorize new archived payloads. Compiler installations, Mathlib
checkouts, `.lake` outputs and downloaded runtimes are not bundled here.

Git integrity and byte preservation do not establish a new Lean build, a reviewed
mathematical statement, book completion or integration acceptance. The separate
book STATE files preserve those boundaries.
