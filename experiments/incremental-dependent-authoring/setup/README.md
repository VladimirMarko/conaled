# Author handoff preparation

These coordinator scripts prepare the two public source closures for #357.
They do not generate a mathematical task or a solution. Task design and author
work have separate records.

`prepare.py` takes a repository, frozen revision, one or more module entrypoints,
a validated artifact donor, and new destination and provenance paths. It exports
the recursive local import closure and checks that every source byte matches the
donor. Each handoff gets independent project artifacts and a private copy of the
pinned dependency directories. No project Git metadata or history is copied.
The source allowlist excludes all other project modules, including other-arm
sources. Dependency source and cached artifacts remain available in `.lake/packages`.

`freeze.py` adds public overlays and writes `public-manifest.json`, the input
format used by the unchanged `experiments/dependent-author-trial/check_attempt.py`.
An overlay cannot replace an exported input. Any additional specification module
must have a compiled output before freezing. The coordinator supplies the common
protocol, task specification, arm-specific guidance and author instructions.
The final manifest hashes every public file and names every allowed local import.

The attempt wrapper checks public inputs before and after each run, archives the
submitted bytes, command arguments, timestamps, diagnostics and hashes, and
rejects imports outside the handoff and pinned toolchain. It is an experimental
access contract, not an operating-system sandbox. Authors are instructed not to
inspect outside their handoffs; the environment does not technically prevent it.

Preparation validation uses unrelated `True` and `False` examples to check the
wrapper's success and failure records. Those examples are setup evidence, not
measured author attempts. Coordinator provenance records must be kept outside
the public handoffs and preserved with the experiment's final evidence. Neither
script copies another author's work or exposes a coordinator solution.

`environment_index.py` creates a fresh Git index containing only the public
manifest and its listed files. It refuses commits and remotes. This gives Nix a
small tracked flake input without copying `.lake` into the store. It does not
fetch or retain the source project's history. Run it again after a coordinator
re-freeze, before dispatch; do not change inputs during author work.

For the public overlay, copy `public-common/` and the appropriate
`public-baseline/` or `public-candidate/` into the prepared handoff, preserving
relative paths. Compile `Examples/IncrementalDependentTrialSpec.lean` with
`lake env lean -o .lake/build/lib/lean/Examples/IncrementalDependentTrialSpec.olean`
followed by its source path, under the pinned environment. Then run `freeze.py`
without `--overlay`, followed by `environment_index.py`. A preliminary manifest
and index can initialize the shell before adding the Spec; archive that manifest
outside the handoff before the final freeze.

`smoke.py` imports the arm's entrypoints and the common Spec, checks `True`, then
checks a deliberately invalid proof of `False`. It expects wrapper statuses
`lean-passed` and `lean-failed`, with verified public inputs before and after both
runs. It moves the setup-only attempts and complete wrapper archives outside the
handoff so authors begin with an empty `attempts/` directory.
