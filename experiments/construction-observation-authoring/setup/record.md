# Trial setup

Public interface revision: `5e5b03987d1f7ab23ea720561147e56319a85f51`.
Frozen protocol commit: `21eaedeed1c78f58437b05a0197b12bcc386c9bb`.
Author worktrees start at the protocol commit, with identical source and pins.
Two fresh agents were spawned with `fork_turns=none`, without model or reasoning
overrides. Neither designed the selected interfaces. Author A and B received the
same protocol and the respective counterbalanced order. They were prohibited
from reading other authors or private coordination/reference records.

Each has a 15-minute cap measured from its own recorded start. Available metadata
is the inherited agent configuration and the repository toolchain; exact serving
model revision, configured reasoning effort, token usage and pricing are not
exposed by these tools. No paid external model call or nested author agent was
used. These trials do not compare capability tiers.

Each checkout has an independent copied `.lake` cache. Both focused setup builds
of `Examples.IndexedCompositional` and `Examples.ObservationExtension` passed
(871 jobs), before dispatch. One coordinator setup command was attempted before
the cache-copy/direnv-allow sequence completed and was rejected by direnv. It was
rerun after setup and passed; no author encountered it, so it is not an author
failure. Frozen Lean version is 4.35.0. Other project builds ran concurrently;
wall times include uncontrolled host contention and are not productivity ratios.

Authors are assigned only their own Examples source and artifact directory, with
no library/import changes or commits. Their compiler attempts are retained
before corrections. The coordinator will check successful sources, retain failed
attempts outside integrated imports, and run the integrated proof audit. Shared
library interface/documentation changes during the trial are prohibited; a
justified correction would require a new frozen revision and rerun.
