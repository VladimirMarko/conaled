# Optional Codex CLI model warning

The [approved configuration file](../../.agents/model-policy.json) is the source
of defaults for the [task policy](task-authority.md#model-eligibility-and-trials).
The optional [monitor](../../scripts/model-warning.py) checks each submitted
Codex CLI turn and displays a hook message when its status changes: 🔴 for a
configuration outside those defaults, ⚠ for unavailable current configuration,
and a recovery message when it returns to an approved configuration. The first
approved turn and repeated identical observations are quiet. This is an advisory
warning, not permission enforcement or an authentication system.

## Install for this checkout

From the repository's development shell, preview the merged configuration:

```sh
direnv exec . python3 scripts/model-warning.py install
```

Add `--write` to install it in this checkout's `.codex/hooks.json`. The installer
preserves existing hook entries and records absolute paths to this script, its
policy, and the Python interpreter running the installer. No global hook is
installed. Repeating the same installation is idempotent. Keep this local hook
configuration out of commits. If the checkout or interpreter moves, remove the
old monitor entry before installing the new one.

Start a new Codex CLI session in the checkout and review/trust the command in
`/hooks`. Codex skips untrusted hooks; an agent must not grant persistent trust
on the user's behalf. Review the generated command and script first. Changes to
hook definitions or scripts may require renewed trust. To uninstall, remove only
this monitor's `UserPromptSubmit` entry, preserving other hooks.

The installed command uses its recorded Python path, so an ordinary CLI session
does not need Python on its shell PATH or a per-turn `direnv` invocation. The
adapter uses POSIX file locking. Other clients can use the same approved
configuration data, but do not need this Codex integration.

## Evidence and diagnostics

The hook accepts JSON on stdin and emits only `systemMessage` JSON. It neither
blocks a turn nor supplies `additionalContext`. The hook's model, session and
turn must match the transcript's session identity and latest matching
`turn_context`; only that record supplies effort. Missing, mismatched or stale
metadata produces an unknown warning. The reader examines a bounded transcript
tail and never substitutes the configured default or an earlier turn's effort.

Latest observations are separate JSON files under
`~/.cache/conaled/model-warning` (or `$XDG_CACHE_HOME/conaled/model-warning`).
They include session, agent and turn identifiers, model, effort, status and
evidence, without prompts or conversation contents. Concurrent sessions use
separate records and repeated observations are serialized. These are diagnostic
observations, not an audit log or proof of approval. Inspect a saved hook input
without changing warning state:

```sh
direnv exec . python3 scripts/model-warning.py inspect < hook-input.json
```

`--state-dir` selects a separate diagnostic directory for tests or another setup.
Monitor failures warn and let work continue. If hooks are disabled, untrusted or
timed out, the script cannot provide coverage; check `/hooks` when no expected
warning appears.

## Scoped exceptions

An operator can represent an existing scoped approval using a local JSON file
passed to installation with `--exceptions /absolute/path/to/exceptions.json`:

```json
{"exceptions": [{"session_id": "exact-session-id", "agent_id": null,
  "model": "exact-model-slug", "effort": null,
  "expires_at": "2027-01-01T00:00:00Z", "reason": "Approved local trial"}]}
```

This example deliberately covers unknown effort for one model in one session;
use an exact effort string for a known configuration. All four identity and
configuration fields must match, and expiry must be in the future. A matching
exception has its own visible status, not ordinary approval. The file records a
human decision; the monitor cannot infer conversational approval or its task
scope. Remove an exception when its approved work ends, even if the session
continues. An exception neither changes repository-wide defaults nor authorizes
publication. Keep local exception files out of commits.

## Tested boundary

Codex CLI 0.161.0 runs `UserPromptSubmit` after the current turn context is written
and renders `systemMessage` in interactive terminal history. It does not promise
red UI chrome; the marker is part of the warning text. In this version,
`codex exec --json` omits those messages. Configured `PreModelRequest` hooks did
not run in the installed-runtime probe, so this adapter does not rely on them.
It checks submitted user turns, not every internal retry or delegated agent.
The monitor notices configuration changes at the next observed user turn.
Operators still select delegated configurations explicitly.

The [official hooks documentation](https://learn.chatgpt.com/docs/hooks) describes
hook trust and warns that transcript format is unstable. Runtime/version changes
can therefore produce unknown warnings; update the adapter from observed data
rather than guessing. Regression checks use the public commands:

```sh
direnv exec . python3 scripts/test-model-warning.py
```
