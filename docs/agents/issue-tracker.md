# Issue tracker: GitHub

Issues and specs live in GitHub Issues for VladimirMarko/conaled.
Use the `gh` CLI from this clone, or pass
`--repo VladimirMarko/conaled` explicitly.

When placing new work or coordinating related issues, consult the
[workstream index and organization guidance](../../README.md#workstreams-and-shared-components).
Use its links to find existing scope owners and related efforts; keep task
acceptance criteria and dependencies in the issues.

## Operations

- Create: `gh issue create --title "..." --body-file <file>`.
  Write multiline bodies to a temporary file first.
- Read: `gh issue view <number> --json number,title,body,labels,comments`.
- List: `gh issue list --state open --json number,title,body,labels`.
  Add label filters as needed and paginate when all results are required.
- Update a body: `gh issue edit <number> --body-file <file>`.
- Comment: `gh issue comment <number> --body-file <file>`.
- Apply or remove labels: `gh issue edit <number> --add-label "..."`
  or `--remove-label "..."`.
- Close: `gh issue close <number>`.
- Link a child: `gh issue edit <parent> --add-sub-issue <child>`.
  If sub-issues are unavailable, add the child to a task list in
  the parent and put `Part of #<parent>` in the child body.

When a skill says "publish to the issue tracker", create a GitHub
issue. When it says "fetch the relevant ticket", read that issue.

GitHub issues and PRs share a number space. If a reference is
ambiguous, resolve its type before acting.

## Pull requests as a triage surface

**PRs as a request surface: no.**

## Wayfinding

For `/wayfinder`, use one issue labelled `wayfinder:map` for the
Notes, Decisions-so-far, and Fog sections. Link child tickets as
sub-issues and label them `wayfinder:<type>`, where type is
`research`, `prototype`, `grilling`, or `task`.

Represent blockers with GitHub native issue dependencies:
`gh api --method POST repos/{owner}/{repo}/issues/<child>/dependencies/blocked_by -F issue_id=<blocker-db-id>`.
Fetch the database ID with
`gh api repos/{owner}/{repo}/issues/<number> --jq .id`.
If dependencies are unavailable, record `Blocked by: #<number>`
in the child body.

Select the first open, unassigned child in map order whose blockers
are all closed. Claim it with
`gh issue edit <number> --add-assignee @me`.
On resolution, comment with the result, close the child, and add
a summary and link to the map's Decisions-so-far section.
