# Local ticket tracker

This tracker replaces GitHub operations solely for the PFDS task, by explicit user instruction. `tickets.json` is authoritative for status, dependencies and acceptance. Numbers 10000 and above are local; commit suffixes such as `(#10002)` refer here.

Status values: `open`, `in_progress`, `blocked`, `review`, `accepted`. A chapter is `accepted` only after its full inspected source scope, formal statements, connected examples, required isolated candidate validation and both independent review axes pass on the same candidate. Source coverage that has not been inspected stays explicit.

Review records live in `../reviews/` outside the source diff and preserve all rounds and unresolved findings. Each record pins the stable base, exact candidate, requirements version, validation inputs, Standards outcome and Spec outcome. Do not close source/access/toolchain blockers by narrowing the user's requested scope.

The dependency chain enforces chapter order. #10000 is cross-cutting setup; additional cross-cutting tickets may be added with an explicit justification and dependent chapters. Publisher/author sources are references, not a license to redistribute full manuscripts in checkpoints.
