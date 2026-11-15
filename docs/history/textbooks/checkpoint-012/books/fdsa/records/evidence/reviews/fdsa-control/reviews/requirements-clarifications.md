# Requirements clarifications

## 2026-11-02 — Triage metadata correction

FDSA-XB01 and FDSA-APP-C live tickets use canonical triage `ready-for-agent`;
workflow progress is recorded separately in `State`. The temporary
`in-progress` triage string did not belong to conaled's five canonical roles.
The frozen original AppendixC requirements remain byte-for-byte intact with
their recorded hash. This correction changes tracker metadata only, not any
formal obligation, validation gate or acceptance scope.
