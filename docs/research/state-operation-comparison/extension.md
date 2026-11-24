# Changed-arity selection

The initial binary/unit interface and all three routes passed the focused build
before this selection. Their hashes are in [frozen-interfaces.sha256](frozen-interfaces.sha256).
The initial contract remains unchanged.

The next independently supplied operation is reversal on the pair carrier:
`(xs, unit) ↦ (xs.reverse, unit)`, with its independently checked involution law.
The helper route will use the existing tuple operation at the Unit index type;
the signature route will add a disjoint unary symbol and reuse the existing
open-equation transport theorem. Record added per-arity wrappers and term setup,
not just shared proofs. The original binary/unit files stay frozen.

For FIFO, supply tail separately on the pair carrier, use transported concatenation
with independently specified singleton states for enqueue, and preserve native
head observation. Prove all native command runs agree and retain the relational
symmetric-list simulation unchanged. Reversal itself is not claimed to be a FIFO
operation, and FIFO correctness is not inferred from arbitrary operation transport.
