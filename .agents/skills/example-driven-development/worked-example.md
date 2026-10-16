# Worked example: composition order

Suppose the requested operation runs `f` first and then `g`. Before defining it,
work out a case: incrementing 3 gives 4, then doubling gives 8. Reversing these
operations gives 7, so this case distinguishes their order.

The expected proposition is:

```lean
example : pipeline (fun n : Nat => n + 1) (fun n => n * 2) 3 = 8 := by
  skip
  -- The connection to pipeline_apply is still missing.
```

This is a scratch obligation, not a completed declaration. Before `pipeline`
exists it exposes a missing interface; after the definition exists, the open
goal exposes the missing proof. Neither state belongs in a completed build.

Develop the operation and its public theorem, then connect the case:

```lean
def pipeline {α β γ : Type} (f : α → β) (g : β → γ) : α → γ :=
  fun x => g (f x)

theorem pipeline_apply {α β γ : Type}
    (f : α → β) (g : β → γ) (x : α) :
    pipeline f g x = g (f x) := by
  rfl

example : pipeline (fun n : Nat => n + 1) (fun n => n * 2) 3 = 8 := by
  calc
    pipeline (fun n : Nat => n + 1) (fun n => n * 2) 3 =
        (3 + 1) * 2 := pipeline_apply _ _ _
    _ = 8 := by rfl
```

The literal 8 comes from the worked calculation. The first step uses the public
result; the last checks the arithmetic. Proving only `(3 + 1) * 2 = 8` would
leave the connection to `pipeline` unexamined.

Statement review checks that the intermediate type is the output of `f` and
input of `g`, that the theorem applies to every input, and that the conclusion
runs the functions in the requested order. There are no extra hypotheses to
satisfy here. The general equation is definitional, so its proof alone does not
validate our choice of order; the independently chosen case helps do that.

If an earlier design reversed the order for endofunctions, keep the expected 8
and correct that design. Changing the expectation to 7 would abandon the
request. If `pipeline_apply` already exists, write the connected example
directly: an artificial red phase adds no evidence.

A next case should answer a new question, such as whether functions with
different input and output types compose. Add it when that use matters, then
retain both cases through changes to the implementation. In a real task, use
the repository's module placement, build, and proof audit for the retained cases.
