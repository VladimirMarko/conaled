# Canonical circuit modules and selected Core 2 execution

This unit lowers Boolean circuits to inspectable, memory-free WebAssembly module
syntax and proves complete closed invocation in a transcription of the reachable
Core 2 rules. It composes that result with the existing first-order frontend,
finite-sum lowering, canonical word bridge and explicit-state programs. It is the
formal unit of [#488](https://github.com/VladimirMarko/conaled/issues/488);
binary production and external execution remain open.

The standard is Core 2.0, tag `v2.0.0`, WebAssembly/spec revision
`05ca4182176763112561ae20153975c12bd689e4`. The links below name exact source
anchors at that revision. This is a reviewed transcription, not an imported
full-standard mechanization. Lean checks the stated rules and their consequences;
faithfulness of those rules to the published standard remains the explicit
specification boundary approved for #488.

## Fragment and public entry

`Applications/Wasm/Circuits.lean` interprets the existing raw `Circuit` syntax
through `FirstOrder.Target`. Routing aliases references. Each gate writes one
fresh local. Pairing evaluates both components with disjoint fresh ranges;
composition feeds the first output references to the second. The generated body
contains only `i32.const`, `local.get`, `local.set`, `i32.eqz`, `i32.and`, `i32.or`
and `i32.xor`. Source words use the unchanged #509 Boolean circuit route.

`Module` has one function type, one function and one export named `run`. It has
no imports, start function, memory, tables, globals or segments. Its parameters
and results are finite i32 lists; multiple results and zero results are allowed.
Parameters precede scratch locals. Unit contributes no ABI slots, products
concatenate left then right, and each Boolean is i32 zero or one.

`ABI.decode_iff` states that raw typed-value decoding succeeds exactly on the
complete canonical encoding. `ABI.decodeSum_iff` also checks every inactive
payload and nested tag using the existing finite-sum decoder. Wrong arity,
non-i32 values and noncanonical Boolean words fail admission. The bare Wasm
export does not perform that Boolean check: `externalInvoke` checks standard
argument types, while the eventual host adapter must apply canonical decoding
before starting a transition.

`Module.validate` is an executable validator for the selected uniform-i32 module
class. Its soundness theorem produces the static typing judgment. It checks local
bounds, stack effects and result arity; module structure and export index zero are
fixed by the inspectable constructor. `Module.withinLimits` additionally checks Nat
counts against an explicit `Limits` profile and u32 bounds before any narrowing.
The default profile permits 1,024 parameters, 1,024 results, 65,536 total locals
and 1,048,576 instruction entries. These are declared engineering limits, not
engine requirements or measured capacities. Binary section/vector lengths and
actual output buffers remain obligations of the later encoder unit.

## Rule correspondence

| Standard obligation | Pinned anchors | Local transcription |
| --- | --- | --- |
| Values, bit patterns and signatures | [syntax-valtype](https://github.com/WebAssembly/spec/blob/05ca4182176763112561ae20153975c12bd689e4/document/core/syntax/types.rst#L102), [syntax-int](https://github.com/WebAssembly/spec/blob/05ca4182176763112561ae20153975c12bd689e4/document/core/syntax/values.rst#L47), [syntax-val](https://github.com/WebAssembly/spec/blob/05ca4182176763112561ae20153975c12bd689e4/document/core/exec/runtime.rst#L16), [syntax-functype](https://github.com/WebAssembly/spec/blob/05ca4182176763112561ae20153975c12bd689e4/document/core/syntax/types.rst#L143) | `Value`, `ValueType`, `FuncType`; arbitrary finite result lists and preserved non-i32 values. |
| Numerical equations | [op-ieqz](https://github.com/WebAssembly/spec/blob/05ca4182176763112561ae20153975c12bd689e4/document/core/exec/numerics.rst#L551), [op-iand](https://github.com/WebAssembly/spec/blob/05ca4182176763112561ae20153975c12bd689e4/document/core/exec/numerics.rst#L388), [op-ior](https://github.com/WebAssembly/spec/blob/05ca4182176763112561ae20153975c12bd689e4/document/core/exec/numerics.rst#L412), [op-ixor](https://github.com/WebAssembly/spec/blob/05ca4182176763112561ae20153975c12bd689e4/document/core/exec/numerics.rst#L424) | `eqz`, `BinOp.eval`; i32 zero-test and BitVec bitwise operations. Boolean canonicality is a separate ABI property. |
| Static instruction rules | [valid-const](https://github.com/WebAssembly/spec/blob/05ca4182176763112561ae20153975c12bd689e4/document/core/valid/instructions.rst#L109), [valid-binop](https://github.com/WebAssembly/spec/blob/05ca4182176763112561ae20153975c12bd689e4/document/core/valid/instructions.rst#L137), [valid-testop](https://github.com/WebAssembly/spec/blob/05ca4182176763112561ae20153975c12bd689e4/document/core/valid/instructions.rst#L151), [valid-local.get](https://github.com/WebAssembly/spec/blob/05ca4182176763112561ae20153975c12bd689e4/document/core/valid/instructions.rst#L659), [valid-local.set](https://github.com/WebAssembly/spec/blob/05ca4182176763112561ae20153975c12bd689e4/document/core/valid/instructions.rst#L678), [valid-instr-seq](https://github.com/WebAssembly/spec/blob/05ca4182176763112561ae20153975c12bd689e4/document/core/valid/instructions.rst#L1515), [valid-expr](https://github.com/WebAssembly/spec/blob/05ca4182176763112561ae20153975c12bd689e4/document/core/valid/instructions.rst#L1568) | `InstrTyped`, `CodeTyped`; local type lookup, typed operand suffixes and sequencing. |
| Closed module validity | [valid-functype](https://github.com/WebAssembly/spec/blob/05ca4182176763112561ae20153975c12bd689e4/document/core/valid/types.rst#L84), [valid-func](https://github.com/WebAssembly/spec/blob/05ca4182176763112561ae20153975c12bd689e4/document/core/valid/modules.rst#L12), [valid-export](https://github.com/WebAssembly/spec/blob/05ca4182176763112561ae20153975c12bd689e4/document/core/valid/modules.rst#L322), [valid-module](https://github.com/WebAssembly/spec/blob/05ca4182176763112561ae20153975c12bd689e4/document/core/valid/modules.rst#L497) | `Module.Valid`, `Module.validate_sound`, `assemble_valid`; one type/function/export, all other sections empty. `Module.withinLimits` adds count limits. |
| Ordinary reductions | [exec-const](https://github.com/WebAssembly/spec/blob/05ca4182176763112561ae20153975c12bd689e4/document/core/exec/instructions.rst#L46), [exec-binop](https://github.com/WebAssembly/spec/blob/05ca4182176763112561ae20153975c12bd689e4/document/core/exec/instructions.rst#L85), [exec-testop](https://github.com/WebAssembly/spec/blob/05ca4182176763112561ae20153975c12bd689e4/document/core/exec/instructions.rst#L115), [exec-local.get](https://github.com/WebAssembly/spec/blob/05ca4182176763112561ae20153975c12bd689e4/document/core/exec/instructions.rst#L1015), [exec-local.set](https://github.com/WebAssembly/spec/blob/05ca4182176763112561ae20153975c12bd689e4/document/core/exec/instructions.rst#L1035) | `Step.get/set/eqz/binary`; `Instr.admin` translates const to an administrative value, with no invented const reduction. |
| Administrative context | [syntax-instr-admin](https://github.com/WebAssembly/spec/blob/05ca4182176763112561ae20153975c12bd689e4/document/core/exec/runtime.rst#L518), [syntax-config](https://github.com/WebAssembly/spec/blob/05ca4182176763112561ae20153975c12bd689e4/document/core/exec/runtime.rst#L613), [syntax-ctxt-eval](https://github.com/WebAssembly/spec/blob/05ca4182176763112561ae20153975c12bd689e4/document/core/exec/runtime.rst#L637), [exec-instr-seq-enter](https://github.com/WebAssembly/spec/blob/05ca4182176763112561ae20153975c12bd689e4/document/core/exec/instructions.rst#L2846), [exec-instr-seq-exit](https://github.com/WebAssembly/spec/blob/05ca4182176763112561ae20153975c12bd689e4/document/core/exec/instructions.rst#L2860) | `Admin`, `Context`, `Step.context/label`; value-only prefixes and pending suffixes, including nested labels. |
| Invocation and return | [exec-invoke](https://github.com/WebAssembly/spec/blob/05ca4182176763112561ae20153975c12bd689e4/document/core/exec/instructions.rst#L2898), [exec-invoke-exit](https://github.com/WebAssembly/spec/blob/05ca4182176763112561ae20153975c12bd689e4/document/core/exec/instructions.rst#L2941), [default-val](https://github.com/WebAssembly/spec/blob/05ca4182176763112561ae20153975c12bd689e4/document/core/exec/runtime.rst#L51) | `Step.invoke/frame/inFrame`; parameter order, default locals, frame and empty-continuation function label, result arity and frame exit. |
| Store representation and allocation | [syntax-store](https://github.com/WebAssembly/spec/blob/05ca4182176763112561ae20153975c12bd689e4/document/core/exec/runtime.rst#L89), [syntax-moduleinst](https://github.com/WebAssembly/spec/blob/05ca4182176763112561ae20153975c12bd689e4/document/core/exec/runtime.rst#L196), [syntax-funcinst](https://github.com/WebAssembly/spec/blob/05ca4182176763112561ae20153975c12bd689e4/document/core/exec/runtime.rst#L230), [alloc-func](https://github.com/WebAssembly/spec/blob/05ca4182176763112561ae20153975c12bd689e4/document/core/exec/modules.rst#L162), [alloc-module](https://github.com/WebAssembly/spec/blob/05ca4182176763112561ae20153975c12bd689e4/document/core/exec/modules.rst#L433), [extend-store](https://github.com/WebAssembly/spec/blob/05ca4182176763112561ae20153975c12bd689e4/document/core/appendix/properties.rst#L643) | `Store.embed/extend/reconstruct`, `Module.instantiate`; old entries and fields preserved, fresh numeric address at the old function-list length. |
| External entry | [exec-instantiation](https://github.com/WebAssembly/spec/blob/05ca4182176763112561ae20153975c12bd689e4/document/core/exec/modules.rst#L589), [exec-invocation](https://github.com/WebAssembly/spec/blob/05ca4182176763112561ae20153975c12bd689e4/document/core/exec/modules.rst#L755), [syntax-exportinst](https://github.com/WebAssembly/spec/blob/05ca4182176763112561ae20153975c12bd689e4/document/core/exec/runtime.rst#L367), [syntax-externval](https://github.com/WebAssembly/spec/blob/05ca4182176763112561ae20153975c12bd689e4/document/core/exec/runtime.rst#L385), [valid-externval-func](https://github.com/WebAssembly/spec/blob/05ca4182176763112561ae20153975c12bd689e4/document/core/exec/modules.rst#L21), [valid-val](https://github.com/WebAssembly/spec/blob/05ca4182176763112561ae20153975c12bd689e4/document/core/exec/modules.rst#L89) | `Module.export_run`, `externalInvoke_generated`, `invoke_entry`; empty imports, named export, argument types and dummy frame. |
| Trap propagation and context order | [exec-instr-seq-enter](https://github.com/WebAssembly/spec/blob/05ca4182176763112561ae20153975c12bd689e4/document/core/exec/instructions.rst#L2846), [exec-invoke-exit](https://github.com/WebAssembly/spec/blob/05ca4182176763112561ae20153975c12bd689e4/document/core/exec/instructions.rst#L2941) | `Admin.trap`, `Step.trap/trapFrame`; the trap clauses occur under these administrative sections. `TrapActive.blocked` and `focus_context` prove selection order. |

## Arbitrary stores and caller contexts

`Store F O` retains arbitrary existing standard function instances in `F`,
including foreign bodies and host functions; `O` is the tuple of every remaining
store field. Instantiate `F` with the full standard function-instance type and
`O` with those actual fields. `Store.embed` injects each existing function with
`Sum.inl`. `Store.extend` appends exactly one `Sum.inr` generated function.
`Store.reconstruct` maps old entries by identity and reconstructs the new function.
Its embed round-trip and extension laws preserve the complete old list and `O`.
`extend_old` preserves each old numeric lookup; `extend_fresh` establishes the
new lookup at `old.funcs.length`. Numeric function/extern references are retained
without rebasing. No premise asserts execution equivalence for opaque contents.

`Module.instance` retains all accessed standard instance fields. The generated
function references its module instance, whose function vector contains the
fresh store address. Export index zero therefore need not mean store address
zero. No generated instruction calls an old function or touches another store
field. Mapping `Function` into the full standard instance syntax is structural;
its single function body is the translated selected expression.

`Admin I` can retain arbitrary full-standard instructions as `foreign I`.
`Admin.reconstruct` rebuilds generated administrative syntax and returns foreign
syntax unchanged. `reconstruct_foreign_suffix` proves exact suffix preservation.
A full standard pending instruction sequence can be supplied element by element
as foreign syntax; no parser or interpreter for those instructions is needed.

`focus` is an auxiliary deterministic operation, not the definition of standard
stepping. `focus_extend` and `focus_context` show that a successful generated
redex remains selected with any value prefix, pending suffix and enclosing label.
`Blocked.context/frame`, `foreign_blocked` and `ambient_invoke_blocked` establish
that an active foreign instruction or old-function invocation would instead
block that focus. `Blocked.not_focus` makes the two possibilities incompatible.
The standard value-prefix context grammar therefore cannot skip an unfinished
generated segment to execute a retained foreign suffix. A separate frame rule
covers callers' activation records. The segment theorem stops at its cutpoint:
resuming an arbitrary continuation can trap, diverge or mutate the store.

`lower_eval` allows aliased read-only inputs, any operand-stack prefix, and any
sufficiently allocated local list. It preserves the module frame and every local
outside the fresh allocation interval, including locals above that interval.
`evalCode_steps`, `Steps.context` and `Steps.inFrame` transport this result to the
transcribed standard relation and the caller context.

## Complete invocation and applicable alternatives

`invoke_entry` establishes selected validation, named export resolution and
external signature checks. `invoke_compiled` establishes the finite trace from
the dummy external frame through invoke, parameter/default-local initialization,
the generated frame and label, body execution, label exit and frame exit.
`invoke_correct` strengthens this to every state reachable from that entry:
active syntax remains in the selected domain, no administrative trap is reached,
and a finite path remains to the complete encoded source result.

The applicable-rule argument has two parts. The checked invariant `outside = 0`
excludes foreign instructions, ambient-function invocations and malformed
administrative const wrappers. Every remaining active form is a value, one of
the selected numeric/local instructions, a generated invoke, label, frame or
trap. The table accounts for all standard rules applicable to those forms;
there are no branch, return, call, memory, reference or host instructions to
activate another rule family. Generated invocation contains no foreign suffix.
The correspondence from this syntactic enumeration to the published grammar is
part of the reviewed transcription boundary, not an additional Lean axiom.

`Step.focus_or_trap` covers every constructor of the selected relation. Active
trap propagation is the explicit exception to focused evaluation.
`Step.deterministic` excludes that exception for clean reachable states.
`Steps.remaining` compares every finite alternative with the successful trace;
`Steps.progress` excludes stuck alternatives and `Steps.normal_result` fixes the
entire final frame and value list. `Step.decreases`, `Step.chain_bound` and
`Step.no_infinite` separately exclude infinite reduction chains. The measure
charges invocation for its body and charges administrative completion; constants
are already values. These facts apply to standard execution through the rule
correspondence above, rather than through an appeal to typing alone.

## Composition and accounting

`compile_source` uses the existing frontend correctness theorem and retains its
context order. `finite_sum_source` uses `FiniteSum.lower_correct`.
`state_step` compares the complete output/state pair with the initialized
program's independent meaning; initialization is supplied once and returned
state is passed to the next invocation. `word_source` uses #509's word theorem
and both codec directions, with no repeated arithmetic proof.

`lower_profile` proves emitted instruction-entry and fresh-local counts for every
circuit. `scanStack` computes operand heights through the ordered generated
instructions; `evalInstr_stack`, `evalCode_stack` and `eval_prefix_bound` connect
successful execution prefixes to that model. `actualPlan_eq` connects actual
syntax and stack-profile counts to the unchanged #509 plan. These are neither
serialized byte counts nor physical memory, latency, host-codec or activation
frame measurements. `invocation_reduction_bound` bounds any finite chain by input slots plus twice
the generated body length plus three. It is a separate reduction model, not an
assertion that all instruction entries reduce once.

The width-32 composed selector has 65 input slots and 96 result slots. Its actual
profile is 3,266 instruction entries, 866 locals including parameters, and peak
body operand height 96. The retained positive admission case connects that
profile to `Module.withinLimits`. The native-i32 comparison from #509 remains only a
comparison route: its 3-parameter/3-result packed ABI and planned 16 entries/6
locals exclude conversion to and from this Boolean ABI. Standard nonzero i32
truthiness is broader than canonical Boolean admission. No native-word Wasm
module is emitted by this unit.

`Examples/WasmCircuit.lean` retains zero-arity invocation, default locals,
aliased input references with asymmetric local sentinels and an i64 prefix,
nonempty ambient stores with preserved references, a foreign suffix, an open
frontend let expression, nested finite-sum case execution and malformed inactive
payloads, a width-two overflow with complete bit order, the universal width-32
selector, and all-input two-delay execution with three successive calls.

## Remaining #488 artifact contract

This unit has no serializer, binary parser, external runtime or host adapter.
The following unit must produce actual `.wasm` artifacts and test the exact
byte/module/ABI/export correspondence at the approved trusted-encoder boundary.
It must validate encoding lengths and buffers, bind tests to artifact hashes,
exercise canonical raw-value marshalling, and commit returned state only after
successful admitted execution. The engine and host environment remain explicit
external assumptions. No source-to-real-runtime or complete #488 claim follows
from the formal module syntax alone.
