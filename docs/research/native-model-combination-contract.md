# Native action and observation contract

Frozen for #437 before interface design, from published `79182c41` and the
complete live issue. This is the bounded successor of the accepted
[paper construction](restricted-model-combination.md).

Input: a native monoid M, a MulAction M X and point x0; independently supplied
Y, y0, D, d0 and o:Y→D; and actual e:X≃Y preserving the selected point.
Both directions of e are data. There is no observer-injectivity, invariance,
or o(y0)=d0 premise. Universe levels remain independent.

Use X as the constructed state presentation, retaining the given action,
point, result carrier and result point. Construct out(x)=o(e(x)). Recovery
includes out(e.symm(y))=o(y), e(x0)=y0 and the left operations/point, rather
than equality of independently encoded records. Derive the mixed expression
out((m*n)•x)=out(m•(n•x)) from the native action law. No final output,
recovery theorem or mixed law may be assumed to construct it.

First native use: Mathlib's multiplicative wrapper of the Boolean XOR
additive monoid acts on Bool. The right carrier is genuinely Fin 2, with
point0 and Boolean observer distinguishing0 from1. Supply the explicit
Bool↔Fin2 equivalence. At false, actiontrue returns true and two actiontrue
steps return false. The native expectation is Boolean XOR, not a generic
model projection. Both inverse maps and point preservation must be checked.

Second native use, selected now: FreeMonoid Nat represents append prefixes,
acting on List Nat. Point is[]. Independently take Y=List Nat×PUnit, point
([],unit), D=Nat, d0=0 and observe(xs,unit)=length xs. Supply e(xs)=(xs,unit)
and inverse projection. Prefix[8,9] applied to state[4] retains ordered state
[8,9,4] and returns3. The length observer is noninjective; distinct ordered
states remain distinct under recovery. Use List.length_append locally while
reusing the same generic recovery and mixed law.

Both rejection cases use the public compatibility/recovery contract. Valid
singleton-action and two-element-observer inputs admit no overlap equivalence.
Any putative joint presentation with invertible recovery of both supplied
carriers would induce that impossible equivalence. On the valid Boolean
example, invariance fails at true acting on false. Show that every alternative
combination recovering the same supplied action, observer and overlap has this
failure, not only the canonical output definition.

No generic signatures, institutions adapter, syntactic conservativity, spatial
gluing or overlap discovery is required. Compare direct composition with the
constructed interface and record actual recurring obligations without claiming
measured productivity. Root owns full build/audit and independent reviews.
