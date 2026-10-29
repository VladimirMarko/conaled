# Discussion of scan and FFT optimality

Archived on 2026-10-29 from a supplied ChatGPT Pro discussion. The first prompt
has been reformulated at the author's request; the responses and second prompt
are preserved as supplied. Embedded citation markers belong to the original
chat and may not resolve outside it.

This is historical research material, not a record of checked Lean results.
The [current assessment](../research/scan-fft-optimality.md) checks primary
sources, identifies qualifications, and proposes integration with the library.


Prompt 1:
````md
Read [Generic parallel functional programming: Scan and FFT](https://conal.net/papers/generic-parallel-functional/). In what precise senses, if any, are its generated scan algorithms optimal in work, depth, or a combination of the two? Which guarantees follow from the algebraic laws behind the construction, and which require a separate cost model and lower-bound argument?
````

Respose 1:
````md
**There is real lawfulness behind the construction, but it does not guarantee optimality.** Some generated scans attain provable lower bounds. Others can be improved—even using the paper’s own combinators. The distinction is between an algebra that generates *equivalent computations* and an argument that selects a computation with *minimum cost*.

There is a particularly interesting connection between the two: the identity law helps prove a lower bound on scan circuits. So algebra can participate in an optimality proof. But the generic construction does not automatically attain that bound.

## 1. The apparent optimality does not hold for all the examples

Let’s make the cost model precise. We have \(n\) independent inputs to a generic monoid scan, and count:

- \(W\): the number of binary monoid operations;
- \(D\): the maximum number of operations on a dependency path.

Wiring and copying are free, and operations involving the identity are eliminated. We require all prefixes, including the total. This is the usual abstract prefix-circuit model; assumptions about fan-out or physical wiring would introduce additional constraints. [scispace.com](https://scispace.com/pdf/parallel-prefix-computation-dfg98u6zz4.pdf?utm_source=chatgpt.com)

In that model, **each of the three 16-input circuits in the paper’s main comparison has a competitor with fewer operations at the same depth**:

| Shape in the paper | \((W,D)\) | Another shape using the same generic instances | \((W,D)\) |
|---|---:|---|---:|
| `RBin 4` | \((32,4)\) | `LBin 3 × RBin 3` | \((31,4)\) |
| `Bush 2` | \((29,5)\) | `RBin 3 ◦ Pair` | \((27,5)\) |
| `LBin 4` | \((26,6)\) | `LVec 4 ◦ LVec 4` | \((24,6)\) |

The first two columns are Figure 20; the last alternative is already Figure 14. The other two alternatives are my derivations from the generic instances. [conal.net](https://conal.net/papers/generic-parallel-functional/generic-parallel-functional.pdf?utm_source=chatgpt.com) [conal.net](https://conal.net/papers/generic-parallel-functional/generic-parallel-functional.pdf?utm_source=chatgpt.com)

I checked the derived alternatives by symbolically evaluating the instances, simplifying identity operations, checking every output as a word in the free monoid, and counting the resulting circuit’s operations and dependency depths.

Here is why these comparisons work.

### A cheaper scan at depth 4

Consider `LBin 3 × RBin 3`: a bottom-up scan of the first eight elements, followed by a top-down scan of the other eight.

The crucial distinction is between when a subscan’s **total** becomes available and when **all its prefixes** become available:

| Eight-input subscan | Work | All outputs available by | Total available at |
|---|---:|---:|---:|
| Left, bottom-up | 11 | Depth 4 | Depth 3 |
| Right, top-down | 12 | Depth 3 | Depth 3 |

Combining these two scans requires adding the left total to the seven nonempty proper prefixes of the right half and to the right total. That costs eight more operations:

\[
W=11+12+8=31.
\]

Every newly adjusted output is ready at depth 4, because its two operands are ready by depth 3. The left prefix outputs also finish by depth 4. Thus

\[
D=4.
\]

This is already an instructive answer to your question: **a subscan can spend longer computing some outputs without delaying the enclosing scan**. Only the outputs used downstream need to arrive early. A uniform choice of locally fastest subscans can therefore waste work.

### A cheaper scan at depth 5

For `RBin 3 ◦ Pair`, organize the inputs into eight adjacent pairs.

First compute the eight pair totals. That takes eight operations at depth 1. Then scan those totals with the eight-input top-down scan, costing twelve operations and finishing by absolute depth 4.

This supplies all even-length prefixes. The seven remaining nontrivial odd-length prefixes each require one additional operation:

\[
W=8+12+7=27,\qquad D=5.
\]

That improves on the bush’s \((29,5)\).

### A scan at depth 6 that really is optimal for a mixed objective

For `LVec 4 ◦ LVec 4`, scan four blocks of four sequentially, then scan their totals sequentially, then adjust the local prefixes.

The operation count is:

\[
\underbrace{4\cdot3}_{\text{local scans}}
+
\underbrace{3}_{\text{scan of totals}}
+
\underbrace{3\cdot3}_{\text{prefix adjustments}}
=24.
\]

The total is available at depth \(3+3=6\), and all other outputs also finish by then.

Consequently, the three original examples are not Pareto optimal in \((W,D)\): in each case, work can decrease while depth stays fixed. They therefore cannot minimize a weighted objective \(\alpha W+\beta D\) when both weights are positive. The top-down example *does* minimize depth alone; its competitor simply achieves that same minimum with less work.

These comparisons concern the specified two costs. A restriction on fan-out, for example, can exclude a competing circuit. Circuit design also considers layout and interconnection costs, as Hinze’s algebra-of-scans paper discusses. Such restrictions change the optimization problem and need their own optimality argument. [cs.ox.ac.uk](https://www.cs.ox.ac.uk/ralf.hinze/publications/MPC04.pdf?utm_source=chatgpt.com)

## 2. What is lawful: the augmented scan is a homomorphism

Here is my algebraic reconstruction of the underlying reason the generic construction works.

Let \((M,\otimes,e)\) be a monoid. Write

\[
S(X)=(P_X,T_X),
\]

where \(P_X\) is the sequence of exclusive prefixes of \(X\), and \(T_X\) is its total reduction. For example,

\[
S([a,b,c])
=
([e,a,a\otimes b],\,a\otimes b\otimes c).
\]

For sequences \(X\) and \(Y\), every prefix in the \(X\) part is already correct. Every prefix in the \(Y\) part needs the contribution of all of \(X\). Therefore

\[
S(X\mathbin{+\!\!+}Y)
=
\left(
P_X\mathbin{+\!\!+}
\operatorname{map}(T_X\otimes -)\,P_Y,\;
T_X\otimes T_Y
\right).
\]

Define an operation on these augmented results:

\[
(P,t)\diamond(Q,u)
=
\left(
P\mathbin{+\!\!+}\operatorname{map}(t\otimes -)\,Q,\;
t\otimes u
\right).
\]

Then the equation becomes a homomorphism law:

\[
\boxed{S(X\mathbin{+\!\!+}Y)=S(X)\diamond S(Y).}
\]

The important fact is that \(\diamond\) is itself associative.

To see this, let \(L_t\) denote left multiplication, lifted pointwise to sequences:

\[
L_t(Q)=\operatorname{map}(t\otimes -)\,Q.
\]

The monoid laws give

\[
L_e=\operatorname{id},
\qquad
L_t\circ L_u=L_{t\otimes u}.
\]

Also, pointwise mapping distributes over sequence concatenation:

\[
L_t(Q\mathbin{+\!\!+}R)=L_t(Q)\mathbin{+\!\!+}L_t(R).
\]

Using these equations, either association of three augmented results produces

\[
\left(
P\mathbin{+\!\!+}L_t(Q)
 \mathbin{+\!\!+}L_{t\otimes u}(R),\;
t\otimes u\otimes v
\right).
\]

The identity is \(([],e)\). Thus the augmented results form a monoid—more specifically, a semidirect-product monoid—and \(S\) is a monoid homomorphism into it.

This makes the role of the extra total precise. **The total is exactly the summary needed to combine scans.** The exclusive prefixes alone omit the contribution of the final input. Adding the total makes a block’s result sufficient for combining it with subsequent blocks.

The same law explains the construction for a structure of structures. If the input consists of blocks \(X_0,\ldots,X_{m-1}\), let

\[
S(X_j)=(P_j,T_j).
\]

A scan of the block totals computes

\[
Q_j=T_0\otimes\cdots\otimes T_{j-1}.
\]

The global prefixes belonging to block \(j\) are then

\[
L_{Q_j}(P_j).
\]

So the three stages—scan the blocks, scan their totals, adjust their prefixes—follow directly from the homomorphism law. Nothing here requires commutativity, arithmetic, or any special behavior of addition.

That is substantial lawfulness. It explains why such a small collection of definitions yields a large family of correct algorithms, and why block totals provide such useful opportunities for sharing.

### Naturality gives another useful law

For any monoid homomorphism \(h:M\to N\), scanning commutes with interpreting the elements through \(h\):

\[
(\operatorname{map}h\times h)\circ S_M
=
S_N\circ\operatorname{map}h.
\]

This follows because \(h\) preserves the identity and multiplication. It does not hold for an arbitrary element function.

The free monoid makes this especially concrete. Treat each input as a distinct letter. Every wire then denotes a word, and correctness means that each output spells exactly the required prefix. Any interpretation of those letters in another monoid preserves the result.

This gives a precise way to establish generic correctness. It also supplies a useful setting for lower-bound arguments. But it still leaves open how many gates a circuit uses to construct those words.

## 3. Why the homomorphism law does not imply minimum cost

The central issue is that \(\diamond\) is associative **as a function**, while its implementation cost depends on the sizes of its arguments.

In

\[
(P,t)\diamond(Q,u),
\]

the value \(t\) is propagated across \(Q\). Propagating a summary across one element costs less than propagating it across a thousand elements. Reassociation changes how often this propagation occurs.

For instance, consider the product construction after eliminating identity operations.

With a fully left-associated shape, each new step appends a singleton. It reuses the already computed total and performs one new operation:

\[
W_{\mathrm{left}}(n)
=
W_{\mathrm{left}}(n-1)+1,
\]

so

\[
W_{\mathrm{left}}(n)=n-1.
\]

With a fully right-associated shape, each step prepends a singleton to a scan of the remaining \(n-1\) elements. That singleton must be incorporated into all the subsequent prefixes:

\[
W_{\mathrm{right}}(n)
=
W_{\mathrm{right}}(n-1)+(n-1),
\]

so

\[
W_{\mathrm{right}}(n)=\frac{n(n-1)}2.
\]

Both depths are \(n-1\). Both constructions satisfy the same homomorphism law. Indeed, the paper prints the eight-input instances with \((W,D)=(7,7)\) and \((28,7)\). [conal.net](https://conal.net/papers/generic-parallel-functional/generic-parallel-functional.pdf?utm_source=chatgpt.com)

The algebra therefore establishes an equivalence class of computations whose members can have very different costs.

This distinction persists if we use more abstract language:

- A universal property can establish uniqueness of the **function** satisfying certain equations.
- Naturality can establish that the function commutes with suitable interpretations.
- Coherence under order-preserving rebracketing can establish that different representations produce corresponding answers.

None of these statements says that every implementation of that function uses the fewest operations.

In symbols, it is entirely possible that

\[
\llbracket C_1\rrbracket=\llbracket C_2\rrbracket
\]

while

\[
(W(C_1),D(C_1))\ne(W(C_2),D(C_2)).
\]

In fact, associativity deliberately forgets some of the information needed to distinguish those costs: which parenthesization was chosen, where intermediate results were shared, and when they became available.

### Why the good examples can nevertheless look inevitable

There is a nearby problem for which the intuition is stronger: computing a **single reduction**.

Every full binary reduction tree over \(n\) distinct inputs has exactly \(n-1\) operation nodes. So, within that class, every parenthesization is work optimal. Balancing the tree then gives minimum depth.

Scan asks for many overlapping reductions. Its circuit is a graph with shared intermediate results, rather than merely one reduction tree. Now the challenge includes choosing intermediates that are useful to multiple outputs. Different lawful decompositions can create more or less useful sharing.

The generic definitions expose sharing through block totals, which is why good algorithms emerge so naturally. But a chosen hierarchy of blocks can still produce intermediates that another hierarchy avoids. The right-associated vector is an extreme example; the 16-input comparisons show that the same issue persists among well-balanced and efficient-looking designs.

## 4. There are genuine optimality theorems

It helps to distinguish exact optimality from asymptotic optimality, and optimization of one resource from optimization of both.

### Elementary lower bounds

For generic scan on \(n\) independent inputs,

\[
\boxed{W\ge n-1}
\qquad\text{and}\qquad
\boxed{D\ge\lceil\log_2 n\rceil}.
\]

The work bound is immediate in the free monoid: the \(n-1\) nontrivial prefixes are distinct required results, and each needs an operation node.

For depth, a value produced by a binary circuit at depth \(d\) can depend on at most \(2^d\) inputs. The total depends on all \(n\), so its depth is at least \(\lceil\log_2 n\rceil\).

Different constructions meet these bounds in different senses.

The left-associated chain has

\[
W=n-1,\qquad D=n-1,
\]

so it attains the absolute minimum work.

For the top-down binary construction, on \(n=2^k\) inputs, the operation recurrence is

\[
W_R(n)=2W_R(n/2)+n/2.
\]

This gives

\[
W_R(n)=\frac n2\log_2 n,
\qquad
D_R(n)=\log_2 n.
\]

It therefore attains the absolute minimum depth. The 31-operation competitor shows why that does not imply minimum work *subject to that depth*.

The bottom-up binary construction has a different recurrence:

\[
W_B(n)=W_B(n/2)+n-1.
\]

The \(n-1\) new operations consist of \(n/2\) pair totals and \(n/2-1\) corrections. Hence

\[
W_B(n)=2n-\log_2 n-2.
\]

Its depth is \(2\log_2 n-2\) for powers of two \(n\ge4\). It therefore has asymptotically optimal work and depth simultaneously:

\[
W_B(n)=\Theta(n),
\qquad
D_B(n)=\Theta(\log n).
\]

That is an important guarantee, but it allows constant factors and lower-order improvements. It is compatible with the exact dominance shown above.

Also, the top-down construction’s \(\Theta(n\log n)\) work is not an unavoidable price of attaining minimum depth: Ladner and Fischer construct prefix circuits with depth exactly \(\lceil\log_2 n\rceil\) and fewer than \(4n\) operations. [scispace.com](https://scispace.com/pdf/parallel-prefix-computation-dfg98u6zz4.pdf?utm_source=chatgpt.com)

### A lower bound for a mixed objective

The particularly relevant result is Snir’s bound:

\[
\boxed{W+D\ge2n-2.}
\]

For prefix computation with a nontrivial binary operation having a right identity, Snir proves this even when the implementing circuit may use arbitrary unary and binary operations. It therefore applies to the generic monoid model being considered here. [snir.cs.illinois.edu](https://snir.cs.illinois.edu/listed/J16.pdf?utm_source=chatgpt.com)

Now return to the four-block, four-element construction:

\[
W+D=24+6=30=2(16)-2.
\]

**This circuit really is optimal for the objective \(W+D\).** The bound also proves that it is Pareto optimal:

- No circuit of depth at most 6 can use fewer than 24 operations.
- No circuit using at most 24 operations can have depth below 6.

This is a precise version of “optimal in an appropriate mix of components and path length.”

There is an important logical qualification. Equality with the bound certifies optimality; failure to attain equality does not by itself prove nonoptimality. A lower bound may not be attainable at a particular small depth. That is why the explicit competitors above matter.

### Here an algebraic law really does enter the cost proof

Snir’s argument uses a property of the prefix problem called self-reducibility. Setting an input to the identity leaves a smaller prefix problem. His induction exploits this reduction to remove either at least two counted operations, or an operation together with a level of depth. [snir.cs.illinois.edu](https://snir.cs.illinois.edu/listed/J16.pdf?utm_source=chatgpt.com)

So the identity law contributes to a resource lower bound. That is a meaningful affirmative answer to your question about lawfulness.

The complete argument, however, needs both parts:

\[
\text{a lower bound on all implementations}
\quad+\quad
\text{a construction attaining it}.
\]

The generic instances supply constructions. Their correctness alone does not establish that they attain the bound.

## 5. Is there a weaker, compositional optimality principle?

There is a useful local principle, provided we state the constraints carefully.

Suppose the scans of two nonempty blocks have already been chosen and are treated as fixed subcircuits. Their interface supplies

\[
(P,t)\quad\text{and}\quad(Q,u).
\]

Let the right block contain \(r\) inputs.

Apart from the already available boundary prefix \(t\), combining the blocks needs \(r\) new global prefixes: the left total multiplied by each nonempty right prefix, including the right total.

In the free monoid these are distinct words, absent from the child interfaces. Each needs a new operation node. The product rule uses exactly \(r\) operations after eliminating the identity adjustment. Thus its stitching step attains a local work lower bound.

This explains part of the construction’s economy. Each combination does exactly the necessary work for the interface it has been given.

**But the interface itself is a choice.** Changing the decomposition can change which intermediate values are available and how many times summaries must be propagated. Locally optimal stitching can therefore assemble into a globally inferior circuit. The quadratic right-associated scan demonstrates that directly.

There is also a timing issue. In the 31-operation construction, the left eight-input scan’s total arrives at depth 3 even though some other outputs take depth 4. The enclosing computation can exploit that difference.

As a result, a compositional optimizer needs more information than one maximum-depth number for each subscan. Depending on the construction language, it may need:

- the arrival time of the total separately from other outputs;
- arrival times or dependency information for individual outputs;
- fan-out constraints and the availability of shared intermediates.

The relevant notion of “best subproblem solution” must preserve all the information that can affect the enclosing computation.

### Fixing the datatype does not by itself establish optimality

One might try to rescue the hypothesis by saying that each scan is optimal *for its datatype*.

But the finite shapes here can be related by order-preserving rebracketings. In the circuit model, these can amount to rewiring. A scan implementation for one shape can therefore convert to another shape, use its scan circuit, and convert the result back.

The datatype determines the decomposition chosen by these generic instances. It does not, by itself, force every correct implementation to use that decomposition.

To obtain a meaningful constrained theorem, we would need to say something such as: “the child circuits and their interfaces are fixed,” or “implementations must obey this particular communication hierarchy.” Those are restrictions on the admissible computations, beyond the extensional type of their inputs and outputs.

## 6. What a stronger algebraic guarantee would look like

The lawfulness establishes a space of equivalent designs. An optimization theorem would add an ordering to that space.

For example, fix a construction language and define

\[
\operatorname{BestWork}(n,d)
=
\min\{W(C):
C\text{ computes the }n\text{-input scan and }D(C)\le d\}.
\]

There are then two different possible results:

1. **Optimality within the construction language.** Prove that a search or dynamic program finds the minimum among the circuits expressible by the allowed combinators.
2. **Optimality among all circuits in the cost model.** Establish a lower bound for every admissible circuit and show that the selected construction attains it.

The first requires a sufficiently rich description of subcircuit interfaces, including timing information. The second requires a circuit-complexity argument such as Snir’s. Exhausting one grammar does not automatically exhaust all possible circuits.

Algebra is useful throughout: it guarantees correctness while rearranging designs, exposes reusable summaries, and can support the derivation of whole circuit families. Hinze’s *An algebra of scans* develops precisely this style of equational construction and reasoning. [cs.ox.ac.uk](https://www.cs.ox.ac.uk/ralf.hinze/publications/MPC04.pdf?utm_source=chatgpt.com)

Your intuition identifies something important: the efficient structure is systematic, and associativity and identity explain why it is available across arbitrary monoids. The stronger statement is that **the laws make efficient decompositions possible and provable; a cost argument determines which decomposition is optimal**. For some of the paper’s instances that argument succeeds exactly. For others, the same lawful framework already contains a better choice.
````


Prompt 2:
````md
https://conal.net/papers/generic-parallel-functional/ also tackles FFTs. What of our optimality discussion transfers to that? Are the FFT algorithms derived the in paper optimal in any sense?
````

Respose 2:
````md
**Yes—there are meaningful, provable senses in which the paper’s FFTs are optimal. One is quite strong: their normalized butterfly networks attain an exact lower bound in a model of two-coordinate unitary gates.** They also have optimal asymptotic work and depth under suitable assumptions.

But the paper’s displayed circuits do **not** minimize real additions and multiplications. There are improvements even to the bush circuit.

So the distinction from our scan discussion survives: algebraic laws explain the decomposition and establish correctness; optimality requires a cost model and a lower-bound argument. For FFTs, the Fourier transform’s additional structure gives us particularly useful lower bounds.

I’ll focus on the paper’s constructions from `Pair`—the binary trees and bushes—with \(N=2^k\).

## 1. What lawfulness gives us: a factorization, together with compositional costs

The relevant algebra is richer than associativity. Define the unnormalized DFT by

\[
(F_Nx)_k=\sum_{j=0}^{N-1}x_j\omega_N^{jk},
\qquad
\omega_N=e^{-2\pi i/N}.
\]

For \(N=mn\), write

\[
j=nj_1+j_2,\qquad k=k_1+mk_2.
\]

The root-of-unity identities give

\[
\omega_N^{jk}
=
\omega_m^{j_1k_1}\,
\omega_N^{j_2k_1}\,
\omega_n^{j_2k_2}.
\]

Consequently,

\[
(F_Nx)_{k_1+mk_2}
=
\sum_{j_2=0}^{n-1}
\omega_n^{j_2k_2}\,
\omega_N^{j_2k_1}
\left(
\sum_{j_1=0}^{m-1}
x_{nj_1+j_2}\omega_m^{j_1k_1}
\right).
\]

This identity yields three computational steps:

1. Compute \(n\) transforms of size \(m\).
2. Multiply by the twiddle factors \(\omega_N^{j_2k_1}\).
3. Compute \(m\) transforms of size \(n\).

Distributivity permits the nested sums; the root-of-unity identities make the smaller transforms appear. The paper expresses this Cooley–Tukey factorization through functor composition, with the output shape reversing the order:

\[
\operatorname{FFO}(g\circ f)
=
\operatorname{FFO}(f)\circ\operatorname{FFO}(g).
\] :chatgpt-content-reference{index="0"}


There is therefore a substantial algebraic reason that a small collection of instances produces good algorithms: the instances expose a recursive factorization of a dense linear transformation into sparse transformations.

What does **not** follow from that identity is that every such factorization has the cheapest implementation. In particular, different factorizations expose different twiddle constants, and those constants need not have equal arithmetic costs.

### An exact cost invariant under reassociation

Let \(B(N)\) count occurrences of the basic two-point transform

\[
(a,b)\longmapsto(a+b,a-b).
\]

The composition rule gives

\[
B(mn)=nB(m)+mB(n),
\qquad B(2)=1.
\]

Dividing by \(mn\),

\[
\frac{B(mn)}{mn}
=
\frac{B(m)}m+\frac{B(n)}n.
\]

Thus the butterfly count per input is additive under multiplication of sizes. For every association of \(k\) copies of `Pair`,

\[
\boxed{B(N)=\frac N2\log_2N.}
\]

This is an exact structural invariant: right-associated trees, left-associated trees, and balanced bushes all have the same number of basic butterflies.

There is a similar invariant for twiddles if we charge equally for every nonidentity complex twiddle multiplication. A composition of sizes \(m,n\) introduces \((m-1)(n-1)\) such factors, giving

\[
Q(mn)=nQ(m)+mQ(n)+(m-1)(n-1),
\qquad Q(2)=0,
\]

and hence

\[
\boxed{Q(N)=\frac N2\log_2N-N+1.}
\]

So reassociation does not even change that abstract twiddle count. **What changes is which twiddles occur, where they occur, and how their arithmetic can be simplified.**

These invariants are a useful example of compositional cost analysis. By themselves, however, they establish equal costs within a construction scheme, rather than minimum costs among all algorithms.

## 2. There is an exact optimality theorem for the butterfly structure

Here is the strongest positive result.

Normalize the transform:

\[
U_N=\frac1{\sqrt N}F_N.
\]

Then \(U_N\) is unitary. A normalized radix-2 butterfly with a twiddle has the form

\[
H_\omega
=
\frac1{\sqrt2}
\begin{pmatrix}
1&\omega\\
1&-\omega
\end{pmatrix},
\qquad |\omega|=1,
\]

which is also unitary.

Consider a computational model with \(N\) complex registers in which one gate applies an arbitrary \(2\times2\) unitary transformation to two registers. No extra registers are available. Count each such gate as one operation.

Ailon proves that computing \(U_N\) in this model requires at least

\[
\boxed{\frac N2\log_2N\text{ gates}.}
\]

The proof uses the matrix entropy

\[
\Phi(M)
=
-\sum_{r,s}|M_{rs}|^2\log_2|M_{rs}|^2.
\]

Initially, \(\Phi(I)=0\). At the Fourier transform,

\[
\Phi(U_N)=N\log_2N,
\]

because every squared entry magnitude is \(1/N\). A two-coordinate unitary gate can increase this potential by at most \(2\), which proves the bound. [arxiv.org](https://arxiv.org/pdf/1305.4745?utm_source=chatgpt.com)

### Applying that theorem to the paper’s constructions

The connection to the generic FFT is my deduction from its factorization:

- Normalize each `Pair` transform by \(1/\sqrt2\).
- Absorb the diagonal twiddle phases into adjacent two-coordinate gates.
- Treat the shape-induced permutations as free wiring.

These operations preserve the butterfly count. Each input-to-output path acquires the overall normalization \(1/\sqrt N\), and the resulting circuit computes \(U_N\).

The construction uses exactly

\[
\frac N2\log_2N
\]

gates, matching the lower bound. Free permutations do not weaken the entropy argument, because they leave \(\Phi\) unchanged.

**Thus the normalized versions of all those pair-composed FFT networks are globally optimal in this gate model—not merely optimal among the type shapes considered in the paper.**

They can also be arranged in exactly \(\log_2N\) parallel butterfly rounds. A two-input gate can at most double the number of original inputs on which a register depends, so fewer rounds cannot produce an output depending on all \(N\) inputs. Consequently, both gate count and round count attain their respective lower bounds.

This is a particularly good answer to your question about lawfulness. There are two ingredients:

- The factorization laws construct the network and determine its butterfly count.
- Unitarity supports a quantitative invariant that bounds how much progress any admissible gate can make.

Together they establish optimality. Correctness of the factorization alone would not.

The qualification about the model matters: a two-coordinate unitary gate may require several real additions and multiplications. Charging one unit for every such gate deliberately suppresses those differences.

## 3. The displayed scalar circuits are not optimal

At the real-arithmetic level, the paper itself already supplies a counterexample to the idea that each generated FFT occupies an optimal work–depth tradeoff.

For \(N=16\), its counts are:

| Construction | Real additions and subtractions | Real multiplications | Arithmetic gates | Depth |
|---|---:|---:|---:|---:|
| `RBin 4` | 148 | 40 | 188 | 8 |
| `LBin 4` | 148 | 40 | 188 | 8 |
| `Bush 2` | 144 | 32 | 176 | 6 |

The paper’s totals also include literal nodes; the table above counts arithmetic gates. [conal.net](https://conal.net/papers/generic-parallel-functional/generic-parallel-functional.pdf?utm_source=chatgpt.com)

The bush circuit improves both work and depth over the two trees. Therefore those tree circuits cannot minimize a positive weighted combination of the two quantities.

The butterfly and twiddle invariants explain this comparison rather neatly. At size \(16\), both constructions have:

\[
B(16)=32,\qquad Q(16)=17.
\]

But, evaluating their twiddle exponents, the tree constructions have seven quarter-turn twiddles, while the bush has nine. Quarter turns can be implemented through sign changes and exchanging real and imaginary parts. The remaining general complex rotations number ten for the trees and eight for the bush.

Using four real multiplications and two real additions/subtractions for each general rotation gives exactly the arithmetic counts above. The bush’s advantage comes from exposing more cheap constants.

### Even the 16-point bush can be improved at the same depth

Here is a further improvement, derived directly from its factorization.

For

\[
c=\frac1{\sqrt2},
\]

multiplication by a \(45^\circ\) twiddle satisfies

\[
(a+ib)e^{-i\pi/4}
=
c(a+b)+i\,c(b-a).
\]

This uses two real multiplications and two additions/subtractions. The generic complex multiplication formula uses four multiplications and two additions/subtractions. Both implementations have arithmetic depth two.

The top-level \(4\times4\) twiddle stage of the 16-point bush has nonidentity exponents

\[
\begin{pmatrix}
1&2&3\\
2&4&6\\
3&6&9
\end{pmatrix}
\]

of \(\omega_{16}\). Four entries—those with exponents \(2\) or \(6\)—have the special \(45^\circ\) form, allowing the same saving.

Therefore four replacements save eight multiplications:

\[
(W,D)=(176,6)\longrightarrow(168,6).
\]

The resulting count is

\[
144\text{ additions/subtractions}
+
24\text{ multiplications}
=
168.
\]

This comparison uses the mathematical DFT with exact roots of unity; the printed floating-point literals would have to be replaced by their intended exact constants.

So even the displayed bush circuit is not minimal in arithmetic work at its depth. This is not a proof that the improved circuit is optimal—it is a concrete proof that the displayed one can be improved.

There is also a wider algorithmic comparison. Classical split-radix has the arithmetic count

\[
4N\log_2N-6N+8,
\]

which is \(6664\) operations at \(N=256\); Johnson and Frigo’s modified split-radix uses \(6552\) there. [fftw.org](https://www.fftw.org/~athena/papers/newsplit.pdf?utm_source=chatgpt.com) The paper’s 256-point bush has \(6978\) arithmetic operations. [conal.net](https://conal.net/papers/generic-parallel-functional/generic-parallel-functional.pdf?utm_source=chatgpt.com) These counts establish further scope for reducing work; they do not, by themselves, compare depths.

## 4. They are asymptotically work-optimal in a bounded-coefficient model

There is a different, classical lower bound that applies more directly to arithmetic work.

In the **bounded-coefficient linear model**, a step forms a new linear combination

\[
u=\alpha v+\beta w,
\]

from previously computed values, with the magnitudes of the coefficients uniformly bounded. For coefficients of magnitude at most \(1\), Morgenstern’s lower bound for the unnormalized DFT is

\[
S\ge\frac N2\log_2N
\]

such steps. In particular, the complexity is \(\Omega(N\log N)\). [dl.acm.org](https://dl.acm.org/doi/10.1145/321752.321761?utm_source=chatgpt.com)

The determinant argument is short enough to show why the restriction matters. Regard every available intermediate value as a linear form in the inputs, and track the largest absolute determinant obtainable from \(N\) available forms.

Initially that maximum is \(1\). Adding a form \(\alpha v+\beta w\), with \(|\alpha|,|\beta|\le1\), can increase it by at most a factor of \(2\), by multilinearity of the determinant. But the DFT matrix satisfies

\[
F_N^*F_N=NI,
\]

so

\[
|\det F_N|=N^{N/2}.
\]

Consequently,

\[
2^S\ge N^{N/2},
\]

giving the bound.

The pair-composed FFTs use \(O(N\log N)\) bounded-coefficient linear operations: there are \(O(N\log N)\) butterflies and twiddles, each requiring only a constant number of such operations. Therefore they match the lower bound **up to constant factors**.

This establishes a genuine asymptotic optimality result across a broad class of linear algorithms. It does not establish the smallest leading constant, let alone the smallest operation count at a particular size.

There are also two important distinctions from the unitary-gate theorem:

- A bounded linear-combination step produces one value; a unitary gate updates two coordinates. Their numerical gate counts are not directly interchangeable.
- The determinant proof concerns the **unnormalized** DFT. The normalized Fourier matrix has determinant of magnitude \(1\), so this particular proof gives no useful bound for it. The entropy argument addresses that case.

Thus “FFT requires \(N\log N\) work” needs its computational assumptions attached. These restricted theorems do not prove an unrestricted lower bound allowing arbitrary coefficients, intermediate values, and algebraic operations.

## 5. Their depth is asymptotically optimal when twiddles are available

The depth lower bound needs much less Fourier-specific machinery.

In a circuit whose gates have at most two inputs, a value at depth \(d\) can depend on at most \(2^d\) original inputs. Every complex DFT output depends on all \(N\) complex inputs. Hence

\[
D\ge\lceil\log_2N\rceil.
\]

With twiddle constants already available, the generic composition has the form

\[
D(mn)\le D(m)+D(n)+O(1).
\]

For a composition of \(k=\log_2N\) pairs, this gives \(O(k)\) depth, regardless of the association of those pairs. Combined with the dependency lower bound,

\[
\boxed{D(N)=\Theta(\log N).}
\]

So the pair-based FFTs are asymptotically depth-optimal in the usual bounded-fan-in arithmetic-circuit model.

This still permits different constant factors. An optimal number of butterfly rounds need not expand into the smallest possible number of scalar arithmetic layers. That is why the paper can report depths \(8\) and \(6\) for different 16-point circuits even though their normalized butterfly networks both have four rounds.

### A wrinkle in the paper’s printed depth analysis

The paper charges depth for generating the twiddle constants, giving a composition recurrence with an additional \(\log_2(mn)\) term. For the trees, its resulting bound is \(O(\log^2N)\). [conal.net](https://conal.net/papers/generic-parallel-functional/generic-parallel-functional.pdf?utm_source=chatgpt.com)

That is different from analyzing the data path of a fixed transform with twiddles precomputed.

For bushes, write

\[
N_j=2^{2^j}.
\]

The corresponding staged recurrence is

\[
D_j=2D_{j-1}+2^j+O(1).
\]

Solving it gives

\[
D_j=O(j2^j)
=
O(\log N_j\,\log\log N_j).
\]

With the twiddles available, the extra \(2^j\) term becomes constant, and the solution is \(O(\log N_j)\).

The distinction is:

| What is charged to the depth calculation? | Pair-based trees | Bushes |
|---|---:|---:|
| Twiddle generation, following the paper’s staged recurrence | \(O(\log^2N)\) | \(O(\log N\log\log N)\) |
| Input-dependent arithmetic with twiddles available | \(\Theta(\log N)\) | \(\Theta(\log N)\) |

The bush bound in the first row is my solution of the recurrence. These larger staged bounds do not show that the Fourier data inherently require more than logarithmic depth.

## 6. Why additional algebra can improve a lawful generic derivation

The most useful lesson from the scalar counterexamples is that **additional laws can reveal additional optimizations**. A construction can be lawful without having exhausted the algebra available for simplifying it.

The \(45^\circ\) identity is a local example. A deeper example is **rescaling intermediate transforms**.

Suppose a recursive component normally returns \(F_mx\). Instead, it might return a diagonally scaled version

\[
S F_mx,
\]

while its caller absorbs \(S^{-1}\) into the next stage’s constants. The complete computation can still return exactly \(F_Nx\), but some multiplications become cheaper.

Johnson and Frigo exploit this kind of rescaling in their modified split-radix FFT. Certain effective twiddles take forms such as

\[
1-i\tan\theta,
\]

whose multiplication can be implemented with fewer real multiplications than a general complex constant. [fftw.org](https://www.fftw.org/~athena/papers/newsplit.pdf?utm_source=chatgpt.com)

This exposes a limitation of a simple compositional optimality argument:

> A cheapest implementation of an unscaled subtransform need not be the best subcomputation for the surrounding transform.

The surrounding context may benefit from a scaled result, a different basis, shared intermediate expressions, or constants that simplify only after two stages are combined. To search those possibilities compositionally, the interface must represent those alternatives, or an optimization pass must transform across the existing interfaces.

For example, a dynamic program that keeps only “the cheapest FFT of size \(m\)” can discard a slightly more expensive scaled variant that makes the caller much cheaper. A sufficiently rich optimizer would need to retain alternatives distinguished by their scaling and other relevant properties, not just by size.

That issue transfers directly from our scan discussion: optimal substructure must itself be established for the chosen representation and cost model.

## What transfers, and what is special to FFT?

The transferable part is the separation between three claims:

1. **Semantic correctness:** every generated network computes the specified function.
2. **Structural cost analysis:** the construction determines recurrences and sometimes exact invariants.
3. **Optimality:** no admissible competing computation can have lower cost.

The paper’s algebra provides the first two. For FFTs, separate lower-bound arguments supply useful versions of the third:

| Meaning of “optimal” | What can be established for the pair-based constructions |
|---|---|
| Fewest normalized two-coordinate unitary gates, with \(N\) registers and free wiring | **Exactly optimal:** \(\frac N2\log_2N\) gates |
| Fewest parallel rounds of those gates | **Exactly optimal:** \(\log_2N\) rounds |
| Arithmetic work in the bounded-coefficient linear model | **Optimal up to constant factors:** \(\Theta(N\log N)\) |
| Arithmetic depth with bounded fan-in and available twiddles | **Optimal up to constant factors:** \(\Theta(\log N)\) |
| Fewest real additions and multiplications in the displayed circuits | **Not optimal in general:** explicit improvements exist |
| Minimum cost under arbitrary scalar-arithmetic implementations | **Not established by the derivation or these lower bounds** |

The scan-specific lower bounds do not transfer automatically. The FFT arguments exploit different invariants: growth of determinants, distribution of coefficient magnitudes, and dependence on all inputs.

So there really is a form of lawfulness responsible for an optimality result here—but it is more specific than lawful functor composition. **The normalized construction preserves unitarity, and unitarity supplies a bound on how much mixing one gate can accomplish. The generated network saturates that bound.** At the level of real arithmetic, the same construction leaves further algebraic simplifications available, and its lawfulness does not select a minimum-cost implementation.
````
