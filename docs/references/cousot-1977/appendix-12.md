# 12. Appendix

[Transcription conventions and provenance](README.md). This file transcribes
Appendix 12; editorial observations appear only in explicitly labelled notes.

## [Printed p. 251](source.pdf#page=15)

We note $\langle L,\cup,\leq,\top,\bot\rangle$ a complete $\cup$-semilattice
$L$, with partial ordering $\leq$, supremum $\top$ and infimum $\bot$.
These definitions are given in Birkhoff[61].

Note: $L$ is a complete lattice.

(proof in Birkhoff[61], p. 49).

We take f is isotone, f is order-preserving or f is monotone to be synonymous
and mean:

$$
\{\forall(x,y)\in L^2,\ \{x\leq y\}\Longrightarrow\{f(x)\leq f(y)\}\}
$$

$$
\Longleftrightarrow
\{\forall(x,y)\in L^2,\ \{f(x\cup y)\}\geq f(x)\cup f(y)\}
$$

**(H1):** Let $F$ be an order-preserving function from the complete semi-lattice
$\langle L,\cup,\leq,\top,\bot\rangle$ in itself.

**($\overline{\mathrm{H1}}$):** Let $\overline F$ be an order-preserving function
from the complete semi-lattice
$\langle\overline L,\overline\cup,\overline\leq,\overline\top,\overline\bot\rangle$
in itself.

**(L1):** The fixpoints of $F$ form a non-empty complete lattice with supremum
$g$, infimum $\ell$ such that:

$$
g=\bigcup\{x\mid(x\in L)\wedge(x\leq F(x))\}
$$

$$
\ell=\bigcap\{x\mid(x\in L)\wedge(F(x)\leq x)\}
$$

(This result is proved in Tarski[55], pp. 286–287). Note that the fixpoints
of $F$ need not form a sublattice of $L$.
We note $\overline g$ and $\overline\ell$ the greatest and least fixpoints of
$\overline F$.

**(H2):** Let $\alpha$ and $\beta$ be such that:

$$
\begin{aligned}
(\mathrm{H2.1})\quad&\alpha:L\to\overline L\\
(\mathrm{H2.2})\quad&\gamma:\overline L\to L\\
(\mathrm{H2.3})\quad&\alpha\text{ is order preserving}\\
(\mathrm{H2.4})\quad&\gamma\text{ is order preserving}\\
(\mathrm{H2.5})\quad&\forall\overline x\in\overline L,\quad
 \overline x=\alpha(\gamma(\overline x))\\
(\mathrm{H2.6})\quad&\forall x\in L,\quad x\leq\gamma(\alpha(x))
\end{aligned}
$$

> **Editorial note A1:** The introductory line prints $\beta$, while H2.2 and
> the subsequent formulas use $\gamma$. Both readings are retained; $\beta$
> has not been silently changed to $\gamma$.

**(H3.1):** $(\mathrm{H1})$, $(\overline{\mathrm{H1}})$, $(\mathrm{H2})$ and
$\{\forall x\in L,\ \overline F(\alpha(x))\mathrel{\overline\geq}\alpha(F(x))\}$

**(H3.2):** $(\mathrm{H1})$, $(\overline{\mathrm{H1}})$, $(\mathrm{H2})$ and
$\{\forall\overline x\in\overline L,\ \gamma(\overline F(\overline x))\geq F(\gamma(\overline x))\}$

**(L2):** $\{\mathrm{H3.1}\}\Longleftrightarrow\{\mathrm{H3.2}\}$

Proof:

$\forall\overline x\in\overline L$,

$$
\begin{aligned}
\overline F(\alpha(\gamma(\overline x)))
 &\mathrel{\overline\geq}\alpha(F(\gamma(\overline x)))
 &&\text{by }x=\gamma(\overline x)\text{ in H3.1}\\
\overline F(\overline x)
 &\mathrel{\overline\geq}\alpha(F(\gamma(\overline x)))
 &&\text{from H2.5}\\
\gamma(\overline F(\overline x))
 &\geq\gamma(\alpha(F(\gamma(\overline x))))
 &&\text{from H2.4}\\
\gamma(\overline F(\overline x))
 &\geq F(\gamma(\overline x))
 &&\text{H2.6 and transitivity.}
\end{aligned}
$$

$\forall x\in L$

$$
\begin{aligned}
\gamma(\overline F(\alpha(x)))
 &\geq F(\gamma(\alpha(x)))
 &&\overline x=\alpha(x)\text{ in H3.2}\\
\gamma(\alpha(x))&\geq x&&\text{H2.6}\\
F(\gamma(\alpha(x)))&\geq F(x)&&F\text{ order preserving in (H1).}\\
\gamma(\overline F(\alpha(x)))&\geq F(x)&&\text{transitivity}\\
\alpha(\gamma(\overline F(\alpha(x))))
 &\mathrel{\overline\geq}\alpha(F(x))&&\text{H2.3}\\
\overline F(\alpha(x))&\mathrel{\overline\geq}\alpha(F(x))&&\text{H2.5}
\end{aligned}
$$

Q.E.D.

Since H3.1 and H3.2 are proved by L2 to be equivalent, we choose:

**(H3):** $(\mathrm{H3.1})$ $\underline{\mathrm{or}}$ $(\mathrm{H3.2})$

**(L3):** Let $F:L\to L$ be an order-preserving function from the semilattice
$\langle L,\cup,\leq,\top,\bot\rangle$ in itself, $\ell$ and $g$ respectively
the least and greatest fixpoints of $F$, then:

$$
\forall x\in L,\quad\{g\cup F(x)\geq x\}\Longleftrightarrow\{g\geq x\}
$$

(The dual of this result is proved in Park [69], pp. 66). By duality:

$$
\forall x\in L,\quad\{\ell\cap F(x)\leq x\}\Longleftrightarrow\{\ell\leq x\}
$$

## [Printed p. 252](source.pdf#page=16)

**(T1):** H1, $\overline{\mathrm{H1}}$, H2, H3 imply that the greatest fixpoints
$g$ and $\overline g$ of $F$ and $\overline F$ are related by:

$$
\{\alpha(g)\mathrel{\overline\leq}\overline g\}
\quad\underline{\mathrm{and}}\quad
\{g\leq\gamma(\overline g)\}
$$

Proof:

The existence of $g$ and $\overline g$ is stated by (L1).

$$
\begin{aligned}
\overline g\mathbin{\overline\cup}\alpha(g)
 &\mathrel{\overline\geq}\alpha(g)&&\text{trivially}\\
\overline g\mathbin{\overline\cup}\alpha(F(g))
 &\mathrel{\overline\geq}\alpha(g)&&\text{since }\underline g=F(g)\\
\overline g\mathbin{\overline\cup}\overline F(\alpha(g))
 &\mathrel{\overline\geq}\alpha(g)
 &&\text{H3.1, }\overline\cup\text{ isotone, }\overline\geq\text{ transitive}\\
\overline g&\mathrel{\overline\geq}\alpha(g)&&\text{L3}\\
\gamma(\overline g)&\geq\gamma(\alpha(g))&&\text{H2.4}\\
\gamma(\overline g)&\geq g&&\text{H2.6, }\geq\text{ transitive.}
\end{aligned}
$$

Q.E.D.

Replacing
$\langle g,\overline g,\overline\cup,\overline\geq,\geq,F,\overline F,\alpha,\gamma,\mathrm{H3.1},\mathrm{H2.4},\mathrm{H2.6}\rangle$
respectively by
$\langle\overline\ell,\ell,\cap,\leq,\overline\leq,\overline F,F,\gamma,\alpha,\mathrm{H3.2},\mathrm{H2.3},\mathrm{H2.5}\rangle$
in the above proof, we get the "dual" theorem:

**(T2):** H1, $\overline{\mathrm{H1}}$, H2, H3 imply that the least fixpoints
$\ell$ and $\overline\ell$ of $F$ and $\overline F$ are related by:

$$
\{\gamma(\overline\ell)\geq\ell\}
\quad\underline{\mathrm{and}}\quad
\{\overline\ell\mathrel{\overline\geq}\alpha(\ell)\}
$$

According to Scott[71] a subset $X\subseteq L$ is called directed if every
finite subset of $X$ has an upper bound (in the sense of $\leq$) belonging to
$X$. (An obvious example of a directed subset is a non-empty ascending chain).
A function $f:D\to D'$ is called continuous if whenever $X\subseteq L$ is
directed, then $f(\cup\{x\mid x\in X\})=\cup\{f(x)\mid x\in X\}$.

> **Editorial note A2:** The continuity sentence prints $f:D\to D'$ and
> then $X\subseteq L$. The domain letter is retained as printed.

**(H4):** Let $F$ be a continuous function from the complete semi-lattice
$\langle L,\cup,\leq,\top,\bot\rangle$ in itself.

**($\overline{\mathrm{H4}}$):** Let $\overline F$ be a continuous function from
the complete semi-lattice
$\langle\overline L,\overline\cup,\overline\leq,\overline\top,\overline\bot\rangle$
in itself.

We note $F^0(x)=x$ and $F^{n+1}(x)=F(F^n(x))$.

**(L4):** $\mathrm{H4}(\overline{\mathrm{H4}})$ implies that
$F\ (\overline F)$ has a least fixpoint $\ell(\overline\ell)$ which is the limit
$\displaystyle\bigcup_{i=0}^{+\infty}F^i(\bot)$ of the Kleene's sequence
$\bot\leq F(\bot)\leq\ldots\leq F^n(\bot)\leq\ldots$.

(The proof is easy to adapt from Kleene[52]'s proof of the first recursion
theorem pp. 348–349).

> **Editorial note A3:** L4 abbreviates the concrete and abstract versions in
> parentheses, then displays the concrete sequence. No abstract sequence has
> been inserted into the transcription.
