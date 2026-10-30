Prompt:
````md
The [https://github.com/conal/talk-2014-elegant-memoization](https://github.com/conal/talk-2014-elegant-memoization) talk does not seem to have been preserved. However, the slides and [https://hackage.haskell.org/package/MemoTrie](https://hackage.haskell.org/package/MemoTrie) remain. To the best of your ability, reconstruct it.
````

Response:
````md
# Elegant memoization — a reconstructed lecture

The central idea of this talk is more interesting than a particular caching technique:

**A function can be represented as a data structure whose shape is derived from its argument type. In a lazy language, that representation becomes an incrementally populated memo table.**

Conal Elliott gave the talk at Hacker Dojo in Mountain View on April 3, 2014. The repository preserves its outline and literate slide source, as well as a link to the PDF. The PDF’s 75 pages are successive builds of 32 numbered slides; slides 25–32 form a correctness-proof appendix. Elliott credits Ralf Hinze’s work and Spencer Janssen’s implementation as the foundations. [GitHub](https://github.com/conal/talk-2014-elegant-memoization)

What follows is a reconstructed lecture, not a recovered transcript. I follow the surviving sequence, expand the mathematical steps, and distinguish supplementary material from what the slides establish. Slide numbers below are the numbers printed on the slides.

## 1. Laziness already gives us most of a cache  
*Slides 2–4*

Start with the operational picture of lazy evaluation.

An expression need not be evaluated until its value is demanded. Once a shared expression has been evaluated, later uses can reuse the result. This applies throughout a lazy data structure: its spine, its elements, and the components of those elements can all be evaluated independently.

For example:

```haskell
let y = expensive x
in (y, y)
```

Both components refer to the same `y`. There is one shared computation.

But this does **not** imply that every occurrence of:

```haskell
expensive x
```

throughout a program automatically shares its result with every other occurrence. Ordinary function application does not come with a global table of previous arguments. An optimizer may discover some sharing, but that is different from providing general memoization. Elliott’s opening contrast is precisely between reuse of data and reuse of function applications. [GitHub](https://raw.githubusercontent.com/conal/talk-2014-elegant-memoization/master/outline.md)

Now consider a function as a collection indexed by its arguments. A value of type:

```haskell
Bool -> v
```

can be regarded as a collection with two entries: the value at `False` and the value at `True`.

Why should repeatedly accessing an entry in this collection behave differently from repeatedly accessing a component of a pair?

The conventional response is to put a mutable table behind the function. On each call, look up the argument; compute and insert the result if it is absent.

But there is another route: **change the representation of the function into something for which the language already provides sharing.**

That is the talk’s defining move: memoization as “conversion of functions into data structures,” without discarding their information. [Conal](https://conal.net/talks/elegant-memoization.pdf)

The mutation needed to remember evaluated results then belongs to the implementation of lazy evaluation, not to an explicitly stateful algorithm written by the programmer. Elliott develops this distinction in his earlier account of functional memo tries. [Conal](https://conal.net/blog/posts/elegant-memoization-with-functional-memo-tries/index.html)

## 2. Discover the representation by trying small domains  
*Slides 5–9*

Take one of the actual examples:

```haskell
f :: Bool -> Int
f x = if x then 3 else 5
```

What information does this function contain?

For its two ordinary Boolean inputs:

```haskell
f False = 5
f True  = 3
```

So we can store that information in a pair:

```haskell
(5, 3)
```

More generally, transform an arbitrary `f :: Bool -> v` into:

```haskell
(f False, f True)
```

Recover a function by selecting the appropriate component.

Here is that entire idea without any abstraction:

```haskell
memoBool :: (Bool -> v) -> Bool -> v
memoBool f =
  let falseResult = f False
      trueResult  = f True
  in \b -> if b then trueResult else falseResult
```

The bindings lie **outside** the returned function. Calls through the same returned function therefore reach the same result bindings.

Neither result has to be computed when `memoBool f` is constructed. A first lookup may evaluate one of them; subsequent lookups reuse it.

Now vary the domain.

A function from `()` has one ordinary input, so its table needs one entry. The slide’s example computes an uppercased string; that string itself can be stored and shared.

A function from `(Bool, Bool)` has four inputs. It can be represented as a pair of pairs:

```haskell
( (h (False, False), h (False, True))
, (h (True,  False), h (True,  True))
)
```

For the slide’s function:

```haskell
h (x, y) = f (x && y) + f (x || y)
```

this gives:

```haskell
((10, 8), (8, 6))
```

A function from `Either Bool Bool` also has four ordinary inputs, but the interpretation differs. It needs one Boolean table for the `Left` inputs and another for the `Right` inputs. These Boolean, unit, product, and sum examples are the examples preserved in the slides. [GitHub](https://raw.githubusercontent.com/conal/talk-2014-elegant-memoization/master/elegant-memoization.lhs)

The point is not that small functions deserve elaborate optimization. These examples expose a pattern:

**The argument type tells us how to organize all the results.**

The result type does not need to provide equality, ordering, or hashing. We merely store values of that type.

The next question is whether we can derive this organization systematically.

## 3. The construction is an algebra of function types  
*Slide 10*

Use the following mathematical notation:

- \(0\): an empty type.
- \(1\): a singleton type, represented by `()`.
- \(A+B\): a disjoint union, represented by `Either A B`.
- \(A\times B\): a product, represented by `(A, B)`.

Temporarily reason about total values. We will return to why that qualification matters.

Four familiar isomorphisms do the work:

\[
\begin{aligned}
(0\to V) &\cong 1,\\
(1\to V) &\cong V,\\
((A+B)\to V) &\cong (A\to V)\times(B\to V),\\
((A\times B)\to V) &\cong A\to(B\to V).
\end{aligned}
\]

These correspond to the exponent laws

\[
v^0=1,\qquad
v^1=v,\qquad
v^{a+b}=v^a v^b,\qquad
v^{ab}=(v^b)^a.
\]

The connection between trie representations and these exponent laws is central to both the slides and Elliott’s earlier explanation. [Conal](https://conal.net/talks/elegant-memoization.pdf)

But this is not merely counting inhabitants. Each equation comes with actual conversions.

**Empty domain.** There are no arguments for which a result must be stored. The table contains no entries, so one empty-table value suffices.

**Singleton domain.** Store the result at the only argument. Conversely, recover a function that returns that stored result.

**Sum domain.** Split a function into its two restrictions:

```haskell
f . Left
f . Right
```

Conversely, inspect whether an argument is `Left` or `Right`, and consult the appropriate function.

**Product domain.** Curry the function. For each first argument, obtain a function of the second argument.

Now apply the same transformation recursively to the function types that remain.

Writing \(T_A(V)\) for the table representation of \(A\to V\), we obtain:

\[
\begin{aligned}
T_0(V) &= 1,\\
T_1(V) &= V,\\
T_{A+B}(V) &= T_A(V)\times T_B(V),\\
T_{A\times B}(V) &= T_A(T_B(V)).
\end{aligned}
\]

Notice the last two equations:

**A sum of keys produces a product of tables. A product of keys produces a table of tables.**

That is the algorithm.

## 4. Turn the algebra into a Haskell interface  
*Slides 11–16*

We need a family of representations indexed by the key type, together with conversions in both directions.

Here is a small standalone version of the core interface. It follows MemoTrie’s associated **data-family** formulation, omitting `enumerate` and the library’s additional operations. The slides use a lighter, schematic associated-type notation. [GitHub](https://raw.githubusercontent.com/conal/MemoTrie/master/src/Data/MemoTrie.hs)

```haskell
{-# LANGUAGE TypeFamilies, TypeOperators, FlexibleInstances #-}

infixr 0 :->:

class HasTrie k where
  data k :->: v
  trie   :: (k -> v) -> (k :->: v)
  untrie :: (k :->: v) -> (k -> v)

memo :: HasTrie k => (k -> v) -> (k -> v)
memo = untrie . trie
```

Read `k :->: v` as “a table indexed by `k`, containing values of type `v`.”

`trie` tabulates a function. `untrie` looks up a table.

The intended laws are:

```haskell
untrie (trie f) = f
trie (untrie t) = t
```

Subject to the totality qualification, these say that neither direction loses information.

The surprising consequence is:

```haskell
memo = untrie . trie
```

is semantically the identity, while operationally changing the representation through which applications are performed.

### Unit and Boolean keys

The representations are exactly the ones we already discovered:

```haskell
instance HasTrie () where
  newtype () :->: v = UnitTrie v

  trie f = UnitTrie (f ())

  untrie (UnitTrie v) () = v


instance HasTrie Bool where
  data Bool :->: v = BoolTrie v v

  trie f = BoolTrie (f False) (f True)

  untrie (BoolTrie falseResult trueResult) b =
    if b then trueResult else falseResult
```

There is no explicit cache-hit branch, cache-miss branch, or insertion operation.

The field is already there as an unevaluated expression. Looking it up demands its value. Lazy evaluation supplies the transition from “not computed yet” to “computed and shared.”

For the empty domain, the corresponding representation is a constructor with no result fields. There is no total key with which to perform a lookup.

### Sum keys

Apply the sum rule directly:

```haskell
instance (HasTrie a, HasTrie b) => HasTrie (Either a b) where
  data Either a b :->: v =
    EitherTrie (a :->: v) (b :->: v)

  trie f =
    EitherTrie
      (trie (f . Left))
      (trie (f . Right))

  untrie (EitherTrie leftTable rightTable) =
    either (untrie leftTable) (untrie rightTable)
```

A function over alternatives must provide answers for **both** alternatives. Its table therefore contains both sub-tables, even though any particular lookup uses only one.

### Product keys

Apply the product rule:

```haskell
instance (HasTrie a, HasTrie b) => HasTrie (a, b) where
  newtype (a, b) :->: v =
    PairTrie (a :->: (b :->: v))

  trie f =
    PairTrie (trie (trie . curry f))

  untrie (PairTrie table) (a, b) =
    untrie (untrie table a) b
```

The outer lookup chooses a row; the inner lookup chooses an entry in that row.

These are the essential unit, Boolean, sum, and product representations found in MemoTrie’s implementation. [GitHub](https://raw.githubusercontent.com/conal/MemoTrie/master/src/Data/MemoTrie.hs)

This also explains why “memoization is the identity” is not a suggestion to optimize it away. Removing the intermediate table removes the intended sharing. The package source explicitly warns against an `untrie (trie f) = f` rewrite that would defeat memoization. [GitHub](https://raw.githubusercontent.com/conal/MemoTrie/master/src/Data/MemoTrie.hs)

## 5. Recursive key types produce recursive tables  
*Slide 17, expanding the earlier examples*

So far the domains have been assembled from small pieces. What about ordinary algebraic data types?

Expose their constructors as sums and their constructor arguments as products. For example:

\[
[A]\cong 1+A\times[A].
\]

A list is either empty or a head paired with a tail.

Apply the table equations:

\[
\begin{aligned}
T_{[A]}(V)
&\cong T_{1+A\times[A]}(V)\\
&\cong T_1(V)\times T_{A\times[A]}(V)\\
&\cong V\times T_A(T_{[A]}(V)).
\end{aligned}
\]

An equivalent table shape is therefore:

```haskell
data ListTable a v =
  ListTable v (a :->: ListTable a v)
```

At each node, store the answer for the empty remaining list, plus a table mapping the next element to another list table.

The actual package obtains its list instance by converting between `[a]` and `Either () (a, [a])`, then reusing the sum and product instances. It does not need a separately invented lookup algorithm for lists. [GitHub](https://raw.githubusercontent.com/conal/MemoTrie/master/src/Data/MemoTrie.hs)

### Boolean lists give an infinite binary tree

Specialize the equation to `Bool`. A Boolean-indexed table is a pair, so:

\[
T_{[\mathrm{Bool}]}(V)
\cong
V\times T_{[\mathrm{Bool}]}(V)\times T_{[\mathrm{Bool}]}(V).
\]

That is a value-labelled binary tree:

```haskell
data BitTable v =
  Node v (BitTable v) (BitTable v)
```

Here is an expanded implementation of that derived shape:

```haskell
tabBits :: ([Bool] -> v) -> BitTable v
tabBits f =
  Node
    (f [])
    (tabBits (f . (False :)))
    (tabBits (f . (True  :)))

lookupBits :: BitTable v -> [Bool] -> v
lookupBits (Node value _ _) [] = value
lookupBits (Node _ left right) (b : bs) =
  lookupBits (if b then right else left) bs

memoBits :: ([Bool] -> v) -> [Bool] -> v
memoBits f = lookupBits (tabBits f)
```

The root holds `f []`. Its left child holds `f [False]`; its right child holds `f [True]`. Continuing down a path builds up the argument.

This tree is infinite in its mathematical description. That is not an instruction to allocate or evaluate an infinite amount of data.

A finite lookup traverses a finite path. Unvisited branches can remain unevaluated, and results at visited nodes can also remain unevaluated until demanded. Further computation of a result may, of course, demand additional lookups.

This is where laziness is essential rather than merely convenient.

### Unary natural numbers give a stream

For unary naturals:

```haskell
data Nat = Zero | Succ Nat
```

we have:

\[
\mathrm{Nat}\cong 1+\mathrm{Nat},
\]

and hence:

\[
T_{\mathrm{Nat}}(V)\cong V\times T_{\mathrm{Nat}}(V).
\]

That is an infinite stream:

```haskell
data Stream v = Cons v (Stream v)
```

Its entries correspond to `Zero`, `Succ Zero`, and so on. Elliott’s related work explicitly develops this correspondence between unary numbers and streams. [Conal](https://conal.net/blog/tag/trie/)

Representation still matters for performance. Indexing a unary stream at position \(n\) requires traversing \(n\) links. A bit-oriented representation can instead navigate according to the digits of the key. MemoTrie’s numeric machinery uses bit representations rather than treating every number as a unary list position. [GitHub](https://raw.githubusercontent.com/conal/MemoTrie/master/src/Data/MemoTrie.hs)

The lesson is not that all representations are equally efficient. It is that the representation can be *derived and justified*, rather than introduced as an unexplained trick.

## 6. Run the construction backward: logarithms of data structures  
*Slides 18–21*

This is a substantial part of the surviving talk, not a passing aside.

So far we have asked:

> Given a key type, what data structure represents functions from it?

Now reverse the question:

> Given a data structure, what is its index type?

If a table is an exponential,

\[
F(V)\cong V^K,
\]

then finding its key type resembles taking a logarithm:

\[
K\cong\log_V F(V).
\]

This is structural algebra, not numerical logarithm evaluation.

The reverse rules say:

\[
\begin{aligned}
\log_V 1 &= 0,\\
\log_V V &= 1,\\
\log_V(U\times W) &= \log_V U+\log_V W,\\
\log_V(U^B) &= B\times\log_V U.
\end{aligned}
\]

The slides turn this into a guessing game using pairs, streams, and infinite binary trees. [Conal](https://conal.net/talks/elegant-memoization.pdf)

### A pair is indexed by a Boolean

For:

```haskell
data Pair v = Pair v v
```

the structure is \(V\times V\). Its index type is:

\[
1+1\cong\mathrm{Bool}.
\]

There are two positions: select the first or select the second.

### A stream is indexed by a natural number

For:

```haskell
data Stream v = Cons v (Stream v)
```

let \(K\) be its index type. Since the structure consists of one value followed by another stream:

\[
K\cong 1+K.
\]

An index either selects the current element or advances and supplies another index.

That is `Zero | Succ K`.

### A full binary tree is indexed by a finite bit sequence

For:

```haskell
data Tree v = Branch v (Tree v) (Tree v)
```

the index can select the root, descend left, or descend right:

\[
K\cong 1+K+K
\cong 1+\mathrm{Bool}\times K.
\]

That is a finite path of Boolean choices.

The important distinction is between the **infinite tree** and a **finite address of one of its nodes**. Elliott develops these reverse derivations in his earlier discussion of “unmemoization.” [Conal](https://conal.net/blog/posts/memoizing-polymorphic-functions-via-unmemoization/index.html)

### Lift the algebra to type constructors

Instead of describing a table separately for each result type, describe the whole table constructor.

Let:

\[
\operatorname{Exp}(K)(V)=T_K(V).
\]

Using identity, constant, product, and composition of type constructors:

\[
\begin{aligned}
\operatorname{Exp}(0) &= \operatorname{Const}(1),\\
\operatorname{Exp}(1) &= \operatorname{Id},\\
\operatorname{Exp}(A+B)
  &=\operatorname{Exp}(A)\times\operatorname{Exp}(B),\\
\operatorname{Exp}(A\times B)
  &=\operatorname{Exp}(A)\circ\operatorname{Exp}(B).
\end{aligned}
\]

Here:

\[
(F\times G)(V)=(F(V),G(V)),
\qquad
(F\circ G)(V)=F(G(V)).
\]

This is what the talk means by using **higher-order types**: type constructors themselves become the building blocks of the representation. It is not yet the separate problem of memoizing functions whose *arguments are functions*. Elliott’s earlier higher-order-types article gives the corresponding Haskell formulation using functor combinators. [Conal](https://conal.net/blog/posts/elegant-memoization-with-higher-order-types/index.html)

On the appropriate class of table constructors, the reverse equations are:

\[
\begin{aligned}
\operatorname{Log}(\operatorname{Const}(1)) &= 0,\\
\operatorname{Log}(\operatorname{Id}) &= 1,\\
\operatorname{Log}(F\times G) &= \operatorname{Log}(F)+\operatorname{Log}(G),\\
\operatorname{Log}(F\circ G) &= \operatorname{Log}(F)\times\operatorname{Log}(G).
\end{aligned}
\]

There is a small reconstruction correction here. Slide 21 prints `Log (Const b) = 0`. As a lossless inverse correspondence, this requires the constant to be the singleton type: an arbitrary constant payload would otherwise disappear. The more general line can describe the absence of element positions, but not by itself an isomorphism of the complete structures. [Conal](https://conal.net/talks/elegant-memoization.pdf)

This also explains why not every container is a table for one fixed key type. A fixed-key function `K -> ()` has one total value. An ordinary list of units can have many lengths. Its varying shape carries information that a fixed-key table does not.

## 7. The flaw: the table may forget non-strict behavior  
*Slide 22*

We have repeatedly said “total values.” Now remove that restriction.

In Haskell, a Boolean argument may fail to produce either `False` or `True`. We write that possibility as \(\bot\), represented by expressions such as `undefined` or a nonterminating computation.

Consider:

```haskell
constant :: Bool -> Int
constant _ = 7
```

Then:

```haskell
constant undefined
```

returns `7`, because `constant` never examines its argument.

But:

```haskell
memoBool constant undefined
```

does not return `7`. The memoized function must inspect the Boolean to choose one of its two stored answers.

The problem is not merely an unfortunate lookup implementation. The tabulation itself has discarded information.

These functions:

```haskell
nonStrict :: Bool -> Int
nonStrict _ = 7

strict :: Bool -> Int
strict b = if b then 7 else 7
```

produce the same table:

```haskell
(7, 7)
```

Yet they behave differently on `undefined`.

Therefore a pair of ordinary Boolean results cannot fully represent every Haskell function of type `Bool -> Int`. Elliott’s non-strict-memoization article explains precisely this failure. [Conal](https://conal.net/blog/posts/nonstrict-memoization/index.html)

The issue extends inside structured keys:

```haskell
first :: (Int, Bool) -> Int
first = fst
```

We have:

```haskell
first (7, undefined)  -- 7
```

But the product trie first chooses an `Int` row and then a `Bool` entry. Selecting that entry demands the second component, which `fst` would otherwise ignore.

Thus being strict only in the outer constructor is not enough. Lookup can introduce demands on components that the original function never examines. The MemoTrie source explicitly acknowledges this problem in its proof commentary. [GitHub](https://raw.githubusercontent.com/conal/MemoTrie/master/src/Data/MemoTrie.hs)

The same phenomenon can affect infinite inputs. A function may produce a result after inspecting a finite prefix, while a trie lookup for an entire list key continues trying to reach its end.

This is the talk’s central irony:

**Laziness makes infinite memo tables usable, but non-strictness invalidates the uncomplicated isomorphism story.**

The slide expresses this as the isomorphisms holding for a strict language. More precisely, the displayed derivations suppress distinctions involving partial values; they are not unrestricted observational-equivalence proofs for arbitrary Haskell programs. The closing slide deliberately foregrounds this limitation rather than hiding it. [Conal](https://conal.net/talks/elegant-memoization.pdf)

## 8. What the closing challenges probably meant  
*Slides 23–24*

The slides end with four terse challenges: non-strict, higher-order, polymorphic, and deep memoization. They do not preserve a detailed explanation of each. [Conal](https://conal.net/talks/elegant-memoization.pdf)

**Non-strict memoization** is the problem just exposed: preserve behavior on partially defined arguments. Merely adding an entry for `undefined` is insufficient, because lookup cannot perform an ordinary pattern match that detects nontermination. Elliott had already explored a solution using least upper bounds and unambiguous choice, so the challenge should not be read as saying that no approaches existed. [Conal](https://conal.net/blog/posts/nonstrict-memoization/index.html)

**Higher-order memoization** concerns keys that are themselves functions:

```haskell
(a -> b) -> r
```

A promising approach is to replace the function-valued key with its trie representation, then memoize over that representation. For a finite domain such as `Bool`, this reduces the key to a finite table. For more general domains, the potentially infinite representation and its strictness requirements become crucial. Elliott’s earlier article explicitly explores this approach. [Conal](https://conal.net/blog/posts/memoizing-higher-order-functions)

**Polymorphic memoization** asks how to represent a whole parametrically polymorphic function, not merely one monomorphic instance. Parametricity can reveal a reusable structure independent of the element type. For example, ignoring partiality, a function of type:

```haskell
forall a. (a, a) -> [a]
```

can encode a pattern of selecting the first or second input. Elliott’s related work develops this connection through the Yoneda lemma and reverse trie constructions. This is supporting context, not evidence that the talk included a Yoneda derivation. [Conal](https://conal.net/blog/posts/memoizing-polymorphic-functions-via-unmemoization/index.html)

**Deep memoization** is the least recoverable item. A plausible reading is memoization of functions nested inside results or larger structures, rather than only an outer function arrow. But the slide supplies only the word “Deep”; a more specific account would be conjecture.

The conceptual conclusion is clear despite those missing explanations: derive a representation from the meaning of a function, and let lazy evaluation provide incremental realization of that representation.

## 9. Reconstructing the correctness appendix  
*Slides 25–32*

The appendix verifies the two conversion laws for the primitive constructions. Its proof style is substitution and simplification, with the same partiality qualification as above. [Conal](https://conal.net/talks/elegant-memoization.pdf)

Here is the essential argument in a notation that makes the recursive structure explicit. Write `buildA` and `lookupA` for tabulation and lookup over keys of type `A`.

For a sum:

```haskell
lookupEither (buildEither f) (Left a)
  = lookupA (buildA (f . Left)) a
  = (f . Left) a
  = f (Left a)
```

The `Right` case is symmetric.

For a product, the constructed table is:

```haskell
buildA (\a -> buildB (\b -> f (a, b)))
```

Lookup at `(a, b)` proceeds as:

```haskell
lookupB
  (lookupA
    (buildA (\a -> buildB (\b -> f (a, b))))
    a)
  b

  = lookupB (buildB (\b -> f (a, b))) b
  = f (a, b)
```

Each simplification invokes a conversion law for a smaller component type.

The reverse direction establishes that rebuilding a table from its lookup function recovers its entries. For Booleans:

```haskell
trie (untrie (BoolTrie x y))
  = BoolTrie
      (untrie (BoolTrie x y) False)
      (untrie (BoolTrie x y) True)
  = BoolTrie x y
```

The sum and product reverse proofs proceed componentwise.

The important methodological point is that the implementation and its proof have the same structure. We do not invent a complicated cache and subsequently try to establish its correctness. We construct it out of conversions whose intended laws explain the implementation.

## 10. A practical companion: using MemoTrie correctly

*This section supplements the reconstruction; Fibonacci is not an example in the surviving main slides.*

The package makes the representation machinery available through `memo`, `memo2`, `memo3`, and `memoFix`. The last one ties recursion through a memoized function:

```haskell
memoFix h = fix (memo . h)
```

That definition is present in the library source. [GitHub](https://raw.githubusercontent.com/conal/MemoTrie/master/src/Data/MemoTrie.hs)

For example:

```haskell
import Data.MemoTrie (memoFix)

fib :: Integer -> Integer
fib = memoFix $ \self n ->
  if n < 0 then
    error "fib: negative argument"
  else if n < 2 then
    n
  else
    self (n - 1) + self (n - 2)

main :: IO ()
main = print (fib 100)
```

The recursive calls go through `self`, which is the memoized function.

By contrast, suppose an ordinary definition recursively calls itself:

```haskell
slowFib n
  | n < 2     = n
  | otherwise = slowFib (n - 1) + slowFib (n - 2)
```

Then:

```haskell
cachedFib = memo slowFib
```

does not change the recursive calls inside `slowFib`. It caches the externally requested result, but the first computation of that result still follows the original recursion. The difference follows directly from which function each recursive call names.

For a curried function:

```haskell
f :: a -> b -> v
```

memoizing only the first arrow stores results of type `b -> v`: functions. Their applications do not automatically become memoized. `memo2` performs memoization on successive arguments; its implementation is equivalent to:

```haskell
memo2 f = memo (memo . f)
```

as the package’s definitions show. [GitHub](https://raw.githubusercontent.com/conal/MemoTrie/master/src/Data/MemoTrie.hs)

Finally, a memo table still has ordinary data-structure costs. Lookup traverses a key representation. Retaining the table retains evaluated portions reachable from it. Rebuilding independent tables does not provide reuse between them. None of the algebra promises free lookup, bounded memory, or automatic eviction.

Those are consequences of the chosen representation and its lifetime, not contradictions of the construction.

---

The most faithful compact reconstruction of the talk’s message is this:

**Memoization is a representation change. The algebra of the argument type derives the table; lazy evaluation makes that table incremental; lookup turns it back into a function. Running the algebra backward identifies the positions of familiar data structures. The elegance is real—but a correct account of Haskell must also preserve the information carried by non-strict behavior.**
````
