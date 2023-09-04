# Predicate Logic

While propositional logic allows us to express things like "if red is blue then Frank is color blind", its expressivity is rather limited.
For example, we can't express "all men are mortal" or "there is a prime number larger than googol" in propositional logic.
Predicate logic provides a more expressive language that allows us to talk about these things.

## Predicates

Roughly, a predicate is a phrase like "$`x`$ is prime", "$`x`$ is larger than $`y`$", "$`x`$ is the sum of $`y`$ and $`z`$", etc.
These variables ($`x, y`$, and $`z`$) can be replaced with names of *individuals* to yield meaningful sentences.
For example, if we replace $`x, y`$, and $`z`$ with 7, 8, and 9, respectively, then we have "7 is prime", "7 is larger than 8", "7 is the sum of 8 and 9".

## Syntax

The language of predicate logic[^1] consists of *predicate symbols*, the usual logical symbols ($`\lnot, \land, \lor, \implies`$), $`\forall`$ (*universal quantifier*), and $`\exists`$ (*existential quantifier*).

The collection of well-formed things[^2] that we can talk about in predicate logic is defined inductively as follows:
- If $`R`$ is an $`n`$-ary predicate symbol and $`t_{1},\ldots,t_{n}`$ are names of individuals, then $`R(t_{1},\ldots,t_{n})`$ is well-formed.
- If $`P`$ is a well-formed, then $`\lnot P`$ is also well-formed.
- If $`P`$ is a well-formed and $`x`$ is a variable, then $`\forall x.P`$ and $`\exists x.P`$ are well-formed.
- If $`P`$ and $`Q`$ are well-formed, then $`P \land Q`$, $`P \lor Q`$, and $`P \implies Q`$ are well-formed. 

> :warning: In this class, we adopt the convention that quantifiers bind more tightly (has higher precedence).
> In some research communities (e.g., programming language theory), the convention is that quanifiers bind very loosely (has lower precedence).

## Free and bound variables

∀ and ∃ are *binders*.
In fact, you are already familiar with the concept of binders.
For example,
```math
  f(x) = x + y
```
In this example, x is *bound*, while y is *free*.

We can calculate the collection of free variables systematically.
Formally, FV(P) is defined by recursion:
- FV(R(x1,...,xn)) = {x1,...,xn}
- FV(¬P) = FV(P)
- FV(P ∧ Q) = FV(P) ∪ FV(Q)
- FV(P ∧ Q) = FV(P) ∪ FV(Q)
- FV(P ⇨ Q) = FV(P) ∪ FV(Q)
- FV(∀x.P) = FV(P) \ {x}
- FV(∃x.P) = FV(P) \ {x}

Ex. FV((∀x.x >= y) -> ∃z.x+y=z)

Note that the first occurrence of x in the formula is bound by the quantifier forall, while the second occurrence of x is not because it is not in the scope of the forall quantifier.
If it's too confusing, we can even change the name of the bound variable.
(∀k.k >= y) -> ∃z.x+y=z
Renaming of bound variables does not change the meaning of the formula[^3].
In fact, you are probably familiar with this principle already:
```math
\begin{align}
    f(x) &= x + y\\
    f(z) &= z + y
\end{align}
```
Even though the bound variables have different names, these two functions are the same.

[^1]: Also known as *first-order logic*.
[^2]: These are called *well-formed formulas*.
[^3]: This is known is the principle of alpha-equivalence.
