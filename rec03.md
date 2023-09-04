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

### Free and bound variables

$`\forall`$ and $`\exists`$ are *binders*.
In fact, you are already familiar with the concept of binders.
For example,
```math
  f(x) = x + y
```
In this example, $`x`$ is *bound* because it varies according to what is plugged into the function, while $`y`$ is *free*.
We can calculate the collection of free variables systematically.
- $`\textrm{FV}(R(x_{1},\ldots,x_{n})) = \{x_{1},\ldots,x_{n}\}`$[^3]
- $`\textrm{FV}(\lnot P) = \textrm{FV}(P)`$
- $`\textrm{FV}(P \land Q) = \textrm{FV}(P) \cup \textrm{FV}(Q)`$
- $`\textrm{FV}(P \lor Q) = \textrm{FV}(P) \cup \textrm{FV}(Q)`$
- $`\textrm{FV}(P \implies Q) = \textrm{FV}(P) \cup \textrm{FV}(Q)`$
- $`\textrm{FV}(\forall x.P) = \textrm{FV}(P) \setminus \{x\}`$
- $`\textrm{FV}(\exists x.P) = \textrm{FV}(P) \setminus \{x\}`$

> :warning: In this class, we adopt the convention that quantifiers bind more tightly (has higher precedence) than other logical symbols.
> This is the opposite of the traditional convention in logic and programming language theory.
> In these research communities, the convention is that quantifiers bind more loosely (has lower precedence) than other logical symbols.

#### Example

```math
\begin{align}
    \textrm{FV}&((\forall x. R(x,y)) \implies \exists z. S(x,y,z))\\
    &= \textrm{FV}(\forall x. R(x,y)) \cup \textrm{FV}(\exists z. S(x,y,z))\\
    &= (\textrm{FV}(R(x,y)) \setminus \{x\}) \cup (\textrm{FV}(S(x,y,z)) \setminus \{z\})\\
    &= (\{x,y\} \setminus \{x\}) \cup (\{x,y,z\} \setminus \{z\})\\
    &= \{x,y\}
\end{align}
```

Note that the first occurrence of x in the formula is bound by the quantifier forall, while the second occurrence of x is not because it is not in the scope of the forall quantifier.
If it's too confusing, we can even change the name of the bound variable.
(∀k.k >= y) -> ∃z.x+y=z
Renaming of bound variables does not change the meaning of the formula[^4].
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
[^3]: Something is being swept under the rug here. Ignore this detail for the time-being.
[^4]: This is known is the principle of alpha-equivalence.
