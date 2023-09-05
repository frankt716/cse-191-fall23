# Predicate Logic

While propositional logic allows us to express things like "if red is blue then Frank is color blind", its expressivity is rather limited.
For example, we can't express "all men are mortal" or "there is a prime number larger than googol" in propositional logic.
Predicate logic provides a more expressive language that allows us to talk about these things.

## Predicates

A predicate is a phrase like "$`x`$ is prime", "$`x`$ is larger than $`y`$", "$`x`$ is the sum of $`y`$ and $`z`$", etc.
These variables ($`x, y`$, and $`z`$) can be replaced with names of *individuals* to yield meaningful sentences.
For example, if we replace $`x, y`$, and $`z`$ with 7, 8, and 9, respectively, then we have "7 is prime", "7 is larger than 8", "7 is the sum of 8 and 9".

## Syntax

The language of predicate logic[^1] consists of *predicate symbols*, the usual logical symbols ($`\mathrm{T}, \mathrm{F}, \lnot, \land, \lor, \implies`$), $`\forall`$ (*universal quantifier*), and $`\exists`$ (*existential quantifier*).

The collection of well-formed formulas is defined inductively as follows:
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

#### Example

```math
\begin{align}
    \textrm{FV}&(\forall x. R(x,y) \implies \exists z. S(x,y,z))\\
    &= \textrm{FV}(\forall x. R(x,y)) \cup \textrm{FV}(\exists z. S(x,y,z))\\
    &= (\textrm{FV}(R(x,y)) \setminus \{x\}) \cup (\textrm{FV}(S(x,y,z)) \setminus \{z\})\\
    &= (\{x,y\} \setminus \{x\}) \cup (\{x,y,z\} \setminus \{z\})\\
    &= \{x,y\}
\end{align}
```

Note that the first occurrence of $`x`$ in the formula is bound by the $\forall$-quantifier, while the second occurrence of $`x`$ is not because it is not within the scope of the $`\forall`$-quantifier.

> :warning: In this class, we adopt the convention that quantifiers bind more tightly (has higher precedence) than other logical symbols.
> This is the opposite of the traditional convention in logic and programming language theory.
> In these research communities, the convention is that quantifiers bind more loosely (has lower precedence) than other logical symbols.

If it's too confusing, we can even rename the bound $`x`$ to, for example, $`k`$, yielding
```math
    \forall k. R(k,y) \implies \exists z. S(x,y,z)
```
Renaming of bound variables should not change the meaning of the formula[^4].
In fact, you are familiar with this principle already:
```math
\begin{align}
    f(x) &= x + y\\
    f(k) &= k + y
\end{align}
```
Even though the bound variables have different names, these two functions are the same.[^5]

## Semantics

Variables are placeholders for individuals.
To assign a meaning to a well-formed formula in predicate logic, we need to provide a collection of individuals $`\mathcal{D}`$, called the *domain of discourse*, over which variables can range.
This could be the collection of all natural numbers, CSE 191 students, UB students, etc.

Predicate symbols are intended to stand for relations on $`\mathcal{D}`$.
Logical symbols are interpreted in the same way as propositional logic.
The two additional logical symbols ($`\forall`$ and $`\exists`$) have the following intended meanings:

| Logical symbol | Intended meaning                                 |
|----------------|--------------------------------------------------|
| $`\forall`$    | for all individuals in $`\mathcal{D}`$, ...      |
| $`\exists`$    | there is some individual in $`\mathcal{D}`$, ... |

Thus,

- $`\forall x. P`$ evaluates to true if for **every** $`a`$ in $`\mathcal{D}`$, $`P(a)`$ evaluates to true, and false otherwise.
- $`\exists x. P`$ evaluates to true if for **some** $`a`$ in $`\mathcal{D}`$, $`P(a)`$ evaluates to true, and false otherwise.[^6]

### Example

Suppose that the domain of discourse $`\mathcal{D}`$ is the collection of all CSE 191 students present in this recitation and $`P(x) =`$ "$`x`$ speaks German".
Then $`\forall x. P`$ evaluates to true when every student here speaks German, while $`\exists x. P`$ evaluates to true when at least one student here speaks German.

## Tautologies

### DeMorgan

If I know that not everyone speaks German, then I should be able to deduce that at least one person does not speak German.
This intuition explains DeMorgan's law:
```math
    \lnot \forall x. P \implies \exists x. \lnot P
```
is a tautology.
Let's verify this:

| $`\forall x. P`$ | $`\exists x. \lnot P`$ | $`\lnot \forall x. P \implies \exists x. \lnot P`$ |
|------------------|------------------------|----------------------------------------------------|
| true             | true                   | true                                               |
| true             | false                  | true                                               |
| false            | true                   | true                                               |
| false            | false                  | true                                               |

The converse also holds.
Try to verify this on your own.

[^1]: Also known as *first-order logic*.
[^3]: Some details have been swept under the rug here.
[^4]: This is known is the principle of alpha-equivalence.
[^5]: Some programming languages have messed-up scoping rules that violate the principle of alpha-equivalence. They make me sad.
[^6]: A lot of details have been omitted here. One can even argue that what I've written down here doesn't even make sense. These details are outside the scope of this course. Interested readers are encouraged to read introductory text on mathematical logic.
