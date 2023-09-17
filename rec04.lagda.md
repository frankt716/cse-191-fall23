# Predicate Logic

Recall that propositional logic consists of those logical symbols: T, F, ∧, ∨, ¬, ⇒.
This allows us to express things like "if it is raining, then the floor will be wet".
But propositional logic is not expressive enough to express things like "all men are mortal".
*Predicate logic*[^1] enables us to talk about these things.

## Predicate

A predicate is a phrase like "x is larger than y", where x and y are variables (placeholders) for some *individuals*.
Substituting individuals for these variables yeilds a proposition.
For example, if we substitute 3 for x and 7 for y, then we get "3 is larger than 7, while if we substitute 10 for x and -12 for y, then we get "10 is larger than -12".

## Syntax

The language of predicate logic consists of
- Terms: variables x, y, z, ... and constants such as 0, 1, 2, ...
- Predicate symbols: R, S, T, ...
- Logical symbols: T, F, ∧, ∨, ¬, ⇒, and two additional symbols ∃ (existential quantifier), and ∀ (universal quantifier).

The set of well-formed formulas are defined inductively by
- if R is an n-ary predicate symbol and t₁,t₂,...,tn are terms, then R(t₁,t₂,...,tn) is a well-formed formula;
- T and F are well-formed formulas;
- if φ is a well-formed formula, then ¬ φ is a well-formed formula;
- if φ and ψ are well-formed formulas, then φ ∧ ψ, φ ∨ ψ, and φ ⇒ ψ are well-formed formulas;
- if φ is a well-formed formulas and x is a variable, then ∃x. φ and ∀x. φ are well-formed formulas.

Quantifiers are *binders*.
They bind to variables.
You're probably familiar with this concept already.

```math
  f(x) = x + y
```

In this example, x is *bound* by the function f, while y is *free*.

> :warning: In logic and programming language theory, quantifiers bind loosely (has lower precedence).
> This course adopts the opposite convention i.e., quantifiers bind tightly (has higher precedence).

### Examples

#### ∀x. (x is even ⇒ x + 1 is odd)

There is no free variables in this formula.

#### is-wed ∧ is-5pm ⇒ ∀x. x is here

There is no free variable in this formula.

#### ∃x. P(x) ⇒ Q(y)

x is bound and y is free in this formula.

#### (∃x. P(x)) ⇒ R(x, y)

The first occurence is x is bound but the second occurence of x and y are free.

If it is too confusing we can rename the bound variable without changing its meaning: (∃z. P(z)) ⇒ R(x, y).[^2]
You're probably familiar with this already:

```math
  \begin{align}
    f(x) &= x + y\\
    f(z) &= z + y
  \end{align}
```

These two functions are the same.

[^1]: Also known as *first-order logic*. 
[^2]: This is known as the principle of *α equivalence*, or *referential transparency* in programming language literature. Some programming languages violate this principle (sigh).
