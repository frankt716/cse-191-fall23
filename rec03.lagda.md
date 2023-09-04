# Predicate Logic

While propositional logic allows us to express things like "if red is blue then Frank is color blind", its expressivity is rather limited.
For example, we can't express "all men are mortal" or "there is a prime number larger than googol" in propositional logic.
Predicate logic (a.k.a. *first-order logic*) provides a more expressive language that allows us to talk about these things.

## Predicates

Roughly, a predicate is a phrase like "x is prime", "x is larger than y", "x is the sum of y and z", etc.
These variables (x, y, and z) can be replaced with names of *individuals* to yield meaningful sentences.
For example, if we replace x, y, and z with 7, 8, and 9, respectively, then we have "7 is prime", "7 is larger than 8", "7 is the sum of 8 and 9".

## Syntax

The language of predicate logic[^1] consists of *predicate symbols*, the usual logical symbols (¬, ∨, ∧, ⇨), ∀ (*universal quantifier*), and ∃ (*existential quantifier*).

The collection of *well-formed formulas* is defined inductively as follows:
- If R is an n-ary predicate symbol and t1,...,tn are names of individuals, then R(t1,...,tn) is a well-formed formula.
- If P is a well-formed formula, then ¬ P is a well-formed formula.
- If P is a well-formed formula and x is a variable, then ∀x.P and ∃x.P are well-formed formulas.
- If P and Q are well-formed formulas, then P ∧ Q, P ∨ Q, and P ⇨ Q are well-formed formulas. 

> :warning: In this class, we adopt the convention that quantifiers bind more tightly (has higher precedence).
> In some research communities (e.g., programming language theory), the convention is that quanifiers bind very loosely (has lower precedence).

## Free and bound variables

∀ and ∃ are *binders*.
In fact, you are already familiar with the concept of binders.
For example,
```math
  f(x) = x + 1
```

[^1]: Also known as *first-order logic*.
