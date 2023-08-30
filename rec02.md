# Propositional Logic

Propositional logic consists of a language.
A language identifies a collection of symbols that can be used to form sentences and specifies those grammatical sentences.
For instance, the English language has 26 letters (52 if you include uppercase letters) plus puntuation symbols, and the grammar dictates that "I am Frank" is grammatical, while "I are Frank" is not. 

The language of propositional logic consists of *propositional variables*, and *logical symbols*: T (*top*), F (*bottom*), ¬ (*negation*), ∧ (*conjunction*), ∨ (*disjunction*), and ⇨ (*implication*).
propositional variables are intended to denote the basic things that we wish to discuss in propositional logic.

For example, perhaps I am interested in "is it raining" and "is it Wednesday".
I can include two propositional variables, "is-raining" and "is-wednesday", in the language to express these ideas.

## Syntax

*Propositions* are defined *inductively* as follows:
  - propositional variables are propositions
  - T and F are propositions
  - if p is a proposition, then ¬ p is a proposition
  - if p and q are propositions, then p ∧ q is a proposition
  - if p and q are propositions, then p ∨ q is a proposition
  - if p and q are propositions, then p ⇨ q is a proposition
  
By composing propositions with logical symbols, we can form more complicated propositions such as "is-wednesday ⇨ is-raining", and "¬ (is-raining) ∨ is-wednesday ⇨ is-wednesday", etc.

## Semantics

The string "Apfel" by itself does not mean anything, but we associate with it the round and usually red or green fruit (it means apple in German).
Similarly, propositions, such as "is-wednesday ⇨ is-raining" and "¬ (is-raining) ∨ is-wednesday ⇨ is-wednesday", do not mean anything by themselves.
We are going to give each proposition a meaning by assigning to it a Boolean value.

Before we can discuss the semantics of propositional logic, we need to define a few Boolean functions.

### Not

The function `not` take a Boolean value and outputs a Boolean value.
It maps true to false and false to true.
We can define this function using a *truth table*.

| `b`   | `not b` |
| ----- | ------- |
| true  | false   |
| false | true    |


### And

The function `and` takes two Boolean values and outputs true whenever both inputs are true, and outputs false otherwise.

| `a`   | `b`   | `a and b` |
| ----- | ----- | --------- |
| true  | true  | true      |
| true  | false | false     |
| false | true  | false     |
| false | false | false     |

### Or

The function `or` is dual to `and`.
It takes two Boolean values and outputs false whenever both inputs are false, and outputs true otherwise.

| `a`   | `b`   | `a or b`  |
| ----- | ----- | --------- |
| true  | true  | true      |
| true  | false | true      |
| false | true  | true      |
| false | false | false     |

### If ... then ...

The function `if ... then ...` also takes two Boolean values.
Its behaviour may seem somewhat strange.
You can think of it as a promise.
If a promises b but b does not happen, then a has broken his promise so the function outputs false.
On the other hand, if a does not promise b, then a cannot break his promise whether b happens or not, so the function outputs true for these cases.

| `a`   | `b`   | `if a then b`  |
| ----- | ----- | -------------- |
| true  | true  | true           |
| true  | false | false          |
| false | true  | true           |
| false | false | true           |

### Interpretations

With these Boolean functions in hand, we can finally assign meanings to propositions.
The intended meanings of the logical symbols are given in the table below:

| Logical symbol | Intended meaning |
| -------------- | ---------------- |
| T              | true             |
| F              | false            |
| ¬              | not              |
| ∧              | and              |
| ∨              | or               |
| ⇨              | if ... then ...  |

Assigning meanings to propositional variables is where we have a bit more freedom.
We would assign true to is-raining on a rainy day, and false on a sunny day.
Similarly, we would assign true to is-wednesday on a Wednesday, and false on all other days.

Since there are 2 propositional variables, there are 4 possible *realizations*.

|     | is-raining | is-wednesday |
| --- | ---------- | ------------ |
| 𝓜₁ | true       | true         | 
| 𝓜₂ | true       | false        |
| 𝓜₃ | false      | true         |
| 𝓜₄ | false      | false        |

If the language has more propositional variables then there will be more realizations.

Of course, the meaning of a proposition depends on which one of the 4 realizations we are using.
Compound propositions can be assigned meanings systematically as follows:
- the meaning of T in a given realization 𝓜 is true
- the meaning of F in a given realization 𝓜 is false
- the meaning of is-raining in a given realization 𝓜 is given by the realization 𝓜
- the meaning of is-wednesday in a given realization 𝓜 is given by the realization 𝓜
- the meaning of ¬ p in a given realization 𝓜 is given by applying the function `not` to the meaning of p in the same realization
- the meaning of p ∧ q in a given realization 𝓜 is given by applying the function `and` to the meanings of p and q in the same realization
- the meaning of p ∨ q in a given realization 𝓜 is given by applying the function `or` to the meanings of p and q in the same realization
- the meaning of p ⇨ q in a given realization 𝓜 is given by applying the function `if ... then ...` to the meanings of p and q in the same realization

We use the notation ⟦ p ⟧ 𝓜 to mean "the meaning of p in realization 𝓜", or equivalently "the interpretation of p in realization 𝓜".
Let's evaluate ⟦ is-raining ⇨ is-wednesday ⟧ 𝓜₁.
  -  ⟦ is-raining ⇨ is-wednesday ⟧ 𝓜₁\
       = if ⟦ is-raining ⟧ 𝓜₁ then ⟦ is-wednesday ⟧ 𝓜₁\
       = if true then true\
       = true

Let's evaluate the same proposition in 𝓜₃.
 - ⟦ is-raining ⇨ is-wednesday ⟧ 𝓜₃\
     = if ⟦ is-raining ⟧ 𝓜₃ then ⟦ is-wednesday ⟧ 𝓜₃\
     = if false then true\
     = false

This is expected since the weather does not dictate the day.
I have certainly had rainy days that were not on Wednesdays.

## Tautologies

We just saw a proposition that is not true in every realization.
Let's evaluate ⟦ is-raining ⇨ is-raining ⟧ 𝓜₁ instead.
  - ⟦ is-raining ⇨ is-raining ⟧ 𝓜₁\
       = if ⟦ is-raining ⟧ 𝓜₁ then ⟦ is-raining ⟧ 𝓜₁\
       = if true then true\
       = true

Ok.
Let's evaluate it in 𝓜₃.
  - ⟦ is-raining ⇨ is-raining ⟧ 𝓜₃\
       = if ⟦ is-raining ⟧ 𝓜₃ then ⟦ is-raining ⟧ 𝓜₃\
       = if false then false\
       = true

It evaluates to true again.
In fact, this proposition evaluates to true in every realization.
This is expected because if it is raining, then of course it is raining.

Propositions that evaluate to true in all realizations are called *tautologies*.
Let's see some examples.

### ⇨-id

Let P be any proposition.
We claim that P ⇨ P is a tautology.
P can evaluate to either true or false depending on the realization so there are two possibilities to check:

| P     | P ⇨ P |
| ----- | ----- |
| true  | true  |
| false | true  |

### The law of excluded middle

Let P be any proposition.
We claim that P ∨ ¬ P is a tautology.
Again, there are two possibilities to check:

| P     | P ∨ ¬ P |
| ----- | ------- |
| true  | true    |
| false | true    |

### Distributive law

Let's try a more complicated example that involves more propositions.

Let P, Q, and R be propositions.
We claim that P ∧ (Q ∨ R) ⇨ ((P ∧ Q) ∨ (P ∧ R)) is a tautology.
This time, we need to check 8 possibilities since every proposition can evaluate to either true or false depending on the realization.

| P     | Q     | R     | P ∧ (Q ∨ R) ⇨ ((P ∧ Q) ∨ (P ∧ R))
| ----- | ----- | ----- | ---- |
| true  | true  | true  | true |
| true  | true  | false | true |
| true  | false | true  | true |
| true  | false | false | true |
| false | true  | true  | true |
| false | true  | false | true |
| false | false | true  | true |
| false | false | false | true |
