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
  - if P is a proposition, then ¬ P is a proposition
  - if P and Q are propositions, then P ∧ Q is a proposition
  - if P and Q are propositions, then P ∨ Q is a proposition
  - if P and Q are propositions, then P ⇨ Q is a proposition
  
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

Since there are 2 propositional variables, there are 4 possible *interpretations*.

|     | is-raining | is-wednesday |
| --- | ---------- | ------------ |
| 𝓜₁ | true       | true         | 
| 𝓜₂ | true       | false        |
| 𝓜₃ | false      | true         |
| 𝓜₄ | false      | false        |

If the language has more propositional variables then there will be more interpretations.

Of course, the meaning of a proposition depends on which one of the 4 interpretations we are using.
Compound propositions can be assigned meanings systematically as follows:
- the meaning of T in a given interpretation 𝓜 is true
- the meaning of F in a given interpretation 𝓜 is false
- the meaning of is-raining in a given interpretation 𝓜 is given by the interpretation 𝓜
- the meaning of is-wednesday in a given interpretation 𝓜 is given by the interpretation 𝓜
- the meaning of ¬ p in a given interpretation 𝓜 is given by applying the function `not` to the meaning of p in the same interpretation
- the meaning of p ∧ q in a given interpretation 𝓜 is given by applying the function `and` to the meanings of p and q in the same interpretation
- the meaning of p ∨ q in a given interpretation 𝓜 is given by applying the function `or` to the meanings of p and q in the same interpretation
- the meaning of p ⇨ q in a given interpretation 𝓜 is given by applying the function `if ... then ...` to the meanings of p and q in the same interpretation

#### Examples

Let's evaluate is-raining ⇨ is-wednesday in 𝓜₁.
- the meaning of is-raining ⇨ is-wednesday in 𝓜₁\
	= if (the meaning of is-raining in 𝓜₁) then (the meaning of is-wednesday in 𝓜₁)\
	= if true then true\
	= true

Now, let's evaluate the same proposition in 𝓜₃.
 - the meaning of is-raining ⇨ is-wednesday in 𝓜₃\
     = if (the meaning of is-raining in 𝓜₃) then (the meaning of is-wednesday in 𝓜₃)\
     = if false then true\
     = false

This is expected since the weather does not dictate the day.
I have certainly had rainy days that were not on Wednesdays.

### Evaluating a general proposition

In general, arbitrary propositions P, Q, R, etc, can be assigned a Boolean value using the scheme described above.
These propositions can form more complicated propositions, such as (P ∧ Q) ⇨ R.
We can use the same scheme to evaluate (P ∧ Q) ⇨ R.
For the sake of this example, suppose that P and R evaluate to true, and Q evaluates to false in some interpretation 𝓜.
Then
- The meaning of (P ∧ Q) ⇨ R in 𝓜\
  = if (the meaning of P ∧ Q in 𝓜) then (the meaning of R in 𝓜)\
  = if (the meaning of P ∧ Q in 𝓜) then true\
  = if ((the meaning of P in 𝓜) and (the meaning of Q in 𝓜)) then true\
  = if (true and false) then true\
  = if false then true\
  = true
  
Since a proposition evaluates to either true or false in any interpretation, we can exhaustively list all the possible values that (P ∧ Q) ⇨ R takes with a truth table.

| P     | Q     | R     | (P ∧ Q) ⇨ R
| ----- | ----- | ----- | ----  |
| true  | true  | true  | true  |
| true  | true  | false | false |
| true  | false | true  | true  |
| true  | false | false | true  |
| false | true  | true  | true  |
| false | true  | false | true  |
| false | false | true  | true  |
| false | false | false | true  |

## Tautologies

We just saw a proposition that is not true in every interpretation.
Let's evaluate is-raining ⇨ is-raining in 𝓜₁ instead.
  - the meaning of is-raining ⇨ is-raining in 𝓜₁\
       = if (the meaning of is-raining in 𝓜₁) then (the meaning of is-raining in 𝓜₁)\
       = if true then true\
       = true

Ok.
Let's evaluate it in 𝓜₃.
  - the meaning of is-raining ⇨ is-raining in 𝓜₃\
       = if (the meaning of is-raining in 𝓜₃) then (the meaning of is-raining in 𝓜₃)\
       = if false then false\
       = true

It evaluates to true again.
In fact, this proposition evaluates to true in every interpretation.
This is expected because if it is raining, then of course it is raining.

Propositions that evaluate to true in all interpretations are called *tautologies*.
Let's see some examples.

### ⇨-id

Let P be any proposition.
We claim that P ⇨ P is a tautology.
P can evaluate to either true or false depending on the interpretation so there are two possibilities to check:

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
This time, we need to check 8 possibilities since every proposition can evaluate to either true or false depending on the interpretation.

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

## Exercises

- Evaluate the proposition ¬ (¬ is-raining) ⇨ is-raining in 𝓜₂ and 𝓜₄.
- Let P be a proposition, is ¬ (¬ P) ⇨ P a tautology?
