# CSE191 Recitation 02 - Propositional Logic

```agda
{-# OPTIONS --safe #-}
module rec02 where
  open import prelude
```

Propositional logic consists of a language.
A language identifies a collection of symbols that can be used to form sentences and specifies those grammatical sentences.
For instance, the English language has 26 letters (52 if you include uppercase letters) plus puntuation symbols, and the Grammar dictates that "I am Frank" is grammatical, while "I are Frank" is not. 

The language of propositional logic consists of *proposition letters*, and *logical symbols*: ⊤ (*top*), ⊥ (*bottom*), ¬ (*negation*), ∧ (*conjunction*), ∨ (*disjunction*), and ⇨ (*implication*).
Proposition letters are intended to denote the basic things that we wish to discuss in propositional logic.

For example, perhaps I am interested in "is it raining" and "is it Wednesday".
I can include two proposition letters, "is-raining" and "is-wednesday", in the language to express these ideas.

## Syntax

A *proposition* is a grammatical sentence.
It is defined *inductively* as follows:
  - proposition letters are propositions
  - ⊤ and ⊥ are propositions
  - if p is a proposition, then ¬ p is a proposition
  - if p and q are propositions, then p ∧ q is a proposition
  - if p and q are propositions, then p ∨ q is a proposition
  - if p and q are propositions, then p ⇨ q is a proposition
  
By composing propositions with logical symbols, we can form more complicated propositions such as "is-wednesday ⇨ is-raining", and "¬ (is-raining) ∨ is-wednesday ⇨ is-wednesday", etc.

```agda
  data 𝐏₀ : Type where
    is-raining is-wednesday : 𝐏₀

  data 𝐏 : Type where
    ⊤ ⊥ : 𝐏
    ι : 𝐏₀ → 𝐏
    ¬_ : 𝐏 → 𝐏
    _∧_ _∨_ _⇨_ : 𝐏 → 𝐏 → 𝐏
  infix 30 ¬_
  infixl 29 _∧_
  infixl 28 _∨_
  infixr 27 _⇨_
```

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
```agda
  not : 𝔹 → 𝔹
  not true = false
  not false = true
```

### And

The function `and` takes two Boolean values and outputs true whenever both inputs are true, and outputs false otherwise.
| `a`   | `b`   | `a and b` |
| ----- | ----- | --------- |
| true  | true  | true      |
| true  | false | false     |
| false | true  | false     |
| false | false | false     |
```agda
  _and_ : 𝔹 → 𝔹 → 𝔹
  true and true = true
  true and false = false
  false and true = false
  false and false = false
```

### Or

The function `or` is dual to `and`.
It takes two Boolean values and outputs false whenever both inputs are false, and outputs true otherwise.
| `a`   | `b`   | `a or b`  |
| ----- | ----- | --------- |
| true  | true  | true      |
| true  | false | true      |
| false | true  | true      |
| false | false | false     |
```agda
  _or_ : 𝔹 → 𝔹 → 𝔹
  true or true = true
  true or false = true
  false or true = true
  false or false = false
```

### If ... then ...

The function `if ... then ...` also takes two Boolean values.
Its behaviour may seem somewhat strange.
You can think of it as a promise.
If a promises b but b does not happen, then a has broken his promise so the function outputs false.
On the other hand, if a does not promise b, then a cannot break his promise whether b happens or not so the function outputs true for these cases.

| `a`   | `b`   | `if a then b`  |
| ----- | ----- | -------------- |
| true  | true  | true           |
| true  | false | false          |
| false | true  | true           |
| false | false | true           |
```agda
  if_then_ : 𝔹 → 𝔹 → 𝔹
  if true then true = true
  if true then  false = false
  if false then true = true
  if false then false = true
```

### Models

With these Boolean functions in hand, we can finally assign meanings to propositions.
The intended meanings of the logical symbols are given in the table below:

| Logical symbol | Intended meaning |
| -------------- | ---------------- |
| ⊤              | true             |
| ⊥              | false            |
| ¬              | not              |
| ∧              | and              |
| ∨              | or               |
| ⇨              | if ... then ...  |

Assigning meanings to proposition letters is where we have a bit more freedom.
We would assign true to is-raining on a rainy day, and false on a sunny day.
Similarly, we would assign true to is-wednesday on Wednesday, and false on all other days.

Since there are 2 proposition letters, there are 4 possible configurations.

|     | is-raining | is-wednesday |
| --- | ---------- | ------------ |
| 𝓜₁ | true       | true         | 
| 𝓜₂ | true       | false        |
| 𝓜₃ | false      | true         |
| 𝓜₄ | false      | false        |

```agda
  record model : Type where
    field
      V₀ : 𝐏₀ → 𝔹
      
  𝓜₁ : model
  𝓜₁ = record { V₀ = V₀ } where
    V₀ : 𝐏₀ → 𝔹
    V₀ is-raining = true
    V₀ is-wednesday = true

  𝓜₂ : model
  𝓜₂ = record { V₀ = V₀ } where
    V₀ : 𝐏₀ → 𝔹
    V₀ is-raining = true
    V₀ is-wednesday = false

  𝓜₃ : model
  𝓜₃ = record { V₀ = V₀ } where
    V₀ : 𝐏₀ → 𝔹
    V₀ is-raining = false
    V₀ is-wednesday = true

  𝓜₄ : model
  𝓜₄ = record { V₀ = V₀ } where
    V₀ : 𝐏₀ → 𝔹
    V₀ is-raining = false
    V₀ is-wednesday = false
```

Of course, the meaning of a proposition depends on which one of the 4 configuration we are using.
Compound propositions can be assigned meanings systematically as follows:
- the meaning of ⊤ in a given configuration 𝓜 is true
- the meaning of ⊥ in a given configuration 𝓜 is false
- the meaning of is-raining in a given configuration 𝓜 is given by the configuration 𝓜
- the meaning of is-wednesday in a given configuration 𝓜 is given by the configuration 𝓜
- the meaning of ¬ p in a given configuration 𝓜 is given by applying the function `not` to the meaning of p in the same configuration
- the meaning of p ∧ q in a given configuration 𝓜 is given by applying the function `and` to the meanings of p and q in the same configuration
- the meaning of p ∨ q in a given configuration 𝓜 is given by applying the function `or` to the meanings of p and q in the same configuration
- the meaning of p ⇨ q in a given configuration 𝓜 is given by applying the function `if ... then ...` to the meanings of p and q in the same configuration

```agda
  ⟦_⟧_ : 𝐏 → model → 𝔹
  ⟦ ⊤ ⟧ 𝓜 = true
  ⟦ ⊥ ⟧ 𝓜 = false
  ⟦ ι is-raining ⟧ record { V₀ = V₀ } = V₀ is-raining
  ⟦ ι is-wednesday ⟧ record { V₀ = V₀ } = V₀ is-wednesday
  ⟦ ¬ p ⟧ 𝓜 = not (⟦ p ⟧ 𝓜)
  ⟦ p ∧ q ⟧ 𝓜 = (⟦ p ⟧ 𝓜) and (⟦ q ⟧ 𝓜)
  ⟦ p ∨ q ⟧ 𝓜 = (⟦ p ⟧ 𝓜) or (⟦ q ⟧ 𝓜)
  ⟦ p ⇨ q ⟧ 𝓜 = if (⟦ p ⟧ 𝓜) then (⟦ q ⟧ 𝓜)
```

We use the notation ⟦ p ⟧ 𝓜 to mean "the meaning of p in configuration 𝓜".
Let's evaluate ⟦ is-raining ⇨ is-wednesday ⟧ 𝓜₁.
  -  ⟦ is-raining ⇨ is-wednesday ⟧ 𝓜₁\
       = if ⟦ is-raining ⟧ 𝓜₁ then ⟦ is-wednesday ⟧ 𝓜₁\
       = if true then true\
       = true

Let try to evaluate the same proposition in 𝓜₃.
 - ⟦ is-raining ⇨ is-wednesday ⟧ 𝓜₃\
     = if ⟦ is-raining ⟧ 𝓜₃ then ⟦ is-wednesday ⟧ 𝓜₃\
     = if false then true\
     = false

This is expected since the whether does not dictate the day.
I have certainly had rainy days that were not on Wednesdays.

## Tautologies

We just saw a proposition that is not true in every configuration.
Let's try to evaluate ⟦ is-raining ⇨ is-raining ⟧ 𝓜₁ instead.
  - ⟦ is-raining ⇨ is-raining ⟧ 𝓜₁\
       = if ⟦ is-raining ⟧ 𝓜₁ then ⟦ is-raining ⟧ 𝓜₁\
       = if true then true\
       = true

Ok.
Let's try to evaluate it in 𝓜₃.
  - ⟦ is-raining ⇨ is-raining ⟧ 𝓜₃\
       = if ⟦ is-raining ⟧ 𝓜₃ then ⟦ is-raining ⟧ 𝓜₃\
       = if false then false\
       = true

It evaluates to true again.
In fact, this proposition evaluates to true in every configuration.
This is expected because if it is raining, then of course it is raining.

Propositions that evaluate to true in all configurations are called *tautologies*.
Let's see some examples.

```agda
  data taut : 𝐏 → Type where
    tautK : {p : 𝐏} → ((𝓜 : model) → ⟦ p ⟧ 𝓜 ≡ true) → taut p
```

### ⇨-id

Let P be any proposition.
We claim that P ⇨ P is a tautology.
P can evaluate to either true or false depending on the configuration so there are two possibilities to check:

| P     | P ⇨ P |
| ----- | ----- |
| true  | true  |
| false | true  |

```agda
  ⇨-id : {p : 𝐏} → taut (p ⇨ p)
  ⇨-id = tautK λ _ → ⇨-id' where
    ⇨-id' : {b : 𝔹} → if b then b ≡ true
    ⇨-id' {true} = ⋆
    ⇨-id' {false} = ⋆
```

### The law of excluded middle

Let P be any proposition.
We claim that P ∨ ¬ P is a tautology.
Again, there are two possibilities to check:

| P     | P ∨ ¬ P |
| ----- | ------- |
| true  | true    |
| false | true    |

```agda
  lem : {p : 𝐏} → taut (p ∨ ¬ p)
  lem = tautK λ _ → lem' where
    lem' : {b : 𝔹} → b or (not b) ≡ true
    lem' {true} = ⋆
    lem' {false} = ⋆
```

### Distributive law

Let's try a more complicated example that involves more propositions.

Let P, Q, and R be propositions.
We claim that P ∧ (Q ∨ R) ⇨ ((P ∧ Q) ∨ (P ∧ R)) is a tautology.
This time, we need to check 8 possibilities since every proposition can evaluate to either true or false depending on the configuration.

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

```agda
  distr : {p q r : 𝐏} → taut (p ∧ (q ∨ r) ⇨ ((p ∧ q) ∨ (p ∧ r)))
  distr = tautK (λ _ → distr') where
    distr' : {a b c : 𝔹} → if (a and (b or c)) then ((a and b) or (a and c)) ≡ true
    distr' {true} {true} {true} = ⋆
    distr' {true} {true} {false} = ⋆
    distr' {true} {false} {true} = ⋆
    distr' {true} {false} {false} = ⋆
    distr' {false} {true} {true} = ⋆
    distr' {false} {true} {false} = ⋆
    distr' {false} {false} {true} = ⋆
    distr' {false} {false} {false} = ⋆
```
