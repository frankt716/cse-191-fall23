# CSE191 Recitation 02 - Propositional Logic

```agda
{-# OPTIONS --safe #-}
module rec02 where
  open import prelude
```
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
  
In the previous example, we included "is-raining" and "is-wednesday" as proposition letters.
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
Its behavior may seem somewhat strange.
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

## Models

With these Boolean functions in hand, we can finally talk about semantics.
The intended meanings of the logical symbols are given in the table below:

| Logical symbol | Intended meaning |
| -------------- | ---------------- |
| ⊤              | true             |
| ⊥              | false            |
| ¬              | not              |
| ∧              | and              |
| ∨              | or               |
| ⇨              | if ... then ...  |

This leaves us with proposition letters.
It is where we have a bit more freedom.
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

  ⟦_⟧_ : 𝐏 → model → 𝔹
  ⟦ ⊤ ⟧ 𝓜 = true
  ⟦ ⊥ ⟧ 𝓜 = false
  ⟦ ι x ⟧ record { V₀ = V₀ } = V₀ x
  ⟦ ¬ p ⟧ 𝓜 = not (⟦ p ⟧ 𝓜)
  ⟦ p ∧ q ⟧ 𝓜 = (⟦ p ⟧ 𝓜) and (⟦ q ⟧ 𝓜)
  ⟦ p ∨ q ⟧ 𝓜 = (⟦ p ⟧ 𝓜) or (⟦ q ⟧ 𝓜)
  ⟦ p ⇨ q ⟧ 𝓜 = if (⟦ p ⟧ 𝓜) then (⟦ q ⟧ 𝓜)
```

### Tautologies
```agda
  data taut : 𝐏 → Type where
    tautK : {p : 𝐏} → ((𝓜 : model) → ⟦ p ⟧ 𝓜 ≡ true) → taut p

  ⇨-id : {p : 𝐏} → taut (p ⇨ p)
  ⇨-id = tautK λ _ → ⇨-id' where
    ⇨-id' : {b : 𝔹} → if b then b ≡ true
    ⇨-id' {true} = ⋆
    ⇨-id' {false} = ⋆

  lem : {p : 𝐏} → taut (p ∨ ¬ p)
  lem = tautK λ _ → lem' where
    lem' : {b : 𝔹} → b or (not b) ≡ true
    lem' {true} = ⋆
    lem' {false} = ⋆

  lnc : {p : 𝐏} → taut (¬ (p ∧ ¬ p))
  lnc = tautK λ _ → lnc' where
    lnc' : {b : 𝔹} → not (b and (not b)) ≡ true
    lnc' {true} = ⋆
    lnc' {false} = ⋆

  dne : {p : 𝐏} → taut (¬(¬ p) ⇨ p)
  dne = tautK λ _ → dne' where
    dne' : {b : 𝔹} → if (not (not b)) then b ≡ true
    dne' {true} = ⋆
    dne' {false} = ⋆

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

  demorgan : {p q : 𝐏} → taut (¬ (p ∨ q) ⇨ ¬ p ∧ ¬ q)
  demorgan = tautK (λ _ → demorgan') where
    demorgan' : {a b : 𝔹} → if (not (a or b)) then ((not a) and (not b)) ≡ true
    demorgan' {true} {true} = ⋆
    demorgan' {true} {false} = ⋆
    demorgan' {false} {true} = ⋆
    demorgan' {false} {false} = ⋆

  exfalso : {p : 𝐏} → taut (⊥ ⇨ p)
  exfalso = tautK (λ _ → exfalso') where
    exfalso' : {b : 𝔹} → if false then b ≡ true
    exfalso' {true} = ⋆
    exfalso' {false} = ⋆

  modus-ponens : {p q : 𝐏} → taut (p ∧ (p ⇨ q) ⇨ q)
  modus-ponens = tautK (λ _ → modus-ponens') where
    modus-ponens' : {a b : 𝔹} → if (a and (if a then b)) then b ≡ true
    modus-ponens' {true} {true} = ⋆
    modus-ponens' {true} {false} = ⋆
    modus-ponens' {false} {true} = ⋆
    modus-ponens' {false} {false} = ⋆
```
