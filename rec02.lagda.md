# CSE 191

```agda
{-# OPTIONS --without-K --safe #-}
module rec02 where
  Type = Set

  data 𝟙 : Type where
    ⋆ : 𝟙

  data 𝟘 : Type where

  data 𝔹 : Type where
    true false : 𝔹

  _≡_ : 𝔹 → 𝔹 → Type
  true ≡ true = 𝟙
  true ≡ false = 𝟘
  false ≡ true = 𝟘
  false ≡ false = 𝟙
  infix 19 _≡_

  ≡-refl : (b : 𝔹) → b ≡ b
  ≡-refl true = ⋆
  ≡-refl false = ⋆
```

### Propositions
```agda
  data 𝐏 : Type where
    ⊤ ⊥ is-raining is-wednesday : 𝐏
    ¬_ : 𝐏 → 𝐏
    _∧_ _∨_ _⇨_ : 𝐏 → 𝐏 → 𝐏
  infix 30 ¬_
  infixl 29 _∧_
  infixl 28 _∨_
  infixr 27 _⇨_
```

### Negation

```agda
  not_ : 𝔹 → 𝔹
  not true = false
  not false = true
```

### Conjunction
```agda
  _and_ : 𝔹 → 𝔹 → 𝔹
  true and true = true
  true and false = false
  false and true = false
  false and false = false
```

### Disjunction
```agda
  _or_ : 𝔹 → 𝔹 → 𝔹
  true or true = true
  true or false = true
  false or true = true
  false or false = false
```

### Implication
```agda
  if_then_ : 𝔹 → 𝔹 → 𝔹
  if true then true = true
  if true then  false = false
  if false then true = true
  if false then false = true
```

### Models
```agda
  record model : Type where
    field
      𝓜 : 𝐏 → 𝔹
      top : 𝓜 ⊤ ≡ true
      bot : 𝓜 ⊥ ≡ false
      neg : {p : 𝐏} → 𝓜 (¬ p) ≡ not (𝓜 p)
      cjn : {p q : 𝐏} → 𝓜 (p ∧ q) ≡ (𝓜 p) and (𝓜 q)
      djn : {p q : 𝐏} → 𝓜 (p ∨ q) ≡ (𝓜 p) or (𝓜 q)
      imp : {p q : 𝐏} → 𝓜 (p ⇨ q) ≡ if (𝓜 p) then (𝓜 q)
  open model

  𝓜₁ : model
  𝓜₁ =
    record
    {
      𝓜 = M
    ; top = ⋆
    ; bot = ⋆
    ; neg = ≡-refl _
    ; cjn = ≡-refl _
    ; djn = ≡-refl _
    ; imp = ≡-refl _
    } where
        M : 𝐏 → 𝔹
        M ⊤ = true
        M ⊥ = false
        M is-raining = true
        M is-wednesday = true
        M (¬ p) = not (M p)
        M (p ∧ q) = (M p) and (M q)
        M (p ∨ q) = (M p) or (M q)
        M (p ⇨ q) = if (M p) then (M q)

  inter : model → 𝐏 → 𝔹
  inter record { 𝓜 = 𝓜 ; top = top ; bot = bot ; neg = neg ; cjn = cjn ; djn = djn ; imp = imp } = 𝓜
```
