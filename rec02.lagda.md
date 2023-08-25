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
      V₀ : 𝐏₀ → 𝔹
      
  𝓜₁ : model
  𝓜₁ = record { V₀ = V₀ } where
    V₀ : 𝐏₀ → 𝔹
    V₀ is-raining = false
    V₀ is-wednesday = false

  𝓜₂ : model
  𝓜₂ = record { V₀ = V₀ } where
    V₀ : 𝐏₀ → 𝔹
    V₀ is-raining = false
    V₀ is-wednesday = true

  𝓜₃ : model
  𝓜₃ = record { V₀ = V₀ } where
    V₀ : 𝐏₀ → 𝔹
    V₀ is-raining = true
    V₀ is-wednesday = false

  𝓜₄ : model
  𝓜₄ = record { V₀ = V₀ } where
    V₀ : 𝐏₀ → 𝔹
    V₀ is-raining = true
    V₀ is-wednesday = true

  ⟦_⟧_ : 𝐏 → model → 𝔹
  ⟦ ⊤ ⟧ 𝓜 = true
  ⟦ ⊥ ⟧ 𝓜 = false
  ⟦ ι p₀ ⟧ record { V₀ = V₀ } = V₀ p₀
  ⟦ ¬ p ⟧ 𝓜 = not (⟦ p ⟧ 𝓜)
  ⟦ p ∧ q ⟧ 𝓜 = (⟦ p ⟧ 𝓜) and (⟦ q ⟧ 𝓜)
  ⟦ p ∨ q ⟧ 𝓜 = (⟦ p ⟧ 𝓜) or (⟦ q ⟧ 𝓜)
  ⟦ p ⇨ q ⟧ 𝓜 = if (⟦ p ⟧ 𝓜) then (⟦ q ⟧ 𝓜)
```
