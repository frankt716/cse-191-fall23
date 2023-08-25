# CSE 191

```agda
{-# OPTIONS --without-K --safe #-}
module rec02 where
  Type = Set

  data 𝔹 : Type where
    true false : 𝔹
```

### Propositions
```agda
  data 𝐏 : Type where
    ⊤ ⊥ is-raining is-wednesday : 𝐏
    ¬_ : 𝐏 → 𝐏
    _∧_ _∨_ _⇨_ : 𝐏 → 𝐏 → 𝐏
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
  ⟦_⟧₁ : 𝐏 → 𝔹
  ⟦ ⊤ ⟧₁ = true
  ⟦ ⊥ ⟧₁ = false
  ⟦ is-raining ⟧₁ = true
  ⟦ is-wednesday ⟧₁ = true
  ⟦ ¬ p ⟧₁ = not ⟦ p ⟧₁
  ⟦ p ∧ q ⟧₁ = ⟦ p ⟧₁ and ⟦ q ⟧₁
  ⟦ p ∨ q ⟧₁ = ⟦ p ⟧₁ or ⟦ q ⟧₁
  ⟦ p ⇨ q ⟧₁ = if ⟦ p ⟧₁ then ⟦ q ⟧₁

  ⟦_⟧₂ : 𝐏 → 𝔹
  ⟦ ⊤ ⟧₂ = true
  ⟦ ⊥ ⟧₂ = false
  ⟦ is-raining ⟧₂ = false
  ⟦ is-wednesday ⟧₂ = true
  ⟦ ¬ p ⟧₂ = not ⟦ p ⟧₂
  ⟦ p ∧ q ⟧₂ = ⟦ p ⟧₂ and ⟦ q ⟧₂
  ⟦ p ∨ q ⟧₂ = ⟦ p ⟧₂ or ⟦ q ⟧₂
  ⟦ p ⇨ q ⟧₂ = if ⟦ p ⟧₂ then ⟦ q ⟧₂

  ⟦_⟧₃ : 𝐏 → 𝔹
  ⟦ ⊤ ⟧₃ = true
  ⟦ ⊥ ⟧₃ = false
  ⟦ is-raining ⟧₃ = false
  ⟦ is-wednesday ⟧₃ = true
  ⟦ ¬ p ⟧₃ = not ⟦ p ⟧₃
  ⟦ p ∧ q ⟧₃ = ⟦ p ⟧₃ and ⟦ q ⟧₃
  ⟦ p ∨ q ⟧₃ = ⟦ p ⟧₃ or ⟦ q ⟧₃
  ⟦ p ⇨ q ⟧₃ = if ⟦ p ⟧₃ then ⟦ q ⟧₃

  ⟦_⟧₄ : 𝐏 → 𝔹
  ⟦ ⊤ ⟧₄ = true
  ⟦ ⊥ ⟧₄ = false
  ⟦ is-raining ⟧₄ = false
  ⟦ is-wednesday ⟧₄ = false
  ⟦ ¬ p ⟧₄ = not ⟦ p ⟧₄
  ⟦ p ∧ q ⟧₄ = ⟦ p ⟧₄ and ⟦ q ⟧₄
  ⟦ p ∨ q ⟧₄ = ⟦ p ⟧₄ or ⟦ q ⟧₄
  ⟦ p ⇨ q ⟧₄ = if ⟦ p ⟧₄ then ⟦ q ⟧₄
```
