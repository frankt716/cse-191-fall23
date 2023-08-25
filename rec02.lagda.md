# CSE191 Recitation 02 - Propositional Logic

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

  ≡-refl : {b : 𝔹} → b ≡ b
  ≡-refl {true} = ⋆
  ≡-refl {false} = ⋆

  _∙_ : {a b c : 𝔹} → a ≡ b → b ≡ c → a ≡ c
  _∙_ {true} {true} {true} p q = ⋆
  _∙_ {false} {false} {false} p q = ⋆
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
  not : 𝔹 → 𝔹
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

### Misc lemmas
```agda
  ap : {a b : 𝔹} {f : 𝔹 → 𝔹} → a ≡ b → f a ≡ f b
  ap {true} {true} p = ≡-refl
  ap {false} {false} p = ≡-refl

  ap₂ : {a b c d : 𝔹} {f : 𝔹 → 𝔹 → 𝔹} → a ≡ b → c ≡ d → f a c ≡ f b d
  ap₂ {true} {true} {true} {true} p q = ≡-refl
  ap₂ {true} {true} {false} {false} p q = ≡-refl
  ap₂ {false} {false} {true} {true} p q = ≡-refl
  ap₂ {false} {false} {false} {false} p q = ≡-refl

  ⇨-id' : {b : 𝔹} → if b then b ≡ true
  ⇨-id' {true} = ⋆
  ⇨-id' {false} = ⋆

  lem' : {b : 𝔹} → b or (not b) ≡ true
  lem' {true} = ⋆
  lem' {false} = ⋆

  lnc' : {b : 𝔹} → not (b and (not b)) ≡ true
  lnc' {true} = ⋆
  lnc' {false} = ⋆

  dne' : {b : 𝔹} → if (not (not b)) then b ≡ true
  dne' {true} = ⋆
  dne' {false} = ⋆

  distr' : {a b c : 𝔹} → if (a and (b or c)) then ((a and b) or (a and c)) ≡ true
  distr' {true} {true} {true} = ⋆
  distr' {true} {true} {false} = ⋆
  distr' {true} {false} {true} = ⋆
  distr' {true} {false} {false} = ⋆
  distr' {false} {true} {true} = ⋆
  distr' {false} {true} {false} = ⋆
  distr' {false} {false} {true} = ⋆
  distr' {false} {false} {false} = ⋆

  demorgan' : {a b : 𝔹} → if (not (a or b)) then ((not a) and (not b)) ≡ true
  demorgan' {true} {true} = ⋆
  demorgan' {true} {false} = ⋆
  demorgan' {false} {true} = ⋆
  demorgan' {false} {false} = ⋆

  exfalso' : {b : 𝔹} → if false then b ≡ true
  exfalso' {true} = ⋆
  exfalso' {false} = ⋆

  modus-ponens' : {a b : 𝔹} → if (a and (if a then b)) then b ≡ true
  modus-ponens' {true} {true} = ⋆
  modus-ponens' {true} {false} = ⋆
  modus-ponens' {false} {true} = ⋆
  modus-ponens' {false} {false} = ⋆
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
  ⇨-id = tautK λ _ → ⇨-id'

  lem : {p : 𝐏} → taut (p ∨ ¬ p)
  lem = tautK λ _ → lem'

  lnc : {p : 𝐏} → taut (¬ (p ∧ ¬ p))
  lnc = tautK λ _ → lnc'

  dne : {p : 𝐏} → taut (¬(¬ p) ⇨ p)
  dne = tautK λ _ → dne'

  distr : {p q r : 𝐏} → taut (p ∧ (q ∨ r) ⇨ ((p ∧ q) ∨ (p ∧ r)))
  distr = tautK (λ _ → distr')

  demorgan : {p q : 𝐏} → taut (¬ (p ∨ q) ⇨ ¬ p ∧ ¬ q)
  demorgan = tautK (λ _ → demorgan')

  exfalso : {p : 𝐏} → taut (⊥ ⇨ p)
  exfalso = tautK (λ _ → exfalso')

  modus-ponens : {p q : 𝐏} → taut (p ∧ (p ⇨ q) ⇨ q)
  modus-ponens = tautK (λ _ → modus-ponens')
```
