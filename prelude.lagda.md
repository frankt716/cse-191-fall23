```agda
{-# OPTIONS --safe #-}
module prelude where
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
