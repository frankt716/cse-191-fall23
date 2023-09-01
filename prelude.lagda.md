```agda
{-# OPTIONS --safe #-}
module prelude where
  open import Agda.Builtin.List
  open import Agda.Builtin.Nat

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

  _≡ℕ_ : Nat → Nat → 𝔹
  zero ≡ℕ zero = true
  zero ≡ℕ suc b = false
  suc a ≡ℕ zero = false
  suc a ≡ℕ suc b = a ≡ℕ b

  ≡-refl : {b : 𝔹} → b ≡ b
  ≡-refl {true} = ⋆
  ≡-refl {false} = ⋆

  _∙_ : {a b c : 𝔹} → a ≡ b → b ≡ c → a ≡ c
  _∙_ {true} {true} {true} p q = ⋆
  _∙_ {false} {false} {false} p q = ⋆

  if_then_else_ : {C : Type} → 𝔹 → C → C → C
  if true then c₁ else c₂ = c₁
  if false then c₁ else c₂ = c₂

  data _∈_ : {A : Type} → A → List A → Type where
    here : {A : Type} → (a : A) → (l : List A) → a ∈ (a ∷ l)
    there : {A : Type} {b : A} → (a : A) → (l : List A) → a ∈ l → a ∈ (b ∷ l)

  map : {A B : Type} → (f : A → B) → List A → List B
  map f [] = []
  map f (x ∷ l) = (f x) ∷ map f l
```
