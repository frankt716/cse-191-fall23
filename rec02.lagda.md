# CSE 191

```agda
  {-# OPTIONS --without-K --safe #-}
  module rec02 where
    Type = Set

    data 𝔹 : Type where
      true false : 𝔹

    if_then_else_ : {A : Type} → 𝔹 → A → A → A
    if true then c₁ else c₂ = c₁
    if false then c₁ else c₂ = c₂
```
