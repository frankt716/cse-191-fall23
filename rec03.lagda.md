# Recitation 03

```agda
{-# OPTIONS --safe #-}
module rec03 where
  open import prelude
  open import Agda.Builtin.Nat
  open import Agda.Builtin.List
```

```agda
  data 𝐓 : Type where
    var : Nat → 𝐓
    fun : Nat → List 𝐓 → 𝐓

  data 𝐏 : Type where
    rel : Nat → List 𝐓 → 𝐏
    ⊤ ⊥ : 𝐏
    ¬_ Π_ Σ_ : 𝐏 → 𝐏
    _∧_ _∨_ _⇨_ : 𝐏 → 𝐏 → 𝐏
  infix 30 ¬_
  infix -1 Π_
  infix -1 Σ_
  infixl 29 _∧_
  infixl 28 _∨_
  infixr 27 _⇨_
```

```agda
  [_/_]_ : 𝐓 → Nat → 𝐏 → 𝐏
  [ t / x ] rel R l = {!!}
  [ t / x ] ⊤ = ⊤
  [ t / x ] ⊥ = ⊥
  [ t / x ] (¬ P) = ¬ ([ t / x ] P)
  [ t / x ] (Π P) = {!!}
  [ t / x ] (Σ P) = {!!}
  [ t / x ] (P ∧ Q) = ([ t / x ] P) ∧ ([ t / x ] Q)
  [ t / x ] (P ∨ Q) = ([ t / x ] P) ∨ ([ t / x ] Q)
  [ t / x ] (P ⇨ Q) = ([ t / x ] P) ⇨ ([ t / x ] Q)
```
