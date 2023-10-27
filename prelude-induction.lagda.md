```agda
{-# OPTIONS --safe #-}
open import Agda.Builtin.Equality renaming (_≡_ to _≐_)
open import Agda.Builtin.Nat renaming (Nat to ℕ)
module prelude-induction where
  Type = Set

  !_ : {A : Type} {a b : A} → a ≐ b → b ≐ a
  ! refl = refl

  _∙_ : {A : Type} {a b c : A} → a ≐ b → b ≐ c → a ≐ c
  refl ∙ q = q

  ap : {A B : Type} {a b : A} → (f : A → B) → a ≐ b → f a ≐ f b
  ap _ refl = refl

  _∘_ : {A B C : Type} → (B → C) → (A → B) → A → C
  (f ∘ g) a = f (g a)

  plus_zero : ∀ {n} → n + 0 ≐ n
  plus_zero {zero} = refl
  plus_zero {suc n} = ap suc plus_zero
```
