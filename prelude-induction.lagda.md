```agda
{-# OPTIONS --safe #-}
module prelude-induction where
  Type = Set

  data _≐_ {A : Type} : A → A → Type where
    refl : ∀ {a} → a ≐ a
  infixl 10 _≐_

  !_ : {A : Type} {a b : A} → a ≐ b → b ≐ a
  ! refl = refl

  _∙_ : {A : Type} {a b c : A} → a ≐ b → b ≐ c → a ≐ c
  refl ∙ q = q

  ap : {A B : Type} {a b : A} → (f : A → B) → a ≐ b → f a ≐ f b
  ap _ refl = refl

  _∘_ : {A B C : Type} → (B → C) → (A → B) → A → C
  (f ∘ g) a = f (g a)
```
