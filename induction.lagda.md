```agda
{-# OPTIONS --safe #-}
module induction where
  data ℕ : Set where
    zero : ℕ
    succ : ℕ → ℕ
  {-# BUILTIN NATURAL ℕ #-}

  data _≐_ {A : Set} : A → A → Set where
    refl : ∀ {a : A} → a ≐ a
  infixl 10 _≐_

  !_ : {A : Set} {a b : A} → a ≐ b → b ≐ a
  ! refl = refl

  _∙_ : {A : Set} {a b c : A} → a ≐ b → b ≐ c → a ≐ c
  refl ∙ refl = refl

  ap : {A B : Set} {a b : A} (f : A → B) → a ≐ b → f a ≐ f b
  ap _ refl = refl

  ℕ-ind : {P : ℕ → Set} →
          P zero →
          (∀ k → P k → P (succ k)) →
          ∀ x → P x
  ℕ-ind c₀ f zero = c₀
  ℕ-ind c₀ f (succ x) = f x (ℕ-ind c₀ f x)

  ℕ-rec : {C : Set} →
          C →
          (ℕ → C → C) →
          ℕ → C
  ℕ-rec = ℕ-ind

  _+_ : ℕ → ℕ → ℕ
  _+_ = ℕ-rec (λ x → x) (λ _ f → λ x → succ (f x))
  infixl 20 _+_

  plus_zero : {n : ℕ} → n + 0 ≐ n
  plus_zero {n} = ℕ-ind {λ x → x + 0 ≐ x} refl (λ k p → ap succ p) n

  succ_swap : {n m : ℕ} → succ n + m ≐ n + succ m
  succ_swap {n} {m} = ℕ-ind
                      {λ x → ∀ y → succ x + y ≐ x + succ y}
                      (λ _ → refl)
                      (λ _ x y → ap succ (x y))
                      n
                      m

  plus_com : {n m : ℕ} → n + m ≐ m + n
  plus_com {n} {m} = ℕ-ind
                     {λ x → x + m ≐ m + x}
                     (! plus_zero)
                     (λ k x → ap succ x ∙ (refl ∙ succ_swap {m} {k}))
                     n
```
