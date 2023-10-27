```agda
{-# OPTIONS --safe #-}
open import prelude-induction
module induction where
  data ℕ : Set where
    zero : ℕ
    succ : ℕ → ℕ
  {-# BUILTIN NATURAL ℕ #-}
```

```agda
  recursor : {C : Type} →
             C →
             (ℕ → C → C) →
             ℕ → C
  recursor c₀ f zero = c₀
  recursor c₀ f (succ n) = f n (recursor c₀ f n)
```

```agda
  induction : {P : ℕ → Type} →
          P zero →
          (∀ k → P k → P (succ k)) →
          ∀ x → P x
  induction c₀ f zero = c₀
  induction c₀ f (succ x) = f x (induction c₀ f x)
```

```agda
  _+_ : ℕ → ℕ → ℕ
  _+_ = recursor (λ x → x) (λ _ f → succ ∘ f)
  infixl 20 _+_

  plus_zero : {n : ℕ} → n + 0 ≐ n
  plus_zero {n} = induction
                  {λ x → x + 0 ≐ x}
                  refl
                  (λ k p → ap succ p)
                  n

  succ_swap : {n m : ℕ} → succ n + m ≐ n + succ m
  succ_swap {n} {m} = induction
                      {λ x → ∀ y → succ x + y ≐ x + succ y}
                      (λ _ → refl)
                      (λ _ x y → ap succ (x y))
                      n
                      m

  plus_com : {n m : ℕ} → n + m ≐ m + n
  plus_com {n} {m} = induction
                     {λ x → x + m ≐ m + x}
                     (! plus_zero)
                     (λ k x → ap succ x ∙ (refl ∙ succ_swap {m} {k}))
                     n

  plus_assoc : {a b c : ℕ} → (a + b) + c ≐ a + (b + c)
  plus_assoc {a} {b} {c} = induction
                           {λ x → x + b + c ≐ x + (b + c)}
                           refl
                           (λ k x → ap succ x)
                           a
```
