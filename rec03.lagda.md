```agda
{-# OPTIONS --safe #-}
module rec03 where
  open import prelude
  open import rec02
```

```agda
  identity-law-1 : {P : 𝐏} → taut (P ∧ ⊤ ⇔ P)
  identity-law-1 = tautK λ 𝓜 → identity-law-1' where
    identity-law-1' : {b : 𝔹} → (if b and true then (if b and b then (b and true))) ≡ true
    identity-law-1' {true} = ⋆
    identity-law-1' {false} = ⋆
```

```agda
  identity-law-2 : {P : 𝐏} → taut (P ∨ ⊥ ⇔ P)
  identity-law-2 = tautK (λ 𝓜 → identity-law-2') where
    identity-law-2' : {b : 𝔹} → (if b or false then (if b and b then (b or false))) ≡ true
    identity-law-2' {true} = ⋆
    identity-law-2' {false} = ⋆
```

```agda
  domination-law-1 : {P : 𝐏} → taut (P ∨ ⊤ ⇔ ⊤)
  domination-law-1 = tautK (λ 𝓜 → domination-law-1') where
    domination-law-1' : {b : 𝔹} → (if b or true then (if true then (b or true))) ≡ true
    domination-law-1' {true} = ⋆
    domination-law-1' {false} = ⋆
```

```agda
  domination-law-2 : {P : 𝐏} → taut (P ∧ ⊥ ⇔ ⊥)
  domination-law-2 = tautK (λ 𝓜 → domination-law-2') where
    domination-law-2' : {b : 𝔹} → (if b and false then (if false then (b and false))) ≡ true
    domination-law-2' {true} = ⋆
    domination-law-2' {false} = ⋆
```
