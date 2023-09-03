# Predicate Logic

```agda
module rec03 where
  open import prelude
  open import rec02 hiding (𝐏 ; taut)
  open import Agda.Builtin.Nat
  open import Agda.Builtin.Sigma renaming (Σ to Sig)
```

```agda
  data 𝐕 : Type where
    var : Nat → 𝐕

  data 𝐓 : Type where
    ι : 𝐕 → 𝐓
    c : 𝐓
    f : 𝐓 → 𝐓

  data 𝐏 : Type where
    _R_ : 𝐓 → 𝐓 → 𝐏
    ⊤ ⊥ : 𝐏
    Π_ Σ_ ¬_ : 𝐏 → 𝐏
    _∧_ _∨_ _⇒_ : 𝐏 → 𝐏 → 𝐏
  infix 30 ¬_
  infixl 29 _∧_
  infixl 28 _∨_
  infixr 27 _⇒_
  infix -1 Π_
  infix -1 Σ_
```

```agda
  data 𝓓 : Type where
    one two three : 𝓓

  next : 𝓓 → 𝓓
  next one = two
  next two = three
  next three = one

  _≤_ : 𝓓 → 𝓓 → 𝔹
  one ≤ _ = true
  two ≤ one = false
  two ≤ _ = true
  three ≤ three = true
  three ≤ _ = false

  val : Type
  val = 𝐕 → 𝓓

  t⟦_⟧_ : 𝐓 → val → 𝓓
  t⟦ ι x ⟧ p = p x
  t⟦ c ⟧ p = one
  t⟦ f t ⟧ p = next (t⟦ t ⟧ p)

  _[_] : val → 𝓓 → val
  (p [ a ]) (var x) = if x ≡ℕ 0 then a else (p (var x))

  p⟦_⟧_ : 𝐏 → val → 𝔹
  p⟦ x R y ⟧ p = (t⟦ x ⟧ p) ≤ (t⟦ y ⟧ p)
  p⟦ ⊤ ⟧ p = true
  p⟦ ⊥ ⟧ p = false
  p⟦ ¬ P ⟧ p = not (p⟦ P ⟧ p)
  p⟦ Π P ⟧ p = (p⟦ P ⟧ (p [ one ])) and (p⟦ P ⟧ (p [ two ])) and (p⟦ P ⟧ (p [ three ]))
  p⟦ Σ P ⟧ p = (p⟦ P ⟧ (p [ one ])) or (p⟦ P ⟧ (p [ two ])) or (p⟦ P ⟧ (p [ three ]))
  p⟦ P ∧ Q ⟧ p = (p⟦ P ⟧ p) and (p⟦ Q ⟧ p)
  p⟦ P ∨ Q ⟧ p = (p⟦ P ⟧ p) or (p⟦ Q ⟧ p)
  p⟦ P ⇒ Q ⟧ p = if (p⟦ P ⟧ p) then (p⟦ Q ⟧ p)
```

```agda
  data taut : 𝐏 → Type where
    tautK : {P : 𝐏} → ((p : val) → p⟦ P ⟧ p ≡ true) → taut P
```
