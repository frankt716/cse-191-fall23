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
    zero : 𝐓
    succ : 𝐓 → 𝐓

  data 𝐏 : Type where
    _≤_ : 𝐓 → 𝐓 → 𝐏
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
  val : Type
  val = 𝐕 → Nat

  t⟦_⟧_ : 𝐓 → val → Nat
  t⟦ ι x ⟧ p = p x
  t⟦ zero ⟧ p = 0
  t⟦ succ t ⟧ p = 1 + t⟦ t ⟧ p

  tsubst : 𝐓 → 𝐓 → Nat → 𝐓
  tsubst (ι (var x)) a n = if x ≡ℕ n then a else (ι (var x))
  tsubst zero a n = zero
  tsubst (succ t) a n = succ (tsubst t a n)

  subst : 𝐏 → 𝐓 → Nat → 𝐏
  subst (x ≤ y) a n = (tsubst x a n) ≤ (tsubst y a n)
  subst ⊤ a n = ⊤
  subst ⊥ a n = ⊥
  subst (¬ P) a n = ¬ (subst P a n)
  subst (Π P) a n = Π (subst P a (suc n))
  subst (Σ P) a n = Σ (subst P a (suc n))
  subst (P ∧ Q) a n = (subst P a n) ∧ (subst Q a n)
  subst (P ∨ Q) a n = (subst P a n) ∨ (subst Q a n)
  subst (P ⇒ Q) a n = (subst P a n) ⇒ (subst Q a n)

  _[_] : 𝐏 → 𝐓 → 𝐏
  P [ a ] = subst P a 0

  postulate
    forallb : 𝐏 → 𝔹
    existsb : 𝐏 → 𝔹

  p⟦_⟧_ : 𝐏 → val → 𝔹
  p⟦ x ≤ y ⟧ p = (t⟦ x ⟧ p) ≤ℕ (t⟦ y ⟧ p)
  p⟦ ⊤ ⟧ p = true
  p⟦ ⊥ ⟧ p = false
  p⟦ ¬ P ⟧ p = not (p⟦ P ⟧ p)
  p⟦ Π P ⟧ p = forallb P
  p⟦ Σ P ⟧ p = existsb P
  p⟦ P ∧ Q ⟧ p = (p⟦ P ⟧ p) and (p⟦ Q ⟧ p)
  p⟦ P ∨ Q ⟧ p = (p⟦ P ⟧ p) or (p⟦ Q ⟧ p)
  p⟦ P ⇒ Q ⟧ p = if (p⟦ P ⟧ p) then (p⟦ Q ⟧ p)

  postulate
    forallbk : {P : 𝐏} {p : val} →
               forallb P ≡ true →
               (a : 𝐓) → p⟦ (P [ a ]) ⟧ p ≡ true
    existsbk1 : {P : 𝐏} {p : val} →
               existsb P ≡ true →
               Sig 𝐓 (λ a → p⟦ (P [ a ]) ⟧ p ≡ true)
    existsbk2 : {P : 𝐏} {p : val} →
               ((Sig 𝐓 (λ a → p⟦ (P [ a ]) ⟧ p ≡ true)) → 𝟘) →
               existsb P ≡ false
               
```

```agda
  data taut : 𝐏 → Type where
    tautK : {P : 𝐏} → ((p : val) → p⟦ P ⟧ p ≡ true) → taut P
```

```agda
  demorgan : {P : 𝐏} → taut ((¬ (Π P)) ⇒ (Σ (¬ P)))
  demorgan = tautK λ p → {!!} where
    h : {P : 𝐏} → (forallb P) ≡ true → (existsb (¬ P)) ≡ false
    h fa = existsbk2 λ x → {!!}
```
