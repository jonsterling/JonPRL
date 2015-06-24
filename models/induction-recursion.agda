{-# OPTIONS --copatterns #-}
{-# OPTIONS --no-positivity-check #-}

-- NOTE: everything in this module can be proved terminating & positive
-- externally; it's also possible to reformulate the definitions such that Agda
-- can prove this, but it obscures things.

module induction-recursion where

open import pervasives
open import coinduction

data IR (I O : Set) : Set₁ where
  ι : O → IR I O
  σ : (S : Set) (T : S → IR I O) → IR I O
  δ : (H : Set) (T : (H → I) → IR I O) → IR I O

element : ∀ {I O} → O → IR I O
element = ι

syntax σ S (λ s → c) = choose⟨ s ∶ S ⟩ c
syntax δ H (λ p → c) = recurse⟨ H ⟩ p ↦ c

record Set/_ (I : Set) : Set₁ where
  constructor _↓_
  field
    dom : Set
    π : dom → I

infixl 100 _↓_
open Set/_

slice : {I : Set} (E : Set) → (E → I) → Set/ I
slice = _↓_

syntax slice E (λ e → p) = e ∶ E ↓ p

infix 0 ⟦_⟧_
⟦_⟧_ : ∀ {I O} → IR I O → Set/ I → Set/ O
⟦ ι o ⟧ X ↓ xi = _ ∶ Unit ↓ o
⟦ σ S T ⟧ X ↓ xi =
  s,t ∶ Σ[ s ∶ S ] dom (⟦ T s ⟧ X ↓ xi) ↓
    let s , t = s,t in π (⟦ T s ⟧ X ↓ xi) t
⟦ δ H T ⟧ X ↓ xi =
  hx,t ∶ Σ[ hx ∶ (H → X) ] dom (⟦ T (xi ∘ hx) ⟧ X ↓ xi) ↓
    let hx , t = hx,t in π (⟦ T (xi ∘ hx) ⟧ X ↓ xi) t

-- Containers (signatures) may be interpreted into IR codes
_◃_ : (S : Set) (P : S → Set) → IR Unit Unit
S ◃ P = choose⟨ s ∶ S ⟩ (recurse⟨ P s ⟩ p ↦ element ⟨⟩)

{-# NO_TERMINATION_CHECK #-}
mutual
  data Fan {I : Set} (c : IR I I) : Set where
    sup : dom (⟦ c ⟧ (Fan c) ↓ fan-idx) → Fan c

  fan-idx : ∀ {I} {c : IR I I} → Fan c → I
  fan-idx {c = c} (sup x) = π (⟦ c ⟧ (Fan c) ↓ fan-idx) x

{-# NO_TERMINATION_CHECK #-}
mutual
  data Spread {I : Set} (c : IR I I) : Set where
    inf : ∞ dom (⟦ c ⟧ Spread c ↓ spread-idx) → Spread c

  spread-idx : ∀ {I} {c : IR I I} → Spread c → I
  spread-idx {c = c} (inf x) = π (⟦ c ⟧ (Spread c) ↓ spread-idx) (♭ x)

-- An IR code for the natural numbers
NatC : IR Unit Unit
NatC = Bool ◃ So

ℕ = Fan NatC

ze : ℕ
ze = sup (ff , absurd , ⟨⟩)

su : ℕ → ℕ
su n = sup (tt , (λ _ → n) , ⟨⟩)

ℕ∞ = Spread NatC

infinity : ℕ∞
infinity = inf (♯ (tt , (λ x → infinity) , ⟨⟩))

ChoiceSequence : Set
ChoiceSequence = Spread (ℕ ◃ λ x → Unit)

ones : ChoiceSequence
ones = inf (♯ (su ze , (λ _ → ones) , ⟨⟩))

nats : ChoiceSequence
nats = go ze
  where
    go : ℕ → ChoiceSequence
    go i = inf (♯ (i , (λ _ → go (su i)) , ⟨⟩))
