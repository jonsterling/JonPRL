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

mutual
  -- wellfounded trees on IR codes. It's not clearly strictly positive &
  -- terminating, but it can be proved externally.
  data Fan {I : Set} (c : IR I I) : Set where
    fan : no-fan c c → Fan c

  fan-idx : {I : Set} {c : IR I I} → Fan c → I
  fan-idx {c = c} (fan t) = de-fan c c t

  no-fan : {I : Set} (c d : IR I I) → Set
  no-fan c (ι x) = Unit
  no-fan c (σ S T) = Σ[ s ∶ S ] no-fan c (T s)
  no-fan c (δ H T) = Σ[ hc ∶ (H → Fan c) ] no-fan c (T (λ h → fan-idx (hc h)))

  de-fan : {I : Set} (c d : IR I I) → no-fan c d → I
  de-fan c (ι i) ⟨⟩ = i
  de-fan c (σ S T) (s , t) = de-fan c (T s) t
  de-fan c (δ H T) (hc , t) = de-fan c (T (λ h → fan-idx (hc h))) t

-- Containers (signatures) may be interpreted into IR codes
_◃_ : (S : Set) (P : S → Set) → IR Unit Unit
S ◃ P = choose⟨ s ∶ S ⟩ (recurse⟨ P s ⟩ p ↦ element ⟨⟩)

-- An IR code for the natural numbers
NatC : IR Unit Unit
NatC = Bool ◃ So

-- The fan on NatC is simply the set of natural numbers
ℕ = Fan NatC

ze : ℕ
ze = fan (ff , absurd , _)

su : ℕ → ℕ
su n = fan (tt , (λ _ → n ) , _)
