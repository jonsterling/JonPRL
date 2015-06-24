module pervasives where

_∘_ : ∀ {a b c} {A : Set a} {B : A → Set b} {C : {x : A} → B x → Set c} → (∀ {x} (y : B x) → C y) → (g : (x : A) → B x) → ((x : A) → C (g x))
f ∘ g = λ x → f (g x)
infixr 9 _∘_

record Σ (A : Set) (B : A → Set) : Set where
  constructor _,_
  field
    fst : A
    snd : B fst

syntax Σ A (λ x → B) = Σ[ x ∶ A ] B

record Unit : Set where
  constructor ⟨⟩

data Void : Set where

absurd : {A : Set} → Void → A
absurd ()

data Bool : Set where
  tt ff : Bool

So : Bool → Set
So tt = Unit
So ff = Void
