module lccc where

open import Agda.Primitive

Π : (A : Set) (B : A → Set) → Set
Π A B = (x : A) → B x

infix 0 Π
syntax Π A (λ x → B) = Π[ x ∶ A ] B

id : {A : Set} → A → A
id x = x

infixr 9 _∘_
_∘_ :
    {A : Set}
  → {B : A → Set}
  → {C : {x : A} → B x → Set}
  → (g : (∀ {x} (y : B x) → C y))
  → (f : (x : A) → B x)
  → ((x : A) → C (f x))
g ∘ f = λ x → g (f x)

infixr 8 _,_
record Σ (A : Set) (B : A → Set) : Set where
  constructor _,_
  field
    fst : A
    snd : B fst
open Σ

infix 0 Σ
syntax Σ A (λ x → B) = Σ[ x ∶ A ] B

infixr 0 _×_
_×_ : (A : Set) (B : Set) → Set
A × B = Σ A (λ _ → B)

infix 1 _≡_
data _≡_ {a} {A : Set a} (x : A) : A → Set a where
  refl : x ≡ x
{-# BUILTIN EQUALITY _≡_ #-}
{-# BUILTIN REFL refl #-}

sym : ∀ {a} {A : Set a} {x y : A} → x ≡ y → y ≡ x
sym refl = refl

trans : ∀ {a} {A : Set a} {x y z : A} → y ≡ z → x ≡ y → x ≡ z
trans refl refl = refl

record Unit : Set where
  constructor ⟨⟩

data Void : Set where

absurd : {A : Set} → Void → A
absurd ()

End : ∀ (I : Set) (φ : I → Set) → Set
End = Π

infix 0 End
syntax End I (λ x → φ) = ∫↓[ x ∶ I ] φ

infixr 0 _⋔_
_⋔_ : Set → Set → Set
A ⋔ B = A → B

Coend : (A : Set) (φ : A → Set) → Set
Coend = Σ

infix 0 Coend
syntax Coend I (λ x → φ) = ∫↑[ x ∶ I ] φ

infixr 0 _⊗_
_⊗_ : Set → Set → Set
A ⊗ B = A × B

𝒫 : Set → Set₁
𝒫 I = I → Set

infix 0 _↓_
record 𝔉 (I : Set) : Set₁ where
  constructor _↓_
  field
    dom : Set
    map : dom → I
open 𝔉

Ran : ∀ {X : Set} {U : Set} → (U → U → Set) → (X → U) → (X → Set) → (U → Set)
Ran {X} _⇒_ f φ y = ∫↓[ x ∶ X ] (y ⇒ f x) ⋔ φ x

Lan : ∀ {X : Set} {U : Set} → (U → U → Set) → (X → U) → (X → Set) → (U → Set)
Lan {X} _⇒_ f φ y = ∫↑[ x ∶ X ] (f x ⇒ y) ⊗ φ x

module Hyperdoctrine where
  ∃⊣ : ∀ {X Y} → (X → Y) → (𝒫 X → 𝒫 Y)
  ∃⊣ = Lan _≡_

  ⊣∀ : ∀ {X Y} → (X → Y) → (𝒫 X → 𝒫 Y)
  ⊣∀ = Ran _≡_

  ∃₁ : ∀ {X Y} → 𝒫 (X × Y) → 𝒫 X
  ∃₁ = ∃⊣ fst

  ∀₁ : ∀ {X Y} → 𝒫 (X × Y) → 𝒫 X
  ∀₁ = ⊣∀ fst

  δ : ∀ {X} → X → X × X
  δ x = x , x

  Θ : ∀ {X} → 𝒫 (X × X)
  Θ = ∃⊣ δ (λ _ → Unit)

module CwF where
  _⁻¹ : ∀ {I} → 𝔉 I → 𝒫 I
  f ⁻¹ = λ i → Σ[ e ∶ dom f ] map f e ≡ i

  Pull : ∀ {I} → 𝔉 I → 𝔉 I → Set
  Pull f g = Σ[ x ∶ dom f ] Σ[ y ∶ dom g ] map f x ≡ map g y

  infix 1 Pull
  syntax Pull {I} f g = f ×[ I ] g

  Sect : ∀ {I} → 𝔉 I → Set
  Sect {I} f = Σ[ f⁻¹ ∶ (I → dom f) ] Π[ i ∶ I ] map f (f⁻¹ i) ≡ i

  _* : ∀ {I J} → (I → J) → (𝔉 J → 𝔉 I)
  _* {I} {J} f i = (I ↓ f) ×[ J ] i ↓ fst

  Ctx : Set₁
  Ctx = Set

  ⋄ : Ctx
  ⋄ = Unit

  Ty : Ctx → Set₁
  Ty = 𝔉

  Tm : (Γ : Ctx) (A : Ty Γ) → Ctx
  Tm _ A = Sect A

  Sub : Ctx → Ctx → Set
  Sub Δ Γ = Δ → Γ

  infix 1 _▸_
  _▸_ : (Γ : Ctx) (A : Ty Γ) → Ctx
  Γ ▸ A = Σ Γ (A ⁻¹)

  --           θ : Sub Δ Γ
  --           A : Ty Γ
  --    A *[ θ ] : Ty Δ
  --             = (Δ ↓ θ) ×[ Γ ] A ↓ π₁
  --             = fam { dom = pull (Δ ↓ θ) A; map = π₁ }
  --             = fam { dom = Σ[ d ∶ Δ ] Σ[ x ∶ dom A ] θ d ≡[Γ] A x; map = π₁ }
  --
  -- A *[ θ ] --- π₁ ∘ π₂ ---> dom A
  --   |                        |
  --   π₁                      map A
  --   |                        |
  --   v                        v
  --   Δ --------- θ ---------> Γ

  infix 2 _*ty[_]
  _*ty[_] : ∀ {Δ Γ} → Ty Γ → (Sub Δ Γ → Ty Δ)
  A *ty[ θ ] = (θ *) A

  wkn : {Γ : Ctx} (A : Ty Γ) → Sub (Γ ▸ A) Γ
  wkn A = map A ∘ fst ∘ snd

  var : (Γ : Ctx) (A : Ty Γ) → Tm (Γ ▸ A) (A *ty[ wkn A ])
  var Γ A = M , sec where
    M : (Γ ▸ A) → (dom (A *ty[ wkn A ]))
    M (._ , _ , refl) = (map A _ , _ , refl) , _ , refl
    sec : Π[ x ∶ Γ ▸ A ] map (A *ty[ wkn A ]) (M x) ≡ x
    sec (._ , _ , refl) = refl

  ext : ∀ {Γ Δ} {A : Ty Γ} (θ : Sub Δ Γ) → Tm Δ (A *ty[ θ ]) → Sub Δ (Γ ▸ A)
  ext θ M x with fst M x | snd M x
  ... | ._ , _ , sec | refl = θ x , _ , sym sec

  -- without uniqueness...
  law : ∀ {Γ Δ}
    → (γ : Sub Δ Γ)
    → (A : Ty Γ)
    → (M : Tm Δ (A *ty[ γ ]))
    → Σ[ θ ∶ Sub Δ (Γ ▸ A) ] θ ≡ ext γ M
  law γ A M = ext γ M , refl

  Σ↓ : ∀ {Δ Γ} → Sub Δ Γ → (Ty Δ → Ty Γ)
  Σ↓ θ M = dom M ↓ θ ∘ map M

  Π↓ : ∀ {Δ Γ} → Sub Δ Γ → (Ty Δ → Ty Γ)
  Π↓ θ M = {!!}
