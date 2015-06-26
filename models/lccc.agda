module lccc where

open import Agda.Primitive

Π : (A : Set) (B : A → Set) → Set
Π A B = (x : A) → B x

infix 0 Π
syntax Π A (λ x → B) = Π[ x ∶ A ] B

id : {A : Set} → A → A
id x = x

infixr 9 _∘_
_∘_ : ∀ {a b c}
  → {A : Set a}
  → {B : A → Set b}
  → {C : {x : A} → B x → Set c}
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

-- NOTE: large extensions are possible here with Yoneda embeddings for homs

Ran : ∀ {X : Set} {U : Set} → (U → U → Set) → (X → U) → (X → Set) → (U → Set)
Ran {X} _⇒_ f φ y = ∫↓[ x ∶ X ] (y ⇒ f x) ⋔ φ x

Lan : ∀ {X : Set} {U : Set} → (U → U → Set) → (X → U) → (X → Set) → (U → Set)
Lan {X} _⇒_ f φ y = ∫↑[ x ∶ X ] (f x ⇒ y) ⊗ φ x

module Hyperdoctrine where
  infix 1 _∈_
  _∈_ : ∀ {I} → I → 𝒫 I → Set
  x ∈ φ = φ x

  infix 0 _⊆_
  _⊆_ : ∀ {I} → 𝒫 I → 𝒫 I → Set
  ψ ⊆ φ = ∀ {i} → i ∈ ψ → i ∈ φ

  ⊤-𝒫 : ∀ {I} → 𝒫 I
  ⊤-𝒫 = λ _ → Unit

  !-𝒫 : ∀ {I} (φ : 𝒫 I) → φ ⊆ ⊤-𝒫
  !-𝒫 = λ _ _ → ⟨⟩

  infix 0 _∩_
  _∩_ : ∀ {I} → 𝒫 I → 𝒫 I → Set
  ψ ∩ φ = ∀ {i} → i ∈ ψ × i ∈ φ

  _* : ∀ {X Y} → (X → Y) → (𝒫 Y → 𝒫 X)
  f * = λ φ → φ ∘ f

  infix 1 _[_]
  _[_] : ∀ {X Y} → 𝒫 Y → (X → Y) → 𝒫 X
  φ [ f ] = (f *) φ

  ∃⊣ : ∀ {X Y} → (X → Y) → (𝒫 X → 𝒫 Y)
  ∃⊣ = Lan _≡_

  ∃⊣-adj₁ : ∀ {X Y} {f : X → Y} {ψ φ} → (∃⊣ f ψ ⊆ φ) → (ψ ⊆ φ [ f ])
  ∃⊣-adj₁ p x = p (_ , refl , x)

  ∃⊣-adj₂ : ∀ {X Y} {f : X → Y} {ψ φ} → (ψ ⊆ φ [ f ]) → (∃⊣ f ψ ⊆ φ)
  ∃⊣-adj₂ p (_ , refl , x) = p x

  ⊣∀ : ∀ {X Y} → (X → Y) → (𝒫 X → 𝒫 Y)
  ⊣∀ = Ran _≡_

  ⊣∀-adj₁ : ∀ {X Y} {f : X → Y} {ψ φ} → (ψ [ f ] ⊆ φ) → (ψ ⊆ ⊣∀ f φ)
  ⊣∀-adj₁ p x _ refl = p x

  ⊣∀-adj₂ : ∀ {X Y} {f : X → Y} {ψ φ} → (ψ ⊆ ⊣∀ f φ) → (ψ [ f ] ⊆ φ)
  ⊣∀-adj₂ p x = p x _ refl

  ∃₁ : ∀ {X Y} → 𝒫 (X × Y) → 𝒫 X
  ∃₁ = ∃⊣ fst

  ∀₁ : ∀ {X Y} → 𝒫 (X × Y) → 𝒫 X
  ∀₁ = ⊣∀ fst

  Δ : ∀ {X} → X → X × X
  Δ x = x , x

  I : ∀ {X} → 𝒫 (X × X)
  I = ∃⊣ Δ ⊤-𝒫

module CwF where
  fiber : ∀ {I} → 𝔉 I → 𝒫 I
  fiber f = λ i → Σ[ e ∶ dom f ] map f e ≡ i

  _⁻¹ : ∀ {I} → 𝔉 I → 𝒫 I
  _⁻¹ = fiber

  module pullM {I} {f g : 𝔉 I} where
    obj : Set
    obj = Σ (dom f) (fiber g ∘ map f)

    π₁ : obj → dom f
    π₁ = fst

    π₂ : obj → dom g
    π₂ = fst ∘ snd

    eq : (E : obj) → (map g ∘ π₂) E ≡ (map f ∘ π₁) E
    eq = snd ∘ snd

  pull : ∀ {I} → 𝔉 I → 𝔉 I → Set
  pull f g = pullM.obj {f = f} {g = g}

  infix 1 pull
  syntax pull {I} f g = f ×[ I ] g

  sect : ∀ {I} → 𝔉 I → Set
  sect f = Σ[ f⁻¹ ∶ (_ → dom f) ] Π[ i ∶ _ ] (map f ∘ f⁻¹) i ≡ i

  _* : ∀ {I J} → (I → J) → (𝔉 J → 𝔉 I)
  f * = λ i → (_ ↓ f) ×[ _ ] i ↓ fst

  Ctx : Set₁
  Ctx = Set

  ⋄ : Ctx
  ⋄ = Unit

  Ty : Ctx → Set₁
  Ty = 𝔉

  Tm : (Γ : Ctx) (A : Ty Γ) → Ctx
  Tm _ = sect

  Sub : Ctx → Ctx → Set
  Sub Δ Γ = Δ → Γ

  infix 1 _▸_
  _▸_ : (Γ : Ctx) → Ty Γ → Ctx
  _▸_ Γ = Σ Γ ∘ fiber

  --           θ : Sub Δ Γ
  --           A : Ty Γ
  --    A *[ θ ] : Ty Δ
  --             = (Δ ↓ θ) ×[ Γ ] A ↓ fst
  --             = fam { dom = pull (Δ ↓ θ) A; map = fst }
  --             = fam { dom = Σ Δ (fiber A ∘ θ); map = fst }
  --             = fam { dom = Σ[ d ∶ Δ ] Σ[ x ∶ dom A ] map A x ≡[Γ] θ d; map = fst }
  --
  -- A *[ θ ] -- π₂ --> dom A
  --   |                 |
  --   π₁               map A
  --   |                 |
  --   v                 v
  --   Δ ------- θ ----> Γ

  infix 2 _*ty[_]
  _*ty[_] : ∀ {Δ Γ} → Ty Γ → (Sub Δ Γ → Ty Δ)
  A *ty[ θ ] = (θ *) A

  wkn : {Γ : Ctx} (A : Ty Γ) → Sub (Γ ▸ A) Γ
  wkn A = map A ∘ fst ∘ snd

  var : (Γ : Ctx) (A : Ty Γ) → Tm (Γ ▸ A) (A *ty[ wkn A ])
  var Γ A = M , prf where
    M : (Γ ▸ A) → (dom (A *ty[ wkn A ]))
    M (._ , _ , refl) = (map A _ , _ , refl) , _ , refl
    prf : Π[ x ∶ Γ ▸ A ] map (A *ty[ wkn A ]) (M x) ≡ x
    prf (._ , _ , refl) = refl

  ext : ∀ {Γ Δ} {A : Ty Γ} (θ : Sub Δ Γ) → Tm Δ (A *ty[ θ ]) → Sub Δ (Γ ▸ A)
  ext θ M x with fst M x | snd M x
  ... | ._ , _ , prf | refl = θ x , _ , prf

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
