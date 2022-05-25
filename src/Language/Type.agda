open import Prelude

module Language.Type where


data Ty : Type where
  ι   : Ty
  _⇒_ : Ty → Ty → Ty
  
infixl 4 _▷_

data _▷_ (Γ : Ty → Type) (A : Ty) : Ty → Type where
  Z
    : (Γ ▷ A) A
  S_
    : {B : Ty}
    → Γ B
    → (Γ ▷ A) B

infixl 4 _⁺

data _⁺ (Γ : Type) : Type where
  z
    : Γ ⁺
  s_
    : Γ
    → Γ ⁺

ext : ∀ {Γ Δ}
  → (Γ → Δ) → Γ ⁺ → Δ ⁺
ext ρ z     = z
ext ρ (s x) = s ρ x

instance
  open import Category.Functor as F
  open RawFunctor; open FunctorLaw; open Functor

  Functor-⁺ : Functor _⁺
  raw Functor-⁺ .fmap = ext
  law Functor-⁺ .fmap-id z     = refl
  law Functor-⁺ .fmap-id (s x) = refl
  law Functor-⁺ .fmap-comp f g z     = refl
  law Functor-⁺ .fmap-comp f g (s x) = refl

private
  variable
    Γ Δ Ξ : Type

ext-id=id
  : (x : Γ ⁺)
  → ext id x ≡ x
ext-id=id z     = refl
ext-id=id (s x) = refl

ext-assoc
  : (f : Γ → Δ) (g : Δ → Ξ)
  → (x : Γ ⁺)
  → (ext g ∘ ext f) x ≡ ext (g ∘ f) x
ext-assoc f g z     = refl
ext-assoc f g (s x) = refl

infixl 10 _^_

_^_ : Type → ℕ → Type
Γ ^ zero  = Γ
Γ ^ suc n = (Γ ^ n) ⁺

punchIn : (n : ℕ)
  → Γ ^ n → (Γ ⁺) ^ n
punchIn zero    x = s x
punchIn (suc n) z     = z
punchIn (suc n) (s x) = s punchIn n x

ext-punchIn=punchIn
  : (n : ℕ)
  → (x : (Γ ^ n) ⁺)
  → ext (punchIn n) x ≡ punchIn (suc n) x
ext-punchIn=punchIn zero z     = refl
ext-punchIn=punchIn zero (s x) = refl
ext-punchIn=punchIn (suc n) z     = refl
ext-punchIn=punchIn (suc n) (s x) = refl

S=punchIn : (x : Γ)
  → s x ≡ punchIn 0 x
S=punchIn x = refl
