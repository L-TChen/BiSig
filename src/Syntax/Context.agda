open import Prelude

module Syntax.Context where

infixr 5 _∙_
data Ctx (T : Set) : Set where
  ∅   :                       Ctx T
  _∙_ : (A : T) (Γ : Ctx T) → Ctx T

private variable
  T   : Set
  Γ Δ : Ctx T
  A B : T

infix 4 _∈_
data _∈_ {T : Set} : T → Ctx T → Set where
  zero
    : A ∈ A ∙ Γ
  suc
    : A ∈ Γ
    → A ∈ B ∙ Γ

Ren : (Γ Δ : Ctx T) → Set
Ren Γ Δ = ∀ {A} → A ∈ Γ → A ∈ Δ

ext : Ren Γ Δ
  → Ren (A ∙ Γ) (A ∙ Δ)
ext f zero    = zero
ext f (suc x) = suc (f x)

_≟_ : ∀ {Γ} → (x y : A ∈ Γ) → Dec (x ≡ y)
zero  ≟ zero  = yes refl
suc x ≟ suc y with x ≟ y
... | no ¬p = no λ where refl → ¬p refl
... | yes p = yes (cong suc p)
zero  ≟ suc _ = no λ ()
suc _ ≟ zero  = no λ ()

