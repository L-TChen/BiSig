open import Prelude

module Syntax.Context (T : Set) where

infixr 5 _∙_
data Ctx : Set where
  ∅   :                     Ctx
  _∙_ : (A : T) (Γ : Ctx) → Ctx

private variable
  Γ Δ : Ctx
  A B : T

infix 4 _∈_
data _∈_ : T → Ctx → Set where
  zero : {A : T} {Γ : Ctx}
    → A ∈ A ∙ Γ
  suc  : {A B : T} {Γ : Ctx}
    → A ∈ Γ → A ∈ B ∙ Γ

Ren : (Γ Δ : Ctx) → Set
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
