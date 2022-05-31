open import Prelude

module Syntax.Untyped.Signature where

Ctx = ℕ

Fam : (ℓ : Level) → Set _
Fam ℓ = Ctx → Set ℓ

Arg  = Ctx
Args = List Ctx

private variable
  O   : Set
  X Y : Fam ℓ

record Sig (O : Set) : Set where
  constructor sig
  field
    ∣_∣ : O → Args

  arity = ∣_∣
open Sig public

⟦_⟧ᵇ_ : Arg → Fam ℓ → Fam ℓ
(⟦ zero  ⟧ᵇ X) Γ = X Γ
(⟦ suc a ⟧ᵇ X) Γ = (⟦ a ⟧ᵇ X) (suc Γ)

⟦_⟧ᵃ_ : Args → Fam ℓ → Fam ℓ
(⟦ []     ⟧ᵃ _) _ = ⊤
(⟦ a ∷ as ⟧ᵃ X) Γ = (⟦ a ⟧ᵇ X) Γ × (⟦ as ⟧ᵃ X) Γ

⟦_⟧_ : (s : Sig O) → Fam ℓ → Fam ℓ
(⟦ sig ar ⟧ X) n = Σ[ o ∈ _ ] (⟦ ar o ⟧ᵃ X) n

mapᵇ : ∀ a
  → (f : X ⇒₁ Y)
  → ⟦ a ⟧ᵇ X ⇒₁ ⟦ a ⟧ᵇ Y
mapᵇ zero    f x = f x
mapᵇ (suc a) f x = mapᵇ a f x

mapᵃ : ∀ as
  → (f : X ⇒₁ Y)
  → ⟦ as ⟧ᵃ X ⇒₁ ⟦ as ⟧ᵃ Y
mapᵃ []       f _       = tt
mapᵃ (a ∷ as) f (x , y) = mapᵇ a f x , mapᵃ as f y

map : ∀ (s : Sig O)
  → (f : X ⇒₁ Y)
  → ⟦ s ⟧ X ⇒₁ ⟦ s ⟧ Y
map s f (o , x) = (o , mapᵃ (arity s o) f x)

_-Algᵇ : (a : Arg) (X : Fam ℓ) → Set ℓ
(a -Algᵇ) X = ⟦ a ⟧ᵇ X ⇒₁ X

_-Algᵃ : (as : Args) (X : Fam ℓ) → Set ℓ
(as -Algᵃ) X = ⟦ as ⟧ᵃ X ⇒₁ X

record _-Alg (s : Sig O) (X : Fam ℓ) : Set ℓ where
  field
    var : Fin     ⇒₁ X
    alg : ⟦ s ⟧ X ⇒₁ X
open _-Alg public