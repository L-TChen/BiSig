open import Prelude

module Syntax.Untyped.Signature where

record Sig (O : Set) : Set where
  constructor sig
  field
    ∣_∣ : O → List ℕ

  arity = ∣_∣
open Sig public

private
  variable
    n m : ℕ
    O   : Set
    X Y : ℕ → Set

⟦_⟧ᵇ_ : ℕ → (ℕ → Set ℓ) → ℕ → Set ℓ
⟦ zero  ⟧ᵇ T = T
⟦ suc a ⟧ᵇ T = ⟦ a ⟧ᵇ T ∘ suc

⟦_⟧ᶜ_ : (as : List ℕ) (X : ℕ → Set ℓ) → (ℕ → Set ℓ)
(⟦ []     ⟧ᶜ _) _ = ⊤
(⟦ a ∷ as ⟧ᶜ T) n = (⟦ a ⟧ᵇ T) n × (⟦ as ⟧ᶜ T) n

⟦_⟧_ : (s : Sig O) (X : ℕ → Set ℓ) → ℕ → Set ℓ
⟦_⟧_ {O} (sig ar) T n = Σ[ o ∈ O ] (⟦ ar o ⟧ᶜ T) n

mapᵇ : (a : ℕ) (f : X ⇒ Y)
  → ⟦ a ⟧ᵇ X ⇒ ⟦ a ⟧ᵇ Y
mapᵇ zero    f x = f x
mapᵇ (suc a) f x = mapᵇ a f x

mapᶜ : (as : List ℕ) (f : X ⇒ Y)
  → ⟦ as ⟧ᶜ X ⇒ ⟦ as ⟧ᶜ Y
mapᶜ []       f _       = tt
mapᶜ (a ∷ as) f (x , y) = mapᵇ a f x , mapᶜ as f y

map : (s : Sig O) (f : X ⇒ Y)
  → ⟦ s ⟧ X ⇒ ⟦ s ⟧ Y
map (sig ar) f (o , x) = (o , mapᶜ (ar o) f x)

_-Algᵇ_ : (a : ℕ) (X : ℕ → Set ℓ) → Set ℓ
a -Algᵇ X = ⟦ a ⟧ᵇ X ⇒ X

_-Algᶜ_ : (as : List ℕ) (X : ℕ → Set ℓ) → Set ℓ
as -Algᶜ X = ⟦ as ⟧ᶜ X ⇒ X

record _-Alg_ (s : Sig O) (X : ℕ → Set ℓ) : Set ℓ where
  field
    var : Fin     ⇒ X
    alg : ⟦ s ⟧ X ⇒ X
open _-Alg_ public