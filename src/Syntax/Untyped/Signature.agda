open import Prelude

module Syntax.Untyped.Signature where

record Signature (O : Set) : Set where
  constructor sig
  field
    ∣_∣ : O → List ℕ

  arity = ∣_∣
open Signature public

private
  variable
    n m : ℕ
    O : Set
    s : Signature O
    T U : ℕ → Set

⟦_⟧ᵇ_ : ℕ → (ℕ → Set ℓ) → ℕ → Set ℓ
⟦ zero  ⟧ᵇ T = T
⟦ suc a ⟧ᵇ T = ⟦ a ⟧ᵇ T ∘ suc

⟦_⟧ᶜ_ : (as : List ℕ) (T : ℕ → Set ℓ) → (ℕ → Set ℓ)
(⟦ []     ⟧ᶜ _) _ = ⊤
(⟦ a ∷ as ⟧ᶜ T) n = (⟦ a ⟧ᵇ T) n × (⟦ as ⟧ᶜ T) n

⟦_⟧ : (s : Signature O) (T : ℕ → Set ℓ) → ℕ → Set ℓ
⟦_⟧ {O} (sig ar) T n = Σ[ o ∈ O ] (⟦ ar o ⟧ᶜ T) n

mapᵇ : (a : ℕ) (f : T ⇒ U)
  → ⟦ a ⟧ᵇ T ⇒ ⟦ a ⟧ᵇ U
mapᵇ zero    f x = f x
mapᵇ (suc a) f x = mapᵇ a f x

mapᶜ : (as : List ℕ) (f : T ⇒ U)
  → ⟦ as ⟧ᶜ T ⇒ ⟦ as ⟧ᶜ U
mapᶜ []       f _       = tt
mapᶜ (a ∷ as) f (x , y) = mapᵇ a f x , mapᶜ as f y

map : (f : T ⇒ U)
  → ⟦ s ⟧ T ⇒ ⟦ s ⟧ U
map {s = sig ar} f (o , x) = (o , mapᶜ (ar o) f x)

record _-Alg_ (s : Signature O) (T : ℕ → Set ℓ) : Set ℓ where
  field
    var : Fin     ⇒ T
    alg : ⟦ s ⟧ T ⇒ T
open _-Alg_ public  