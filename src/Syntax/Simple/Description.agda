open import Prelude

module Syntax.Simple.Description where

private variable
  X Y : ℕ → Set

Desc = List ℕ

⟦_⟧_ : Desc → (ℕ → Set) → (ℕ → Set)
(⟦ Ds ⟧ X) n = ∃[ D ] Σ[ _ ∈ (D ∈ Ds) ] (X n) ^ D

mapⁿ : {X Y : Set} (n : ℕ) (f : X → Y)
  → X ^ n → Y ^ n
mapⁿ zero    f _        = _
mapⁿ (suc n) f (x , xs) = f x , mapⁿ n f xs

fmap : (D : Desc) (f : X ⇒₁ Y)
  → ⟦ D ⟧ X ⇒₁ ⟦ D ⟧ Y
fmap Ds f (D , i , x) = D , i , mapⁿ D f x

record _-Alg (D : Desc) (X : ℕ → Set) : Set₁ where
  field
    var : Fin     ⇒₁ X
    alg : ⟦ D ⟧ X ⇒₁ X
open _-Alg public