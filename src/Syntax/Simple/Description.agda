open import Prelude

module Syntax.Simple.Description where

private variable
  X Y : Set

Desc = List ℕ

⟦_⟧ : Desc → Set → Set
⟦ Ds ⟧ X = ∃[ D ] Σ[ _ ∈ (D ∈ Ds) ] X ^ D

mapⁿ : {X Y : Set} (n : ℕ) (f : X → Y)
  → X ^ n → Y ^ n
mapⁿ zero    f _        = _
mapⁿ (suc n) f (x , xs) = f x , mapⁿ n f xs

fmap : (D : Desc) (f : X → Y)
  → ⟦ D ⟧ X → ⟦ D ⟧ Y
fmap Ds f (D , i , xs) = D , i , mapⁿ D f xs

record _-Alg (D : Desc) (X : ℕ → Set) : Set₁ where
  field
    var : Fin       ⇒₁ X
    alg : ⟦ D ⟧ ∘ X ⇒₁ X
open _-Alg public
