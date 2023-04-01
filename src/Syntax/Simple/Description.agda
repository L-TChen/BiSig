{-# OPTIONS --with-K --safe #-}

open import Prelude

module Syntax.Simple.Description where

private variable
  X Y : Set

Desc = List ℕ

⟦_⟧ : Desc → Set → Set
⟦ Ds ⟧ X = ∃[ D ] Σ[ _ ∈ (D ∈ Ds) ] X ^ D

∂⟦_⟧_ : Desc → Set → Set
∂⟦ Ds ⟧ X = ∃[ D ]       -- the arity (for some f) is D + 1
  Σ[ i ∈ (suc D ∈ Ds) ]  -- the i-th operation f
  Fin (suc D)            -- the j-th position and 
  × X ^ D                -- the other n many arguments for ar(f) = suc n
  
mapⁿ : {X Y : Set} {n : ℕ} (f : X → Y)
  → X ^ n → Y ^ n
mapⁿ f xs = V.map f xs
-- mapⁿ (suc n) f (x ∷ xs) = f x ∷ mapⁿ n f xs

fmap : (D : Desc) (f : X → Y)
  → ⟦ D ⟧ X → ⟦ D ⟧ Y
fmap Ds f (D , i , xs) = D , i , mapⁿ f xs

record _-Alg (D : Desc) (X : ℕ → Set) : Set₁ where
  field
    var : Fin       ⇒₁ X
    alg : ⟦ D ⟧ ∘ X ⇒₁ X
open _-Alg public
