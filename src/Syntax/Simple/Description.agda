{-# OPTIONS --safe #-}

open import Prelude

module Syntax.Simple.Description where

private variable
  X Y : Set

record Desc : Set₁ where
  constructor desc
  field
    Op        : Set
    ⦃ decEq ⦄ : DecEq Op
    rules     : Op → ℕ
open Desc public

⟦_⟧ : Desc → Set → Set
⟦ D ⟧ X = Σ[ i ∈ D .Op ] X ^ D .rules i 
-- Desc = List ℕ

-- ⟦_⟧ : Desc → Set → Set
-- ⟦ Ds ⟧ X = ∃[ D ] Σ[ _ ∈ (D ∈ Ds) ] X ^ D

mapⁿ : {X Y : Set} {n : ℕ} (f : X → Y)
  → X ^ n → Y ^ n
mapⁿ f xs = V.map f xs
-- mapⁿ (suc n) f (x ∷ xs) = f x ∷ mapⁿ n f xs

fmap : (D : Desc) (f : X → Y)
  → ⟦ D ⟧ X → ⟦ D ⟧ Y
fmap Ds f (i , xs) = i , mapⁿ f xs

record _-Alg (D : Desc) (X : ℕ → Set) : Set₁ where
  field
    var : Fin       ⇒₁ X
    alg : ⟦ D ⟧ ∘ X ⇒₁ X
open _-Alg public
