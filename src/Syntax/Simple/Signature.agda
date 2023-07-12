open import Prelude

module Syntax.Simple.Signature where

private variable
  X Y : Set

record SigD : Set₁ where
  constructor sigd
  field
    Op        : Set
    ⦃ decEq ⦄ : DecEq Op
    ar        : Op → ℕ
open SigD public

⟦_⟧ : SigD → Set → Set
⟦ D ⟧ X = Σ[ i ∈ D .Op ] X ^ D .ar i

mapⁿ : {X Y : Set} {n : ℕ} (f : X → Y)
  → X ^ n → Y ^ n
mapⁿ f xs = V.map f xs

fmap : (D : SigD) (f : X → Y)
  → ⟦ D ⟧ X → ⟦ D ⟧ Y
fmap Ds f (i , xs) = i , mapⁿ f xs

record _-Alg (D : SigD) (X : ℕ → Set) : Set₁ where
  field
    var : Fin       ⇒₁ X
    alg : ⟦ D ⟧ ∘ X ⇒₁ X
open _-Alg public
