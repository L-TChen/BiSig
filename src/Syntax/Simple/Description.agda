open import Prelude

module Syntax.Simple.Description where

private variable
  X Y : ℕ → Set

Desc = List ℕ

_^_ : Set → ℕ → Set
X ^ zero  = ⊤
X ^ suc n = X × X ^ n

⟦_⟧_ : Desc → (ℕ → Set) → (ℕ → Set)
(⟦ ∅      ⟧ _) _ = ⊥
(⟦ D ∙ Ds ⟧ X) n = (X n) ^ D ⊎ (⟦ Ds ⟧ X) n

mapⁿ : {X Y : Set} (n : ℕ) (f : X → Y)
  → X ^ n → Y ^ n
mapⁿ zero    f _        = _
mapⁿ (suc n) f (x , xs) = f x , mapⁿ n f xs

fmap : (D : Desc) (f : X ⇒₁ Y)
  → ⟦ D ⟧ X ⇒₁ ⟦ D ⟧ Y
fmap (n ∙ ns) f (inl x) = inl (mapⁿ n f x)
fmap (n ∙ ns) f (inr y) = inr (fmap ns f y)

record _-Alg (D : Desc) (X : ℕ → Set) : Set₁ where
  field
    var : Fin     ⇒₁ X
    alg : ⟦ D ⟧ X ⇒₁ X
open _-Alg public