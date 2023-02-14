open import Prelude
  hiding (_++_)
open import Syntax.Simple.Description

module Syntax.Simple.Association (D : Desc) where

import Data.Fin as F

open import Syntax.Simple.Term D
  renaming (_≟_ to _≟Tm_)

private variable
  n m l : ℕ
  
data AList : (m n : ℕ) → Set where
  []   : AList n n
  _/_∷_ : (t : Tm m) (x : Fin (suc m)) (σ : AList m n) → AList (suc m) n

_/_∷′_ : Tm m → Fin (suc m) → ∃ (AList m) → ∃ (AList (suc m))
t / x ∷′ (n , σ) = n , (t / x ∷ σ)

_++_ : AList m n → AList n l → AList m l
[]           ++ σ₂ = σ₂
(t / x ∷ σ₁) ++ σ₂ = t / x ∷ (σ₁ ++ σ₂)

-- toSub : AList m n → Sub m n
-- toSub []          = ids
-- toSub (t / x ∷ p) = (t for x) ⨟ toSub p
