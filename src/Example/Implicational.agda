{-# OPTIONS --safe #-}

open import Prelude
  hiding (_↣_)

module Example.Implicational where

open import Syntax.Simple.Description

data ΛₜO : Set where
  base imp : ΛₜO

instance
  ΛₜOEq : DecEq ΛₜO
  ΛₜOEq ._≟_ base base =  yes refl
  ΛₜOEq ._≟_ imp  imp  =  yes refl
  ΛₜOEq ._≟_ base imp  =  no λ ()
  ΛₜOEq ._≟_ imp  base =  no λ ()

ΛₜD : Desc
ΛₜD = desc ΛₜO λ where
  base → 0
  imp  → 2

{-
data Λₜ : Set where
  ι   :              Λₜ
  _↣_ : (A B : Λₜ) → Λₜ
-}

open import Syntax.Simple.Term ΛₜD
  using (`_; op)
  renaming (Tm to Λₜ)
  public

open import Syntax.Context ΛₜD public

pattern _↣_ A B = op (imp , A ∷ B ∷ [])
infixr 8 _↣_
