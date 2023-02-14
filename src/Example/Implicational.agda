open import Prelude
  hiding (_↣_)

module Example.Implicational where

open import Syntax.Simple.Description

ΛₜD : Desc
ΛₜD = 0 -- base type
    ∙ 2 -- function type
    ∙ ∅

open import Syntax.Simple.Term ΛₜD
  using (`_; op; ∅ₛ; _∙ₛ_)
  renaming (Tm to Λₜ)
  public

{-
data Λₜ : Set where
  ι   :              Λₜ
  _↣_ : (A B : Λₜ) → Λₜ
-}

open import Syntax.Context ΛₜD public

pattern _↣_ A B = op (2 , there (here refl) , A , B , _)
infixr 8 _↣_
