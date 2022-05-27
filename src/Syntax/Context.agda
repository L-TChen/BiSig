open import Prelude

module Syntax.Context (T : Set) (_≟T_ : Decidable (_≡_ {A = T}))  where

open import Data.List
open import Data.List.Membership.DecPropositional (_≟T_) public

Ctx = List T

pattern ∅       = []
pattern _∙_ A Γ = A ∷ Γ
