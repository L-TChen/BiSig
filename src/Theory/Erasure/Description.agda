{-# OPTIONS --safe #-}

open import Prelude
  hiding (map)

import Syntax.Simple.Description  as S

module Theory.Erasure.Description {SD : S.Desc} where

open import Syntax.Typed.Description   {SD} as T
open import Syntax.BiTyped.Description {SD} as B

private variable
  Ξ     : ℕ

eraseᵃ : B.ArgD Ξ → T.ArgD Ξ
eraseᵃ (Θ ⊢[ m ] B)= Θ ⊢ B

eraseᵃˢ : B.ArgsD Ξ → T.ArgsD Ξ
eraseᵃˢ = L.map eraseᵃ

eraseᶜ : B.ConD → T.ConD
eraseᶜ (ι {n} mod A D) = ι A (eraseᵃˢ D)

erase : B.Desc → T.Desc
erase (desc Op decOp rules) = desc Op decOp (eraseᶜ ∘ rules)
