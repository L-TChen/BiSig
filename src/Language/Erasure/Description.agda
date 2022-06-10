open import Prelude

import Syntax.Simple.Description  as S

module Language.Erasure.Description {SD : S.Desc} where

open import Syntax.Typed.Description   {SD} as T
open import Syntax.BiTyped.Description {SD} as B

private variable
  Ξ     : ℕ

eraseᵃ : B.ArgD Ξ → T.ArgD Ξ
eraseᵃ (ι m B)   = ⊢ B
eraseᵃ (A ∙ Δ) = A ∙ eraseᵃ Δ

eraseᵃˢ : B.ArgsD Ξ → T.ArgsD Ξ
eraseᵃˢ ι        = ι
eraseᵃˢ (ρ D Ds) = ρ (eraseᵃ D) (eraseᵃˢ Ds)

eraseᶜ : B.ConD → T.ConD
eraseᶜ (ι Ξ m A D) = ι Ξ A (eraseᵃˢ D)

erase : B.Desc → T.Desc
erase Ds = map eraseᶜ Ds