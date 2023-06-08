open import Prelude

import Syntax.Simple.Description  as S

module Theory.Erasure.Description {SD : S.Desc} where

open import Syntax.Typed.Description   SD as T
open import Syntax.BiTyped.Description SD as B

private variable
  Ξ     : ℕ

eraseᵃ : B.ArgD Ξ → T.ArgD Ξ
eraseᵃ (Δ ⊢[ d ] B)= Δ ⊢ B

eraseᵃˢ : B.ArgsD Ξ → T.ArgsD Ξ
eraseᵃˢ = L.map eraseᵃ

eraseᶜ : B.ConD → T.ConD
eraseᶜ (ι {Ξ} d A D) = ι A (eraseᵃˢ D)

erase : B.Desc → T.Desc
erase (desc Op rules) = desc Op (eraseᶜ ∘ rules)
