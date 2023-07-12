import Syntax.Simple.Signature  as S

module Theory.Erasure {SD : S.SigD} where

open import Prelude

open import Syntax.Typed.Signature   SD as T
open import Syntax.BiTyped.Signature SD as B

private variable
  Ξ : ℕ

eraseᵃ : B.ArgD Ξ → T.ArgD Ξ
eraseᵃ (Δ ⊢[ _ ] B)= Δ ⊢ B

eraseᵃˢ : B.ArgsD Ξ → T.ArgsD Ξ
eraseᵃˢ = L.map eraseᵃ

eraseᶜ : B.OpD → T.OpD
eraseᶜ (ι _ A D) = ι A (eraseᵃˢ D)

erase : B.SigD → T.SigD
erase (sigd Op ar) = sigd Op (eraseᶜ ∘ ar)
