import Syntax.Simple.Signature as S

module Theory.ModeCorrectness.Decidability (SD : S.SigD) where

open import Prelude

open import Syntax.Simple            SD
open import Syntax.BiTyped.Signature SD

open import Theory.ModeCorrectness.Signature SD

private variable
  Ξ : ℕ

Cover? : (S : Fins# Ξ) (A : TExp Ξ) → Dec (vars A #⊆ S)
Cover? S A = vars A #⊆? S

ModeCorrectᵃ? : (S : Fins# Ξ) (D : ArgD Ξ) → Dec (ModeCorrectᵃ S D)
ModeCorrectᵃ? S (Δ ⊢[ Chk ] A) = all? (Cover? S) (A ∷ Δ)
ModeCorrectᵃ? S (Δ ⊢[ Syn ] A) = all? (Cover? S) Δ

ModeCorrectᵃˢ? : (S : Fins# Ξ) (Ds : ArgsD Ξ) → Dec (ModeCorrectᵃˢ S Ds)
ModeCorrectᵃˢ? S []       = yes tt
ModeCorrectᵃˢ? S (D ∷ Ds) with ModeCorrectᵃ? (S ∪ known Ds) D
... | no ¬p = no λ (p , _) → ¬p p
... | yes p with ModeCorrectᵃˢ? S Ds
... | no ¬q = no λ (_ , q) → ¬q q
... | yes q = yes (p , q)

ModeCorrectᶜ? : (D : OpD) → Dec (ModeCorrectᶜ D)
ModeCorrectᶜ? (ι Chk A Ds) with F.all? (_#∈? (vars A ∪ known Ds)) | ModeCorrectᵃˢ? (vars A) Ds
... | no ¬p | _     = no λ (p , _) → ¬p p
... | _     | no ¬q = no λ (_ , q) → ¬q q
... | yes p | yes q = yes (p , q)
ModeCorrectᶜ? (ι Syn A Ds) with F.all? (_#∈? known Ds) | ModeCorrectᵃˢ? [] Ds
... | no ¬p | _     = no λ (p , _) → ¬p p
... | _     | no ¬q = no λ (_ , q) → ¬q q
... | yes p | yes q = yes (p , q)
