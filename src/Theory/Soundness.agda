open import Prelude

import Syntax.Simple.Description as S

module Theory.Soundness {SD : S.Desc} where

open import Syntax.Simple.Term SD
  renaming (Tm to TExp; Tms to TExps; Sub to TSub)
open import Syntax.Context     SD

open import Syntax.Typed.Description    SD as T
open import Syntax.BiTyped.Description  SD as B

open import Syntax.Typed.Intrinsic.Functor    as T
open import Syntax.BiTyped.Intrinsic.Functor  as B

open import Syntax.Typed.Intrinsic.Term
open import Syntax.BiTyped.Intrinsic.Term
  renaming (Tm to BTm)

open import Theory.Erasure.Description

private variable
  d   : Mode
  Ξ Θ : ℕ
  A B : TExp Θ
  ρ   : TSub Ξ Θ
  Γ   : Cxt Θ

-- A bidirectional typing is sound with respect to a base typing
-- if every bidirectional typing rule corresonds to a base typing rule.
Soundness : B.Desc → T.Desc → Set
Soundness BD TD = (j : BD .Op) → Σ[ i ∈ TD .Op ] eraseᶜ (BD .rules j) ≡ TD .rules i

module _ (BD : B.Desc) (TD : T.Desc) (s : Soundness BD TD) where mutual
  forget
    : BTm BD Θ d A Γ
    → Tm  TD Θ A Γ
  forget (` x)        = ` x
  forget (_ ∋ t)      = forget t
  forget (t ↑by refl) = forget t
  forget (op (i , r)) = op (_ , forgetᶜ (proj₂ (s i)) r)

  forgetᶜ
    : ∀ {D D′} → eraseᶜ D′ ≡ D
    → B.⟦ D′ ⟧ᶜ (BTm BD Θ) d A Γ
    → T.⟦ D ⟧ᶜ  (Tm  TD Θ)   A Γ
  forgetᶜ refl (_ , σ , A=B , ts) = σ , A=B , forgetMap _ ts
  -- p is ignored.

  forgetMap
    : (D : B.ArgsD Ξ)
    → B.⟦ D ⟧ᵃˢ         (BTm BD Θ) ρ Γ
    → T.⟦ eraseᵃˢ D ⟧ᵃˢ (Tm TD Θ)  ρ Γ
  forgetMap []                 _        = _
  forgetMap (Θ ⊢[ m ] B ∷ Ds) (t , ts) = forgetMapᵃ Θ t , forgetMap Ds ts

  forgetMapᵃ
    : (Δ : TExps Ξ)
    → B.⟦ Δ ⟧ᵃ (BTm BD Θ d A) ρ Γ
    → T.⟦ Δ ⟧ᵃ (Tm  TD Θ   A) ρ Γ
  forgetMapᵃ []       t = forget t
  forgetMapᵃ (_ ∷ Θ) t = forgetMapᵃ Θ t
