import Syntax.Simple.Signature as S

module Syntax.Typed.Raw.Ordering.Functor (SD : S.SigD) where

open import Prelude

open import Syntax.Simple            SD
open import Syntax.Typed.Signature SD
import      Syntax.Typed.Raw.Functor SD as R

Fam : (ℓ′ : Level) → (X : R.Fam ℓ) → Set (ℓ ⊔ lsuc ℓ′)
Fam ℓ′ X = {n : ℕ} → X n → X n → Set ℓ′

Fam₀ : (X : R.Fam ℓ) → Set (ℓ ⊔ lsuc 0ℓ)
Fam₀ X = Fam 0ℓ X

private variable
  Ξ : ℕ

⟦_⟧ᵃˢ : (Ds : ArgsD Ξ) (X : R.Fam ℓ) (Y : Fam ℓ′ X) → Fam ℓ′ (R.⟦ Ds ⟧ᵃˢ X)
⟦ []     ⟧ᵃˢ _ _ _        _          = ⊤
⟦ _ ∷ Ds ⟧ᵃˢ X Y (x , xs) (x' , xs') = Y x x' × ⟦ Ds ⟧ᵃˢ X Y xs xs'

⟦_,_⟧ᶜ : (D D′ : OpD) (X : R.Fam ℓ) (Y : Fam ℓ′ X)
       → D ≡ D′ → {n : ℕ} → R.⟦ D ⟧ᶜ X n → R.⟦ D′ ⟧ᶜ X n → Set ℓ′
⟦ ι _ Ds , ._ ⟧ᶜ X Y refl xs xs' = ⟦ Ds ⟧ᵃˢ X Y xs xs'

⟦_⟧ : (D : SigD) (X : R.Fam ℓ) (Y : Fam ℓ′ X) → Fam ℓ′ (R.⟦ D ⟧ X)
⟦ D ⟧ X Y (i , xs) (i' , xs') =
  Σ[ ieq ∈ i ≡ i' ] ⟦ D .ar i , D .ar i' ⟧ᶜ X Y (cong (ar D) ieq) xs xs'
