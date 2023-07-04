open import Prelude

import Syntax.Simple.Description  as S

module Theory.ModeCorrectness.Functor (SD : S.Desc) (Id : Set)  where

open import Syntax.Simple              SD
open import Syntax.NamedContext        SD Id

open import Syntax.BiTyped.Description SD
import      Syntax.BiTyped.Raw.Functor SD Id as R

open import Theory.ModeCorrectness.Description SD

private variable
    Ξ Θ : ℕ
    ρ : TSub Ξ Θ
    d : Mode
    X : Mode → Set ℓ

Pred :  (ℓ′ : Level) → (X : Mode → Set ℓ) → Set (ℓ ⊔ lsuc ℓ′)
Pred ℓ′ X = (d : Mode) → TExp 0 → Cxt 0 → X d → Set ℓ′

⟦_⟧ᵃ : (Δ : TExps Ξ) ((xs , ρ) : ∃Sub⊆ Ξ) → Cover xs Δ
  → (X : Mode → Set ℓ) → (Cxt 0 → X d → Set ℓ′)
  → Cxt 0 → R.⟦ Δ ⟧ᵃ (X d)
  → Set ℓ′
⟦ []    ⟧ᵃ _  _             X P Γ t       = P Γ t
⟦ A ∷ Δ ⟧ᵃ (xs , ρ) (A⊆xs ∷ Δ⊆xs) X P Γ (x , t) =
  ⟦ Δ ⟧ᵃ (xs , ρ) Δ⊆xs X P (x ⦂ sub⊆ ρ A A⊆xs , Γ) t

⟦_⟧ᵃˢ : (Ds : ArgsD Ξ) ((xs , ρ) : ∃Sub⊆ Ξ)
  → (ys : Fins# Ξ)→ ys ∪ known Ds #⊆ xs
  → (MC : ModeCorrectᵃˢ ys Ds)
  → (X : Mode → Set ℓ) (P : Pred ℓ′ X)
  → Cxt 0 → R.⟦ Ds ⟧ᵃˢ X → Set ℓ′
⟦ []                ⟧ᵃˢ _ _ _ _ _ _ _ _ = ⊤

⟦ Δ ⊢[ Chk ] A ∷ Ds ⟧ᵃˢ (xs , ρ) ys Ds⊆xs (A⊆Ds ∷ Δ⊆Ds , MC) X P Γ (t , ts) =
    ⟦ Δ ⟧ᵃ (_ , ρ) Δ⊆xs X (P Chk (sub⊆ ρ A (Ds⊆xs ∘ A⊆Ds))) Γ t
  × ⟦ Ds ⟧ᵃˢ (xs , ρ) ys Ds⊆xs MC X P Γ ts
  where
    Δ⊆xs : Cover xs Δ
    Δ⊆xs = L.A.map (λ {A} A⊆ {x} x∈ → Ds⊆xs (A⊆ x∈)) Δ⊆Ds

⟦ Δ ⊢[ Syn ] A ∷ Ds ⟧ᵃˢ (xs , ρ) ys Ds⊆xs (Δ⊆Ds , MC) X P Γ (t , ts) =
    ⟦ Δ ⟧ᵃ (_ , ρ) Δ⊆xs X (P Syn (sub⊆ ρ A (Ds⊆xs ∘ ∪⁺ʳ ys ∘ ∪⁺ˡ))) Γ t
    × ⟦ Ds ⟧ᵃˢ (xs , ρ) ys (Ds⊆xs ∘ ∪-monotoneʳ ys (∪⁺ʳ (vars A))) MC X P Γ ts
  where
    Δ⊆xs : Cover xs Δ
    Δ⊆xs = L.A.map (λ {B} B⊆ {x} x∈ → Ds⊆xs (∪-monotoneʳ ys (∪⁺ʳ (vars A)) (B⊆ x∈))) Δ⊆Ds
