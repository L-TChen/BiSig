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

⟦_⟧ᵃ : (Δ : TExps Ξ) (xs : Fins# Ξ) → Cover xs Δ
  → (X : Mode → Set ℓ) → (Cxt 0 → X d → Set ℓ′)
  → Sub⊆ Ξ xs
  → Cxt 0 → R.⟦ Δ ⟧ᵃ (X d)
  → Set ℓ′
⟦ []    ⟧ᵃ _  _             X P ρ Γ t       = P Γ t
⟦ A ∷ Δ ⟧ᵃ xs (A⊆xs ∷ Δ⊆xs) X P ρ Γ (x , t) =
  ⟦ Δ ⟧ᵃ xs Δ⊆xs X P ρ (x ⦂ sub⊆ ρ A A⊆xs , Γ) t

⟦_⟧ᵃˢ : (Ds : ArgsD Ξ) (xs : Fins# Ξ) (ys : Fins# Ξ)→ ys ∪ known Ds #⊆ xs
  → (MC : ModeCorrectᵃˢ ys Ds)
  → (X : Mode → Set ℓ) (P : Pred ℓ′ X)
  → Sub⊆ Ξ xs
  → Cxt 0 → R.⟦ Ds ⟧ᵃˢ X → Set ℓ′
⟦ []                ⟧ᵃˢ _ _ _ _ _ _ _ _ _ = ⊤

⟦ Δ ⊢[ Chk ] A ∷ Ds ⟧ᵃˢ xs ys Ds⊆xs (A⊆Ds ∷ Δ⊆Ds , MC) X P ρ Γ (t , ts) =
    ⟦ Δ ⟧ᵃ xs Δ⊆xs X (P Chk (sub⊆ ρ A (Ds⊆xs ∘ A⊆Ds))) ρ Γ t
  × ⟦ Ds ⟧ᵃˢ xs ys Ds⊆xs MC X P ρ Γ ts
  where
    Δ⊆xs : Cover xs Δ
    Δ⊆xs = L.A.map (λ {A} A⊆ {x} x∈ → Ds⊆xs (A⊆ x∈)) Δ⊆Ds

⟦ Δ ⊢[ Syn ] A ∷ Ds ⟧ᵃˢ xs ys Ds⊆xs (Δ⊆Ds , MC) X P ρ Γ (t , ts) =
    ⟦ Δ ⟧ᵃ xs Δ⊆xs X (P Syn (sub⊆ ρ A (Ds⊆xs ∘ ∪⁺ʳ ys ∘ ∪⁺ˡ))) ρ Γ t
    × ⟦ Ds ⟧ᵃˢ xs ys (Ds⊆xs ∘ ∪-monotoneʳ {xs = ys} (∪⁺ʳ (vars A))) MC X P ρ Γ ts
  where
    Δ⊆xs : Cover xs Δ
    Δ⊆xs = L.A.map (λ {B} B⊆ {x} x∈ → Ds⊆xs (∪-monotoneʳ {xs = ys} (∪⁺ʳ (vars A)) (B⊆ x∈))) Δ⊆Ds
