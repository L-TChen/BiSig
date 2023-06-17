open import Prelude

import Syntax.Simple.Description  as S

module Theory.ModeCorrectness.Description (SD : S.Desc)   where

open import Syntax.Simple              SD
open import Syntax.BiTyped.Description SD

private variable
  Ξ : ℕ

-- every variable in A is contained in some As 
Cover : Fins Ξ → TExps Ξ → Set
Cover xs Δ = fvs Δ ⊆ xs -- All (λ A → fv A ⊆ xs) Δ

known : ArgsD Ξ → Fins Ξ
known []                = []
known (_ ⊢[ d ] A ∷ Ds) = helper d A ++ known Ds
  where
    helper : Mode → TExp Ξ → Fins _
    helper Chk A = []
    helper Syn A = fv A

ModeCorrectᵃ : Fins Ξ → ArgD Ξ → Set
ModeCorrectᵃ xs (Δ ⊢[ Chk ] A) = Cover xs (A ∷ Δ)
ModeCorrectᵃ xs (Δ ⊢[ Syn ] A) = Cover xs Δ

ModeCorrectᵃˢ : Fins Ξ → ArgsD Ξ → Set
ModeCorrectᵃˢ _  []       = ⊤
ModeCorrectᵃˢ xs (D ∷ Ds) =
  ModeCorrectᵃ (xs ++ known Ds) D × ModeCorrectᵃˢ xs Ds

ModeCorrectᶜ : ConD → Set
ModeCorrectᶜ (ι {Ξ} Chk A Ds) =
  ((i : Fin Ξ) → i ∈ (fv A ++ known Ds)) × ModeCorrectᵃˢ (fv A) Ds
ModeCorrectᶜ (ι {Ξ} Syn A Ds) =
  ((i : Fin Ξ) → i ∈ known Ds) × ModeCorrectᵃˢ []     Ds × fv A ⊆ known Ds
  -- Every i exsits in some variable of inferred types

ModeCorrect : Desc → Set
ModeCorrect D = (i : D .Op) → ModeCorrectᶜ (D .rules i)

------------------------------------------------------------------------
-- Functors that take a partial substitution instead

module Functor (Id : Set) where
  open import Syntax.NamedContext        SD Id
  import      Syntax.BiTyped.Raw.Functor SD Id as R

  private
    variable
      Θ : ℕ
      ρ : TSub Ξ Θ
      d : Mode
      X : Mode → Set ℓ

    Pred :  (ℓ′ : Level) → ℕ → (X : Mode → Set ℓ) → Set (ℓ ⊔ lsuc ℓ′)
    Pred ℓ′ Θ X = (d : Mode) → TExp Θ → Cxt Θ → X d → Set ℓ′

  ⟦_⟧ᵃ : (Δ : TExps Ξ) (xs : Fins Ξ) → Cover xs Δ
    → (X : Mode → Set ℓ) → (Cxt Θ → X d → Set ℓ′)
    → Sub⊆ xs Θ
    → Cxt Θ → R.⟦ Δ ⟧ᵃ (X d)
    → Set ℓ′
  ⟦ []    ⟧ᵃ _  _    X P ρ Γ t       = P Γ t
  ⟦ A ∷ Δ ⟧ᵃ xs Δ⊆xs X P ρ Γ (x , t) =
    ⟦ Δ ⟧ᵃ xs (Δ⊆xs ∘ L.++⁺ʳ _) X P ρ (x ⦂ sub⊆ ρ A (Δ⊆xs ∘ L.++⁺ˡ) , Γ) t

  ⟦_⟧⇒ᵃˢ : (Ds : ArgsD Ξ) (xs : Fins Ξ) → known Ds ⊆ xs → (MC : ModeCorrectᵃˢ [] Ds)
    → (X : Mode → Set ℓ) (P : Pred ℓ′ Θ X)
    → Sub⊆ xs Θ
    → Cxt Θ → R.⟦ Ds ⟧ᵃˢ X → Set ℓ′
  ⟦ []                ⟧⇒ᵃˢ _ _ _ _ _ _ _ _ = ⊤

  ⟦ Δ ⊢[ Chk ] A ∷ Ds ⟧⇒ᵃˢ xs Ds⊆xs (Δ⊆Ds , MC) X P ρ Γ (t , ts) =
    ⟦ Δ ⟧ᵃ xs (Ds⊆xs ∘ Δ⊆Ds ∘ L.++⁺ʳ _) X (P Chk $ sub⊆ ρ A (Ds⊆xs ∘ Δ⊆Ds ∘ L.++⁺ˡ)) ρ Γ t
    × ⟦ Ds ⟧⇒ᵃˢ xs Ds⊆xs MC X P ρ Γ ts
    
  ⟦ Δ ⊢[ Syn ] A ∷ Ds ⟧⇒ᵃˢ xs Ds⊆xs (Δ⊆Ds , MC) X P ρ Γ (t , ts) =
    ⟦ Δ ⟧ᵃ xs (Ds⊆xs ∘ L.++⁺ʳ _ ∘ Δ⊆Ds) X (P Syn $ sub⊆ ρ A (Ds⊆xs ∘ L.++⁺ˡ)) ρ Γ t
       × ⟦ Ds ⟧⇒ᵃˢ xs (Ds⊆xs ∘ L.++⁺ʳ _) MC X P ρ Γ ts
