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
known []                  = []
known (_ ⊢[ Chk ] A ∷ Ds) =         known Ds
known (_ ⊢[ Syn ] A ∷ Ds) = fv A ++ known Ds

module Chk (B : TExp Ξ) where
  ModeCorrectᵃˢ : ArgsD Ξ → Set
  ModeCorrectᵃˢ []       = ⊤
  ModeCorrectᵃˢ (Δ ⊢[ Chk ] A ∷ Ds) =
    Cover (fv B ++ known Ds) (A ∷ Δ) × ModeCorrectᵃˢ Ds 
  ModeCorrectᵃˢ (Δ ⊢[ Syn ] A ∷ Ds) =
    Cover (fv B ++ known Ds) Δ       × ModeCorrectᵃˢ Ds


module Syn where 
  ModeCorrectᵃˢ : ArgsD Ξ → Set
  ModeCorrectᵃˢ []                  = ⊤
  ModeCorrectᵃˢ (Δ ⊢[ Chk ] A ∷ Ds) =
    Cover (known Ds) (A ∷ Δ) × ModeCorrectᵃˢ Ds
  ModeCorrectᵃˢ (Δ ⊢[ Syn ] A ∷ Ds) =
    Cover (known Ds) Δ       × ModeCorrectᵃˢ Ds

ModeCorrectᶜ : ConD → Set
ModeCorrectᶜ (ι Chk A Ds) = Chk.ModeCorrectᵃˢ A Ds
ModeCorrectᶜ (ι Syn A Ds) = Syn.ModeCorrectᵃˢ Ds × fv A ⊆ known Ds

ModeCorrect : Desc → Set
ModeCorrect D = (i : D .Op) → ModeCorrectᶜ (D .rules i)

Tightᶜ : ConD → Set
Tightᶜ (ι {Ξ} Chk A Ds) =
  (i : Fin Ξ) → i ∈ (fv A ++ known Ds)
Tightᶜ (ι {Ξ} Syn A Ds) =
  (i : Fin Ξ) → i ∈ known Ds
  -- Every i exsits in some variable of inferred types

-- Cover-dec : (A : TExp Ξ) {As Δ : TExps Ξ}
--   → Cover As (A ∷ Δ) → Cover As Δ 
-- Cover-dec A (_ ∷ As⊆Δ) = As⊆Δ
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
    → ∈Sub xs Θ
    → Cxt Θ → R.⟦ Δ ⟧ᵃ (X d)
    → Set ℓ′
  ⟦ []    ⟧ᵃ _  _    X P ρ Γ t       = P Γ t
  ⟦ A ∷ Δ ⟧ᵃ xs Δ⊆As X P ρ Γ (x , t) =
    ⟦ Δ ⟧ᵃ xs (Δ⊆As ∘ L.++⁺ʳ (fv A)) X P ρ (x ⦂ ∈sub A (⊆-∈Sub (Δ⊆As ∘ L.++⁺ˡ) ρ) , Γ) t
--    ⟦ Δ ⟧ᵃ xs Δ⊆As X P ρ (x ⦂ ∈sub A (⊆-∈Sub A⊆As ρ) , Γ) t 

  ⟦_⟧⇒ᵃˢ : (Ds : ArgsD Ξ) (xs : Fins Ξ) → known Ds ⊆ xs → (MC : Syn.ModeCorrectᵃˢ Ds)
    → (X : Mode → Set ℓ) (P : Pred ℓ′ Θ X)
    → ∈Sub xs Θ
    → Cxt Θ → R.⟦ Ds ⟧ᵃˢ X → Set ℓ′
  ⟦ []                ⟧⇒ᵃˢ xs Ds⊆xs _           _ _ _ _ _        = ⊤
  ⟦ Δ ⊢[ Chk ] A ∷ Ds ⟧⇒ᵃˢ xs Ds⊆xs (Δ⊆Ds , MC) X P ρ Γ (t , ts) =
    ⟦ Δ ⟧ᵃ xs (Ds⊆xs ∘ Δ⊆Ds ∘ L.++⁺ʳ _) X (P Chk (∈sub A (⊆-∈Sub (Ds⊆xs ∘ Δ⊆Ds ∘ L.++⁺ˡ) ρ))) ρ Γ t
    × ⟦ Ds ⟧⇒ᵃˢ xs Ds⊆xs MC X P ρ Γ ts
  ⟦ Δ ⊢[ Syn ] A ∷ Ds ⟧⇒ᵃˢ xs Ds⊆xs (Δ⊆Ds        , MC) X P ρ Γ (t , ts) =
    let ρA  = ⊆-∈Sub (Ds⊆xs ∘ L.++⁺ˡ) ρ
    in ⟦ Δ ⟧ᵃ xs (Ds⊆xs ∘ L.++⁺ʳ _ ∘ Δ⊆Ds) X (P Syn (∈sub A ρA)) ρ Γ t -- ρDs Γ t
      × ⟦ Ds ⟧⇒ᵃˢ xs (Ds⊆xs ∘ L.++⁺ʳ _) MC X P ρ Γ ts
