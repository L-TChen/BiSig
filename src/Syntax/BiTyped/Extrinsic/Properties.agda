open import Prelude

import Syntax.Simple.Description  as S
import Syntax.BiTyped.Description as B

module Syntax.BiTyped.Extrinsic.Properties
  {SD : S.Desc} (Id : Set) (D : B.Desc SD) where

open import Syntax.NamedContext SD Id

open import Syntax.Simple SD

open import Syntax.BiTyped.Extrinsic.Functor     SD  Id
open import Syntax.BiTyped.Extrinsic.Term            Id D
import      Syntax.BiTyped.Raw.Functor           SD  Id   as R
open import Syntax.BiTyped.Raw.Term                  Id D

open ≡-Reasoning
open Equivalence

private variable
  Θ Ξ : ℕ
  n   : ℕ
  d   : Mode
  Γ Δ : Cxt n
  x   : Id
  A B : TExp Θ
  σ ρ : TSub Ξ Θ
  t u : Raw Θ d

-- Membership : TExp Θ → Cxt Θ → Id → 𝐘 {ℕ} {TSub} Θ
-- Membership A Γ x _ σ = x ⦂ A ⟨ σ ⟩ ∈ Γ ⟨ σ ⟩

-- Typability : TExp Θ → Cxt Θ → Raw Θ d → 𝐘 {ℕ} {TSub} Θ
-- Typability A Γ t _ σ = ⊢⇆ _ (A ⟨ σ ⟩) (Γ ⟨ σ ⟩) (t ⟨ σ ⟩)
-- 
-- Typabilityⁿ : (D : B.ArgsD SD Ξ)
--   → TSub Ξ Θ → Cxt Θ → R.⟦ D ⟧ᵃˢ (Raw Θ) → 𝐘 {ℕ} {TSub} Θ
-- Typabilityⁿ D ρ Γ ts n σ =
--   ⟦ D ⟧ᵃˢ (Raw n) ⊢⇆ (ρ ⨟ σ) (Γ ⟨ σ ⟩) (ts ⟨ σ ⟩)
-- 
-- Typabilityᵃ : (Δ : TExps Ξ)
--   → TSub Ξ Θ → TExp Θ → Cxt Θ → R.⟦ Δ ⟧ᵃ (Raw Θ d) → 𝐘 Θ
-- Typabilityᵃ Θ ρ A Γ t n σ = ⟦ Θ ⟧ᵃ (Raw n)
--   (⊢⇆ _ $ A ⟨ σ ⟩) (ρ ⨟ σ) (Γ ⟨ σ ⟩) (tsubᵃ σ _ t)
-- 
-- Synthesis : Cxt Θ → Raw Θ d → 𝐘 {ℕ} {TSub} Θ
-- Synthesis Γ t _ σ = ∃[ A ] Typability A Γ t _ σ
-- 
-- Synthesisᵃ : (Δ : TExps Ξ)
--   → TSub Ξ Θ → Cxt Θ → R.⟦ Δ ⟧ᵃ (Raw Θ d) → 𝐘 {ℕ} {TSub} Θ
-- Synthesisᵃ Δ ρ Γ t n σ = ∃[ A ] Typabilityᵃ Δ ρ A Γ t n σ
-- 
-- module _ (σ : TSub Θ n) where
--   sub-∈
--     : x ⦂ A ∈ Γ
--     → Membership A Γ x _ σ
--   sub-∈ zero        = zero
--   sub-∈ (suc ¬p x∈) = suc ¬p (sub-∈ x∈)
-- 
-- module _ {Θ : ℕ} (σ : TSub Θ n) where mutual
--   sub-⊢
--     : ⊢⇆ d     A Γ t 
--     → Typability A Γ t _ σ
--   sub-⊢ (⊢` x∈)    = ⊢` (sub-∈ σ x∈)
--   sub-⊢ (⊢⦂ ⊢t)    = ⊢⦂ (sub-⊢ ⊢t)
--   sub-⊢ (⊢↑ eq ⊢t) = ⊢↑ (cong (sub σ) eq) (sub-⊢ ⊢t) 
--   sub-⊢ {A = A} (⊢op (i , m=d , ts) (ρ , eq , ⊢ts)) =
--     ⊢op (i , m=d , ts ⟨ σ ⟩) (ρ ⨟ σ , AExp⟨ρσ⟩=A , sub-⊢ᵃˢ _ ρ ⊢ts)
--     where
--       AExp = B.ConD.type (D .B.rules i)
--       AExp⟨ρσ⟩=A = begin
--         AExp ⟨ ρ ⨟ σ ⟩
--           ≡⟨ ⟨⟩-⨟ ρ σ (B.ConD.type (D .B.rules i)) ⟩
--         AExp ⟨ ρ ⟩ ⟨ σ ⟩
--           ≡⟨ cong (_⟨ σ ⟩) eq ⟩
--         A ⟨ σ ⟩
--           ∎
-- 
--   sub-⊢ᵃˢ 
--     : (D : B.ArgsD SD Ξ) (ρ : TSub Ξ Θ) {ts : R.⟦ D ⟧ᵃˢ (Raw Θ)}
--     → ⟦ D ⟧ᵃˢ (Raw Θ) ⊢⇆ ρ Γ ts
--     → Typabilityⁿ D ρ Γ ts _ σ
--   sub-⊢ᵃˢ []                 ρ _          = tt
--   sub-⊢ᵃˢ (Θ B.⊢[ _ ] A ∷ D) ρ (⊢t , ⊢ts) rewrite ⟨⟩-⨟ ρ σ A =
--     sub-⊢ᵃ Θ ρ ⊢t , sub-⊢ᵃˢ D ρ ⊢ts
-- 
--   sub-⊢ᵃ
--     : (Δ : TExps Ξ) (ρ : TSub Ξ Θ) {t : R.⟦ Δ ⟧ᵃ (Raw Θ d)}
--     → ⟦ Δ ⟧ᵃ (Raw Θ) (⊢⇆ _ A) ρ Γ t -- ⟦ Θ ⟧ᵃ (Raw m) ρ
--     → Typabilityᵃ Δ ρ A Γ t _ σ 
--   sub-⊢ᵃ []      ρ ⊢t = sub-⊢ ⊢t
--   sub-⊢ᵃ (A ∷ Θ) ρ ⊢t rewrite ⟨⟩-⨟ ρ σ A = sub-⊢ᵃ Θ ρ ⊢t
-- 
-- module _ {Θ : ℕ} (σ : TSub Θ n) where
--   Typability-ext
--     : (t : Raw Θ d) (A : TExp Θ) (Γ : Cxt Θ)
--     → Typability A Γ t [ σ ⨟] ≗ Typability (A ⟨ σ ⟩) (Γ ⟨ σ ⟩) (t ⟨ σ ⟩) 
--   Typability-ext t A Γ ρ = ≡to⟺ $ begin
--     ⊢⇆ _ (A ⟨ σ ⨟ ρ ⟩) (Γ ⟨ σ ⨟ ρ ⟩) (t ⟨ σ ⨟ ρ ⟩)
--       ≡⟨ cong (⊢⇆ _ (A ⟨ σ ⨟ ρ ⟩) (Γ ⟨ σ ⨟ ρ ⟩)) (⟨⟩-⨟ σ ρ t) ⟩
--     ⊢⇆ _ (A ⟨ σ ⨟ ρ ⟩) (Γ ⟨ σ ⨟ ρ ⟩) (t ⟨ σ ⟩ ⟨ ρ ⟩)
--       ≡⟨ cong₂ (λ A Γ → ⊢⇆ _ A Γ (t ⟨ σ ⟩ ⟨ ρ ⟩)) (⟨⟩-⨟ σ ρ A) (⟨⟩-⨟ σ ρ Γ) ⟩
--     ⊢⇆ _ (A ⟨ σ ⟩ ⟨ ρ ⟩) (Γ ⟨ σ ⟩ ⟨ ρ ⟩) (t ⟨ σ ⟩ ⟨ ρ ⟩)
--       ∎
-- 
--   subst-∈→∈
--     : (Γ : Cxt Θ)
--     → ¬ (∃[ A ] x ⦂ A ∈ Γ)
--     → ¬ (Σ[ B ∈ TExp _ ] x ⦂ B ∈ Γ ⟨ σ ⟩)
--   subst-∈→∈ (_ ∷ _)       ¬∃ (D , zero)      = ¬∃ (_ , zero)
--   subst-∈→∈ ((y , C) ∷ Γ) ¬∃ (D , suc ¬p x∈) =
--     subst-∈→∈ Γ (λ where (_ , x∈) → ¬∃ (_ , suc ¬p x∈)) (_ , x∈)
