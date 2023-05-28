{-# OPTIONS  #-}

open import Prelude

import Syntax.Simple.Description  as S
import Syntax.BiTyped.Description as B

module Syntax.BiTyped.Extrinsic.Properties
  {SD : S.Desc} (Id : Set) (D : B.Desc SD) where

open import Syntax.NamedContext SD Id

open import Syntax.Simple SD

open import Syntax.BiTyped.Extrinsic.Functor     SD  Id
open import Syntax.BiTyped.Extrinsic.Term            Id D
import      Syntax.BiTyped.Raw.Functor           SD  Id as R
open import Syntax.BiTyped.Raw.Term                  Id D

open ≡-Reasoning
open Equivalence

private variable
  n m l k Ξ : ℕ
  mod : Mode
  Γ Δ : Cxt m
  x   : Id
  A B : TExp m
  σ ρ : TSub m n
  t u : Raw m mod

Membership : TExp m → Cxt m → Id → 𝐘 {ℕ} {TSub} m
Membership A Γ x _ σ = x ⦂ A ⟨ σ ⟩ ∈ Γ ⟨ σ ⟩

Typability : TExp m → Cxt m → Raw m mod → 𝐘 {ℕ} {TSub} m
Typability A Γ t _ σ = ⊢⇆ _ (A ⟨ σ ⟩) (Γ ⟨ σ ⟩) (t ⟨ σ ⟩)

Typabilityⁿ : (D : B.ArgsD SD k)
  → TSub k m → Cxt m → R.⟦ D ⟧ᵃˢ (Raw m) → 𝐘 {ℕ} {TSub} m
Typabilityⁿ D ρ Γ ts n σ =
  ⟦ D ⟧ᵃˢ (Raw n) ⊢⇆ (ρ ⨟ σ) (Γ ⟨ σ ⟩) (ts ⟨ σ ⟩)

Typabilityᵃ : (Θ : TExps k)
  → TSub k m → TExp m → Cxt m → R.⟦ Θ ⟧ᵃ (Raw m mod) → 𝐘 m
Typabilityᵃ Θ ρ A Γ t n σ = ⟦ Θ ⟧ᵃ (Raw n)
  (⊢⇆ _ $ A ⟨ σ ⟩) (ρ ⨟ σ) (Γ ⟨ σ ⟩) (tsubᵃ σ t)

Synthesis : Cxt m → Raw m mod → 𝐘 {ℕ} {TSub} m
Synthesis Γ t _ σ = ∃[ A ] Typability A Γ t _ σ

Synthesisᵃ : (Δ : TExps k)
  → TSub k m → Cxt m → R.⟦ Δ ⟧ᵃ (Raw m mod) → 𝐘 {ℕ} {TSub} m
Synthesisᵃ Δ ρ Γ t n σ = ∃[ A ] Typabilityᵃ Δ ρ A Γ t n σ

AccTypability : TExp m → Cxt m → Raw m mod → AList m n → 𝐘 n
AccTypability A Γ t σ = Typability A Γ t [ toSub σ ⨟]

AccTypabilityⁿ : (D : B.ArgsD SD k)
  → TSub k m → Cxt m → R.⟦ D ⟧ᵃˢ (Raw m) → AList m n → 𝐘 n
AccTypabilityⁿ D ρ Γ ts σ = Typabilityⁿ D ρ Γ ts [ toSub σ ⨟]

AccTypabilityᵃ : (Θ : TExps k)
  → TSub k m → TExp m → Cxt m → R.⟦ Θ ⟧ᵃ (Raw m mod) → AList m n → 𝐘 n
AccTypabilityᵃ Θ ρ A Γ t σ = Typabilityᵃ Θ ρ A Γ t [ toSub σ ⨟]

AccSynthesis : Cxt m → Raw m mod → AList m n → 𝐘 n
AccSynthesis Γ t σ = Synthesis Γ t [ toSub σ ⨟]

AccSynthesisᵃ : (Δ : TExps k)
  → TSub k m → Cxt m → R.⟦ Δ ⟧ᵃ (Raw m mod) → AList m n → 𝐘 n
AccSynthesisᵃ Δ ρ Γ t σ = Synthesisᵃ Δ ρ Γ t [ toSub σ ⨟]

module _ {m n : ℕ} (Γ : Cxt m) (σ : AList m n) where
  DecAccSynthesis : Raw⇉ m → Set
  DecAccSynthesis t = DecMinₐ (AccSynthesis Γ t σ)

  DecAccInheritance : Raw⇇ m → TExp m → Set
  DecAccInheritance t A = DecMinₐ (AccTypability A Γ t σ)

module _ {m : ℕ} (σ : TSub m n) where
  sub-∈
    : x ⦂ A ∈ Γ
    → Membership A Γ x _ σ
  sub-∈ zero        = zero
  sub-∈ (suc ¬p x∈) = suc ¬p (sub-∈ x∈)

module _ {m : ℕ} (σ : TSub m n) where mutual
  sub-⊢
    : ⊢⇆ mod     A Γ t 
    → Typability A Γ t _ σ
  sub-⊢ (⊢` x∈)    = ⊢` (sub-∈ σ x∈)
  sub-⊢ (⊢⦂ ⊢t eq) = ⊢⦂ (sub-⊢ ⊢t) (cong (sub σ) eq)
  sub-⊢ (⊢⇉ eq ⊢t) = ⊢⇉ (cong (sub σ) eq) (sub-⊢ ⊢t) 
  sub-⊢ {A = A} (⊢op (i , m=mod , ts) (ρ , eq , ⊢ts)) =
    ⊢op (i , m=mod , ts ⟨ σ ⟩) (ρ ⨟ σ , AExp⟨ρσ⟩=A , sub-⊢ᵃˢ _ ρ ⊢ts)
    where
      AExp = B.ConD.type (D .B.rules i)
      AExp⟨ρσ⟩=A = begin
        AExp ⟨ ρ ⨟ σ ⟩
          ≡⟨ ⟨⟩-⨟ ρ σ (B.ConD.type (D .B.rules i)) ⟩
        AExp ⟨ ρ ⟩ ⟨ σ ⟩
          ≡⟨ cong (_⟨ σ ⟩) eq ⟩
        A ⟨ σ ⟩
          ∎

  sub-⊢ᵃˢ 
    : (D : B.ArgsD SD k) (ρ : TSub k m) {ts : R.⟦ D ⟧ᵃˢ (Raw m)}
    → ⟦ D ⟧ᵃˢ (Raw m) ⊢⇆ ρ Γ ts
    → Typabilityⁿ D ρ Γ ts _ σ
  sub-⊢ᵃˢ []                 ρ _          = tt
  sub-⊢ᵃˢ (Θ B.⊢[ _ ] A ∷ D) ρ (⊢t , ⊢ts) rewrite ⟨⟩-⨟ ρ σ A =
    sub-⊢ᵃ Θ ρ ⊢t , sub-⊢ᵃˢ D ρ ⊢ts

  sub-⊢ᵃ
    : (Θ : TExps k) (ρ : TSub k m) {t : R.⟦ Θ ⟧ᵃ (Raw m mod)}
    → ⟦ Θ ⟧ᵃ (Raw m) (⊢⇆ _ A) ρ Γ t -- ⟦ Θ ⟧ᵃ (Raw m) ρ
    → Typabilityᵃ Θ ρ A Γ t _ σ 
  sub-⊢ᵃ []      ρ ⊢t = sub-⊢ ⊢t
  sub-⊢ᵃ (A ∷ Θ) ρ ⊢t rewrite ⟨⟩-⨟ ρ σ A = sub-⊢ᵃ Θ ρ ⊢t
      

module _ {m : ℕ} (σ : TSub m n) where
  Typability-ext
    : (t : Raw m mod) (A : TExp m) (Γ : Cxt m)
    → Typability A Γ t [ σ ⨟] ≗ Typability (A ⟨ σ ⟩) (Γ ⟨ σ ⟩) (t ⟨ σ ⟩) 
  Typability-ext t A Γ ρ = ≡to⟺ $ begin
    ⊢⇆ _ (A ⟨ σ ⨟ ρ ⟩) (Γ ⟨ σ ⨟ ρ ⟩) (t ⟨ σ ⨟ ρ ⟩)
      ≡⟨ cong (⊢⇆ _ (A ⟨ σ ⨟ ρ ⟩) (Γ ⟨ σ ⨟ ρ ⟩)) (⟨⟩-⨟ σ ρ t) ⟩
    ⊢⇆ _ (A ⟨ σ ⨟ ρ ⟩) (Γ ⟨ σ ⨟ ρ ⟩) (t ⟨ σ ⟩ ⟨ ρ ⟩)
      ≡⟨ cong₂ (λ A Γ → ⊢⇆ _ A Γ (t ⟨ σ ⟩ ⟨ ρ ⟩)) (⟨⟩-⨟ σ ρ A) (⟨⟩-⨟ σ ρ Γ) ⟩
    ⊢⇆ _ (A ⟨ σ ⟩ ⟨ ρ ⟩) (Γ ⟨ σ ⟩ ⟨ ρ ⟩) (t ⟨ σ ⟩ ⟨ ρ ⟩)
      ∎

  subst-∈→∈
    : (Γ : Cxt m)
    → ¬ (∃[ A ] x ⦂ A ∈ Γ)
    → ¬ (Σ[ B ∈ TExp _ ] x ⦂ B ∈ Γ ⟨ σ ⟩)
  subst-∈→∈ (_ ∷ _)       ¬∃ (D , zero)      = ¬∃ (_ , zero)
  subst-∈→∈ ((y , C) ∷ Γ) ¬∃ (D , suc ¬p x∈) =
    subst-∈→∈ Γ (λ where (_ , x∈) → ¬∃ (_ , suc ¬p x∈)) (_ , x∈)

module _ {m : ℕ} where
  postulate
    ∈⟨σ⟩↑ 
      : (x : Id) (A : TExp m) (Γ : Cxt m) 
      → ↑-closed $ Membership A Γ x
    -- ∈⟨σ⟩↑ x A (y ⦂ B , Γ) σ ρ (γ , σ⨟γ=ρ) x∈ = {!!}

    ⊢⟨σ⟩↑ : (A : TExp m) (Γ : Cxt m) (t : Raw m mod) 
      → ↑-closed $ Typability A Γ t
    -- ⊢⟨σ⟩↑ t A Γ σ ρ (γ , ρ⨟γ=ρ) ⊢t = {!!}
