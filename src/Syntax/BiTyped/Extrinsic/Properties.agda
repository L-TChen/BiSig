{-# OPTIONS --rewriting #-}

open import Prelude

import Syntax.Simple.Description  as S
import Syntax.BiTyped.Description as B

module Syntax.BiTyped.Extrinsic.Properties
  {SD : S.Desc} (Id : Set) (D : B.Desc SD) where


open import Syntax.NamedContext SD Id

open import Syntax.Simple.Term SD
  renaming (Tm to TExp; Tms to TExps; Sub to TSub)
open import Syntax.Simple.Association            SD
open import Syntax.Simple.Properties             SD
open import Syntax.Simple.Unification            SD
open import Syntax.Simple.Unification.Properties SD

open import Syntax.BiTyped.Extrinsic.Functor     SD  Id
open import Syntax.BiTyped.Extrinsic.Term            Id D
import Syntax.BiTyped.Raw.Functor                SD  Id as R


open import Syntax.BiTyped.Raw.Term    Id D

private variable
  n m : ℕ
  mod  : Mode
  Γ   : Cxt m
  x   : Id
  A B : TExp m
  t   : Raw m mod

sub-∈ : ∀ {x} (σ : TSub m n)
  → x ⦂ A       ∈ Γ
  → x ⦂ A ⟨ σ ⟩ ∈ Γ ⟨ σ ⟩
sub-∈ σ zero        = zero
sub-∈ σ (suc ¬p x∈) = suc ¬p (sub-∈ σ x∈)

subst-∈→∈
  : ∀ (Γ : Cxt m) x
  → ¬ (∃[ A ] (x ⦂ A ∈ Γ))
  → (σ : TSub m n)
  → ¬ (Σ[ B ∈ TExp _ ] (x ⦂ B ∈ Γ ⟨ σ ⟩))
subst-∈→∈ (_ ∷ _)       _ ¬∃ σ (D , zero)      = ¬∃ (_ , zero)
subst-∈→∈ ((y , C) ∷ Γ) x ¬∃ σ (D , suc ¬p x∈) =
  subst-∈→∈ Γ x (λ where (_ , x∈) → ¬∃ (_ , suc ¬p x∈)) σ (_ , x∈)

-- ∈⟨σ⟩↑ 
--   : ∀ (Γ : Cxt m) (A : TExp m) (x : _)
--   → ↑-closed λ n (σ : TSub m n)
--     → x ⦂ A ⟨ σ ⟩ ∈ Γ ⟨ σ ⟩
-- ∈⟨σ⟩↑ Γ A x σ ρ (γ , σ⨟γ=ρ) x∈ = sub-∈ ρ {!!}

-- ⊢⟨σ⟩↑ : (Γ : Cxt m) (A : TExp m) (t : Raw m mod)
--   → ↑-closed λ n (σ : TSub m n)
--     → ⊢⇄ mod (A ⟨ σ ⟩) (Γ ⟨ σ ⟩) (t ⟨ σ ⟩)
-- ⊢⟨σ⟩↑ Γ A t σ ρ (γ , ρ⨟γ=ρ) ⊢t = {!!}
