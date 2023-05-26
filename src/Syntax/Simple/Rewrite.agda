{-# OPTIONS --with-K --rewriting  #-}

open import Syntax.Simple.Description

module Syntax.Simple.Rewrite (D : Desc) where

open import Prelude

open import Syntax.Simple.Term       D
open import Syntax.Simple.Properties D
open import Syntax.Simple.Association D

open import Agda.Builtin.Equality.Rewrite

private variable
  n m l k : ℕ
  A   : Set
  t u : Tm n
  σ ρ : AList m n

lem1 : (σ : AList m n) (ρ : AList n l) → toSub (σ ⨟ ρ) ≡ toSub σ ⨟ toSub ρ
lem1 σ ρ = toSub-++ σ ρ

lem2 : (i : Fin n) → lookup (tabulate `_) i ≡ ` i
lem2 = lookup∘tabulate `_

lem3 : (ρ : Sub m n) (σ : Sub n l ) (γ : Sub l k) → Sub-⨟ ((SubIsCategory IsCategory.⨟ ρ) σ) γ ≡ ρ ⨟ (σ ⨟ γ)
lem3 _ _ _ = ⨟-assoc _ _ _

-- The following leads to unsolved meta variables
-- lem3 : (σ : AList m n) (ρ : AList n l) (t : Tm m)
--   → sub (tabulate (λ i → sub (toSub ρ) (lookup (toSub σ) i))) t ≡ t ⟨ σ ⟩ ⟨ ρ ⟩
-- lem3 σ ρ t = begin
--   sub (tabulate (λ i → sub (toSub ρ) (lookup (toSub σ) i))) t
--     ≡⟨ sym (cong (t ⟨_⟩) (lem1 σ ρ)) ⟩
--   t ⟨ σ ⨟ ρ ⟩
--     ≡⟨ ⟨⟩-⨟ σ ρ t ⟩
--   t ⟨ σ ⟩ ⟨ ρ ⟩
--     ∎
--   where open ≡-Reasoning

{-# REWRITE lem1 lem2 lem3 #-}
