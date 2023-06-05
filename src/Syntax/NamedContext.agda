{-# OPTIONS --with-K --safe #-}

open import Prelude
open import Syntax.Simple.Description

module Syntax.NamedContext (D : Desc) (Id : Set) where

open import Syntax.NamedContext.Base Id public
open import Syntax.Simple.Term        D

Cxt : ℕ → Set
Cxt m = Context (Tm m)

cxtSub : {m n : ℕ} → Sub m n
  → Cxt m → Cxt n
cxtSub σ []          = []
cxtSub σ ((x , A) ∷ Γ) = (x , sub σ A) ∷ cxtSub σ Γ

instance
  CxtSubIsPresheaf : IsPresheaf Cxt
  CxtSubIsPresheaf ._⟨_⟩ Γ σ   = cxtSub σ Γ
  CxtSubIsPresheaf .⟨⟩-id []             = refl
  CxtSubIsPresheaf .⟨⟩-id ((x , A) ∷ Γ)    = cong₂ (λ A Γ → (x , A) ∷ Γ) (⟨⟩-id {ℕ} {Sub} A) (⟨⟩-id Γ)
  CxtSubIsPresheaf .⟨⟩-⨟ σ ρ []          = refl
  CxtSubIsPresheaf .⟨⟩-⨟ σ ρ ((x , A) ∷ Γ) =
    cong₂ (λ A Γ → (x , A) ∷ Γ) (⟨⟩-⨟ σ ρ A) (⟨⟩-⨟ σ ρ Γ)

--  CxtAListIsPresheaf : IsPresheaf Cxt
--  CxtAListIsPresheaf ._⟨_⟩ Γ σ = Γ ⟨ toSub σ ⟩
--  CxtAListIsPresheaf .⟨⟩-id []             = refl
--  CxtAListIsPresheaf .⟨⟩-id ((x , A) ∷ Γ)    =
--    cong₂ (λ A Γ → (x , A) ∷ Γ) (⟨⟩-id {ℕ} {AList} A) (⟨⟩-id {ℕ} {AList} Γ)
--  CxtAListIsPresheaf .⟨⟩-⨟ σ ρ []          = refl
--  CxtAListIsPresheaf .⟨⟩-⨟ σ ρ ((x , A) ∷ Γ) =
--    cong₂ (λ A Γ → (x , A) ∷ Γ) (⟨⟩-⨟ σ ρ A) (⟨⟩-⨟ σ ρ Γ)
