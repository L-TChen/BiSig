{-# OPTIONS --safe #-}

open import Prelude
open import Syntax.Simple.Description

module Syntax.Context (D : Desc) where

open import Syntax.Context.Base  public
open import Syntax.Simple D

Cxt : ℕ → Set
Cxt m = Context (TExp m)

cxtSub : {m n : ℕ} → TSub m n
  → Cxt m → Cxt n
cxtSub σ []      = []
cxtSub σ (A ∷ Γ) = A ⟨ σ ⟩ ∷ cxtSub σ Γ

instance
  CxtSubIsPresheaf : IsPresheaf {ℕ} {TSub} Cxt
  CxtSubIsPresheaf ._⟨_⟩ Γ σ         = cxtSub σ Γ
  CxtSubIsPresheaf .⟨⟩-id []         = refl
  CxtSubIsPresheaf .⟨⟩-id (A ∷ Γ)    = cong₂ (_∷_) (⟨⟩-id {ℕ} {TSub} A) (⟨⟩-id Γ)
  CxtSubIsPresheaf .⟨⟩-⨟ σ ρ []      = refl
  CxtSubIsPresheaf .⟨⟩-⨟ σ ρ (A ∷ Γ) = cong₂ (_∷_) (⟨⟩-⨟ σ ρ A) (⟨⟩-⨟ σ ρ Γ)

--  CxtAListIsPresheaf : IsPresheaf Cxt
--  CxtAListIsPresheaf ._⟨_⟩ Γ σ = Γ ⟨ toSub σ ⟩ -- Γ ⟨ toSub σ ⟩
--  CxtAListIsPresheaf .⟨⟩-id []         = refl
--  CxtAListIsPresheaf .⟨⟩-id (A ∷ Γ)    =
--    cong₂ (_∷_) (⟨⟩-id {ℕ} {AList} A) (⟨⟩-id {ℕ} {AList} Γ)
--  CxtAListIsPresheaf .⟨⟩-⨟ σ ρ []      = refl
--  CxtAListIsPresheaf .⟨⟩-⨟ σ ρ (A ∷ Γ) =
--    cong₂ (_∷_) (⟨⟩-⨟ σ ρ A) (⟨⟩-⨟ σ ρ Γ)
