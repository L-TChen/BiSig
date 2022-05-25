open import Prelude

module Language.Annotatability where

open import Cubical.Data.Maybe
open import Language.Type


module Untyped where
  open import Language.Untyped.Term as U
  open import Language.STLC.Term    as S

  private
    variable
      Γ Δ : Ty → Type
      A B : Ty

  E :  (Type → Type) → (Ty → Type) → Ty → Type
  E T Γ A = T (Σ _ Γ) 

  ▷-⁺ : Σ Ty (Γ ▷ B) → (Σ Ty Γ) ⁺
  ▷-⁺ (A , Z)     = Z
  ▷-⁺ (A , (S x)) = S (A , x)

  δᵗ : Ty → ((Ty → Type) → Ty → Type) → (Ty → Type) → Ty → Type
  δᵗ A T Γ B = T (Γ ▷ A) B

  δ : (Type → Type) → Type → Type
  δ T Γ = T (Γ ⁺)

  τ : {T : Type → Type} (map : ∀ {X Y} → (X → Y) → T X → T Y)
    → δᵗ B (E T) Γ A
    → E    (δ T) Γ A
  τ map t = map ▷-⁺ t

  -- Tm : [Ty, Type] → [Ty, Type] 
  -- Λ  : Type → Type
  erase : Tm Γ A → (E Λ) Γ A
  erase {A = A} (` x)   = ` (A , x)
  erase (t · u)         = erase t · erase u
  erase {A = A} (ƛ t)   = ƛ τ {A = A} (U.⟨_⟩_) (erase t) -- τ {A = A} (U.⟨_⟩_) (erase t)
  -- Goal: Λ ((Σ Ty Γ) ⁺)
  -- Have: Λ (Σ Ty (Γ ▷ A₁))

module STLC where
  open import Language.STLC.Term    as S
  open import Language.BiSTLC.Term  as B

  private
    variable
      A B : Ty
      m   : Bool
      Γ Δ : Ty → Type

  E : ((Ty → Type) → Ty → Type) → (Ty → Type) → Bool → Ty → Type
  E T Γ _ A = T Γ A

  forget : B.Tm Γ m A → E S.Tm Γ m A
  forget (` x)       = ` x
  forget (t ⦂ _)     = forget t
  forget (conv eq t) = subst (S.Tm _) eq (forget t)
  forget (t · u)     = forget t · forget u
  forget (ƛ t)       = ƛ forget t

-- 1. Morphism of signature: S ∘ E -> E ∘ S' 
-- 2. Functor: Alg(S') --> Alg(S)
-- 3. fold: S(μ S) -------------→ μ S
--             |                  |
--             ↓                  ↓
--          S(μ S') → S' (μ S') -→ μ S'
