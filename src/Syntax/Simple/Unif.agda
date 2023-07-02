open import Prelude
 
open import Syntax.Simple.Description

module Syntax.Simple.Unif (D : Desc) where

open import Syntax.Simple.Term       D
open import Syntax.Simple.Properties D


private variable
  A         : Set
  Ξ Θ m n l : ℕ
  x         : Fin Ξ
  xs ys     : Fins# Ξ

open ≡-Reasoning
open Equivalence

insert : (x : Fin Ξ) (t : Tm 0) (ρ : ∃Sub⊆ Ξ) → MinDec (Ext ρ (` x ≈ t))
insert x t (xs , ρ) with fresh? x xs
... | inl x#xs = yesₘ (_ , extend ρ x#xs t) record
  { proof      = record
    { ext = record
      { domain-ext  = there
      ; consistency = λ _ → refl
      }
    ; witness = (λ { (here eq) → here eq }) , refl
    }
  ; minimality = λ where
    σ (ext-con (≤-con xs⊆ys con) (x∈zs , eq)) → record
      { domain-ext  = λ where
        (here refl) → x∈zs (here refl)
        (there y∈)  → xs⊆ys y∈
      ; consistency = λ where
        (here refl) → sym eq
        (there x∈)  → con x∈
      } 
  }
... | inr x∈xs with ρ x∈xs ≟ t
... | yes eq = yesₘ (_ , ρ) (Pρ→MinExtP (_ , ρ) ((λ { (here refl) → x∈xs }) , eq))
... | no neq = noₘ λ where
  (zs , σ) (ext-con (≤-con xs⊆zs con) (x∈zs , eq)) → neq (begin
    ρ x∈xs
      ≡⟨ con x∈xs ⟩
    σ (xs⊆zs x∈xs)
      ≡⟨ cong σ (#∈-uniq _ _) ⟩
    σ (x∈zs (here refl))
      ≡⟨ eq ⟩
    t
      ∎)

mutual
  acmp : (t : Tm Ξ) (u : Tm 0) (ρ : ∃Sub⊆ Ξ)
    → MinDec (Ext ρ (t ≈ u))
  acmp (` x)         t             ρ = insert x t ρ
  acmp (op (i , ts)) (op (j , us)) ρ with i ≟ j
  ... | no  i≠j  = noₘ λ where
    σ (ext-con ρ≤σ (_ , refl)) → i≠j refl
  ... | yes refl = MinDec⇔ (Ext⇔ (ts≈us⇔opts≈opus ts us) ρ) .to (acmpⁿ ts us ρ)

  acmpⁿ : (ts : Tm Ξ ^ n) (us : Tm 0 ^ n) (ρ : ∃Sub⊆ Ξ)
    → MinDec (Ext ρ (ts ≈ⁿ us))
  acmpⁿ []       []       ρ = yesₘ ρ (Pρ→MinExtP ρ ((λ ()) , refl))
  acmpⁿ (t ∷ ts) (u ∷ us) ρ with acmpⁿ ts us ρ
  ... | noₘ ¬σ      = noₘ λ σ (ext-con ρ≤σ (t∷ts⊆ , eq)) →
    ¬σ σ (ext-con ρ≤σ ((λ x∈ → t∷ts⊆ (∪⁺ʳ (vars t) x∈)) , V.∷-injectiveʳ eq))
  ... | yesₘ ρ̅  minρ̅ with acmp t u ρ̅
  ... | noₘ ¬Ext = noₘ (λ σ Qσ → failure-propagate ρ ρ̅ minρ̅ ¬Ext σ (Ext⇔ (t≈u×ts≈us⇔tts≈uus t u ts us) ρ σ .from Qσ))
  ... | yesₘ ρ′ minρ′ = yesₘ ρ′ (Min⇔ (Ext⇔ (t≈u×ts≈us⇔tts≈uus t u ts us) ρ) ρ′ .to
    (optimist ρ ρ̅ ρ′ (↑≈ⁿ ts us) minρ̅ minρ′))

