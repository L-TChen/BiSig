open import Prelude
open import Syntax.Simple.Description

module Syntax.Simple.Operation {D : Desc} where

import Data.Fin  as F
open import Syntax.Simple.Term D

private variable
  Δ Ξ : ℕ

freeAlg : (D -Alg) (List ∘ Fin)
var freeAlg x = x ∙ ∅
alg freeAlg = algᶜ _
  where
    algⁿ : ∀ n → List (Fin Ξ) ^ n → List (Fin Ξ)
    algⁿ zero    _        = ∅
    algⁿ (suc n) (t , ts) = t ++ algⁿ _ ts
    algᶜ : ∀ D → ⟦ D ⟧ (List ∘ Fin) ⇒₁ List ∘ Fin
    algᶜ Ds (_ , i , ts) = algⁿ _ ts
fv : Tm ⇒₁ List ∘ Fin
fv = fold freeAlg

mutual
  _≟_ : (t u : Tm Ξ) → Dec (t ≡ u)
  (` x) ≟ (` y) with  x F.≟ y
  ... | yes p = yes (cong `_ p)
  ... | no ¬p = no λ where refl → ¬p refl
  op t  ≟ op u  with compareMap _ t u
  ... | yes p = yes (cong op p) 
  ... | no ¬p = no λ where refl → ¬p refl
  (` x) ≟ op u  = no λ ()
  op x  ≟ (` y) = no λ ()

  compareMap : ∀ D → (t u : (⟦ D ⟧ Tm) Ξ) → Dec (t ≡ u)
  compareMap _ (D , i , ts) (_ , j , us) with i ≟∈ j
  ... | no ¬p    = no λ where refl → ¬p refl
  ... | yes refl with compareMapⁿ D ts us
  ... | no ¬q    = no λ where refl → ¬q refl
  ... | yes refl = yes refl

  compareMapⁿ : ∀ n → (ts us : Tm Ξ ^ n) → Dec (ts ≡ us)
  compareMapⁿ zero    _        _        = yes refl
  compareMapⁿ (suc n) (t , ts) (u , us) with t ≟ u
  ... | no ¬p = no λ where refl → ¬p refl
  ... | yes p with compareMapⁿ n ts us 
  ... | no ¬q = no λ where refl → ¬q refl
  ... | yes q = yes (cong₂ _,_ p q)

_≟s_ : (σ σ′ : Sub Ξ Δ) → Dec (σ ≡ σ′)
[]      ≟s []      = yes refl
(A ∷ Δ) ≟s (B ∷ Γ) with A ≟ B
... | no ¬p =  no λ where refl → ¬p refl
... | yes p with Δ ≟s Γ 
... | no ¬q =  no λ where refl → ¬q refl
... | yes q =  yes (cong₂ _∷_ p q)