{-# OPTIONS --with-K --safe #-}

open import Prelude
  hiding (_++_)
open import Syntax.Simple.Description

module Syntax.Simple.Unification (D : Desc) where

open import Syntax.Simple.Term D
open import Syntax.Simple.Association D

private variable
  n m l : ℕ

-- 
flex∉ : {x : Fin (suc m)} {t : Tm (suc m)}
  → x ∉ₜ t → AList (suc m) m
flex∉ {x = x} x∉ = punchOutTm x∉ / x ∷ []

flex : (x : Fin m) (t : Tm m) → Maybe (∃ (AList m))
flex {suc m} x t with x ∈ₜ? t
flex {suc m} x (` y)  | yes (here x=y) = just (_ , [])
flex {suc m} x (op _) | yes _          = nothing
... | no x∉ = just (_ , flex∉ x∉)

mutual
  amgu : (t u : Tm m) (ac : ∃ (AList m))
    → Maybe (∃ (AList m))
  amgu (op (_ , i , ts)) (op (_ , j , us)) ac with i ≟∈ j
  ... | no ¬p    = nothing
  ... | yes refl = amguⁿ ts us ac
  amgu (` x)  u        (_ , []) = flex x u
  amgu t      (` y)    (_ , []) = flex y t
  amgu t      u        (n , r / z ∷ σ) with amgu (t ⟨ r for z ⟩) (u ⟨ r for z ⟩) (n , σ)
  ... | just (l , σ′) = just (l , r / z ∷ σ′)
  ... | nothing = nothing

  amguⁿ : (ts us : Tm m ^ l) (ac : ∃ (AList m))
    → Maybe (∃ (AList m))
  amguⁿ {l = zero}  _        _        ac = just ac
  amguⁿ {l = suc l} (t ∷ ts) (u ∷ us) ac with amgu t u ac
  ... | just ac′ = amguⁿ ts us ac′
  ... | nothing   = nothing
