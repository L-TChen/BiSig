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
  → x ∉ᵥ t → AList (suc m) m
flex∉ {x = x} x∉ = punchOutTm x∉ / x ∷ []

flex : (x : Fin m) (t : Tm m) → Maybe (∃ (AList m))
flex {suc m} x t with x ∈ᵥ? t
flex {suc m} x (` y)  | yes (here x=y) = just (_ , [])
flex {suc m} x (op _) | yes _          = nothing
... | no x∉ = just (_ , flex∉ x∉)

mutual
  amgu : (t u : Tm m) → ∃ (AList m) → Maybe (∃ $ AList m)

  amgu (op (_ , i , ts)) (op (_ , j , us)) σ with i ≟∈ j
  ... | no ¬p    = nothing
  ... | yes refl = amguⁿ ts us σ

  amgu (` x)  u        (_ , []) = flex x u
  amgu t      (` y)    (_ , []) = flex y t

  amgu t      u        (n , r / z ∷ σ) with amgu (t ⟨ r for z ⟩) (u ⟨ r for z ⟩) (n , σ)
  ... | just (l , ρ) = just (l , r / z ∷ ρ)
  ... | nothing = nothing

  amguⁿ : (ts us : Tm m ^ l) → ∃ $ AList m → Maybe (∃ $ AList m)
  amguⁿ {_} {zero}  _        _        σ = just σ
  amguⁿ {_} {suc l} (t ∷ ts) (u ∷ us) σ with amgu t u σ
  ... | just ρ  = amguⁿ ts us ρ
  ... | nothing = nothing

mgu : (t u : Tm m) → Maybe (∃ $ AList m)
mgu t u = amgu t u (_ , [])
