{-# OPTIONS --with-K --safe #-}

open import Prelude
  hiding (_++_)
open import Syntax.Simple.Description

module Syntax.Simple.Unification (D : Desc) where

open import Syntax.Simple.Term D
  hiding (_≟_)
open import Syntax.Simple.Association D

private variable
  n m l : ℕ

-- 
flexRigid∉ : (x : Fin (suc m)) (t : Tm (suc m))
  → x ∉ₜ t → AList (suc m) m
flexRigid∉ x t x∉ = punchOutTm x t x∉ / x ∷ []

flexRigid : (x : Fin m) (t : Tm m) → Maybe (∃ (AList m))
flexRigid {m = suc m} x t with x ∈ₜ? t
... | yes _ = nothing
... | no x∉ = just (_ , flexRigid∉ x t x∉)

flexFlex-≢ : {x y : Fin (suc m)}
  → (¬p : x ≢ y)
  → AList (suc m) m
flexFlex-≢ {x = x} ¬p = (` punchOut ¬p) / x ∷ []

flexFlex : (x y : Fin m) → ∃ (AList m)
flexFlex {m = suc m} x y with x F.≟ y
... | yes p = suc m , []
... | no ¬p = m , flexFlex-≢ ¬p 

mutual
  amgu : (t u : Tm m) (acc : ∃ (AList m))
    → Maybe (∃ (AList m))
  amgu {m} (op (_ , i , ts)) (op (_ , j , us)) acc with i ≟∈ j
  ... | no ¬p    = nothing
  ... | yes refl = amguⁿ ts us acc
  amgu (` x)  (` y)  (_ , []) = just (flexFlex x y)
  amgu (` x)  u      (_ , []) = flexRigid x u
  amgu t      (` y)  (_ , []) = flexRigid y t
  amgu t      u      (n , r / z ∷ σ) with amgu (t ⟪ r for z ⟫) (u ⟪ r for z ⟫) (n , σ)
  ... | just σ′ = just (r / z ∷′ σ′)
  ... | nothing = nothing

  amguⁿ : (ts us : Tm m ^ l) (acc : ∃ (AList m))
    → Maybe (∃ (AList m))
  amguⁿ {l = zero}  _        _        acc = just acc
  amguⁿ {l = suc l} (t ∷ ts) (u ∷ us) acc with amgu t u acc
  ... | just acc′ = amguⁿ ts us acc′
  ... | nothing   = nothing
