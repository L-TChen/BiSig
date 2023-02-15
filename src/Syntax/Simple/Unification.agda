{-# OPTIONS --with-K --safe #-}

open import Prelude
  hiding (_++_)
open import Syntax.Simple.Description

module Syntax.Simple.Unification {D : Desc} where

open import Syntax.Simple.Term D
  hiding (_≟_)
open import Syntax.Simple.Association D

open import Data.Fin
open import Data.List.Membership.Propositional.Properties

private variable
  Ξ n m l : ℕ

mutual
  checkFv : (x : Fin m) (t : Tm m) → Dec (x ∈ fv t)
  checkFv x (` y)  with x ≟ y
  ... | yes p = yes (here p)
  ... | no ¬p = no λ where (here p) → ¬p p
  checkFv x (op (_ , _ , ts)) = checkFvⁿ x ts

  checkFvⁿ : (x : Fin m) (t : Tm m ^ l) → Dec (x ∈ fvⁿ t)
  checkFvⁿ {l = zero}  _ _        = no λ ()
  checkFvⁿ {l = suc l} x (t , ts) with checkFv x t
  ... | yes p = yes (∈-++⁺ˡ p)
  ... | no ¬p with checkFvⁿ x ts
  ... | yes q = yes (∈-++⁺ʳ (fv t) q)
  ... | no ¬q = no λ where x → case ∈-++⁻ (fv t) x of λ where
    (inl ∈t)  → ¬p ∈t
    (inr ∈ts) → ¬q ∈ts

mutual
  check : (x : Fin (suc Ξ)) (t : Tm (suc Ξ))
    → ¬ x ∈ fv t → Tm Ξ
  check x (` y)  x∉t with x ≟ y
  ... | yes x=y = ⊥-elim₀ (x∉t (here x=y))
  ... | no ¬x=y = ` punchOut ¬x=y
  check x (op (_ , i , ts)) x∉t =
    op (_ , i , checkⁿ x ts x∉t)

  checkⁿ : (x : Fin (suc Ξ)) (ts : Tm (suc Ξ) ^ n)
    → ¬ x ∈ fvⁿ ts → Tm Ξ ^ n
  checkⁿ {n = zero}  _ _        _    = _ 
  checkⁿ {n = suc l} x (t , ts) x∉ts =
    check x t (x∉ts ∘ ∈-++⁺ˡ) , checkⁿ x ts (x∉ts ∘ ∈-++⁺ʳ (fv t))

flexFlex : (x y : Fin m) → ∃ (AList m)
flexFlex {m = suc m} x y with thick x y
... | just y′ = m , ((` y′) / x ∷ [])
... | nothing = suc m , []

flexRigid : (x : Fin m) (t : Tm m) → Maybe (∃ (AList m))
flexRigid {m = suc m} x t with checkFv x t
... | yes _ = nothing
... | no ¬p = just (m , (check x t ¬p / x ∷ []))

mutual
  amgu : (t u : Tm m) (acc : ∃ (AList m))
    → Maybe (∃ (AList m))
  amgu {m} (op (_ , i , ts)) (op (_ , j , us)) acc with i ≟∈ j
  ... | no ¬p    = nothing
  ... | yes refl = amguⁿ ts us acc
  amgu {m} (` x)  (` y)  (_ , [])        = just (flexFlex x y)
  amgu {m} (` x)  u      (_ , [])        = flexRigid x u
  amgu {m} t      (` y)  (_ , [])        = flexRigid y t
  amgu {m} t      u      (n , r / z ∷ σ) with amgu (⟪ r for z ⟫ t) (⟪ r for z ⟫ u) (n , σ)
  ... | just σ′  = just (r / z ∷′ σ′)
  ... | nothing = nothing

  amguⁿ : (ts us : Tm m ^ l) (acc : ∃ (AList m))
    → Maybe (∃ (AList m))
  amguⁿ {l = zero}  _        _        acc = just acc
  amguⁿ {l = suc l} (t , ts) (u , us) acc with amgu t u acc
  ... | just acc′ = amguⁿ ts us acc′
  ... | nothing   = nothing
