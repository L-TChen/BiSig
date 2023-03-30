{-# OPTIONS --with-K --safe #-}

open import Prelude
  hiding (_++_)
open import Syntax.Simple.Description

module Syntax.Simple.Unification {D : Desc} where

open import Syntax.Simple.Term D
  hiding (_≟_)
open import Syntax.Simple.Association D

open import Data.Fin as F
open import Data.Vec as V
open import Data.List.Membership.Propositional.Properties

private variable
  Ξ n m l : ℕ

-- 
flexRigid∉ : (x : Fin (suc m)) (t : Tm (suc m))
  → x ∉ fv t → AList (suc m) m
flexRigid∉ x t x∉ = punchOutTm x t x∉ / x ∷ []

flexRigid : (x : Fin m) (t : Tm m) → Maybe (∃ (AList m))
flexRigid {m = suc m} x t with checkFv x t
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
  amguⁿ {l = suc l} (t , ts) (u , us) acc with amgu t u acc
  ... | just acc′ = amguⁿ ts us acc′
  ... | nothing   = nothing

------------------------------------------------------------------------------
-- A serier of proofs that amgu does provide a maximal general unifier

punchOut-for-x≢y
  : {x y : Fin (suc m)}
  → (¬p : x ≢ y)
  → ` x ⟪ (` punchOut ¬p) for x ⟫ ≡ ` y ⟪ (` punchOut ¬p) for x ⟫
punchOut-for-x≢y {x = x} {y} ¬p = begin
  ` x ⟪ (` punchOut ¬p) for x ⟫
    ≡⟨ sub-for-x-in-x x ⟩
  ` punchOut ¬p
    ≡⟨ (sym $ sub-for-x-in-y ¬p) ⟩
  ` y ⟪ (` punchOut ¬p) for x ⟫
    ∎
  where open ≡-Reasoning

flexFlex-is-unifier
  : (x y : Fin m)
  → let σ = flexFlex x y .proj₂ in
    ` x ⟪ σ ⟫ₐ ≡ ` y ⟪ σ ⟫ₐ
flexFlex-is-unifier {m = suc m} x y with x F.≟ y
... | yes refl = refl
... | no ¬p = begin
  ` x ⟪ flexFlex-≢ ¬p ⟫ₐ
    ≡⟨ toSub-/∷[] x (` x) ⟩
  ` x ⟪ (` punchOut ¬p) for x ⟫
    ≡⟨ punchOut-for-x≢y ¬p ⟩
  ` y ⟪ (` punchOut ¬p) for x ⟫
    ≡⟨ sym $ toSub-/∷[] x (` y) ⟩
  ` y ⟪ flexFlex-≢ ¬p ⟫ₐ
    ∎
  where open ≡-Reasoning

flexRigid∉-is-unifier
  : (x : Fin (suc m)) (t : Tm (suc m))  (x∉ : x ∉ fv t)
  → let σ = flexRigid∉ x t x∉ in
    t ⟪ σ ⟫ₐ ≡ ` x ⟪ σ ⟫ₐ
flexRigid∉-is-unifier x t x∉ = begin
  t ⟪ flexRigid∉ x t x∉ ⟫ₐ
    ≡⟨⟩
  t ⟪ punchOutTm x t x∉ / x ∷ [] ⟫ₐ
    ≡⟨ toSub-/∷[] x t ⟩
  t ⟪ punchOutTm x t x∉ for x ⟫
    ≡⟨ sub-for-nonfree=punchOut t x∉ ⟩
  punchOutTm x t x∉
    ≡⟨ sym $ sub-for-x-in-x x ⟩
  ` x ⟪ (punchOutTm x t x∉) for x ⟫
     ≡⟨ (sym $ toSub-/∷[] x (` x)) ⟩
  ` x ⟪ flexRigid∉ x t x∉ ⟫ₐ
  ∎
  where open ≡-Reasoning

lem : (x : Fin m) {l : ℕ} (i : l ∈ D) (ts : Tm m ^ l) 
  → x ∈ fvⁿ ts
  → (σ : Sub m n)
  → ¬ ` x ⟪ σ ⟫ ≡ op (l , i , ts) ⟪ σ ⟫
lem x {suc _} i (t , ts) x∈ σ p with V.lookup σ x
lem x {suc _} i (t , ts) x∈ σ refl | .(op (_ , i , sub σ t , subⁿ σ ts)) =
  {!!}

flexRigid-is-unifier
  : (x : Fin (suc m)) (i : l ∈ D) (ts : Tm (suc m) ^ l)
  → Dec (Σ[ σ ∈ AList (suc m) m ] op (l , i , ts) ⟪ σ ⟫ₐ ≡ ` x ⟪ σ ⟫ₐ)
flexRigid-is-unifier x i ts with checkFvⁿ x ts
... | no x∉ = yes
  (flexRigid∉ x (op (_ , i , ts)) x∉ , flexRigid∉-is-unifier x (op (_ , i , ts)) x∉)
... | yes x∈ = no λ where (σ , p) → lem x i ts x∈ (toSub σ)  (sym p) 
