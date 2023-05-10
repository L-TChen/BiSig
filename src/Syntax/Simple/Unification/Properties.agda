{-# OPTIONS --with-K  #-}

open import Prelude
  hiding (_++_; _+_)
open import Syntax.Simple.Description

module Syntax.Simple.Unification.Properties (D : Desc) where

open import Syntax.Simple.Term        D
open import Syntax.Simple.Association D
open import Syntax.Simple.Unification D
open import Syntax.Simple.Properties  D

open N using (_+_)

open ≡-Reasoning

private variable
  Γ Δ Ξ m n l i j k : ℕ
  ts us   : Tm Ξ ^ n
  σ₁ σ₂   : Sub Γ Δ
  x y     : Fin Ξ

private variable
  t u v : Tm m

------------------------------------------------------------------------------
-- Association list implies the inequality relation

AList→≥ : AList m n → m ≥ n
AList→≥ []           = ≤-refl
AList→≥ (t / x ∷ ge) = ≤-step (AList→≥ ge)
  
------------------------------------------------------------------------------
-- Proofs about toSub

{-
toSub-∷
  : {u : Tm m} (x : Fin (suc m)) (ρ : AList m n)
  → (t : Tm (suc m))
  → t ⟨ u / x ∷ ρ ⟩ ≡ t ⟨ u for x ⟩ ⟨ ρ ⟩
toSub-∷ {_} {_} {u} x ρ t = ⟨⟩-⨟ (u for x) (toSub ρ) t
-}

toSub-∷[]
  : {u : Tm m} (x : Fin (suc m))
  → (t : Tm (suc m))
  → t ⟨ u / x ∷ [] ⟩ ≡ t ⟨ u for x ⟩
toSub-∷[] {_} {u} x t = begin
  t ⟨ u / x ∷ [] ⟩
    ≡⟨ ⟨⟩-⨟ (u for x) (toSub []) t ⟩
  t ⟨ u for x ⟩ ⟨ [] ⟩
    ≡⟨ ⟨⟩-id {ℕ} {Sub} (t ⟨ u for x ⟩) ⟩
  t ⟨ u for x ⟩
    ∎

---------------------------------------------------------------------------
-- Proofs that amgu does provide a maximal general unifier

flexFlex≢-Unifies
  : {x y : Fin (suc m)}
  → (¬p : x ≢ y)
  → ` x ≈ ` y by flexFlex-≢ ¬p
flexFlex≢-Unifies {_} {x} {y} ¬p = begin
  ` x ⟨ flexFlex-≢ ¬p ⟩
    ≡⟨ toSub-∷[] x (` x) ⟩
  ` x ⟨ (` punchOut ¬p) for x ⟩
    ≡⟨ punchOut-for-x≢y ¬p ⟩
  ` y ⟨ (` punchOut ¬p) for x ⟩
    ≡⟨ sym $ toSub-∷[] x (` y) ⟩
  ` y ⟨ flexFlex-≢ ¬p ⟩
    ∎

flexRigid∉-Unifies
  : (x : Fin (suc m)) (t : Tm (suc m))  (x∉ : x ∉ₜ t)
  → t ≈ ` x by flexRigid∉ x∉
flexRigid∉-Unifies x t x∉ = begin
  t ⟨ flexRigid∉ x∉ ⟩
    ≡⟨⟩
  t ⟨ punchOutTm x∉ / x ∷ [] ⟩
    ≡⟨ toSub-∷[] x t ⟩
  t ⟨ punchOutTm x∉ for x ⟩
    ≡⟨ sub-for-nonfree=punchOut t x∉ ⟩
  punchOutTm x∉
    ≡⟨ sym $ sub-for-x-in-x x ⟩
  ` x ⟨ (punchOutTm x∉) for x ⟩
    ≡⟨ (sym $ toSub-∷[] x (` x)) ⟩
  ` x ⟨ flexRigid∉ x∉ ⟩
    ∎

------------------------------------------------------------------------------
-- Correctness of amgu
------------------------------------------------------------------------------
flexFlex-Unifies
  : (x y : Fin m)
  → ∃ₘ $ ` x ≈ ` y by_
flexFlex-Unifies {suc m} x y with x ≟ y
... | yes refl = _ , [] , refl
... | no ¬p    = _ , flexFlex-≢ ¬p , flexFlex≢-Unifies ¬p

flexRigid-Unifies
  : (x : Fin m) (i : k ∈ D) (ts : Tm m ^ k)
  → Dec (∃ₘ $ op′ i ts ≈ ` x by_)
flexRigid-Unifies {suc m} x i ts with x ∈ₜ? op′ i ts
... | no x∉  = yes (m , flexRigid∉ x∉ , flexRigid∉-Unifies x (op′ i ts) x∉)
... | yes x∈ = no λ where
  (l , σ , p) →  var≢op x i ts (unify-occurrence (toSub σ) x∈ (sym p)) 

flexRigid-Unifies′
  : (x : Fin m) (i : k ∈ D) (ts : Tm m ^ k)
  → Dec (∃ₘ {ℕ} {AList} $ ` x ≈ op′ i ts by_)
flexRigid-Unifies′ {suc m} x i ts = map′
  (λ where (_ , σ , eq) → (_ , σ , sym eq))
  (λ where (_ , σ , eq) → (_ , σ , sym eq))
  $ flexRigid-Unifies x i ts

-- Give it a name?
Lem₁
  : (t u : Tm (suc m)) (z : Fin (suc m)) (r : Tm m)
  → (σ : AList m n) 
  → t ≈ u by r / z ∷ σ
  → t ⟨ r for z ⟩ ≈ u ⟨ r for z ⟩ by σ
Lem₁ t u z r σ eq = begin
  t ⟨ r for z ⟩ ⟨ σ ⟩
    ≡⟨ sym (⟨⟩-⨟ (r for z) (toSub σ) t) ⟩
  t ⟨ r / z ∷ σ ⟩
    ≡⟨ eq ⟩
  u ⟨ r / z ∷ σ ⟩
    ≡⟨ ⟨⟩-⨟ (r for z) (toSub σ) u ⟩
  u ⟨ r for z ⟩ ⟨ σ ⟩
    ∎

Lem₂
  : (t u : Tm (suc m)) (z : Fin (suc m)) (r : Tm m)
  → (σ : AList m n) 
  → t ⟨ r for z ⟩ ≈ u ⟨ r for z ⟩ by σ
  → t ≈ u by (r / z ∷ σ) 
Lem₂ t u z r σ eq = begin
  t ⟨ r / z ∷ σ ⟩
    ≡⟨ ⟨⟩-⨟ (r for z) (toSub σ) t ⟩
  t ⟨ r for z ⟩ ⟨ σ ⟩
    ≡⟨ eq ⟩
  u ⟨ r for z ⟩ ⟨ σ ⟩
    ≡⟨ sym (⟨⟩-⨟ (r for z) (toSub σ) u) ⟩
  u ⟨ r / z ∷ σ ⟩
    ∎

mutual
  amgu⁺ : (t u : Tm m) (σ : AList m n)
    → Dec (∃ₘ $ λ ρ → t ≈ u by σ ⨟ ρ)
  amgu⁺ (op′ i ts) (op′ j us) σ with i ≟∈ j
  ... | no ¬p    = no λ where (_ , ρ , p) → ¬p (op-inj₁₂ p)
  ... | yes refl = map′
    (map₂ $ map₂ λ eq → cong (λ ts → op′ i ts) eq)
    (map₂ $ map₂ λ eq → op-inj₃ eq)
    $ amguⁿ⁺ ts us σ
  amgu⁺ (` x)      (` y)      []          = yes (flexFlex-Unifies x y)
  amgu⁺ (op′ i ts) (` y)      []          = flexRigid-Unifies y i ts
  amgu⁺ (` x)      (op′ i us) []          = flexRigid-Unifies′ x i us
  amgu⁺ t                   u (r / z ∷ σ) = map′
    (map₂ λ (ρ , eq) → ρ , Lem₂ t u z r (σ ++ ρ) eq)
    (map₂ λ (ρ , eq) → ρ , Lem₁ t u z r (σ ++ ρ) eq)
    $ amgu⁺ (t ⟨ r for z ⟩) (u ⟨ r for z ⟩) σ

  amguⁿ⁺ : (ts us : Tm m ^ l) (σ : AList m n)
    → Dec (∃ₘ λ ρ → ts ≈ us by σ ⨟ ρ)
  amguⁿ⁺ []       []       σ = yes (_ , [] , refl)
  amguⁿ⁺ (t ∷ ts) (u ∷ us) σ with amgu⁺ t u σ
  ... | no ¬p = no λ where (_ , ρ , eq) → ¬p (_ , ρ , V.∷-injectiveˡ eq)
  ... | yes (l , ρ , eq) with amguⁿ⁺ ts us (σ ++ ρ)
  ... | no ¬q = no λ
    where
      (l₁ , ρ₁ , eq′) → let (ρ₂ , eq₂) = f .proj₂ ρ₁ (V.∷-injectiveʳ eq′)
        in ¬q (_ , ρ₂ , (begin
          ts ⟨ (σ ++ ρ) ++ ρ₂ ⟩
            ≡⟨ cong (ts ⟨_⟩) (sym $ ++-assoc σ) ⟩
          ts ⟨ σ ++ (ρ ++ ρ₂) ⟩
            ≡⟨ cong (λ ρ → ts ⟨ σ ++ ρ ⟩) (sym eq₂)  ⟩
          ts ⟨ σ ++ ρ₁ ⟩
            ≡⟨ V.∷-injectiveʳ eq′ ⟩
          us ⟨ σ ++ ρ₁ ⟩
            ≡⟨ cong (λ ρ → us ⟨ σ ++ ρ ⟩) eq₂ ⟩
          us ⟨ σ ++ (ρ ++ ρ₂) ⟩
            ≡⟨ cong (us ⟨_⟩) (++-assoc σ) ⟩
          us ⟨ (σ ++ ρ) ++ ρ₂ ⟩
            ∎))
        where postulate f : Min (λ ρ → ts ≈ us by σ ⨟ ρ) ρ
        -- TODO: Remove it and prove that amgu does produce the most general unifier.
  ... | yes (_ , ρ′ , eq′) = yes (_ , ρ ++ ρ′ , (begin
    (t ∷ ts) ⟨ σ ++ (ρ ++ ρ′) ⟩
      ≡⟨ cong ((t ∷ ts) ⟨_⟩) (++-assoc σ) ⟩
    (t ∷ ts) ⟨ (σ ++ ρ) ++ ρ′ ⟩
      ≡⟨ cong₂ _∷_ (unifies-⨟ (σ ++ ρ) ρ′ t u eq) eq′ ⟩
    (u ∷ us) ⟨ (σ ++ ρ) ++ ρ′ ⟩
      ≡⟨ cong ((u ∷ us) ⟨_⟩) (sym $ ++-assoc σ) ⟩
    (u ∷ us) ⟨ σ ++ ρ ++ ρ′ ⟩
      ∎))
