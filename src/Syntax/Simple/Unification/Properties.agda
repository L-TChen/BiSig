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
  
---------------------------------------------------------------------------
-- Proofs that amgu does provide a maximal general unifier

module _ {m : ℕ} where

  helper
    : (σ : Sub (suc m) m) (x : Fin (suc m)) (t : Tm m)
    → (y : Fin (suc m))
    → lookup (t for x ⨟ tabulate (lookup σ ∘ punchIn x)) y
      ≡ sub-for t x y ⟨ tabulate (`_ ∘ punchIn x) ⟩ ⟨ σ ⟩
  helper σ x t y = begin
    lookup (t for x ⨟ tabulate (lookup σ ∘ punchIn x)) y
      ≡⟨⟩
    lookup (tabulate λ i → lookup (t for x) i ⟨ tabulate (lookup σ ∘ punchIn x) ⟩) y
      ≡⟨ lookup∘tabulate (_⟨ tabulate (lookup σ ∘ punchIn x) ⟩ ∘ lookup (t for x)) y ⟩
    lookup (t for x) y ⟨ tabulate (lookup σ ∘ punchIn x) ⟩
      ≡⟨ cong _⟨ tabulate (lookup σ ∘ punchIn x) ⟩ (lookup∘tabulate (sub-for t x) y) ⟩
    sub-for t x y ⟨ tabulate (lookup σ ∘ punchIn x) ⟩
      ≡⟨ cong (sub-for t x y ⟨_⟩)
        (tabulate-cong (λ i → cong (_⟨ σ ⟩) (sym $ lookup∘tabulate (`_ ∘ punchIn x) i))) ⟩
    sub-for t x y ⟨ tabulate (`_ ∘ punchIn x) ⨟ σ ⟩ 
      ≡⟨ ⟨⟩-⨟ (tabulate (`_ ∘ punchIn x)) σ (sub-for t x y) ⟩
    sub-for t x y ⟨ tabulate (`_ ∘ punchIn x) ⟩ ⟨ σ ⟩
      ∎
      
  lem
    : (σ : Sub (suc m) m) (x : Fin (suc m)) (t : Tm m)
    → ` x ⟨ σ ⟩ ≡ punchInTm x t ⟨ σ ⟩
    → (y : Fin (suc m))
    → lookup (t for x ⨟ tabulate (lookup σ ∘ punchIn x)) y ≡ lookup σ y
  lem σ x t eq y with x ≟ y
  ... | yes refl = begin
    lookup (t for x ⨟ tabulate (lookup σ ∘ punchIn x)) x
      ≡⟨ helper σ x t x ⟩
    sub-for t x x ⟨ tabulate (`_ ∘ punchIn x) ⟩ ⟨ σ ⟩
      ≡⟨ (cong (λ t → t ⟨ tabulate _ ⟩ ⟨ σ ⟩) $ sub-t-for-x-x {t = t} {x}) ⟩
    t ⟨ tabulate (`_ ∘ punchIn x) ⟩ ⟨ σ ⟩
      ≡⟨ sym eq ⟩
    lookup σ x
      ∎
  ... | no ¬p    = begin
    lookup (t for x ⨟ tabulate (lookup σ ∘ punchIn x)) y
      ≡⟨ helper σ x t y ⟩
    sub-for t x y ⟨ tabulate (`_ ∘ punchIn x) ⟩ ⟨ σ ⟩
      ≡⟨ (cong (λ t → t ⟨ tabulate _ ⟩ ⟨ σ ⟩) $ sub-t-for-x-y ¬p) ⟩
    lookup (tabulate (`_ ∘ punchIn x)) (punchOut ¬p) ⟨ σ ⟩
      ≡⟨ cong (sub σ) (lookup∘tabulate (`_ ∘ punchIn x) (punchOut ¬p)) ⟩
    ` punchIn x (punchOut ¬p) ⟨ σ ⟩
      ≡⟨ cong (lookup σ) (F.punchIn-punchOut ¬p) ⟩
    lookup σ y
      ∎

  var-elim
    : (σ : Sub (suc m) m) (x : Fin (suc m)) (t : Tm m)
    → ` x ⟨ σ ⟩ ≡ punchInTm x t ⟨ σ ⟩
    → t for x ⨟ tabulate (lookup σ ∘ punchIn x) ≡ σ 
  var-elim σ x t eq = begin
    t for x ⨟ tabulate (lookup σ ∘ punchIn x)
      ≡⟨ (sym $ tabulate∘lookup _) ⟩
    tabulate (lookup (t for x ⨟ tabulate (lookup σ ∘ punchIn x)))
      ≡⟨ tabulate-cong (lem σ x t eq) ⟩
    tabulate (lookup σ)
      ≡⟨ tabulate∘lookup σ ⟩
    σ
      ∎

  flexFlex≢-Unifies
    : {x y : Fin (suc m)}
    → (¬p : x ≢ y)
    → ` x ≈ ` y by flexFlex-≢ ¬p
  flexFlex≢-Unifies {x} {y} ¬p = begin
    ` x ⟨ flexFlex-≢ ¬p ⟩
      ≡⟨ ⟨⟩-⨟ (_ for x) id (` x) ⟩
    ` x ⟨ (` punchOut ¬p) for x ⟩ ⟨ [] ⟩
      ≡⟨ cong (_⟨ [] ⟩) $ punchOut-for-x≢y ¬p ⟩
    ` y ⟨ (` punchOut ¬p) for x ⟩ ⟨ [] ⟩
      ≡⟨ sym $ ⟨⟩-⨟ (_ for x) id (` y) ⟩
    ` y ⟨ flexFlex-≢ ¬p ⟩
      ∎

  flexRigid∉-Unifies
    : (x : Fin (suc m)) (t : Tm (suc m))  (x∉ : x ∉ₜ t)
    → t ≈ ` x by flexRigid∉ x∉
  flexRigid∉-Unifies x t x∉ = begin
    t ⟨ flexRigid∉ x∉ ⟩
      ≡⟨⟩
    t ⟨ punchOutTm x∉ / x ∷ [] ⟩
      ≡⟨ ⟨⟩-⨟ (_ for x) id t ⟩
    t ⟨ punchOutTm x∉ for x ⟩ ⟨ [] ⟩
      ≡⟨ cong (_⟨ [] ⟩) (sub-for-nonfree=punchOut t x∉) ⟩
    punchOutTm x∉ ⟨ [] ⟩
      ≡⟨ cong (_⟨ [] ⟩) (sym $ x⟨t/x⟩=t x) ⟩
    ` x ⟨ (punchOutTm x∉) for x ⟩ ⟨ [] ⟩
      ≡⟨ sym (⟨⟩-⨟ (_ for x) id (` x)) ⟩
    ` x ⟨ flexRigid∉ x∉ ⟩
      ∎

------------------------------------------------------------------------------
-- Correctness of amgu
------------------------------------------------------------------------------
flexFlex-Unifies
  : (x y : Fin m)
  → ∃ₘ $ ` x ≈ ` y by_
flexFlex-Unifies {suc m} x y with x ≟ y
... | yes refl = _ , id , refl
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
    (map₂ λ (ρ , eq) → ρ , Lem₂ t u z r (σ ⨟ ρ) eq)
    (map₂ λ (ρ , eq) → ρ , Lem₁ t u z r (σ ⨟ ρ) eq)
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
          ts ⟨ (σ ⨟ ρ) ⨟ ρ₂ ⟩
            ≡⟨ cong (ts ⟨_⟩) (⨟-assoc σ _ _) ⟩
          ts ⟨ σ ⨟ (ρ ⨟ ρ₂) ⟩
            ≡⟨ cong (λ ρ → ts ⟨ σ ⨟ ρ ⟩) (sym eq₂)  ⟩
          ts ⟨ σ ⨟ ρ₁ ⟩
            ≡⟨ V.∷-injectiveʳ eq′ ⟩
          us ⟨ σ ⨟ ρ₁ ⟩
            ≡⟨ cong (λ ρ → us ⟨ σ ⨟ ρ ⟩) eq₂ ⟩
          us ⟨ σ ⨟ (ρ ⨟ ρ₂) ⟩
            ≡⟨ cong (us ⟨_⟩) (sym $ ⨟-assoc σ _ _) ⟩
          us ⟨ (σ ⨟ ρ) ⨟ ρ₂ ⟩
            ∎))
        where postulate f : Min (λ ρ → ts ≈ us by σ ⨟ ρ) ρ
        -- TODO: Remove it and prove that amgu does produce the most general unifier.
  ... | yes (_ , ρ′ , eq′) = yes (_ , ρ ⨟ ρ′ , (begin
    (t ∷ ts) ⟨ σ ⨟ (ρ ⨟ ρ′) ⟩
      ≡⟨ cong ((t ∷ ts) ⟨_⟩) (sym $ ⨟-assoc σ _ _) ⟩
    (t ∷ ts) ⟨ (σ ⨟ ρ) ⨟ ρ′ ⟩
      ≡⟨ cong₂ _∷_ (unifies-⨟ (σ ⨟ ρ) ρ′ t u eq) eq′ ⟩
    (u ∷ us) ⟨ (σ ⨟ ρ) ⨟ ρ′ ⟩
      ≡⟨ cong ((u ∷ us) ⟨_⟩) (⨟-assoc σ _ _) ⟩
    (u ∷ us) ⟨ σ ⨟ (ρ ⨟ ρ′) ⟩
      ∎))
