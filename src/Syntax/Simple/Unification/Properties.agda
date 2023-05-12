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
  m n l i j k : ℕ
  t u     : Tm m
  ts us   : Tm m ^ k
  σ σ₁ σ₂ : Sub m n
  x y     : Fin m
  
---------------------------------------------------------------------------
-- Variable Elimination Lemma

module Variable-Elimination {m : ℕ} (σ : Sub (suc m) n) (x : Fin (suc m)) (t : Tm m) where
  helper
    : (y : Fin (suc m))
    → lookup (t for x ⨟ tabulate (lookup σ ∘ punchIn x)) y
      ≡ sub-for t x y ⟨ tabulate (`_ ∘ punchIn x) ⟩ ⟨ σ ⟩
  helper y = begin
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
      
  var-elim-pointwise
    : ` x ≈ punchInTm x t $ σ
    → (y : Fin (suc m))
    → lookup (t for x ⨟ tabulate (lookup σ ∘ punchIn x)) y ≡ lookup σ y
  var-elim-pointwise eq y with x ≟ y
  ... | yes refl = begin
    lookup (t for x ⨟ tabulate (lookup σ ∘ punchIn x)) x
      ≡⟨ helper x ⟩
    sub-for t x x ⟨ tabulate (`_ ∘ punchIn x) ⟩ ⟨ σ ⟩
      ≡⟨ (cong (λ t → t ⟨ tabulate _ ⟩ ⟨ σ ⟩) $ sub-t-for-x-x {t = t} {x}) ⟩
    t ⟨ tabulate (`_ ∘ punchIn x) ⟩ ⟨ σ ⟩
      ≡⟨ (cong _⟨ σ ⟩ $ rename-is-sub t) ⟩
    t ⟨ tabulate (punchIn x) ⟩ ⟨ σ ⟩
      ≡⟨ sym eq ⟩
    lookup σ x
      ∎
  ... | no ¬p    = begin
    lookup (t for x ⨟ tabulate (lookup σ ∘ punchIn x)) y
      ≡⟨ helper y ⟩
    sub-for t x y ⟨ tabulate (`_ ∘ punchIn x) ⟩ ⟨ σ ⟩
      ≡⟨ (cong (λ t → t ⟨ tabulate _ ⟩ ⟨ σ ⟩) $ sub-t-for-x-y ¬p) ⟩
    ` punchOut ¬p ⟨ tabulate (`_ ∘ punchIn x) ⟩ ⟨ σ ⟩
      ≡⟨ cong (_⟨ σ ⟩) (lookup∘tabulate (`_ ∘ punchIn x) _) ⟩
    ` punchIn x (punchOut ¬p) ⟨ σ ⟩
      ≡⟨ cong (lookup σ) (F.punchIn-punchOut ¬p) ⟩
    lookup σ y
      ∎

  var-elim
    : ` x ≈ punchInTm x t $ σ
    → t for x ⨟ tabulate (lookup σ ∘ punchIn x) ≡ σ 
  var-elim eq = begin
    t for x ⨟ tabulate (lookup σ ∘ punchIn x)
      ≡⟨ (sym $ tabulate∘lookup _) ⟩
    tabulate (lookup (t for x ⨟ tabulate (lookup σ ∘ punchIn x)))
      ≡⟨ tabulate-cong (var-elim-pointwise eq) ⟩
    tabulate (lookup σ)
      ≡⟨ tabulate∘lookup σ ⟩
    σ
      ∎
open Variable-Elimination using (var-elim)

module _ {m : ℕ} {x : Fin (suc m)} where
  ≈-flexRigid∉
    : {t : Tm (suc m)}
    → (x∉ : x ∉ₜ t)
    → ` x ≈ t $ punchOutTm x∉ for x
  ≈-flexRigid∉ {t} x∉ = begin
    ` x ⟨ (punchOutTm x∉) for x ⟩
      ≡⟨ x⟨t/x⟩=t x ⟩
    punchOutTm x∉
      ≡⟨ sym (punchIn-t⟨u/x⟩=t (punchOutTm x∉)) ⟩
    punchInTm x (punchOutTm x∉) ⟨ (punchOutTm x∉) for x ⟩
      ≡⟨ (cong _⟨ punchOutTm x∉ for x ⟩ $ punchInTm-punchOutTm x∉) ⟩
    t ⟨ (punchOutTm x∉) for x ⟩
      ∎

  flexRigid∉-mgu
    : {t : Tm (suc m)}
    → (x∉ : x ∉ₜ t)
    → Min (` x ≈ t) (punchOutTm x∉ for x)
  flexRigid∉-mgu {t} x∉ = ≈-flexRigid∉ x∉ , λ σ eq →
    tabulate (lookup σ ∘ punchIn x) , sym (var-elim σ x _ (begin
      ` x ⟨ σ ⟩
        ≡⟨ eq  ⟩
      t ⟨ σ ⟩
        ≡⟨ (sym $ cong _⟨ σ ⟩ $ punchInTm-punchOutTm x∉) ⟩
      punchInTm x (punchOutTm x∉) ⟨ σ ⟩
        ∎))

----------------------------------------------------------------------
-- Correctness of amgu
----------------------------------------------------------------------
flex-mgu′
  : (x : Fin m) (t : Tm m) 
  → Dec (∃₂ λ n (ρ : AList m n) → Min (` x ≈ t) (toSub ρ))
flex-mgu′ {suc m} x t with x ∈ₜ? t
flex-mgu′ x (` y)     | yes (here refl) = yes (_ , id , id-minimal id (` y))
flex-mgu′ x (op′ _ _) | yes x∈ = no λ where
  (_ , σ , eq , min) → op≢var (unify-occur (toSub σ) x∈ eq)
... | no  x∉ = yes (_ , flexRigid∉ x∉ , minimal-⨟-id (_ for x) _ t (flexRigid∉-mgu x∉))

flex-mgu
  : (x : Fin m) (t : Tm m) 
  → Dec (∃₂ λ n (ρ : AList m n) → Min (` x ≈ t [ id ⨟_]) (toSub ρ))
flex-mgu x t = map′
  (map₂ $ map₂ (Min-[id⨟]₁ {ℕ} {Sub} {Tm} _ _))
  (map₂ $ map₂ (Min-[id⨟]₂ {ℕ} {Sub} {Tm} _ _))
  (flex-mgu′ x t) 

-- [TODO]: Tidy up these ugly proofs!!!

helper 
  : (t : Tm (suc m)) (x : Fin (suc m)) (r : Tm m)
  → (σ : AList m n) (ρ : Sub n l)
  → t ⟨ r for x ⨟ toSub σ ⨟ ρ ⟩ ≡ t ⟨ r for x ⟩ ⟨ toSub σ ⨟ ρ ⟩
helper t x r σ ρ = begin
  t ⟨ r for x ⨟ toSub σ ⨟ ρ ⟩
    ≡⟨ cong (t ⟨_⟩) (⨟-assoc (r for x) (toSub σ) ρ) ⟩
  t ⟨ r for x ⨟ (toSub σ ⨟ ρ) ⟩
    ≡⟨ ⟨⟩-⨟ (r for x) (toSub σ ⨟ ρ) t ⟩
  t ⟨ r for x ⟩ ⟨ toSub σ ⨟ ρ ⟩
    ∎

t≈u⟨r/x⟩[σ]→t≈u[r/x,σ]
  : (t u : Tm (suc m)) (x : Fin (suc m)) (r : Tm m)
  → (σ : AList m n) (ρ : Sub n l)
  → t ⟨ r for x ⟩ ≈ u ⟨ r for x ⟩ $ (toSub σ) ⨟ ρ
  → t ≈ u $ toSub (r / x ∷ σ) ⨟ ρ
t≈u⟨r/x⟩[σ]→t≈u[r/x,σ] t u x r σ ρ eq = begin
  t ⟨ r for x ⨟ toSub σ ⨟ ρ ⟩
    ≡⟨ helper t x r σ ρ ⟩
  t ⟨ r for x ⟩ ⟨ toSub σ ⨟ ρ ⟩
    ≡⟨ eq ⟩
  u ⟨ r for x ⟩ ⟨ toSub σ ⨟ ρ ⟩
    ≡⟨ sym (helper u x r σ ρ) ⟩
  u ⟨ toSub (r / x ∷ σ) ⨟ ρ ⟩
    ∎

t≈u[r/x,σ]→t≈u⟨r/x⟩[σ]
  : (t u : Tm (suc m)) (x : Fin (suc m)) (r : Tm m)
  → (σ : AList m n) (ρ : Sub n l)
  → t ≈ u $ toSub (r / x ∷ σ) ⨟ ρ
  → t ⟨ r for x ⟩ ≈ u ⟨ r for x ⟩ $ (toSub σ) ⨟ ρ
t≈u[r/x,σ]→t≈u⟨r/x⟩[σ] t u x r σ ρ eq = begin
  t ⟨ r for x ⟩ ⟨ toSub σ ⨟ ρ ⟩
    ≡⟨ (sym $ helper t x r σ ρ) ⟩
  t ⟨ r for x ⨟ toSub σ ⨟ ρ ⟩
    ≡⟨ eq ⟩
  u ⟨ r for x ⨟ toSub σ ⨟ ρ ⟩
    ≡⟨ helper u x r σ ρ ⟩
  u ⟨ r for x ⟩ ⟨ toSub σ ⨟ ρ ⟩
    ∎ 

Lem₁
  : (t u : Tm (suc m)) (x : Fin (suc m)) (r : Tm m)
  → (σ : AList m n) (ρ : AList n l)
  → Min (t ⟨ r for x ⟩ ≈ u ⟨ r for x ⟩ [ toSub σ ⨟_]) (toSub ρ)
  → Min (t ≈ u [ toSub (r / x ∷ σ) ⨟_]) (toSub ρ)
Lem₁ t u x r σ ρ (Pρ , min) = t≈u⟨r/x⟩[σ]→t≈u[r/x,σ] t u x r σ (toSub ρ) Pρ ,
  λ g t≈u → min g (t≈u[r/x,σ]→t≈u⟨r/x⟩[σ] t u x r σ g t≈u)

Lem₂
  : (t u : Tm (suc m)) (x : Fin (suc m)) (r : Tm m)
  → (σ : AList m n) (ρ : AList n l)
  → Min (t ≈ u [ toSub (r / x ∷ σ) ⨟_]) (toSub ρ)
  → Min (t ⟨ r for x ⟩ ≈ u ⟨ r for x ⟩ [ toSub σ ⨟_]) (toSub ρ)
Lem₂ t u x r σ ρ (Pρ , min) = t≈u[r/x,σ]→t≈u⟨r/x⟩[σ] t u x r σ (toSub ρ) Pρ ,
  λ g t≈u → min g (t≈u⟨r/x⟩[σ]→t≈u[r/x,σ] t u x r σ g t≈u)


mutual
  amgu⁺ : (t u : Tm m) (σ : AList m n)
    → Dec (∃₂ λ l (ρ : AList n l)
        → Min (t ≈ u [ toSub σ ⨟_]) (toSub ρ))
  amgu⁺ (` x)      t     []          = flex-mgu x t
  amgu⁺ t          (` y) []          = map′
    (map₂ $ map₂ λ {ρ} → minimal≈-sym id (toSub ρ) (` y) t)
    (map₂ $ map₂ λ {ρ} → minimal≈-sym id (toSub ρ) t (` y))
    (flex-mgu y t)
  amgu⁺ (op′ i ts) (op′ j us) σ with i ≟∈ j
  ... | no ¬p    = no λ where (_ , ρ , p , _) → ¬p (op-inj₁₂ p)
  ... | yes refl = map′
    (map₂ $ map₂ λ (Pρ , min) → cong (op′ i) Pρ , λ γ Pγ → min γ (op-inj₃ Pγ))
    (map₂ $ map₂ λ (Pρ , min) → op-inj₃ Pρ , λ {_} γ Pγ → min γ (cong (op′ i) Pγ))
    (amguⁿ⁺ ts us σ)
  amgu⁺ t          u     (r / x ∷ σ) =
    map′
    (map₂ (λ (ρ , Minρ) → ρ , Lem₁ t u x r σ ρ Minρ))
    (map₂ (λ (ρ , Minρ) → ρ , Lem₂ t u x r σ ρ Minρ))
    (amgu⁺ (t ⟨ r for x ⟩) (u ⟨ r for x ⟩) σ)

  amguⁿ⁺ : (ts us : Tm m ^ l) (σ : AList m n)
    → Dec (∃₂ λ (l : ℕ) (ρ : AList n l)
        → Min (ts ≈ us [ toSub σ ⨟_]) $ toSub ρ)
  amguⁿ⁺ []       []       σ = yes (_ , [] , refl , λ ρ _ → ρ , sym (⨟-idₗ ρ))
  amguⁿ⁺ (t ∷ ts) (u ∷ us) σ with amgu⁺ t u σ
  ... | no ¬p = no {!!}
  ... | yes (_ , ρ , Pρ , min) with amguⁿ⁺ ts us (σ ⨟ ρ)
  ... | no ¬q = {!!}
  ... | yes p = {!!}

-- mutual
--   amguⁿ⁺ : (ts us : Tm m ^ l) (σ : AList m n)
--     → Dec (∃ₘ λ ρ → ts ≈ us by σ ⨟ ρ)
--   amguⁿ⁺ []       []       σ = yes (_ , [] , refl)
--   amguⁿ⁺ (t ∷ ts) (u ∷ us) σ with amgu⁺ t u σ
--   ... | no ¬p = no λ where (_ , ρ , eq) → ¬p (_ , ρ , V.∷-injectiveˡ eq)
--   ... | yes (l , ρ , eq) with amguⁿ⁺ ts us (σ ++ ρ)
--   ... | no ¬q = no λ
--     where
--       (l₁ , ρ₁ , eq′) → let (ρ₂ , eq₂) = f .proj₂ ρ₁ (V.∷-injectiveʳ eq′)
--         in ¬q (_ , ρ₂ , (begin
--           ts ⟨ (σ ⨟ ρ) ⨟ ρ₂ ⟩
--             ≡⟨ cong (ts ⟨_⟩) (⨟-assoc σ _ _) ⟩
--           ts ⟨ σ ⨟ (ρ ⨟ ρ₂) ⟩
--             ≡⟨ cong (λ ρ → ts ⟨ σ ⨟ ρ ⟩) (sym eq₂)  ⟩
--           ts ⟨ σ ⨟ ρ₁ ⟩
--             ≡⟨ V.∷-injectiveʳ eq′ ⟩
--           us ⟨ σ ⨟ ρ₁ ⟩
--             ≡⟨ cong (λ ρ → us ⟨ σ ⨟ ρ ⟩) eq₂ ⟩
--           us ⟨ σ ⨟ (ρ ⨟ ρ₂) ⟩
--             ≡⟨ cong (us ⟨_⟩) (sym $ ⨟-assoc σ _ _) ⟩
--           us ⟨ (σ ⨟ ρ) ⨟ ρ₂ ⟩
--             ∎))
--         where postulate f : Min (λ ρ → ts ≈ us by σ ⨟ ρ) ρ
--         -- TODO: Remove it and prove that amgu does produce the most general unifier.
--   ... | yes (_ , ρ′ , eq′) = yes (_ , ρ ⨟ ρ′ , (begin
--     (t ∷ ts) ⟨ σ ⨟ (ρ ⨟ ρ′) ⟩
--       ≡⟨ cong ((t ∷ ts) ⟨_⟩) (sym $ ⨟-assoc σ _ _) ⟩
--     (t ∷ ts) ⟨ (σ ⨟ ρ) ⨟ ρ′ ⟩
--       ≡⟨ cong₂ _∷_ (unifies-⨟ (σ ⨟ ρ) ρ′ t u eq) eq′ ⟩
--     (u ∷ us) ⟨ (σ ⨟ ρ) ⨟ ρ′ ⟩
--       ≡⟨ cong ((u ∷ us) ⟨_⟩) (⨟-assoc σ _ _) ⟩
--     (u ∷ us) ⟨ σ ⨟ (ρ ⨟ ρ′) ⟩
--       ∎))
