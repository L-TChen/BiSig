open import Prelude
open import Syntax.Simple.Description

module Syntax.Simple.Properties {D : Desc} where
open import Syntax.Simple.Term D

import      Data.Fin      as F
open import Data.Product.Properties
open import Data.List.Properties
open import Data.List.Relation.Unary.Any.Properties

private variable
  Γ Δ Ξ n : ℕ
  ts us   : Tm Ξ ^ n
  σ₁ σ₂   : Sub Γ Δ
  x y     : Fin Ξ

op-inj
  : {i : n ∈ D} {ts us : Tm Ξ ^ n}
  → op (n , i , ts) ≡ op (n , i , us)
  → ts ≡ us
op-inj refl = refl

module _ {σ₁ σ₂ : Sub Γ Δ} where mutual
  ≡-fv-inv : (A : Tm Γ)
    → ⟪ σ₁ ⟫ A ≡ ⟪ σ₂ ⟫ A
    → x ∈ fv A
    → σ₁ x ≡ σ₂ x
  ≡-fv-inv (` x)             eq (here refl) = eq
  ≡-fv-inv (op (Ξ , i , ts)) eq j = ≡-fv-invⁿ Ξ ts (op-inj eq) j

  ≡-fv-invⁿ : (n : ℕ) (As : Tm Γ ^ n)
    → subⁿ σ₁ _ As ≡ subⁿ σ₂ _ As
    → x ∈ fvⁿ As
    → σ₁ x ≡ σ₂ x
  ≡-fv-invⁿ (suc n) (A , As) p i with ++⁻ (fv A) i
  ... | inl j = ≡-fv-inv     A (,-injectiveˡ p) j
  ... | inr j = ≡-fv-invⁿ n As (,-injectiveʳ p) j 

-- module _ {σ₁ σ₂ : Sub Γ Δ} where mutual
--   ≡-fv-inv : (A : Tm Γ) 
--     → ⟪ σ₁ ⟫ A ≡ ⟪ σ₂ ⟫ A
--     → x ∈ fv A
--     → lookup σ₁ x ≡ lookup σ₂ x
--   ≡-fv-inv (` x)             p (here refl) = p
--   ≡-fv-inv (op (Ξ , i , ts)) p j = ≡-fv-invⁿ Ξ ts (op-inj p) j

--   ≡-fv-invⁿ : (n : ℕ) (As : Tm Γ ^ n)
--     → subⁿ σ₁ _ As ≡ subⁿ σ₂ _ As
--     → x ∈ fvⁿ As
--     → lookup σ₁ x ≡ lookup σ₂ x
--   ≡-fv-invⁿ (suc n) (A , As) p i with ++⁻ (fv A) i
--   ... | inl j = ≡-fv-inv      A  (,-injectiveˡ p) j
--   ... | inr j = ≡-fv-invⁿ n As (,-injectiveʳ p) j

module _ {σ₁ σ₂ : Sub Γ Δ} where mutual
  ≡-fv : (A : Tm Γ)
    → (∀ {x} → x ∈ fv A → σ₁ x ≡ σ₂ x)
    → ⟪ σ₁ ⟫ A ≡ ⟪ σ₂ ⟫ A
  ≡-fv (` x)             eq = eq (here refl)
  ≡-fv (op (Ξ , _ , ts)) eq = cong (λ ts → op (Ξ , _ , ts)) (≡-fvⁿ Ξ ts eq) 

  ≡-fvⁿ : (n : ℕ) (As : Tm Γ ^ n)
    → (∀ {x} → x ∈ fvⁿ  As → σ₁ x ≡ σ₂ x)
    → subⁿ σ₁ _ As ≡ subⁿ σ₂ _ As
  ≡-fvⁿ zero    _        _  = refl
  ≡-fvⁿ (suc n) (A , As) eq = cong₂ _,_
    (≡-fv A (λ k → eq (++⁺ˡ k))) (≡-fvⁿ n As λ k → eq (++⁺ʳ (fv A) k))

-- module _ {σ₁ σ₂ : Sub Γ Δ} where mutual
--   ≡-fv : (A : Tm Γ)
--     → (∀ {x} → x ∈ fv A → lookup σ₁ x ≡ lookup σ₂ x)
--     → ⟪ σ₁ ⟫ A ≡ ⟪ σ₂ ⟫ A
--   ≡-fv (` x)             p = p (here refl)
--   ≡-fv (op (n , _ , ts)) p = cong (λ ts → op (n , _ , ts)) (≡-fvⁿ n ts p)

--   ≡-fvⁿ : (n : ℕ) (As : Tm Γ ^ n)
--     → (∀ {x} → x ∈ fvⁿ  As → lookup σ₁ x ≡ lookup σ₂ x)
--     → subⁿ σ₁ _ As ≡ subⁿ σ₂ _ As
--   ≡-fvⁿ zero    _        _ = refl
--   ≡-fvⁿ (suc n) (A , As) p = cong₂ _,_
--     (≡-fv A λ k → p (++⁺ˡ k)) (≡-fvⁿ n As λ k → p (++⁺ʳ (fv A) k))

-- -- sub-inv₂
-- --   : ∀ {n} {i : n ∈ _}
-- --   → (ts : Tm Γ ^ n) (σ : SubFv (fvⁿ ts) Δ)
-- --   → ∀ {x} → (j k : x ∈ fvⁿ ts) 
-- --   → sub-inv₁ {i = i} ts σ j ≡ sub-inv₁ {i = i} ts σ k
-- -- sub-inv₂ {n = zero}  _        σ       () 
-- -- sub-inv₂ {n = suc n} (t , ts) (σ , p) j k with ++⁻ (fv t) j | ++⁻ (fv t) k
-- -- ... | inl ∈t  | inl ∈t′  = p (++⁺ˡ ∈t) (++⁺ˡ ∈t′)
-- -- ... | inl ∈t  | inr ∈ts  = p (++⁺ˡ ∈t) (++⁺ʳ (fv t) ∈ts)
-- -- ... | inr ∈ts | inl ∈t   = p (++⁺ʳ (fv t) ∈ts) (++⁺ˡ ∈t)
-- -- ... | inr ∈ts | inr ∈ts′ = p (++⁺ʳ (fv t) ∈ts) (++⁺ʳ (fv t) ∈ts′)


SubFv : List (Fin Ξ) → ℕ → Set
SubFv xs Δ = Σ[ ys ∈ List (Fin _ × Tm Δ) ] map proj₁ ys ≡ xs -- Vec (Tm Δ) (length xs)

Covered : {Ξ : ℕ} → List (Fin Ξ) → Set
Covered xs = (x : Fin _) → x ∈ xs

-- -- sub-inv₁
-- --   : ∀ {n} {i : n ∈ _} → (ts : Tm Γ ^ n)
-- --   → SubFv (fvⁿ ts) Δ
-- --   → SubFv (fv (op (n , i , ts))) Δ
-- -- sub-inv₁ {n = zero}  _        σ ()
-- -- sub-inv₁ {n = suc n} (t , ts) σ j with ++⁻ (fv t) j
-- -- ... | inl ∈t  = σ (++⁺ˡ ∈t)
-- -- ... | inr ∈ts = σ (++⁺ʳ (fv t) ∈ts)

-- -- fromSub : {xs : List (Fin Ξ)}
-- --   → (∀ x → x ∈ xs)
-- --   → Sub Ξ Δ
-- --   → SubFv xs Δ
-- -- fromSub ∀x σ {x} _ = V.lookup σ x

-- -- lem : {xs : List (Fin Ξ)}
-- --   → (p : ∀ x → x ∈ xs)
-- --   → (σ : SubFv xs Δ)
-- --   → ∀ {x} (i : x ∈ xs)
-- --   → fromSub p (toSub p σ) i ≡ σ i
-- -- lem {suc Ξ} {xs = zero ∙ xs} p σ {zero}  i = {!   !}
-- -- lem {suc Ξ} {xs = zero ∙ xs} p σ {suc y} i = {!   !}
-- -- lem {suc Ξ} {xs = suc x ∙ xs} p σ {y}    i = {!   !}

-- -- mutual
-- --   subByFv : (A : Tm Γ)
-- --     → SubFv (fv A) Δ
-- --     → Tm Δ
-- --   subByFv (` x)             σ = σ {x} (here refl)
-- --   subByFv (op (n , i , ts)) σ = op (n , i , subByFvⁿ ts σ)

-- --   subByFvⁿ : (A : Tm Ξ ^ n)
-- --     → SubFv (fvⁿ A) Δ
-- --     → Tm Δ ^ n
-- --   subByFvⁿ {n = zero}  _        _ = _
-- --   subByFvⁿ {n = suc n} (t , ts) σ =
-- --     subByFv t (σ ∘ ++⁺ˡ) , subByFvⁿ ts (σ ∘ ++⁺ʳ (fv t))

-- -- mutual
-- --   closed-subst-invariant
-- --     : (A : Tm Γ)
-- --     → fv A ≡ ∅
-- --     → ⟪ σ₁ ⟫ A ≡ ⟪ σ₂ ⟫ A
-- --   closed-subst-invariant (op (n , i , ts)) p =
-- --     cong (λ ts → op (n , i , ts)) (closed-subst-invariantMap ts p)

-- --   closed-subst-invariantMap : {n : ℕ}
-- --     → (As : Tm Γ ^ n)
-- --     → fvMap As ≡ ∅
-- --     → subMap σ₁ n As ≡ subMap σ₂ n As
-- --   closed-subst-invariantMap {n = zero}  _        _ = refl
-- --   closed-subst-invariantMap {n = suc n} (t , ts) p =
-- --     cong₂ _,_ (closed-subst-invariant t (++-conicalˡ (fv t) (fvMap ts) p)) (closed-subst-invariantMap ts (++-conicalʳ (fv t) (fvMap ts) p))
