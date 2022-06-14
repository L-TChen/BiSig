open import Prelude
open import Syntax.Simple.Description

module Syntax.Simple.Properties {D : Desc} where
open import Syntax.Simple.Term D

import      Data.Fin      as F
open import Data.Vec as V using (lookup)
open import Data.Product.Properties
open import Data.List.Properties
open import Data.List.Relation.Unary.Any.Properties

private variable
  Γ Δ Ξ n : ℕ
  ts us : Tm Ξ ^ n
  σ₁ σ₂ : Sub Γ Δ
  x y   : Fin Ξ

op-inj
  : {i : n ∈ D} {ts us : Tm Ξ ^ n}
  → op (n , i , ts) ≡ op (n , i , us)
  → ts ≡ us
op-inj refl = refl

module _ (σ₁ σ₂ : Sub Γ Δ) where mutual
  ≡-fv-inv : (A : Tm Γ) 
    → ⟪ σ₁ ⟫ A ≡ ⟪ σ₂ ⟫ A
    → x ∈ fv A
    → lookup σ₁ x ≡ lookup σ₂ x
  ≡-fv-inv (` x)             p (here refl) = p
  ≡-fv-inv (op (Ξ , i , ts)) p j = ≡-fv-invMap Ξ ts (op-inj p) j

  ≡-fv-invMap : (n : ℕ) (As : Tm Γ ^ n)
    → subMap σ₁ _ As ≡ subMap σ₂ _ As
    → x ∈ fvMap As
    → lookup σ₁ x ≡ lookup σ₂ x
  ≡-fv-invMap (suc n) (A , As) p i with ++⁻ (fv A) i
  ... | inl j = ≡-fv-inv      A  (,-injectiveˡ p) j
  ... | inr j = ≡-fv-invMap n As (,-injectiveʳ p) j

module _ (σ₁ σ₂ : Sub Γ Δ) where mutual
  ≡-fv : (A : Tm Γ)
    → (∀ {x} → x ∈ fv A → lookup σ₁ x ≡ lookup σ₂ x)
    → ⟪ σ₁ ⟫ A ≡ ⟪ σ₂ ⟫ A
  ≡-fv (` x)             p = p (here refl)
  ≡-fv (op (n , _ , ts)) p = cong (λ ts → op (n , _ , ts)) (≡-fvMap n ts p)

  ≡-fvMap : (n : ℕ) (As : Tm Γ ^ n)
    → (∀ {x} → x ∈ fvMap As → lookup σ₁ x ≡ lookup σ₂ x)
    → subMap σ₁ _ As ≡ subMap σ₂ _ As
  ≡-fvMap zero    _        _ = refl
  ≡-fvMap (suc n) (A , As) p = cong₂ _,_
    (≡-fv A λ k → p (++⁺ˡ k)) (≡-fvMap n As λ k → p (++⁺ʳ (fv A) k))

mutual
  closed-subst-invariant
    : (A : Tm Γ)
    → fv A ≡ ∅
    → ⟪ σ₁ ⟫ A ≡ ⟪ σ₂ ⟫ A
  closed-subst-invariant (op (n , i , ts)) p =
    cong (λ ts → op (n , i , ts)) (closed-subst-invariantMap ts p)

  closed-subst-invariantMap : {n : ℕ}
    → (As : Tm Γ ^ n)
    → fvMap As ≡ ∅
    → subMap σ₁ n As ≡ subMap σ₂ n As
  closed-subst-invariantMap {n = zero}  _        _ = refl
  closed-subst-invariantMap {n = suc n} (t , ts) p =
    cong₂ _,_ (closed-subst-invariant t (++-conicalˡ (fv t) (fvMap ts) p)) (closed-subst-invariantMap ts (++-conicalʳ (fv t) (fvMap ts) p))