{-# OPTIONS --safe #-}

open import Prelude

import Syntax.Simple.Description  as S
import Syntax.BiTyped.Description as B

module Syntax.BiTyped.Raw.Term {SD : S.Desc}
  (Id : Set) (D : B.Desc SD) where

open import Syntax.Simple SD

open import Syntax.BiTyped.Raw.Functor SD Id

open B SD

private variable
  n m l : ℕ
  Ξ Θ Θ₁ Θ₂ : ℕ
  d : Mode

infix 5 _⦂_

data Raw (Θ : ℕ) : Mode → Set where
  `_  : (x : Id)                     → Raw Θ Syn
  _⦂_ : (t : Raw Θ Chk) (A : TExp Θ) → Raw Θ Syn
  _↑  : (t : Raw Θ Syn)              → Raw Θ Chk
  op  : ⟦ D ⟧ (Raw Θ) d              → Raw Θ d

Raw⇐ Raw⇒ : ℕ → Set
Raw⇐ Θ = Raw Θ Chk
Raw⇒ Θ = Raw Θ Syn

module _ (ρ : TRen Θ₁ Θ₂) where mutual
  trename : Raw Θ₁ d → Raw Θ₂ d
  trename (` x)   = ` x
  trename (t ⦂ A) = trename t ⦂ rename ρ A
  trename (t ↑)   = trename t ↑
  trename (op (i , refl , ts))  = op (i , refl , trenameⁿ _ ts)

  trenameⁿ : (D : ArgsD Ξ)
    → ⟦ D ⟧ᵃˢ (Raw Θ₁) → ⟦ D ⟧ᵃˢ (Raw Θ₂)
  trenameⁿ []      _        = _
  trenameⁿ (Δ ⊢[ _ ] A ∷ D) (t , ts) = trenameᵃ Δ t , trenameⁿ D ts

  trenameᵃ : (Δ : TExps Ξ)
    → ⟦ Δ ⟧ᵃ (Raw Θ₁ d) → ⟦ Δ ⟧ᵃ (Raw Θ₂ d)
  trenameᵃ []      t       = trename t
  trenameᵃ (A ∷ Δ) (x , t) = x , trenameᵃ Δ t

{-
twkˡ : m ≤ n → Raw m d → Raw n d
twkˡⁿ : {D : ArgsD k} → m ≤ n
  → ⟦ D ⟧ᵃˢ (Raw m) → ⟦ D ⟧ᵃˢ (Raw n)
twkˡᵃ : {D : TExps k} → m ≤ n
  → ⟦ D ⟧ᵃ (Raw m d) → ⟦ D ⟧ᵃ (Raw n d)

twkˡ  (less-than-or-equal refl) = trename  injectˡ
twkˡⁿ (less-than-or-equal refl) = trenameⁿ injectˡ _ -- trenameⁿ injectˡ
twkˡᵃ (less-than-or-equal refl) = trenameᵃ injectˡ _

twkᵐ : (m n {l} : ℕ) → Raw (m + l) d → Raw (m + n + l) d
twkᵐⁿ : {D : ArgsD k} (m n {l} : ℕ)
  → ⟦ D ⟧ᵃˢ (Raw (m + l)) → ⟦ D ⟧ᵃˢ (Raw (m + n + l))
twkᵐᵃ : {D : TExps k} (m n {l} : ℕ)
  → ⟦ D ⟧ᵃ (Raw (m + l) d) → ⟦ D ⟧ᵃ (Raw (m + n + l) d)

twkᵐ  m n = trename  (insert-mid m n)
twkᵐⁿ m n = trenameⁿ (insert-mid m n) _
twkᵐᵃ m n = trenameᵃ (insert-mid m n) _
-}

module _ (σ : TSub m n) where mutual
  tsub : Raw m d → Raw n d
  tsub (` x)   = ` x
  tsub (t ⦂ A) = tsub t ⦂ sub σ A
  tsub (t ↑)   = tsub t ↑
  tsub (op (i , eq , ts)) = op (i , eq , tsubⁿ _ ts)

  tsubⁿ : (D : ArgsD Ξ)
    → ⟦ D ⟧ᵃˢ (Raw m) → ⟦ D ⟧ᵃˢ (Raw n)
  tsubⁿ []       _       = _
  tsubⁿ (A ∷ D) (t , ts) = tsubᵃ _ t , tsubⁿ _ ts

  tsubᵃ : (Δ : TExps Ξ)
    → ⟦ Δ ⟧ᵃ (Raw m d) → ⟦ Δ ⟧ᵃ (Raw n d)
  tsubᵃ []      t       = tsub t
  tsubᵃ (A ∷ Δ) (x , t) = x , tsubᵃ _ t

module _ {Θ : ℕ} where mutual
  tsub-id : (t : Raw Θ d)
    → tsub id t ≡ t
  tsub-id (` x)              = refl
  tsub-id (t ⦂ A)            =
    cong₂ _⦂_ (tsub-id t) (⟨⟩-id {ℕ} {TSub} A)
  tsub-id (t ↑)              = cong _↑ (tsub-id t)
  tsub-id (op (i , eq , ts)) =
    cong (λ ts → op (i , eq , ts)) (tsubⁿ-id ts)

  tsubⁿ-id : {D : ArgsD Ξ}
    → (ts : ⟦ D ⟧ᵃˢ (Raw Θ))
    → tsubⁿ id _ ts ≡ ts
  tsubⁿ-id {D = []}     ts       = refl
  tsubⁿ-id {D = D ∷ Ds} (t , ts) = cong₂ _,_ (tsubᵃ-id t) (tsubⁿ-id ts)

  tsubᵃ-id : {Δ : TExps Ξ}
    → (t : ⟦ Δ ⟧ᵃ (Raw Θ d))
    → tsubᵃ id _ t ≡ t
  tsubᵃ-id {Δ = []}             = tsub-id
  tsubᵃ-id {Δ = D ∷ Ds} (x , t) = cong (x ,_) (tsubᵃ-id t)

module _ (σ : TSub m n) (ρ : TSub n l) where mutual
  tsub-⨟ : (t : Raw m d)
    → tsub (σ ⨟ ρ) t ≡ tsub ρ (tsub σ t)
    
  tsub-⨟ (` x)   = refl
  tsub-⨟ (t ⦂ A) = cong₂ _⦂_ (tsub-⨟ t) (⟨⟩-⨟ σ ρ A)
  tsub-⨟ (t ↑)   = cong _↑ (tsub-⨟ t)
  tsub-⨟ (op (i , eq , ts)) = cong (λ ts → op (i , eq , ts)) (tsubⁿ-⨟ ts)

  tsubⁿ-⨟ : {D : ArgsD Ξ}
    → (ts : ⟦ D ⟧ᵃˢ (Raw m))
    → tsubⁿ (σ ⨟ ρ) _ ts ≡ tsubⁿ ρ _ (tsubⁿ σ _ ts)
  tsubⁿ-⨟ {D = []}     ts       = refl
  tsubⁿ-⨟ {D = D ∷ Ds} (t , ts) = cong₂ _,_ (tsubᵃ-⨟ t) (tsubⁿ-⨟ ts)

  tsubᵃ-⨟ : {Δ : TExps Ξ}
    → (t : ⟦ Δ ⟧ᵃ (Raw m d))
    → tsubᵃ (σ ⨟ ρ) _ t ≡ tsubᵃ ρ _ (tsubᵃ σ _ t)
  tsubᵃ-⨟ {Δ = []}            = tsub-⨟
  tsubᵃ-⨟ {Δ = _ ∷ _} (x , t) = cong (x ,_) (tsubᵃ-⨟ t)

module _ {d : Mode} (σ : AList m n) (ρ : AList n l) where mutual
  tsubₐ-⨟ : (t : Raw m d)
    → tsub (toSub (σ ⨟ ρ)) t ≡ tsub (toSub ρ) (tsub (toSub σ) t)
  tsubₐ-⨟ t = begin
    tsub (toSub (σ ⨟ ρ)) t
      ≡⟨ cong (λ σ → tsub σ t) (toSub-++ σ ρ) ⟩
    tsub (toSub σ ⨟ toSub ρ) t
      ≡⟨ tsub-⨟ (toSub σ) (toSub ρ) t ⟩
    _ ∎ 
    where open ≡-Reasoning

instance
  RawSubIsPresheaf : IsPresheaf λ m → Raw m d
  RawSubIsPresheaf ._⟨_⟩ t σ   = tsub σ t
  RawSubIsPresheaf .⟨⟩-id      = tsub-id
  RawSubIsPresheaf .⟨⟩-⨟ σ ρ t = tsub-⨟ σ ρ t
 
  RawⁿSubIsPresheaf : {AD : ArgsD Ξ} → IsPresheaf λ m → ⟦ AD ⟧ᵃˢ (Raw m)
  RawⁿSubIsPresheaf ._⟨_⟩ t σ   = tsubⁿ σ _ t
  RawⁿSubIsPresheaf .⟨⟩-id      = tsubⁿ-id
  RawⁿSubIsPresheaf .⟨⟩-⨟ σ ρ t = tsubⁿ-⨟ σ ρ t

--  RawᵃSubIsPresheaf : {Θ : TExps Ξ} → IsPresheaf λ m → ⟦ Θ ⟧ᵃ (Raw m d)
--  RawᵃSubIsPresheaf ._⟨_⟩ t σ   = tsubᵃ σ t
--  RawᵃSubIsPresheaf .⟨⟩-id      = tsubᵃ-id
--  RawᵃSubIsPresheaf .⟨⟩-⨟ σ ρ t = tsubᵃ-⨟ σ ρ t

  RawAListIsPresheaf : IsPresheaf λ m → Raw m d
  RawAListIsPresheaf ._⟨_⟩ t σ   = tsub (toSub σ) t
  RawAListIsPresheaf .⟨⟩-id      = tsub-id
  RawAListIsPresheaf .⟨⟩-⨟       = tsubₐ-⨟
