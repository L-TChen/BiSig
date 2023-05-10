{-# OPTIONS --safe #-}

open import Prelude

import Syntax.Simple.Description  as S
open import Syntax.BiTyped.Description as B

module Syntax.BiTyped.Raw.Term {SD : S.Desc} (Id : Set) (D : B.Desc {SD}) where

open import Syntax.Simple.Term        SD
  renaming (Tm to TExp)
open import Syntax.Simple.Association SD

open import Syntax.BiTyped.Raw.Functor {SD} Id

private variable
  n m k l : ℕ
  mod : Mode

infix 4 _⦂_

data Raw (m : ℕ) : Mode → Set where
  `_  : (x : Id)                       → Raw m Infer
  _⦂_ : (t : Raw m Check) (A : TExp m) → Raw m Infer
  _↑  : (t : Raw m Infer)              → Raw m Check
  op  : ⟦ D ⟧ (Raw m) mod              → Raw m mod

Raw⇇ Raw⇉ : ℕ → Set
Raw⇇ m = Raw m Check
Raw⇉ m = Raw m Infer

module _ (ρ : Ren m n) where mutual
  trename : Raw m mod → Raw n mod
  trename (` x)   = ` x
  trename (t ⦂ A) = trename t ⦂ rename ρ A
  trename (t ↑)   = trename t ↑
  trename (op (i , refl , ts))  = op (i , refl , trenameⁿ ts)

  trenameⁿ : {D : B.ArgsD k}
    → ⟦ D ⟧ᵃˢ (Raw m) → ⟦ D ⟧ᵃˢ (Raw n)
  trenameⁿ {D = []}     _        = _
  trenameⁿ {D = A ∷ D} (t , ts) = trenameᵃ t , trenameⁿ ts

  trenameᵃ : {D : List (TExp k)}
    → ⟦ D ⟧ᵃ (Raw m mod) → ⟦ D ⟧ᵃ (Raw n mod)
  trenameᵃ {D = []}     t       = trename t
  trenameᵃ {D = A ∷ D} (x , t) = x , trenameᵃ t

twkˡ : m ≤ n → Raw m mod → Raw n mod
twkˡⁿ : {D : B.ArgsD k} → m ≤ n
  → ⟦ D ⟧ᵃˢ (Raw m) → ⟦ D ⟧ᵃˢ (Raw n)
twkˡᵃ : {D : List (TExp k)} → m ≤ n
  → ⟦ D ⟧ᵃ (Raw m mod) → ⟦ D ⟧ᵃ (Raw n mod)

twkˡ  (less-than-or-equal refl) = trename  injectˡ
twkˡⁿ (less-than-or-equal refl) = trenameⁿ injectˡ
twkˡᵃ (less-than-or-equal refl) = trenameᵃ injectˡ

twkᵐ : (m n {l} : ℕ) → Raw (m + l) mod → Raw (m + n + l) mod
twkᵐⁿ : {D : B.ArgsD k} (m n {l} : ℕ)
  → ⟦ D ⟧ᵃˢ (Raw (m + l)) → ⟦ D ⟧ᵃˢ (Raw (m + n + l))
twkᵐᵃ : {D : List (TExp k)} (m n {l} : ℕ)
  → ⟦ D ⟧ᵃ (Raw (m + l) mod) → ⟦ D ⟧ᵃ (Raw (m + n + l) mod)

twkᵐ  m n = trename  (V.tabulate (insert-mid m n)) -- (insert-mid m n)
twkᵐⁿ m n = trenameⁿ (V.tabulate (insert-mid m n)) -- (insert-mid m n)
twkᵐᵃ m n = trenameᵃ (V.tabulate (insert-mid m n)) -- (insert-mid m n)

module _ (σ : Sub m n) where mutual
  tsub : Raw m mod → Raw n mod
  tsub (` x)   = ` x
  tsub (t ⦂ A) = tsub t ⦂ sub σ A
  tsub (t ↑)   = tsub t ↑
  tsub (op (i , eq , ts)) = op (i , eq , tsubⁿ ts)

  tsubⁿ : {D : B.ArgsD k}
    → ⟦ D ⟧ᵃˢ (Raw m) → ⟦ D ⟧ᵃˢ (Raw n)
  tsubⁿ {D = []}     _        = _
  tsubⁿ {D = A ∷ D} (t , ts) = tsubᵃ t , tsubⁿ ts

  tsubᵃ : {D : List (TExp k)}
    → ⟦ D ⟧ᵃ (Raw m mod) → ⟦ D ⟧ᵃ (Raw n mod)
  tsubᵃ {D = []}     t      = tsub t
  tsubᵃ {D = A ∷ D} (x , t) = x , tsubᵃ t

module _ {m : ℕ} where mutual
  tsub-id : (t : Raw m mod)
    → tsub id t ≡ t
  tsub-id (` x)              = refl
  tsub-id (t ⦂ A)            = cong₂ _⦂_ (tsub-id t) (⟨⟩-id {ℕ} {Sub} A)
  tsub-id (t ↑)              = cong _↑ (tsub-id t)
  tsub-id (op (i , eq , ts)) =
    cong (λ ts → op (i , eq , ts)) (tsubⁿ-id ts)

  tsubⁿ-id : {D : B.ArgsD k}
    → (ts : ⟦ D ⟧ᵃˢ (Raw m))
    → tsubⁿ id ts ≡ ts
  tsubⁿ-id {D = []}     ts       = refl
  tsubⁿ-id {D = D ∷ Ds} (t , ts) = cong₂ _,_ (tsubᵃ-id t) (tsubⁿ-id ts)

  tsubᵃ-id : {D : List (TExp k)}
    → (t : ⟦ D ⟧ᵃ (Raw m mod))
    → tsubᵃ id t ≡ t
  tsubᵃ-id {D = []}             = tsub-id
  tsubᵃ-id {D = D ∷ Ds} (x , t) = cong (x ,_) (tsubᵃ-id t)

module _ (σ : AList m n) (ρ : AList n l) where mutual
  tsub-⨟ : (t : Raw m mod)
    → tsub (toSub (σ ⨟ ρ)) t ≡ tsub (toSub ρ) (tsub (toSub σ) t)
  tsub-⨟ (` x)   = refl
  tsub-⨟ (t ⦂ A) = cong₂ _⦂_ (tsub-⨟ t) (⟨⟩-⨟ σ ρ A)
  tsub-⨟ (t ↑)   = cong _↑ (tsub-⨟ t)
  tsub-⨟ (op (i , eq , ts)) = cong (λ ts → op (i , eq , ts)) (tsubⁿ-⨟ ts)

  tsubⁿ-⨟ : {D : B.ArgsD k}
    → (ts : ⟦ D ⟧ᵃˢ (Raw m))
    → tsubⁿ (toSub (σ ⨟ ρ)) ts ≡ tsubⁿ (toSub ρ) (tsubⁿ (toSub σ) ts)
  tsubⁿ-⨟ {D = []}     ts       = refl
  tsubⁿ-⨟ {D = D ∷ Ds} (t , ts) = cong₂ _,_ (tsubᵃ-⨟ t) (tsubⁿ-⨟ ts)

  tsubᵃ-⨟ : {D : List (TExp k)}
    → (t : ⟦ D ⟧ᵃ (Raw m mod))
    → tsubᵃ (toSub (σ ⨟ ρ)) t ≡ tsubᵃ (toSub ρ) (tsubᵃ (toSub σ) t)
  tsubᵃ-⨟ {D = []}             = tsub-⨟
  tsubᵃ-⨟ {D = D ∷ Ds} (x , t) = cong (x ,_) (tsubᵃ-⨟ t)

instance
  RawAListIsPresheaf : {mod : Mode} → IsPresheaf λ m → Raw m mod
  RawAListIsPresheaf ._⟨_⟩ t σ   = tsub (toSub σ) t
  RawAListIsPresheaf .⟨⟩-id      = tsub-id
  RawAListIsPresheaf .⟨⟩-⨟ σ ρ t = tsub-⨟ σ ρ t


