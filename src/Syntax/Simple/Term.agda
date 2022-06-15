open import Prelude
open import Syntax.Simple.Description

module Syntax.Simple.Term (D : Desc) where

import      Data.Fin      as F
open import Data.List using  (_++_)
open import Data.Vec  hiding (_++_)

private variable
  Ξ Δ : ℕ
  n m l : ℕ
  A B : Set

infix 9 `_
data Tm : ℕ → Set where
  `_ : Fin      ⇒₁ Tm
  op : ⟦ D ⟧ Tm ⇒₁ Tm

Tm₀ : Set
Tm₀ = Tm 0

Tms : ℕ → Set
Tms Ξ = List (Tm Ξ)

Ren : (n m : ℕ) → Set
Ren n m = Fin n → Fin m

module _ {n m : ℕ} (f : Ren n m) where mutual
  rename : Tm n → Tm m
  rename (` x)  = ` f x
  rename (op (_ , i , ts)) = op (_ , i , renameMap _ ts)

  renameMap : (l : ℕ)
    → Tm n ^ l → Tm m ^ l
  renameMap zero    _        = _
  renameMap (suc n) (t , ts) = rename t , renameMap n ts
    
Sub : (A B : ℕ) → Set
Sub A B = Vec (Tm B) A

Sub₀ : (Ξ : ℕ) → Set
Sub₀ Ξ = Sub Ξ 0

module _ {A B : ℕ} (σ : Sub A B) where mutual
  sub : Tm A → Tm B
  sub (` x)  = lookup σ x
  sub (op (_ , i , ts)) = op (_ , i , subMap _ ts)

  subMap : ∀ n
    → Tm A ^ n → Tm B ^ n
  subMap zero    _        = _
  subMap (suc n) (t , ts) = sub t , subMap n ts

infixr 8 ⟨_⟩_ ⟪_⟫_

⟨_⟩_ : {A B : ℕ} → Ren A B → Tm A → Tm B
⟨ f ⟩ t = rename f t

⟪_⟫_ : {A B : ℕ} → Sub A B → Tm A → Tm B
⟪ f ⟫ t = sub f t

module _ {X : ℕ → Set} (α : (D -Alg) X) where mutual
  fold : Tm ⇒₁ X
  fold (` x)  = α .var x
  fold (op (_ , i , ts)) = α .alg (_ , i , foldMap _ ts)

  foldMap : ∀ {A : ℕ} n → Tm A ^ n → X A ^ n
  foldMap zero    _        = _
  foldMap (suc n) (t , ts) = fold t , foldMap n ts

mutual
  fv : Tm Ξ → List (Fin Ξ)
  fv (` x)  = x ∙ ∅
  fv (op (n , i , ts)) = fvMap ts

  fvMap : Tm Ξ ^ n → List (Fin Ξ)
  fvMap {n = zero}  _        = ∅
  fvMap {n = suc n} (t , ts) = fv t ++ fvMap ts

mutual
  _≟_ : (t u : Tm Ξ) → Dec (t ≡ u)
  (` x) ≟ (` y) with  x F.≟ y
  ... | yes p = yes (cong `_ p)
  ... | no ¬p = no λ where refl → ¬p refl
  op (D , i , ts) ≟ op (_ , j , us) with i ≟∈ j
  ... | no ¬p = no λ where refl → ¬p refl
  ... | yes refl with compareMap ts us
  ... | no ¬q = no λ where refl → ¬q refl
  ... | yes q = yes (cong (λ ts → op (D , i , ts)) q)
  (` x) ≟ op u  = no λ ()
  op x  ≟ (` y) = no λ ()

  compareMap : (ts us : Tm Ξ ^ n) → Dec (ts ≡ us)
  compareMap {n = zero}  _        _        = yes refl
  compareMap {n = suc n} (t , ts) (u , us) with t ≟ u
  ... | no ¬p = no λ where refl → ¬p refl
  ... | yes p with compareMap ts us 
  ... | no ¬q = no λ where refl → ¬q refl
  ... | yes q = yes (cong₂ _,_ p q)

_≟s_ : (σ σ′ : Sub Ξ Δ) → Dec (σ ≡ σ′)
[]      ≟s []      = yes refl
(A ∷ Δ) ≟s (B ∷ Γ) with A ≟ B
... | no ¬p =  no λ where refl → ¬p refl
... | yes p with Δ ≟s Γ 
... | no ¬q =  no λ where refl → ¬q refl
... | yes q =  yes (cong₂ _∷_ p q)