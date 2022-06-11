open import Prelude
open import Syntax.Simple.Description

module Syntax.Simple.Term (D : Desc) where

open import Data.Vec

private variable
  A B : Set

infix 9 `_
data Tm : ℕ → Set where
  `_ : Fin      ⇒₁ Tm
  op : ⟦ D ⟧ Tm ⇒₁ Tm

Tm₀ : Set
Tm₀ = Tm 0

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