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
  rename (op x) = op (renameMap _ x)

  renameMap : (D : Desc)
    → (⟦ D ⟧ Tm) n → (⟦ D ⟧ Tm) m
  renameMap (n ∷ ns) (inl x) = inl (renameMapⁿ n x)
  renameMap (h ∷ ns) (inr y) = inr (renameMap ns y)

  renameMapⁿ : (l : ℕ)
    → Tm n ^ l → Tm m ^ l
  renameMapⁿ zero    _        = _
  renameMapⁿ (suc n) (t , ts) = rename t , renameMapⁿ n ts
    
Sub : (A B : ℕ) → Set
Sub A B = Vec (Tm B) A

Sub₀ : (Ξ : ℕ) → Set
Sub₀ Ξ = Sub Ξ 0

module _ {A B : ℕ} (σ : Sub A B) where mutual
  sub : Tm A → Tm B
  sub (` x)  = lookup σ x
  sub (op x) = op (subMap _ x) 

  subMap : ∀ as
    → (⟦ as ⟧ Tm) A → (⟦ as ⟧ Tm) B
  subMap (a ∷ as) (inl ts) = inl (subMapⁿ a ts)
  subMap (a ∷ as) (inr y)  = inr (subMap as y)

  subMapⁿ : ∀ n
    → Tm A ^ n → Tm B ^ n
  subMapⁿ zero    _        = _
  subMapⁿ (suc n) (t , ts) = sub t , subMapⁿ n ts

infixr 8 ⟨_⟩_ ⟪_⟫_

⟨_⟩_ : {A B : ℕ} → Ren A B → Tm A → Tm B
⟨ f ⟩ t = rename f t

⟪_⟫_ : {A B : ℕ} → Sub A B → Tm A → Tm B
⟪ f ⟫ t = sub f t

module _ {X : ℕ → Set} (α : (D -Alg) X) where mutual
  fold : Tm ⇒₁ X
  fold (` x)  = α .var x
  fold (op t) = α .alg (foldMap _ t)

  foldMap : ∀ D → ⟦ D ⟧ Tm ⇒₁ ⟦ D ⟧ X
  foldMap (D ∷ Ds) (inl x) = inl (foldMapⁿ D x)
  foldMap (D ∷ Ds) (inr y) = inr (foldMap Ds y)

  foldMapⁿ : ∀ {A : ℕ} n → Tm A ^ n → X A ^ n
  foldMapⁿ zero    _        = _
  foldMapⁿ (suc n) (t , ts) = fold t , foldMapⁿ n ts