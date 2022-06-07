open import Prelude
open import Syntax.Simple.Description

module Syntax.Simple.Term (D : Desc) where

private variable
  A B : Set

data Tm : Set → Set where
  `_ : id       ⇒₁ Tm
  op : ⟦ D ⟧ Tm ⇒₁ Tm

Tm₀ : Set
Tm₀ = Tm ⊥

module _ (f : A → B) where mutual
  rename : Tm A → Tm B
  rename (` x)  = ` f x
  rename (op x) = op (renameMap _ x)

  renameMap : (D : Desc)
    → (⟦ D ⟧ Tm) A → (⟦ D ⟧ Tm) B
  renameMap (n ∷ ns) (inl x) = inl (renameMapⁿ n x)
  renameMap (h ∷ ns) (inr y) = inr (renameMap ns y)

  renameMapⁿ : (n : ℕ)
    → Tm A ^ n → Tm B ^ n
  renameMapⁿ zero    _        = _
  renameMapⁿ (suc n) (t , ts) = rename t , renameMapⁿ n ts
    
Sub : (A B : Set) → Set
Sub A B = A → Tm B

module _ (f : Sub A B) where mutual
  subst : Tm A → Tm B
  subst (` x)  = f x
  subst (op x) = op (substMap _ x) 

  substMap : ∀ as
    → (⟦ as ⟧ Tm) A → (⟦ as ⟧ Tm) B
  substMap (a ∷ as) (inl ts) = inl (substMapⁿ a ts)
  substMap (a ∷ as) (inr y)  = inr (substMap as y)

  substMapⁿ : ∀ n
    → Tm A ^ n → Tm B ^ n
  substMapⁿ zero    _        = _
  substMapⁿ (suc n) (t , ts) = subst t , substMapⁿ n ts

infixr 8 ⟨_⟩_ ⟪_⟫_

⟨_⟩_ : (A → B) → Tm A → Tm B
⟨ f ⟩ t = rename f t

⟪_⟫_ : Sub A B → Tm A → Tm B
⟪ f ⟫ t = subst f t

module _ {X : Set → Set} (α : (D -Alg) X) where mutual
  fold : Tm ⇒₁ X
  fold (` x)  = α .var x
  fold (op t) = α .alg (foldMap _ t)

  foldMap : ∀ D → ⟦ D ⟧ Tm ⇒₁ ⟦ D ⟧ X
  foldMap (D ∷ Ds) (inl x) = inl (foldMapⁿ D x)
  foldMap (D ∷ Ds) (inr y) = inr (foldMap Ds y)

  foldMapⁿ : ∀ n → Tm A ^ n → X A ^ n
  foldMapⁿ zero    _        = _
  foldMapⁿ (suc n) (t , ts) = fold t , foldMapⁿ n ts

open import Syntax.Context Tm₀

TExp : Ctx → Set
TExp Ξ = Tm (∃ (_∈ Ξ))

flatten : {Ξ : Ctx} → TExp Ξ → Tm₀
flatten = ⟪ id ⟫_ ∘ rename proj₁